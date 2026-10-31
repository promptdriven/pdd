import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, readdirSync, rmSync, symlinkSync, existsSync, statSync, realpathSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { execFileSync, spawnSync } from 'node:child_process';
import { parseArgv, CommandInputError } from '../src/argument-parser.mjs';
import { PUBLIC_COMMAND_IDS, PUBLIC_COMMAND_MANIFEST } from '../src/command-catalog.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { renderCompletion } from '../src/completion.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const temp = t => { const p = mkdtempSync(join(tmpdir(), 'pdd-alpha-')); t.after(() => rmSync(p, { recursive: true, force: true })); return p; };
const capture = () => ({ text: '', write(value) { this.text += value; } });

// Wrong: deleting the adapter leaves private catalog/validator routes or unknown help succeeds.
test('ALPHA1: only local plans are admitted without Host disposition or forwarded arguments', () => {
  assert.deepEqual(PUBLIC_COMMAND_IDS, ['product.status', 'product.next', 'product.start', 'workflow.run', 'workflow.prove', 'workflow.done', 'workflow.evidence', 'workflow.ask', 'workflow.approve', 'workflow.changes', 'workflow.cancel', 'workflow.status', 'workflow.view', 'workflow.open', 'help', 'version', 'completion', 'workflow.list', 'check', 'lint', 'approve', 'try', 'jobs', 'contracts', 'contracts.sync', 'mcp', 'setup']);
  for (const argv of [[], ['--help'], ['-h'], ['help'], ['--version'], ['completion', 'bash'],
    ['completion', 'zsh'], ['jobs'], ['mcp'], ['setup'], ['workflow', 'list'], ['workflow', 'list', '--json'], ['workflow', '--help']]) {
    const input = [...argv], plan = parseArgv(input);
    assert.equal(plan.hostArgv, undefined); assert.equal(plan.host, undefined); assert.deepEqual(input, argv);
  }
  // G1: people call the skills in their own chat; pdd starts no session and no named-workflow chat.
  for (const argv of [['session'], ['session','--agent','claude','Draft a prompt'], ['workflow','feature'], ['workflow','bug','--agent','claude'], ['workflow','small-change','Fix it'],
    ['setup', 'now'], ['setup', '--json'], ['run', 'start', 'issue'], ['verify'], ['runtime', 'discover'],
    ['replay'], ['call'], ['tests'], ['doctor'], ['phone'], ['machine'], ['repo'], ['agents'], ['workbench'],
    ['unknown', '--help'], ['workflow', 'new', 'feature'], ['workflow', 'list', '--brief'],
    ['workflow', 'list', '--json', '--json'], ['workflow', 'list', 'extra'], ['completion', 'fish'],
    ['completion'], ['--version', 'extra'], ['--skill'], ['--skill', '--json'], ['help', 'runtime'], ['--help', 'extra'], ['\0']]) {
    assert.throws(() => parseArgv(argv), CommandInputError, JSON.stringify(argv));
  }
});

// Wrong: source-only smoke passes while packed dependencies, bin mappings or bundled guidance fail in a clean consumer.
test('ALPHA4: actual packed package runs every advertised local command without private Host network or auth', t => {
  const sandbox = temp(t), home = join(sandbox, 'home'), consumer = join(sandbox, 'consumer'), project = join(sandbox, 'project');
  for (const p of [home, consumer, project]) mkdirSync(p);
  const emptyConfig = join(sandbox, 'empty-user-npmrc'), globalConfig = join(sandbox, 'empty-global-npmrc');
  writeFileSync(emptyConfig, ''); writeFileSync(globalConfig, '');
  const env = { PATH: process.env.PATH, HOME: home, TMPDIR: sandbox,
    npm_config_cache: join(sandbox, 'cache'), npm_config_userconfig: emptyConfig, npm_config_globalconfig: globalConfig,
    npm_config_offline: 'true', npm_config_audit: 'false', npm_config_fund: 'false' };
  const pack = JSON.parse(execFileSync('npm', ['pack', '--ignore-scripts', '--json', '--pack-destination', sandbox],
    { cwd: root, env, encoding: 'utf8', timeout: 30000 }))[0];
  const archive = join(sandbox, pack.filename), names = pack.files.map(f => f.path);
  for (const required of ['bin/pdd.mjs', 'RUNBOOK.md', 'docs/prompting-guide.md', 'skills/pdd-prompting/SKILL.md',
    'src/workflow-runner.mjs', 'skills/pdd-feature/workflow.json', 'skills/pdd-bug/workflow.json', 'skills/pdd-small-change/workflow.json']) assert.ok(names.includes(required), required);
  for (const file of readdirSync(join(root, 'skills'), { recursive: true }))
    if (file.startsWith('pdd-') && statSync(join(root, 'skills', file)).isFile()) assert.ok(names.includes(`skills/${file}`), file);
  // RUNBOOK §21's installed examples require these six runnable scenarios; no native tests, fixtures or other test assets ship.
  assert.deepEqual(names.filter(name => name.startsWith('test/')).sort(), [
    'test/runtime/fake-database.json', 'test/runtime/fake-decision.json', 'test/runtime/fake-factory.json',
    'test/runtime/fake-files.json', 'test/runtime/fake-hash.json', 'test/runtime/fake-service.json'
  ]);
  assert.equal(names.some(name => name.includes('host-adapter') || /^(?:ops|infra|ui|\.pdd)\//.test(name) || name.startsWith('skills/pdd/') || name === 'src/guidance.mjs'), false);
  execFileSync('npm', ['install', '--prefix', consumer, archive, '--ignore-scripts', '--offline', '--no-audit', '--no-fund', '--package-lock=false'],
    { cwd: consumer, env, encoding: 'utf8', timeout: 30000 });
  const metadata = JSON.parse(readFileSync(join(root, 'package.json'))), packed = join(consumer, 'node_modules', metadata.name);
  const bin = join(consumer, 'node_modules/.bin/pdd'); assert.ok(existsSync(bin));
  const guard = join(sandbox, 'no-private-effects.mjs');
  writeFileSync(guard, `import fs from 'node:fs';import http from 'node:http';import https from 'node:https';import net from 'node:net';import child from 'node:child_process';import {syncBuiltinESMExports} from 'node:module';
const stop=()=>{throw Error('Forbidden private/network/process effect');};
for(const x of [http,https]){x.request=stop;x.get=stop;}net.connect=stop;net.createConnection=stop;globalThis.fetch=stop;
for(const key of ['spawn','spawnSync','exec','execFile','execSync','execFileSync','fork'])child[key]=stop;
for(const key of ['readFileSync','readdirSync','statSync','lstatSync']){const original=fs[key];fs[key]=function(path,...args){if(/(?:\\/toolbox\\/|\\/\\.ssh(?:\\/|$)|\\/credentials(?:\\/|$)|\\/\\.npmrc$)/.test(String(path)))stop();return original.call(this,path,...args);};}syncBuiltinESMExports();`);
  const run = (args, cwd = project) => spawnSync(process.execPath, ['--import', guard, bin, ...args],
    { cwd, env, encoding: 'utf8', timeout: 5000 });
  for (const argv of [[], ['--help'], ['-h'], ['help'], ['workflow', '--help'], ['workflow', 'list', '--help'], ['completion', '--help'], ['setup','--help'], ['workflow','start','--help'], ['workflow','done','--help'], ['workflow','approve','--help'], ['workflow','open','--help']]) {
    const answer = run(argv); assert.equal(answer.status, 0, answer.stderr); assert.equal(answer.stderr, '');
    assert.ok(answer.stdout.includes('pdd')); assert.doesNotMatch(answer.stdout, /pdd (?:run|verify|runtime|doctor|phone)\b/);
  }
  // help-teaches-pdd: root help and the prompting topic name the guide files of the installed package, not of the cwd.
  for (const argv of [['help'], ['help', 'prompting']]) {
    const answer = run(argv); assert.equal(answer.status, 0, answer.stderr); assert.equal(answer.stderr, '');
    for (const file of ['docs/prompting-guide.md', 'RUNBOOK.md']) {
      const path = answer.stdout.split('\n').find(line => line.endsWith(`/${file}`))?.replace(/^[^/]*/, '');
      assert.equal(path, join(realpathSync(packed), file)); assert.ok(existsSync(path), file);
    }
  }
  const version = run(['--version']); assert.equal(version.status, 0); assert.equal(version.stdout, `${metadata.version}\n`);
  const skill = run(['--skill']); assert.equal(skill.status, 2); assert.equal(skill.stdout, '');
  const empty = run(['workflow', 'list', '--json']); assert.equal(empty.status, 0,empty.stderr);
  assert.deepEqual(JSON.parse(empty.stdout).workflows.map(w=>w.name),['bug','feature','product','small-change']);assert.equal(JSON.parse(empty.stdout).default,null);
  const recipes = run(['workflow', 'list', '--json'], packed); assert.equal(recipes.status, 0);
  assert.deepEqual(JSON.parse(recipes.stdout).workflows.map(w => w.name), ['bug', 'feature', 'product', 'small-change']);
  const human = run(['workflow', 'list'], packed); assert.equal(human.status, 0); assert.ok(human.stdout.includes('feature'));assert.ok(human.stdout.includes('Listing starts no work.'));
  for (const shell of ['bash', 'zsh']) {
    const result = run(['completion', shell]); assert.equal(result.status, 0, result.stderr);
    assert.doesNotMatch(result.stdout, /\b(?:runtime|doctor|verify|phone|machine)\b/);
    const script = join(sandbox, `completion.${shell}`); writeFileSync(script, result.stdout);
    if (shell === 'bash') {
      const loaded = spawnSync('bash', ['--noprofile', '--norc', '-c', 'source "$1"; COMP_WORDS=(pdd workflow ""); COMP_CWORD=2; _pdd_complete; printf "%s\\n" "${COMPREPLY[@]}"', 'test', script], { env, encoding: 'utf8' });
      assert.equal(loaded.status, 0, loaded.stderr); assert.ok(loaded.stdout.split('\n').includes('list'));
      const selected=spawnSync('bash',['--noprofile','--norc','-c','source "$1"; COMP_WORDS=(pdd workflow bug --agent ""); COMP_CWORD=4; _pdd_complete; printf "%s\\n" "${COMPREPLY[@]}"','test',script],{env,encoding:'utf8'});
      assert.equal(selected.status,0,selected.stderr);assert.deepEqual(selected.stdout.trim().split('\n').sort(),['claude','codex']);
    } else {
      const loaded = spawnSync('zsh', ['-f', '-c', 'autoload -Uz compinit; compinit -D -i || exit 1; source "$1"; [[ $_comps[pdd] == _pdd ]] || exit 3; _describe() { print -rl -- "${choices[@]}"; }; words=(pdd workflow ""); CURRENT=3; _pdd', 'test', script], { env, encoding: 'utf8' });
      assert.equal(loaded.status, 0, loaded.stderr); assert.ok(loaded.stdout.split('\n').includes('list'));
      const selected=spawnSync('zsh',['-f','-c','autoload -Uz compinit; compinit -D -i || exit 1; source "$1"; _describe() { print -rl -- "${choices[@]}"; }; words=(pdd workflow feature --agent ""); CURRENT=5; _pdd','test',script],{env,encoding:'utf8'});
      assert.equal(selected.status,0,selected.stderr);assert.deepEqual(selected.stdout.trim().split('\n').sort(),['claude','codex']);
    }
  }
  for (const word of ['run', 'verify', 'runtime', 'replay', 'call', 'tests', 'doctor', 'phone', 'machine', 'repo', 'agents', 'workbench', 'unknown']) {
    for (const args of [[word], [word, '--help'], [word, '-h']]) {
      const result = run(args); assert.equal(result.status, 2, JSON.stringify(args)); assert.equal(result.stdout, ''); assert.ok(result.stderr.trim());
    }
  }
  for (const args of [['session'], ['session', '--agent', 'claude', 'Help'], ['workflow', 'feature'], ['workflow', 'bug', '--', 'Fix it']]) {
    const refused = run(args); assert.equal(refused.status, 2, args.join(' ')); assert.equal(refused.stdout, '');
  }
  assert.deepEqual(readdirSync(home), []); assert.deepEqual(readdirSync(project), []);
  assert.ok(PUBLIC_COMMAND_MANIFEST.length > 0);
});

// Wrong: runner routes reach the wrong export, drop parsed values, retry after a failure, or print an object instead of the message.
test('ALPHA7: each runner route calls its own export once with parsed values, cwd and package root, and prints the message', async () => {
  const cases = [
    [['workflow','start','feature','owner/repo#42','--agent','claude'], 'startRun', { name: 'feature', issue: 'owner/repo#42', agent: 'claude' }],
    [['workflow','start','small-change','1'], 'startRun', { name: 'small-change', issue: '1', agent: 'codex' }],
    [['workflow','start','bug','2','--base','round3/tipjar-workflow-base'], 'startRun', { name: 'bug', issue: '2', agent: 'codex', base: 'round3/tipjar-workflow-base' }],
    [['workflow','done','prompt-story','--summary','Story and cases written'], 'stepDone', { step: 'prompt-story', summary: 'Story and cases written' }],
    [['workflow','done','scope'], 'stepDone', { step: 'scope' }],
    [['workflow','approve'], 'approveRun', { ref: undefined }],
    [['workflow','ask','--','Should','-h','work?'], 'askPerson', { text: 'Should -h work?' }],
    [['workflow','approve','https://github.com/o/r/issues/7'], 'approveRun', { ref: 'https://github.com/o/r/issues/7' }],
    [['workflow','changes','7','use','--','--blue'], 'changeRun', { ref: '7', text: 'use --blue' }],
    [['workflow','cancel','o/r#7'], 'cancelRun', { ref: 'o/r#7' }],
    [['workflow','status'], 'runStatus', { ref: undefined }],
    [['workflow','status','--all','--json'], 'runStatus', { ref: undefined, all: true, json: true }],
    [['workflow','status','7','--cancelled'], 'runStatus', { ref: '7', cancelled: true }],
    [['workflow','open','7'], 'openRun', { ref: '7' }]];
  for (const [argv, name, input] of cases) {
    const calls = [], stdout = capture(), stderr = capture();
    const runner = { [name]: async value => { calls.push(value); return { exitCode: 0, message: `${name} ok` }; } };
    assert.equal(await runPdd(argv, { workflowRunner: runner, cwd: '/chosen', packageRoot: '/bundle', stdout, stderr }), 0, argv.join(' '));
    assert.deepEqual(calls, [{ ...input, cwd: '/chosen', packageRoot: '/bundle' }]);
    assert.equal(stdout.text, `${name} ok\n`); assert.equal(stderr.text, '');
  }
  const stderr = capture();
  assert.equal(await runPdd(['workflow','approve','7'], { workflowRunner: { approveRun: async () => ({ exitCode: 1, message: 'Only the person can approve.' }) }, stdout: capture(), stderr }), 1);
  assert.equal(stderr.text, 'Only the person can approve.\n');
});

// Wrong: malformed references/options reach effects, or an owner failure is retried.
test('ALPHA8: runner argument failures and invalid replies are finite without a second call', async () => {
  const invalid = [['workflow','run'],['workflow','run','../unknown','1'],['workflow','run','feature','0'],['workflow','run','feature','42','extra'],
    ['workflow','run','feature','42','--agent','other'],['workflow','run','bug','2','--base'],
    ['workflow','run','bug','2','--base','one','--base','two'],['workflow','done'],['workflow','done','Scope'],['workflow','done','scope','--summary'],
    ['workflow','approve','7','8'],['workflow','approve','a1234567-1234-4123-8123-123456789abc'],['workflow','changes','7'],['workflow','cancel'],
    ['workflow','open'],['workflow','resume','7'],['workflow','attach','7'],['workflow','status','7','--brief'],['workflow','status','--all','--all']];
  for (const args of invalid) assert.equal(await runPdd(args, { stdout: capture(), stderr: capture(), workflowRunner: new Proxy({}, { get: () => assert.fail('No runner') }) }), 2, args.join(' '));
  for (const answer of [undefined, { exitCode: NaN, message: 'no' }, { exitCode: 0, message: '' }]) {
    let calls = 0;
    assert.equal(await runPdd(['workflow','status'], { stdout: capture(), stderr: capture(), workflowRunner: { runStatus: async () => { calls++; return answer; } } }), 1); assert.equal(calls, 1);
  }
  let calls = 0;
  assert.equal(await runPdd(['workflow','open','7'], { stdout: capture(), stderr: capture(), workflowRunner: { openRun: async () => { calls++; throw Error('possible effect'); } } }), 1); assert.equal(calls, 1);
});


test('workflow evidence routes required saved summary file without progressing steps', async () => {
  const stdout = capture(), stderr = capture(); let input;
  const runner = { recordEvidence: async args => { input = args; return { exitCode: 0, message: 'Recorded saved evidence.' }; } };
  assert.equal(await runPdd(['workflow','evidence','17','--summary','/tmp/check.json'], { workflowRunner: runner, cwd: '/chosen', stdout, stderr }), 0);
  assert.equal(input.ref, '17'); assert.equal(input.summaryFile, '/tmp/check.json');
  input = null;
  assert.equal(await runPdd(['workflow','evidence','17'], { workflowRunner: runner, stdout, stderr }), 2);
  assert.equal(input, null);
});

test('Try accepts named local launchers while workflow agent choices stay bounded', () => {
  for (const name of ['Codex (work5)', 'Claude (work3)', 'codex', 'claude', 'gemini']) {
    const plan=parseArgv(['simulate','my-story','--agent',name]);
    assert.equal(plan.commandId,'try');assert.equal(plan.options['--agent'],name);
  }
  for (const args of [['simulate','--agent'],['simulate','--agent',''],['simulate','--agent','   '],['workflow','run','bug','42','--agent','Codex (work5)'],['workflow','run','bug','42','--agent','gemini']]) assert.throws(()=>parseArgv(args),CommandInputError);
  for (const shell of ['bash','zsh']) {
    const completion=renderCompletion(shell);
    assert.doesNotMatch(completion,/(?:try|sim|simulate):--agent\)/);
    assert.match(completion,/workflow:--agent\)/);
  }
});

test('2640 CLI parses and forwards --adopt-corpus exactly and retains startup exit 2',async t=>{
  const cwd=temp(t),stdout=capture(),stderr=capture();let input;
  const args=['workflow','run','replay','17','--base','main','--adopt-corpus','/approval folder/corpus.json'];
  assert.equal(parseArgv(args).options['--adopt-corpus'],'/approval folder/corpus.json');
  const code=await runPdd(args,{cwd,stdout,stderr,env:{HOME:cwd,PATH:''},workflowRunner:{startRun:async value=>{input=value;return {exitCode:2,message:'Cannot adopt (content-mismatch).'};}}});
  assert.equal(code,2);assert.equal(input.adoptCorpus,'/approval folder/corpus.json');assert.equal(input.name,'replay');assert.equal(input.base,'main');assert.match(stderr.text,/Cannot adopt/);assert.equal(stdout.text,'');
  for(const option of [[],[''],['a','--adopt-corpus','b']])assert.throws(()=>parseArgv(['workflow','run','replay','17','--adopt-corpus',...option]),CommandInputError);
  for(const shell of ['bash','zsh'])assert.match(renderCompletion(shell),/--adopt-corpus/);
});
