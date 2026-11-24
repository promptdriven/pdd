import './helpers/test-home.mjs';
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
import { bundleInstalledDependencies } from './helpers/pack-offline.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const temp = t => { const p = mkdtempSync(join(tmpdir(), 'pdd-alpha-')); t.after(() => rmSync(p, { recursive: true, force: true })); return p; };
const capture = () => ({ text: '', write(value) { this.text += value; } });

// Wrong: deleting the adapter leaves private catalog/validator routes or unknown help succeeds.
test('ALPHA1: only local plans are admitted without Host disposition or forwarded arguments', () => {
  assert.deepEqual(PUBLIC_COMMAND_IDS, ['setup', 'init', 'status', 'check', 'lint', 'prove', 'try', 'approve', 'files', 'owner', 'update', 'contracts', 'contracts.sync', 'jobs', 'mcp', 'upgrade', 'doctor', 'accounts', 'accounts.list', 'accounts.status', 'accounts.add', 'accounts.import', 'accounts.use', 'accounts.next', 'accounts.codex', 'accounts.sync', 'accounts.auto', 'accounts.pause', 'accounts.unpause', 'accounts.share', 'accounts.accept', 'accounts.unshare', 'accounts.leave', 'accounts.remove', 'accounts.log', 'product.status', 'product.next', 'product.start', 'product.contracts', 'graph', 'autopilot.doctor', 'autopilot.start', 'autopilot.suite', 'autopilot.status', 'autopilot.logs', 'autopilot.stop', 'autopilot.observe', 'autopilot.auto', 'autopilot.off', 'autopilot.trust', 'autopilot.untrust', 'autopilot.add', 'autopilot.release', 'autopilot.intake', 'autopilot.graph', 'autopilot.report', 'autopilot.regressions', 'autopilot.alerts', 'autopilot.alert', 'autopilot.check-base', 'metrics', 'metrics.stages', 'metrics.skills', 'metrics.full', 'metrics.on', 'metrics.off', 'completion', 'help', 'version', 'version.detailed']);
  for (const argv of [[], ['--help'], ['-h'], ['help'], ['--version'], ['completion', 'bash'],
    ['completion', 'zsh'], ['doctor'], ['doctor', '--json'], ['autopilot', 'doctor'], ['jobs'], ['mcp'], ['setup'], ['setup', '--skills-dir', '/tmp/s'], ['init'], ['status'], ['status', '--changed', '--json'], ['sim', 'demo'], ['product', '--help'], ['autopilot', '--help']]) {
    const input = [...argv], plan = parseArgv(input);
    assert.equal(plan.hostArgv, undefined); assert.equal(plan.host, undefined); assert.deepEqual(input, argv);
  }
  // G1: people call the skills in their own chat; pdd starts no session and no named-workflow chat.
  for (const argv of [['interface', 'draft'], ['session'], ['session','--agent','claude','Draft a prompt'], ['workflow','feature'], ['workflow','bug','--agent','claude'], ['workflow','small-change','Fix it'], ['workflow','list'], ['workflow','run','bug','1'],
    ['setup', 'now'], ['setup', '--json'], ['doctor', 'extra'], ['run', 'start', 'issue'], ['verify'], ['runtime', 'discover'],
    ['replay'], ['call'], ['tests'], ['phone'], ['machine'], ['repo'], ['agents'], ['workbench'],
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
  for (const required of ['bin/pdd.mjs', 'skills/pdd/SKILL.md', 'skills/pdd/references/prompting.md',
    'skills/pdd/references/stories.md', 'skills/pdd/references/verification.md', 'src/autopilot/job-rules.md']) assert.ok(names.includes(required), required);
  for (const file of readdirSync(join(root, 'skills'), { recursive: true }))
    if (file.startsWith('pdd/') && statSync(join(root, 'skills', file)).isFile()) assert.ok(names.includes(`skills/${file}`), file);
  // Installed examples require these six runnable scenarios; no native tests, fixtures or other test assets ship.
  assert.deepEqual(names.filter(name => name.startsWith('test/')).sort(), [
    'test/runtime/fake-database.json', 'test/runtime/fake-decision.json', 'test/runtime/fake-factory.json',
    'test/runtime/fake-files.json', 'test/runtime/fake-hash.json', 'test/runtime/fake-service.json'
  ]);
  assert.equal(names.some(name => name.includes('host-adapter') || /^(?:ops|infra|ui|\.pdd)\//.test(name) || name.startsWith('prompts/cli/') || name === 'src/guidance.mjs'), false);
  bundleInstalledDependencies(root, archive, sandbox);
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
  for (const argv of [[], ['--help'], ['-h'], ['help'], ['completion', '--help'], ['setup','--help'], ['doctor','--help'], ['init','--help'], ['status','--help'], ['lint','--help'], ['prove','--help'], ['test','--help'], ['approve','--help'], ['product','--help'], ['autopilot','--help']]) {
    const answer = run(argv); assert.equal(answer.status, 0, answer.stderr); assert.equal(answer.stderr, '');
    assert.ok(answer.stdout.includes('pdd')); assert.doesNotMatch(answer.stdout, /pdd (?:run|verify|runtime|phone)\b/);
  }
  // help-teaches-pdd: root help and the prompting topic name the skill and guide files of the installed package, not of the cwd.
  for (const argv of [['help'], ['help', 'prompting']]) {
    const answer = run(argv); assert.equal(answer.status, 0, answer.stderr); assert.equal(answer.stderr, '');
    for (const file of ['skills/pdd/SKILL.md', 'skills/pdd/references/prompting.md']) {
      const path = answer.stdout.split('\n').find(line => line.endsWith(`/${file}`))?.replace(/^[^/]*/, '');
      assert.equal(path, join(realpathSync(packed), file)); assert.ok(existsSync(path), file);
    }
  }
  const version = run(['--version']); assert.equal(version.status, 0); assert.equal(version.stdout, `${metadata.version}\n`);
  const skill = run(['--skill']); assert.equal(skill.status, 2); assert.equal(skill.stdout, '');
  for (const shell of ['bash', 'zsh']) {
    const result = run(['completion', shell]); assert.equal(result.status, 0, result.stderr);
    // Both top-level `pdd doctor` and `pdd autopilot doctor` are supported; excluded commands remain absent.
    const autopilotChoices = result.stdout.split('\n').filter(line => /^\s*autopilot\) choices=/.test(line));
    assert.equal(autopilotChoices.length, 1); assert.match(autopilotChoices[0], /\bdoctor\b/);
    assert.doesNotMatch(result.stdout.split('\n').filter(line => !line.includes('--kind)')).join('\n'), /\b(?:verify|phone|machine)\b|(?<!-)\bruntime\b/);
    const script = join(sandbox, `completion.${shell}`); writeFileSync(script, result.stdout);
    for (const context of ['root', 'autopilot']) {
      const probe = shell === 'bash'
        ? 'source "$1"; if [ "$2" = root ]; then COMP_WORDS=(pdd ""); COMP_CWORD=1; else COMP_WORDS=(pdd autopilot ""); COMP_CWORD=2; fi; _pdd_complete; printf "%s\\n" "${COMPREPLY[@]}"'
        : 'autoload -Uz compinit; compinit -D -i || exit 1; source "$1"; _describe() { print -rl -- "${choices[@]}"; }; if [[ $2 == root ]]; then words=(pdd ""); CURRENT=2; else words=(pdd autopilot ""); CURRENT=3; fi; _pdd';
      const completed = spawnSync(shell, [...(shell === 'bash' ? ['--noprofile', '--norc'] : ['-f']), '-c', probe, 'test', script, context], {env, encoding:'utf8'});
      assert.equal(completed.status, 0, completed.stderr);
      assert.equal(completed.stdout.trim().split('\n').includes('doctor'), true);
    }
    if (shell === 'bash') {
      const loaded = spawnSync('bash', ['--noprofile', '--norc', '-c', 'source "$1"; COMP_WORDS=(pdd product ""); COMP_CWORD=2; _pdd_complete; printf "%s\\n" "${COMPREPLY[@]}"', 'test', script], { env, encoding: 'utf8' });
      assert.equal(loaded.status, 0, loaded.stderr); assert.ok(loaded.stdout.split('\n').includes('status'));
      const selected=spawnSync('bash',['--noprofile','--norc','-c','source "$1"; COMP_WORDS=(pdd product start --agent ""); COMP_CWORD=4; _pdd_complete; printf "%s\\n" "${COMPREPLY[@]}"','test',script],{env,encoding:'utf8'});
      assert.equal(selected.status,0,selected.stderr);assert.deepEqual(selected.stdout.trim().split('\n').sort(),['agy','claude','codex','gemini']);
    } else {
      const loaded = spawnSync('zsh', ['-f', '-c', 'autoload -Uz compinit; compinit -D -i || exit 1; source "$1"; [[ $_comps[pdd] == _pdd ]] || exit 3; _describe() { print -rl -- "${choices[@]}"; }; words=(pdd product ""); CURRENT=3; _pdd', 'test', script], { env, encoding: 'utf8' });
      assert.equal(loaded.status, 0, loaded.stderr); assert.ok(loaded.stdout.split('\n').includes('status'));
      const selected=spawnSync('zsh',['-f','-c','autoload -Uz compinit; compinit -D -i || exit 1; source "$1"; _describe() { print -rl -- "${choices[@]}"; }; words=(pdd product start --agent ""); CURRENT=5; _pdd','test',script],{env,encoding:'utf8'});
      assert.equal(selected.status,0,selected.stderr);assert.deepEqual(selected.stdout.trim().split('\n').sort(),['agy','claude','codex','gemini']);
    }
  }
  for (const word of ['run', 'verify', 'runtime', 'replay', 'call', 'tests', 'phone', 'machine', 'repo', 'agents', 'workbench', 'unknown', 'workflow']) {
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

test('Try and product accept named local launchers; product completion keeps the built-in agent choices', () => {
  for (const name of ['Codex (work5)', 'Claude (work3)', 'codex', 'claude', 'gemini']) {
    const plan=parseArgv(['simulate','my-story','--agent',name]);
    assert.equal(plan.commandId,'try');assert.equal(plan.options['--agent'],name);
  }
  for (const args of [['simulate','--agent'],['simulate','--agent',''],['simulate','--agent','   '],['product','start','run-1','--agent'],['product','start','run-1','--agent',''],['product','start','run-1','--agent','   ']]) assert.throws(()=>parseArgv(args),CommandInputError);
  // 2901: --agent may name an agents.json entry; the agent owner refuses an unknown name, not the parser.
  for (const agent of ['codex','claude','gemini','agy','Codex (work5)','other']) assert.equal(parseArgv(['product','start','run-1','--agent',agent]).options['--agent'],agent);
  for (const shell of ['bash','zsh']) {
    const completion=renderCompletion(shell);
    assert.doesNotMatch(completion,/(?:try|sim|simulate):--agent\)/);
    assert.match(completion,/product:--agent\)/);
  }
});

test('3157 autopilot release routes issue reference to runAutopilotLauncher', async () => {
  const stdout = capture(), stderr = capture(); let received;
  const autopilotLauncher = { runAutopilotLauncher: async input => { received = input; return { exitCode: 0, message: 'Released the Autopilot claim for owner/repo#17.' }; } };
  assert.equal(await runPdd(['autopilot', 'release', 'owner/repo#17'], { autopilotLauncher, cwd: '/chosen', packageRoot: '/bundle', stdout, stderr }), 0);
  assert.equal(received.command, 'release');
  assert.deepEqual(received.issues, ['owner/repo#17']);
  assert.equal(stdout.text, 'Released the Autopilot claim for owner/repo#17.\n');
  assert.throws(() => parseArgv(['autopilot', 'release']), CommandInputError);
});

test('3578 pdd lint --local enforces default-on structural errors without pdd.json and exits 0 once fixed', async t => {
  const repo = temp(t);
  const home = temp(t);
  const state = temp(t);
  mkdirSync(join(repo, 'prompts/trust'), { recursive: true });
  writeFileSync(
    join(repo, 'prompts/trust/access.prompt.md'),
    '# Access\n\nOwn `src/access.mjs`. Use `store.load` and `store.save`.\n\n## Dependencies\n\nNone.\n',
  );
  writeFileSync(
    join(repo, 'prompts/trust/service.prompt.md'),
    '---\nkind: native-only\nreason: Native SQLite adapter.\n---\n\n# Service\n\nWire `store.load` and `access.commit`.\n\n## Dependencies\n\n- [access](access.prompt.md)\n',
  );
  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  const env = { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'invalid' };
  const errOut = capture(), errErr = capture();
  const failCode = await runPdd(['lint', '--local'], { cwd: repo, env, stdout: errOut, stderr: errErr });
  assert.equal(failCode, 1);
  assert.match(errErr.text, /Error:.*\[native-only-unknown-port\].*"access\.commit"/);

  writeFileSync(
    join(repo, 'prompts/trust/service.prompt.md'),
    '---\nkind: native-only\nreason: Native SQLite adapter.\n---\n\n# Service\n\nWire `store.load` and `store.save`.\n\n## Dependencies\n\n- [access](access.prompt.md)\n',
  );
  const okOut = capture(), okErr = capture();
  const okCode = await runPdd(['lint', '--local'], { cwd: repo, env, stdout: okOut, stderr: okErr });
  assert.equal(okCode, 0, okErr.text);
  assert.equal(okErr.text, '');
});
