import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFileSync, readdirSync, lstatSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runStatus } from '../src/workflow-runner.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { cases, setup, gitEnv, packageRoot } from './helpers/workflow-step-results-2922-fixture.mjs';
import { assertJson, assertText, checkLines, noneLine, satisfyingJson, satisfyingText, textSections } from './helpers/workflow-step-results-2922-assert.mjs';

for (const operation of cases.operations) test(`2922 ${operation.criterion}: ${operation.id} retains every saved step/area and explicit none`, async t => {
  const f = await setup(t);
  const result = await f.observe(operation);
  (operation.id === 'json-status' ? assertJson : assertText)(result);
});

test('2922 assertion controls accept independent satisfying displays', () => {
  assertJson({ exitCode: 0, message: JSON.stringify(satisfyingJson()) });
  assertText({ exitCode: 0, message: satisfyingText() });
});

const jsonControl = (name, mutate) => test(`2922 rejection json-status: ${name}`, () => {
  const doc = satisfyingJson(); mutate(doc);
  assert.throws(() => assertJson({ exitCode: 0, message: JSON.stringify(doc) }));
});
const step = (doc, name) => doc.runs[0].steps.find(row => row.step === name);
jsonControl('wrong-step', doc => { step(doc, 'verify').pddResults = step(doc, 'check').pddResults; step(doc, 'check').pddResults = []; });
test('2922 rejection json-status: invalid-json with every lexical marker', () => {
  const control = cases.rejectedCounterexamples.find(row => row.id === 'invalid-json');
  assert.throws(() => assertJson({ exitCode: 0, message: control.message }), SyntaxError);
});
for (const index of [0, 1]) {
  for (const field of cases.rejectedCounterexamples.find(row => row.id === 'lost-field').independentFields)
    jsonControl(`lost-field record ${index} ${field}`, doc => { delete step(doc, 'check').pddResults[index][field]; });
  for (const field of ['batch', 'at']) jsonControl(`changed-payload record ${index} ${field}`, doc => {
    const record = step(doc, 'check').pddResults[index];
    record[field] = field === 'at' ? 12345 : 'changed-batch';
  });
  for (const requestIndex of cases.expected.byStep.find(row => row.step === 'check').pddResults[index].requests.keys())
    jsonControl(`changed-payload record ${index} requests[${requestIndex}]`, doc => { step(doc, 'check').pddResults[index].requests[requestIndex] = 'changed-nested-request'; });
  jsonControl(`lost-record ${index}`, doc => { step(doc, 'check').pddResults.splice(index, 1); });
}
jsonControl('lost-record order', doc => { step(doc, 'check').pddResults.reverse(); });
jsonControl('added-payload-field', doc => { step(doc, 'check').pddResults[0].extra = 'not saved'; });
jsonControl('additional-wrong-step-attribution', doc => { step(doc, 'verify').pddResults = structuredClone(step(doc, 'check').pddResults); });
for (const name of ['reproduce', 'verify', 'finish']) jsonControl(`missing-individual-none ${name}`, doc => { delete step(doc, name).pddResults; });
jsonControl('unrelated-empty-array', doc => { for (const row of doc.runs[0].steps) if (row.step !== 'check') delete row.pddResults; });

function replaceSection(message, name, transform) {
  return message.replace(new RegExp(`(^Step: [^\\n]+ / ${name}\\n)((?:  [^\\n]*(?:\\n|$))*)`, 'm'), (_, label, body) => label + transform(body));
}
for (const operation of ['text-status', 'passive-view']) {
  const textControl = (name, mutate) => test(`2922 rejection ${operation}: ${name}`, () => {
    const message = mutate(satisfyingText());
    assert.throws(() => assertText({ exitCode: 0, message }));
  });
  textControl('wrong-step', message => {
    const moved = replaceSection(message, 'check', body => body.split('\n').filter(line => !line.startsWith('  pdd result:')).join('\n'));
    return replaceSection(moved, 'verify', body => checkLines.map(line => `  ${line}\n`).join('') + body.replace(`  ${noneLine}\n`, ''));
  });
  for (const name of ['reproduce', 'verify', 'finish']) textControl(`missing-individual-none ${name}`, message =>
    replaceSection(message, name, body => body.replace(`  ${noneLine}`, '  Agent note — not checked by pdd: none')));
  textControl('generic-none', message => message.replaceAll(`  ${noneLine}`, '  Agent note — not checked by pdd: no results in note'));
  textControl('check-results-only-in-agent-notes', message => replaceSection(message, 'check', body => body.replaceAll('  pdd result:', '  Agent note — not checked by pdd: pdd result:')));
}

test('2922 public CLI dispatch runs real status text/JSON and real passive view', async t => {
  const f = await setup(t);
  for (const operation of cases.operations) {
    let stdout = '', stderr = ''; const dispatched = [];
    const argv = ['workflow', operation.export === 'viewRun' ? 'view' : 'status', '2922', ...(operation.input.json ? ['--json'] : [])];
    const exitCode = await runPdd(argv, { cwd: f.root, packageRoot, env: f.ports.env,
      stdout: { write: s => { stdout += s; } }, stderr: { write: s => { stderr += s; } },
      workflowRunner: { runStatus: async input => { dispatched.push(input); return runStatus(input, f.ports); } } });
    assert.equal(exitCode, 0, stderr);
    if (operation.export !== 'viewRun') {
      assert.equal(dispatched.length, 1);
      assert.equal(dispatched[0].ref, '2922'); assert.equal(dispatched[0].cwd, f.root);
      assert.equal(dispatched[0].json === true, operation.input.json === true);
    }
    (operation.id === 'json-status' ? assertJson : assertText)({ exitCode, message: stdout.trimEnd() });
  }
});

test('2922 status keeps grouping, fields and active chat/PR refresh', async t => {
  const f = await setup(t, { completed: false });
  f.h.idle();
  const inspect = async (options, group) => {
    const start = f.h.calls.length;
    const result = await runStatus({ cwd: f.source, json: true, ...options }, f.ports);
    let row;
    if (options.all) {
      assert.equal(result.exitCode, 0);
      const doc = JSON.parse(result.message);
      assert.equal(doc.version, 1);
      row = doc.runs.find(run => run.repo === cases.expected.selectedRun.repo && run.number === cases.expected.selectedRun.number);
      assert.ok(row, 'Select the run by repository and issue');
      for (const field of ['steps', 'chats', 'requests', 'ordinaryOwnership']) assert.ok(!Object.hasOwn(row, field), field);
    } else row = assertJson(result);
    assert.equal(row.group, group);
    for (const field of ['ref', 'repo', 'number', 'workflow', 'area', 'group', 'words', 'prs', 'stories', 'updatedAt', 'root', 'runDir', 'viewCommand']) assert.ok(Object.hasOwn(row, field), field);
    if (!options.all) for (const field of ['requests', 'ordinaryOwnership']) assert.ok(Object.hasOwn(row, field), field);
    assert.ok(f.h.calls.slice(start).some(args => args[0] === 'agent' && args[1] === 'get'), 'Active chat observation still occurs');
    return row;
  };
  await inspect({ ref: '2922' }, 'waiting');
  await inspect({}, 'waiting');
  await inspect({ all: true }, 'waiting');
  // The saved records and empty run-wide reader remain unchanged by display.
  assert.deepEqual(f.record().done, cases.input.selectedRun.done);
  assert.deepEqual(f.results, []);
  // A real PR-refresh path is exercised by completed setup and its saved effect.
  const merged = await setup(t);
  assert.equal(merged.record().state, 'completed');
  assert.equal(merged.record().pr[0].state, 'merged');
  assert.ok(merged.calls.some(call => call.file === 'gh' && call.args[0] === 'pr' && call.args[1] === 'view'));
});

// Snapshot all bytes plus file modes/directories; the child guard additionally
// refuses effect attempts, including swallowed failures and network calls.
function snapshot(root) {
  const entries = [];
  const visit = path => {
    const stat = lstatSync(path);
    entries.push([path.slice(root.length), stat.mode, stat.isFile() ? createHash('sha256').update(readFileSync(path)).digest('hex') : null]);
    if (stat.isDirectory()) for (const name of readdirSync(path).sort()) visit(join(path, name));
  }; visit(root); return entries;
}
function passiveGuard(worktree) {
  return `import fs from 'node:fs'; import fp from 'node:fs/promises'; import child from 'node:child_process'; import http from 'node:http'; import https from 'node:https'; import net from 'node:net';
import {syncBuiltinESMExports} from 'node:module'; import {inspect,promisify} from 'node:util';
const stop=(operation,...args)=>{process.stderr.write('FORBIDDEN VIEW EFFECT '+inspect({operation,args},{depth:null})+'\\n');process.exitCode=97;throw Error('View effect: '+operation);};
const forbid=operation=>(...args)=>stop(operation,...args);
for(const key of ['writeFileSync','appendFileSync','mkdirSync','renameSync','unlinkSync','rmSync','copyFileSync','truncateSync','chmodSync','symlinkSync','linkSync'])fs[key]=forbid('fs.'+key);
for(const key of ['writeFile','appendFile','mkdir','rename','unlink','rm','copyFile','truncate','chmod','symlink','link'])fp[key]=forbid('fs/promises.'+key);
const readOnly=flags=>typeof flags==='number'?(flags&(fs.constants.O_WRONLY|fs.constants.O_RDWR|fs.constants.O_CREAT|fs.constants.O_TRUNC|fs.constants.O_APPEND))===0:['r','rs'].includes(flags);
const openSync=fs.openSync;fs.openSync=(path,flags,...rest)=>{if(!readOnly(flags))stop('fs.openSync',path,flags,...rest);return openSync(path,flags,...rest);};
const open=fp.open;fp.open=(path,flags,...rest)=>{if(!readOnly(flags))stop('fs/promises.open',path,flags,...rest);return open(path,flags,...rest);};
for(const [name,module] of [['http',http],['https',https]])for(const key of ['request','get'])module[key]=forbid(name+'.'+key);
for(const key of ['connect','createConnection'])net[key]=forbid('net.'+key);
const report=(operation,args)=>process.stderr.write('READ-ONLY VIEW PROCESS '+inspect({operation,args},{depth:null})+'\\n');
const localGit=(file,args)=>file==='git'&&['rev-parse','diff','ls-files','--no-optional-locks'].includes(args[0]==='-C'?args[2]:args[0]);
const exec=child.execFile;child.execFile=(file,args,...rest)=>{if(!localGit(file,args))stop('child_process.execFile',file,args,...rest);report('child_process.execFile',[file,args,...rest]);return exec(file,args,...rest);};
child.execFile[promisify.custom]=(file,args,options)=>new Promise((resolve,reject)=>child.execFile(file,args,options,(error,stdout,stderr)=>error?reject(error):resolve({stdout,stderr})));
const execSync=child.execFileSync;child.execFileSync=(file,args,...rest)=>{if(!localGit(file,args))stop('child_process.execFileSync',file,args,...rest);report('child_process.execFileSync',[file,args,...rest]);return execSync(file,args,...rest);};
const same=(value,expected)=>Array.isArray(value)&&value.length===expected.length&&expected.every((item,index)=>value[index]===item);
// Only the existing discovery listing in runtime-preflight.gitFiles is admitted.
const listing=(file,args,options)=>file==='git'&&same(args,['ls-files','-z','-co','--exclude-standard'])&&options&&Object.getPrototypeOf(options)===Object.prototype&&Reflect.ownKeys(options).length===3&&['cwd','maxBuffer','stdio'].every(key=>Object.hasOwn(options,key))&&options.cwd===${JSON.stringify(worktree)}&&options.maxBuffer===536870912&&same(options.stdio,['ignore','pipe','pipe']);
const spawnSync=child.spawnSync;child.spawnSync=(...args)=>{if(args.length!==3||!listing(...args))stop('child_process.spawnSync',...args);report('child_process.spawnSync',args);return spawnSync(...args);};
for(const key of ['exec','spawn','execSync','fork'])child[key]=forbid('child_process.'+key);globalThis.fetch=forbid('fetch');syncBuiltinESMExports();`;
}

test('2922 passivity guard rejects unsafe spawnSync calls before execution', async t => {
  const f = await setup(t), guard = join(f.base, 'passive-guard.mjs');
  writeFileSync(guard, passiveGuard(f.root));
  const args = ['ls-files', '-z', '-co', '--exclude-standard'];
  const options = { cwd: f.root, maxBuffer: 536870912, stdio: ['ignore', 'pipe', 'pipe'] };
  const controls = [
    ['mutating Git', 'git', ['update-ref', 'refs/heads/forbidden-guard-control', 'HEAD'], options],
    ['non-Git process', process.execPath, ['-e', `require('node:fs').writeFileSync(${JSON.stringify(join(f.base, 'forbidden-control'))}, 'effect')`], options],
    ['extra Git argument', 'git', [...args, '--debug'], options],
    ['different cwd', 'git', args, { ...options, cwd: f.source }],
    ['shell option', 'git', args, { ...options, shell: true }],
    ['environment option', 'git', args, { ...options, env: {} }],
    ['different buffer limit', 'git', args, { ...options, maxBuffer: 1024 }],
    ['inherited stdio', 'git', args, { ...options, stdio: 'inherit' }],
    ['missing options', 'git', args]
  ];
  const before = snapshot(f.base);
  for (const [name, ...invocation] of controls) {
    const script = `import {spawnSync} from 'node:child_process';try{spawnSync(...${JSON.stringify(invocation)});process.stdout.write('EXECUTED\\n');}catch{process.stdout.write('REJECTED BEFORE EXECUTION\\n');}`;
    const result = spawnSync(process.execPath, ['--import', guard, '--input-type=module', '-e', script],
      { cwd: f.root, env: { ...gitEnv, HOME: f.home }, encoding: 'utf8', timeout: 15000 });
    assert.equal(result.status, 97, `${name}: ${result.stderr}`);
    assert.equal(result.stdout, 'REJECTED BEFORE EXECUTION\n', name);
    assert.match(result.stderr, /FORBIDDEN VIEW EFFECT[\s\S]*child_process\.spawnSync/, name);
    assert.deepEqual(snapshot(f.base), before, `${name} changes no fixture bytes, directories or modes`);
  }
});

test('2922 actual bin view is physically passive with saved results and separated notes', async t => {
  const f = await setup(t), guard = join(f.base, 'passive-guard.mjs');
  writeFileSync(guard, passiveGuard(f.root));
  const before = snapshot(f.base);
  const result = spawnSync(process.execPath, ['--import', guard, join(packageRoot, 'bin/pdd.mjs'), 'workflow', 'view', '2922'],
    { cwd: f.root, env: { ...gitEnv, HOME: f.home }, encoding: 'utf8', timeout: 15000 });
  if (result.stderr) t.diagnostic(result.stderr.trimEnd());
  assert.equal(result.status, 0, result.stderr);
  assert.doesNotMatch(result.stderr, /FORBIDDEN VIEW EFFECT/);
  assertText({ exitCode: result.status, message: result.stdout.trimEnd() });
  assert.deepEqual(snapshot(f.base), before, 'View changes no fixture bytes, directories or modes');
  for (const [identity, lines] of textSections(result.stdout)) {
    const name = identity.split('/')[1];
    assert.ok(lines.includes(`Agent note — not checked by pdd: ${cases.input.selectedRun.done[name].summary}`));
  }
});
