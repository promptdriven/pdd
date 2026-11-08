import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { calculateCheckCapacity, executeSuite, runTestSuite } from '../src/test-suite-queue.mjs';
import { checkMachine, withCheckLifetime } from './helpers/check-machine.mjs';

const quote = value => `'${value.replaceAll("'", "'\\''")}'`;
function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-suite-environment-'));
  t.after(() => rmSync(root, {recursive:true, force:true}));
  const queue = join(root, 'queue'), caller = join(root, 'caller');
  mkdirSync(queue); mkdirSync(caller);
  writeFileSync(join(caller, 'keep'), 'caller-owned');
  const machine = checkMachine({taskset:null});
  writeFileSync(join(queue, 'capacity.json'), JSON.stringify(withCheckLifetime(calculateCheckCapacity({checks:3}, machine.ports))));
  return {root, queue, caller, ports:machine.ports};
}
const receipts = queue => readdirSync(queue).filter(name => /^ticket-.*\.json$/.test(name))
  .map(name => JSON.parse(readFileSync(join(queue, name), 'utf8')));
async function child(file, args, options) {
  const proc = spawn(file, args, options);
  let output = '';
  proc.stdout.on('data', bytes => output += bytes);
  proc.stderr.on('data', bytes => output += bytes);
  const timer = setTimeout(() => proc.kill('SIGKILL'), 30_000);
  try {
    const code = await new Promise((done, fail) => { proc.once('error', fail); proc.once('close', done); });
    assert.equal(code, 0, output);
    return output;
  } finally { clearTimeout(timer); }
}

test('agent caller and clean VM compatibility caller run the same controlled npm suite', async t => {
  const f = fixture(t), cwd = join(f.root, 'repository'); mkdirSync(cwd);
  // A complete, synthetic repository suite. This never runs this repo's full suite.
  writeFileSync(join(cwd, 'package.json'), JSON.stringify({scripts:{test:`${quote(process.execPath)} --test smoke.test.cjs`}}));
  writeFileSync(join(cwd, 'smoke.test.cjs'), `
const test = require('node:test'), assert = require('node:assert/strict'), fs = require('node:fs');
test('suite environment contract', () => {
  const env = process.env;
  const absent = ['CODEX_HOME','PDD_AUTOPILOT_CONTEXT','HERDR_SESSION','HERDR_CONFIG',
    'CLAUDECODE','CLAUDE_CONFIG_DIR','CODEX_THREAD_ID','PDD_AGENT_SESSION',
    'OPENAI_API_KEY','ANTHROPIC_API_KEY','PDD_INTERPRETER_QUEUE','PDD_MAX_JOBS','BASH_ENV','NODE_OPTIONS'];
  for (const key of absent) assert.equal(env[key], undefined, key);
  const paths = ['HOME','PDD_STATE_DIR','XDG_CONFIG_HOME','TMPDIR'].map(key => env[key]);
  assert.equal(new Set(paths).size, 4);
  for (const path of paths) { assert.ok(fs.statSync(path).isDirectory()); assert.equal(fs.existsSync(require('node:path').join(path, 'keep')), false); }
  assert.equal(env.PDD_CHECK_CPUS, '13');
  assert.equal(env.POCKET_BROWSER_BIN, '/usr/bin/google-chrome');
  fs.writeFileSync('observation.json', JSON.stringify({paths, result:'passed'}));
});
`);
  const command = 'npm test';
  const clean = {PATH:process.env.PATH, HOME:f.caller, XDG_CONFIG_HOME:f.caller, PDD_SUITE_QUEUE:f.queue, SUITE:command};
  const dirty = {...clean, PDD_STATE_DIR:f.caller, TMPDIR:f.caller,
    CODEX_HOME:f.caller, PDD_AUTOPILOT_CONTEXT:'synthetic-agent', HERDR_SESSION:'synthetic', HERDR_CONFIG:f.caller,
    CLAUDECODE:'1', CLAUDE_CONFIG_DIR:f.caller, CODEX_THREAD_ID:'synthetic', PDD_AGENT_SESSION:'1',
    OPENAI_API_KEY:'synthetic-unused', ANTHROPIC_API_KEY:'synthetic-unused',
    PDD_INTERPRETER_QUEUE:f.caller, PDD_MAX_JOBS:'1', NODE_OPTIONS:'--no-warnings', BASH_ENV:join(f.caller, 'hook')};
  writeFileSync(dirty.BASH_ENV, `touch ${quote(join(f.caller, 'hook-ran'))}\n`);
  const observations = [];
  for (const [file, args, env] of [
    [process.execPath, [resolve('bin/pdd.mjs'), 'workflow', 'suite', '--command', command], dirty],
    ['/bin/bash', [resolve('scripts/vm-suite-lock.sh')], clean],
  ]) {
    const output = await child(file, args, {cwd, env});
    assert.match(output, /# pass 1/); assert.match(output, /# fail 0/);
    const seen = JSON.parse(readFileSync(join(cwd, 'observation.json'), 'utf8'));
    assert.ok(seen.paths.every(path => !existsSync(path)), 'owned directories are removed after success');
    observations.push(seen.result);
  }
  assert.deepEqual(observations, ['passed', 'passed']);
  assert.equal(existsSync(join(f.caller, 'hook-ran')), false);
  assert.equal(readFileSync(join(f.caller, 'keep'), 'utf8'), 'caller-owned');
  for (const row of receipts(f.queue)) {
    assert.equal(row.state, 'finished'); assert.equal(row.reason, null);
    assert.equal(row.environmentPolicy, 'clean-v1'); assert.equal(row.coresPerCheck, 13);
    assert.equal(JSON.stringify(row).includes('synthetic-unused'), false);
  }
  assert.equal(readdirSync(f.queue).some(name => name.startsWith('suite-env-')), false);
});

for (const outcome of ['nonzero', 'timeout', 'error']) test(`private suite environment is removed after ${outcome}`, async t => {
  const f = fixture(t), env = {PATH:process.env.PATH, HOME:f.caller, PDD_SUITE_QUEUE:f.queue};
  const before = {...env}; let paths, allocated;
  const result = await runTestSuite({cwd:f.root, command:outcome === 'timeout' ? 'exec sleep 30' : 'exit 7', env}, {
    ...f.ports, say:() => {}, execute:async (command, options) => {
      paths = ['HOME','PDD_STATE_DIR','XDG_CONFIG_HOME','TMPDIR'].map(key => options.env[key]);
      allocated = paths.every(path => typeof path === 'string' && existsSync(path));
      if (outcome === 'error') throw Error('synthetic-execution-error');
      return executeSuite(command, {...options, timeoutMs:50});
    },
  });
  assert.equal(result.exitCode, outcome === 'timeout' ? 124 : outcome === 'nonzero' ? 7 : 1);
  assert.equal(allocated, true, 'suite execution must receive four private directories');
  assert.ok(paths.every(path => !existsSync(path)));
  assert.deepEqual(env, before); assert.equal(readFileSync(join(f.caller, 'keep'), 'utf8'), 'caller-owned');
  assert.equal(receipts(f.queue)[0].environmentPolicy, 'clean-v1');
});
