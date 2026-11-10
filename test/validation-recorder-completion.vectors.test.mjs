import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawn} from 'node:child_process';

const vectors = JSON.parse(readFileSync(new URL('./runtime-admission/validation-recorder-completion-cases.json', import.meta.url)));
const recorder = fileURLToPath(new URL('../src/test-suite-recorder.mjs', import.meta.url));
const quote = s => `'${s.replaceAll("'", "'\\''")}'`;
const read = path => JSON.parse(readFileSync(path, 'utf8'));
const pause = ms => Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms);

for (const vector of vectors.cases) test(`recorder completion vector: ${vector.id}`, {timeout: 15000}, async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-recorder-completion-'));
  t.after(() => rmSync(root, {recursive: true, force: true}));
  const environmentRoot = join(root, 'environment');
  mkdirSync(environmentRoot);
  const receiptPath = join(root, 'receipt.json'), logPath = join(root, 'output.log');
  const invocations = join(root, 'invocations'), program = join(root, 'emit.cjs');
  const summary = 'TAP version 13\n1..2\n' + Object.entries(vectors.expected.counts).map(([key, value]) => `# ${key} ${value}\n`).join('');
  const output = ('x'.repeat(999) + '\n').repeat(vector.lines) + summary;
  writeFileSync(program, `const fs=require('node:fs');fs.appendFileSync(${JSON.stringify(invocations)},${JSON.stringify('once\n')});process.stdout.write(${JSON.stringify(output)});process.exitCode=7;`);
  writeFileSync(logPath, '', {mode: 0o600});
  const record = {pid: process.pid, state: 'running', outcome: 'running', childPid: null,
    receiptPath, logPath, command: '[redacted]', source: {head: null}, counts: null};
  writeFileSync(receiptPath, JSON.stringify(record));
  const env = {PATH: process.env.PATH, HOME: environmentRoot};
  const child = spawn(process.execPath, [recorder], {cwd: root, env, stdio: ['ignore', 'ignore', 'pipe', 'ipc']});
  t.after(() => { if (child.exitCode === null && child.signalCode === null) child.kill('SIGKILL'); });
  let forwarded = '', terminal, stderr = '';
  child.stderr.on('data', bytes => { stderr += bytes; });
  child.on('message', message => {
    if (message.stream) {
      const bytes = Buffer.from(message.bytes, 'base64');
      assert.ok(readFileSync(logPath).includes(bytes), 'output is durable before forwarding');
      forwarded += bytes;
    }
    if (message.result) terminal = message.result;
  });
  const closed = new Promise((resolve, reject) => { child.once('error', reject); child.once('close', resolve); });
  await new Promise((resolve, reject) => { child.once('spawn', resolve); child.once('error', reject); });
  child.send({start: {command: `${quote(process.execPath)} ${quote(program)}`, cwd: root, env,
    timeoutMs: 10000, record: {...record, recorderPid: child.pid}, environmentRoot}});
  // Hold the caller's event loop while the real recorder writes its result.
  // This leaves IPC output queued without relying on machine load or pipe timing.
  const deadline = Date.now() + 10000;
  while (read(receiptPath).state !== 'finished' && Date.now() < deadline) pause(5);
  assert.equal(read(receiptPath).state, 'finished', 'recorder saves completion while caller is paused');
  pause(50);
  await closed;
  assert.ok(terminal, `completion must survive queued IPC output: ${stderr}`);
  assert.equal(terminal.exitCode, vectors.expected.exitCode);
  assert.deepEqual(terminal.record.counts, vectors.expected.counts);
  assert.equal(forwarded, output);
  assert.equal(readFileSync(logPath, 'utf8'), output);
  assert.equal(readFileSync(invocations, 'utf8'), 'once\n');
});
