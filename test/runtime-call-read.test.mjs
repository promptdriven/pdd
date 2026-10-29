import test from 'node:test';
import assert from 'node:assert/strict';
import { runCheck, runDoorCall } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor, PLACE, TOKEN } from './runtime-fake.mjs';

const CALL = '1b3b9253-8488-4c3a-a138-168d97db262a';
const result = { stdout: 'saved\nsecond line\n', stderr: 'app warning\n', exit_code: 7 };
const envFor = (setup, fake) => ({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });

test('call read: a UUID reads one owner call without a saved batch or any POST', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => ({ status: 200, json: f.job(CALL, 'call', 'passed', { program_result: result }, 2) }));
  const { ports } = portsFor(envFor(setup, fake));
  const code = await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true, '--json': true } }, ports);
  assert.equal(code, 0, ports.stderr.text);
  const out = JSON.parse(ports.stdout.text);
  assert.equal(out.request_id, CALL); assert.equal(out.command, 'call'); assert.equal(out.state, 'passed');
  assert.deepEqual(out.program_result, result); assert.equal(out.calls, 2);
  assert.equal(out.exit_code, 0, 'receipt succeeded even though program exited 7');
  assert.equal(fake.posts.length + fake.jsonPosts.length, 0);
  assert.deepEqual(fake.gets.map(x => x.url), [`/v1/runs/${CALL}`]);
  assert.doesNotMatch(ports.stdout.text + ports.stderr.text, new RegExp(TOKEN));
});

test('call read: a running receipt stays pending and supplies its exact recovery command', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => ({ status: 202, json: f.job(CALL, 'call', 'running', null, 1) }));
  const { ports } = portsFor(envFor(setup, fake));
  const code = await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true } }, ports);
  assert.equal(code, 3, ports.stderr.text);
  assert.ok((ports.stdout.text + ports.stderr.text).includes(`pdd check --read ${CALL}`));
  assert.equal(fake.posts.length + fake.jsonPosts.length, 0);
});

test('call read: a mismatched receipt never exposes the other result as this call', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => ({ status: 200, json: f.job('22222222-2222-4222-8222-222222222222', 'call', 'passed', { program_result: result }, 2) }));
  const { ports } = portsFor(envFor(setup, fake));
  const code = await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true, '--json': true } }, ports);
  assert.equal(code, 3, ports.stderr.text);
  assert.doesNotMatch(ports.stdout.text, /second line/);
});

test('call recovery: an interrupted dispatched door names the UUID and its later read returns the result', async t => {
  const setup = harbor(t), controller = new AbortController();
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST') { controller.abort(); return { status: 202, json: f.job(CALL, 'call', 'running') }; }
    return { status: 200, json: f.job(CALL, 'call', 'passed', { program_result: result }, 2) };
  });
  const env = envFor(setup, fake);
  const { ports } = portsFor(env, { signal: controller.signal, randomUUID: () => CALL });
  await assert.rejects(runDoorCall({ root: setup.repo, origin: fake.origin, sessionId: 'session', login: 'octo', prompt: PLACE, operation: 'main' }, { argv: ['save'] }, ports), error => {
    assert.ok(error.message.includes(`pdd check --read ${CALL}`), error.message);
    return true;
  });
  const next = portsFor(env).ports;
  assert.equal(await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true, '--json': true } }, next), 0, next.stderr.text);
  assert.deepEqual(JSON.parse(next.stdout.text).program_result, result);
  assert.equal(fake.jsonPosts.length, 1, 'read must not dispatch the side effect again');
});
