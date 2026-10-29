import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync, symlinkSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck, runDoorCall } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor, PLACE } from './runtime-fake.mjs';
const CALL = '1b3b9253-8488-4c3a-a138-168d97db262a';

test('inventory malformed paths and metadata refuse before authentication or transport', async t => {
  for (const kind of ['extra-key', 'traversal', 'symlink', 'duplicate', 'unknown-story']) {
    const setup = harbor(t, root => {
      mkdirSync(join(root, 'src')); writeFileSync(join(root, 'src/module.mjs'), '');
      const entry = { module: 'src/module.mjs', stories: ['user_stories/place-order.md'], prompt: PLACE };
      if (kind === 'extra-key') entry.extra = true;
      if (kind === 'traversal') entry.module = '../module.mjs';
      if (kind === 'symlink') { symlinkSync('module.mjs', join(root, 'src/link.mjs')); entry.module = 'src/link.mjs'; }
      if (kind === 'unknown-story') entry.stories = [PLACE];
      writeFileSync(join(root, 'pdd-bindings.json'), JSON.stringify({ schema_version: 'pdd.bindings.v1', modules: kind === 'duplicate' ? [entry, entry] : [entry] }));
    });
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state });
    ports.gh = () => { throw Error('must not sign in'); };
    ports.fetch = () => { throw Error('must not send'); };
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--lint': true } }, ports), 4, kind);
    assert.match(ports.stderr.text, /pdd-bindings.json/);
  }
});

test('file preview and normal checks carry the selected inventory', async t => {
  const setup = harbor(t, root => {
    mkdirSync(join(root, 'src')); writeFileSync(join(root, 'src/module.mjs'), '');
    writeFileSync(join(root, 'pdd-bindings.json'), JSON.stringify({ schema_version: 'pdd.bindings.v1', modules: [{ module: 'src/module.mjs', stories: ['user_stories/place-order.md'], prompt: PLACE }] }));
  });
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  for (const options of [{ '--files': true }, { '--json': true }]) {
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options }, ports), 0, ports.stderr.text);
    if (options['--json']) assert.equal(JSON.parse(ports.stdout.text).coverage.bound, 1);
    else assert.match(ports.stdout.text + ports.stderr.text, /1 of 1 modules bound/);
  }
});

test('call reads reject missing results and wrong command receipts without exposing their payload', async t => {
  for (const command of ['call', 'try']) {
    const setup = harbor(t);
    const fake = await fakeRuntime(t, (entry, f) => ({ status: 200, json: f.job(CALL, command, 'passed', command === 'try' ? { program_result: { stdout: 'foreign' } } : {}) }));
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
    assert.equal(await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true, '--json': true } }, ports), 3);
    assert.equal(JSON.parse(ports.stdout.text).program_result, null);
    assert.doesNotMatch(ports.stdout.text, /foreign/);
    assert.equal(fake.posts.length + fake.jsonPosts.length, 0);
  }
});

test('a saved call keeps its original origin and enforces its original owner before GET', async t => {
  const setup = harbor(t), controller = new AbortController();
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST') controller.abort();
    return { status: 200, json: f.job(CALL, 'call', 'passed', { program_result: { stdout: 'done\n', exit_code: 0 } }) };
  });
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };
  const first = portsFor(env, { signal: controller.signal, randomUUID: () => CALL }).ports;
  await assert.rejects(runDoorCall({ root: setup.repo, origin: fake.origin, sessionId: 'session', login: 'octo', prompt: PLACE, operation: 'main' }, {}, first));
  assert.equal(JSON.parse(readFileSync(join(setup.state, 'calls', `${CALL}.meta.json`))).origin, fake.origin);
  const different = portsFor(env).ports;
  different.gh = args => ({ status: 0, stdout: args[0] === 'auth' ? 'token' : 'other 42' });
  assert.equal(await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true } }, different), 5);
  assert.equal(fake.gets.length, 0);
  const original = portsFor({ ...env, PDD_RUNTIME_URL: 'https://changed.example' }).ports;
  assert.equal(await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true } }, original), 0);
  assert.equal(fake.gets.length, 1);
});

test('UUID read also accepts a check identity and remains GET-only', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => ({ status: 200, json: f.check(CALL) }));
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  assert.equal(await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true, '--json': true } }, ports), 0);
  assert.equal(JSON.parse(ports.stdout.text).rows[0].state, 'passed');
  assert.equal(fake.posts.length + fake.jsonPosts.length, 0);
});

test('call text retains complete multiline output while sanitizing echoed credentials', async t => {
  const setup = harbor(t);
  const { TOKEN } = await import('./runtime-fake.mjs');
  const fake = await fakeRuntime(t, (entry, f) => ({ status: 200, json: f.job(CALL, 'call', 'passed', { program_result: { stdout: `line one\nline two ${TOKEN}\n`, stderr: 'warning\n', exit_code: 7, extra: { kept: true } } }, 3) }));
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  assert.equal(await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true } }, ports), 0);
  assert.ok(ports.stdout.text.includes('line one\nline two [secret]\n'));
  assert.match(ports.stdout.text, /"kept": true/);
  assert.match(ports.stdout.text, /Usage:/);
  assert.doesNotMatch(ports.stdout.text, new RegExp(TOKEN));
});
