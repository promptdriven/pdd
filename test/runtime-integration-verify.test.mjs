import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';
const ID = '1b3b9253-8488-4c3a-a138-168d97db262a';

test('independent call receipt accounting matrix is GET-only', async t => {
  for (const [state, expected] of [['passed', 0], ['failed', 1], ['refused', 4], ['queued', 3], ['running', 3], ['unknown', 3]]) {
    const setup = harbor(t);
    const fake = await fakeRuntime(t, (entry, f) => ({ status: 200, json: f.job(ID, 'call', state, { program_result: { stdout: 'receipt\n', exit_code: 17 } }, 2) }));
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
    assert.equal(await runCheck({ cwd: setup.repo, words: [ID], options: { '--read': true, '--json': true } }, ports), expected, state);
    const out = JSON.parse(ports.stdout.text);
    assert.equal(out.state, state); assert.equal(out.calls, 2);
    assert.equal(fake.gets.length, 1); assert.equal(fake.posts.length + fake.jsonPosts.length, 0);
  }
});

test('saved descriptor invalid origin refuses without reading any runtime', async t => {
  const setup = harbor(t);
  mkdirSync(join(setup.state, 'calls'), { recursive: true });
  writeFileSync(join(setup.state, 'calls', `${ID}.meta.json`), JSON.stringify({ login: 'octo', origin: 'https://runtime.example/other' }));
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state });
  let requests = 0; ports.fetch = () => { requests++; throw Error('must not send'); };
  assert.equal(await runCheck({ cwd: setup.repo, words: [ID], options: { '--read': true } }, ports), 2);
  assert.equal(requests, 0);
});
