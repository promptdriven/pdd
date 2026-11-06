import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runTry } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

// Native execution of the approved case table; no executable Runtime scenario exists (#2548).
const cases = JSON.parse(readFileSync(new URL('../fixtures/native-cases/try-lint-setup-wait.json', import.meta.url)));
const start = Date.parse('2026-10-27T16:27:47Z');
for (const [id, interactive, readyAt] of [
  ['agent-slow-lint', false, 122000], ['terminal-slow-lint', true, 122000],
  ['last-available-time', false, 299000], ['pending-boundary', false, Infinity],
]) test(`Try setup native case: ${id}`, async t => {
  assert.ok(cases.cases.some(row => row.id === id));
  const h = harbor(t, repo => writeFileSync(join(repo, 'app-map.json'), '{"schema_version":"prompt-runtime.app-map.v1","name":"Harbor","initial_screen":"menu"}'));
  let clock;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST') return entry.command === 'lint'
      ? { status: 202, json: f.job(entry.request.requestId, 'lint', 'queued') }
      : { status: 200, json: { ...f.tryJob(entry.request.requestId), result: { ...f.tryJob(entry.request.requestId).result, session: { ...f.tryJob(entry.request.requestId).result.session, max_calls: 40, remaining_calls: 40 } } } };
    const requestId = entry.url.split('/').at(-1);
    return { status: 200, json: clock.now - start >= readyAt ? f.lint(requestId) : f.job(requestId, 'lint', 'running') };
  });
  const p = portsFor({ HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: fake.origin }, { interactive, pollMs: 1000 });
  clock = p.clock;
  const code = await runTry({ cwd: h.repo, words: ['place-order'], options: { '--app-map': 'app-map.json', '--max-calls': '40', '--no-open': true, '--no-wait': true } }, p.ports);
  assert.equal(code, readyAt === Infinity ? 3 : 0, p.ports.stderr.text);
  assert.equal(clock.now - start, readyAt === Infinity ? 300000 : readyAt);
  assert.deepEqual(fake.posts.map(post => post.command), readyAt === Infinity ? ['lint'] : ['lint', 'try']);
  if (readyAt === Infinity) assert.match(p.ports.stderr.text + p.ports.stdout.text, /Lint is still running/);
  else {
    const sent = fake.posts[1];
    assert.equal(sent.request.max_calls, 40);
    assert.equal(sent.request.app_map, 'app-map.json');
    assert.ok(sent.tar.length > 0);
  }
});
