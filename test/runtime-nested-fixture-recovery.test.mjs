import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { runCheck } from '../src/runtime/runtime-client.mjs';
import { captureSource } from '../src/runtime/runtime-preflight.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

const fixture = 'test/fixtures/example';
const fixtureStory = `${fixture}/user_stories/fixture-only.md`;
function setupRepo(repo) {
  const write = (path, bytes) => { mkdirSync(dirname(join(repo, path)), { recursive: true }); writeFileSync(join(repo, path), bytes); };
  write(fixtureStory, readFileSync(join(repo, 'user_stories/place-order.md')));
  const doc = JSON.parse(readFileSync(join(repo, 'tests/place-order.json')));
  doc.story_path = fixtureStory;
  write(`${fixture}/tests/fixture-only.json`, JSON.stringify(doc));
  // Two unrelated fixture prompts name an existing source file and would trigger a warning if scanned.
  write(`${fixture}/prompts/a.prompt.md`, '`src/place_order.py`');
  write(`${fixture}/prompts/b.prompt.md`, '`src/place_order.py`');
  write('src/place_order.py', 'fixture warning target');
}
function makePorts(setup, fake, captures) {
  return portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, {
    captureSource(root, options) { const capture = captureSource(root, options); captures.push(capture); return capture; },
  });
}
const checks = f => f.posts.filter(p => p.command === 'check');
const excludedReads = capture => capture.reads.filter(row => row.path === fixtureStory);

test('unqualified normal batch does not warn about unrelated fixture prompts', async t => {
  const setup = harbor(t, setupRepo), captures = [];
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const { ports } = makePorts(setup, fake, captures);
  assert.equal(await runCheck({ cwd: setup.repo, words: [], options: { '--json': true } }, ports), 0, ports.stderr.text + ports.stdout.text);
  assert.ok(!JSON.parse(ports.stdout.text).warnings.some(warning => warning.includes('src/place_order.py is named by')));
  assert.ok(captures.length);
  assert.deepEqual(excludedReads(captures[0]), []);
});

test('saved batch restart preserves the discovery boundary in real source recapture', async t => {
  const setup = harbor(t, setupRepo), captures = []; let resume = false;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'check') return { status: 202, json: f.check(entry.request.requestId, resume ? 'passed' : 'running') };
    if (entry.method === 'GET' && checks(f).length) {
      const id = entry.url.split('/').at(-1);
      return { status: 200, json: resume ? f.job(id, 'check', 'unknown', { refusals: [{ code: 'service-restarted' }] }, 'unknown') : f.check(id, 'running') };
    }
    return f.normal(entry);
  });
  const first = makePorts(setup, fake, captures);
  assert.equal(await runCheck({ cwd: setup.repo, words: [], options: { '--json': true, '--timeout': 1 } }, first.ports), 3);
  const batch = JSON.parse(first.ports.stdout.text).batch;
  assert.deepEqual(excludedReads(captures[0]), []);
  const before = captures.length; resume = true;
  const next = makePorts(setup, fake, captures); next.clock.now = first.clock.now;
  await runCheck({ cwd: setup.repo, words: [batch], options: { '--read': true, '--json': true } }, next.ports);
  assert.equal(checks(fake).length, 4, next.ports.stderr.text);
  assert.ok(captures.length > before, 'restart must recapture source');
  for (const capture of captures.slice(before)) assert.deepEqual(excludedReads(capture), []);
});
