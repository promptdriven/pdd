// #3241, rule B5: the Autopilot core sends a Runtime check once more by itself: a check that was never sent (held in
// maintenance, stopped before sending) after the window, and a sent check with no verdict and no failed check (an AI
// provider failure). These tests prove the local reader of such checks and the maintenance end in the free health
// check, with a real pdd test against a fake interpreter.
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck, resendableStoryChecks, checkRuntimeHealth } from '../src/runtime-seam.mjs';
import { fakeRuntime, harbor, portsFor, temp } from './runtime-fake.mjs';

const STORY = 'user_stories/place-order.md';
const makePorts = (setup, fake) => portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
const resendable = (setup, since = 0) => resendableStoryChecks({ root: setup.repo, since }, { env: { HOME: setup.home, PDD_STATE_DIR: setup.state } });
const none = { stories: [], neverSent: [], noVerdict: [], failed: [], maintenance: false };
const CHECK = { criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'equals', expected: 900, actual: 900, passed: true };
const PROVIDER = [{ code: 'graph-provider-failure', message: 'The AI provider failed during the run.' }];

test('a check stopped in maintenance is unsent; after the window one fresh check passes and nothing is unsent', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (e, f) => f.normal(e));
  const made = makePorts(setup, fake);
  let until = made.clock.now + 30 * 60_000;
  fake.capacity = () => ({ status: 200, json: { maintenance: made.clock.now < until ? { until: new Date(until).toISOString(), reason: 'deploy' } : null } });
  // The agent stops pdd test while it waits for the maintenance: nothing is sent.
  const sleep = made.ports.sleep;
  made.ports.sleep = async ms => { made.clock.now += ms; made.clock.interrupt(); };
  assert.equal(await runCheck({ words: [STORY], cwd: setup.repo, options: { '--json': true } }, made.ports), 3);
  assert.equal(fake.posts.length, 0, 'no lint and no check was sent');
  assert.deepEqual(await resendable(setup), { ...none, stories: [STORY], neverSent: [STORY], maintenance: true });
  assert.deepEqual(await resendable(setup, made.clock.now + 60_000), none, 'since leaves out older batches');
  assert.deepEqual(await resendableStoryChecks({ root: temp(t), since: 0 }, { env: { HOME: setup.home, PDD_STATE_DIR: setup.state } }), none, 'another root has none');

  // The free health check names the end while the window runs.
  const health = await checkRuntimeHealth({ env: { PDD_RUNTIME_URL: fake.origin } }, { ...made.ports, gh: () => ({ status: 0, stdout: 'gho_health_token' }) });
  assert.equal(health.state, 'unavailable'); assert.equal(health.detail, 'maintenance');
  assert.equal(health.until, new Date(until).toISOString()); assert.equal(health.reason, 'deploy');

  // After the window the same Story is sent once and passes.
  made.clock.now = until + 1000; made.ports.sleep = sleep;
  const fresh = makePorts(setup, fake); fresh.clock.now = made.clock.now;
  assert.equal(await runCheck({ words: [STORY], cwd: setup.repo, options: { '--json': true } }, fresh.ports), 0, fresh.ports.stderr.text);
  assert.equal(fake.posts.filter(e => e.command === 'check').length, 1);
  assert.deepEqual(await resendable(setup), none);
  const after = await checkRuntimeHealth({ env: { PDD_RUNTIME_URL: fake.origin } }, { ...fresh.ports, gh: () => ({ status: 0, stdout: 'gho_health_token' }) });
  assert.equal(after.state, 'healthy'); assert.equal(after.until, undefined);
});

for (const [name, failed] of [['no failed check: sent once more', false], ['a failed check: never sent again', true]]) test(`B5 a sent check with an AI provider failure and ${name}`, async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => e.command === 'check' ? { status: 200, json: f.check(e.request.requestId, 'unknown', failed ? [CHECK, { ...CHECK, actual: 901, passed: false }] : [CHECK], PROVIDER) } : f.normal(e));
  const made = makePorts(setup, fake);
  assert.equal(await runCheck({ words: [STORY], cwd: setup.repo, options: { '--json': true } }, made.ports), 3, made.ports.stderr.text);
  assert.equal(fake.posts.filter(e => e.command === 'check').length, 1);
  assert.deepEqual(await resendable(setup), failed ? { ...none, failed: [STORY] } : { ...none, stories: [STORY], noVerdict: [STORY] });
});

test('a sent check with no saved answer, a native-only row, an access gate and a lint-only batch are never resendable', async t => {
  const dir = temp(t), root = join(dir, 'repo'), state = join(dir, 'state'); mkdirSync(root);
  const batch = (name, rows, extra = {}) => {
    mkdirSync(join(state, 'batches', name), { recursive: true });
    writeFileSync(join(state, 'batches', name, 'batch.json'), JSON.stringify({ version: 1, batch: name, root, intent: 'check', created_at: '2026-11-11T08:00:00.000Z', files: ['user_stories/a.md', 'user_stories/b.md'], rows, ...extra }));
  };
  const row = (story, extra) => ({ test: `tests/${story}.json`, story, request_ids: [], recovery_state: 'not_run', refusals: [], note: { code: 'interrupted', message: 'Stopped before sending.' }, ...extra });
  batch('20261111-080000-aaaa', [row('a'), row('b'), row('c', { story: 'user_stories/c.md' })]);
  batch('20261111-080100-bbbb', [row('a', { request_ids: ['3f8a2c1e-0000-4000-8000-000000000001'], recovery_state: 'unknown' })]);  // sent later, no saved answer: maybe still open
  batch('20261111-080200-cccc', [row('b', { unsent: true, note: { code: 'native-only', message: 'prompts/b.prompt.md: native' } })]);
  batch('20261111-080300-dddd', [row('d', { story: 'user_stories/d.md', note: { code: 'blocked', message: 'Run gh auth login' } })]);
  batch('20261111-080400-eeee', [row('e', { story: 'user_stories/e.md' })], { intent: 'lint-only' });
  writeFileSync(join(state, 'batches', 'not-a-batch'), '');
  const read = await resendableStoryChecks({ root }, { env: { PDD_STATE_DIR: state } });
  assert.deepEqual(read, { ...none, stories: ['user_stories/c.md'], neverSent: ['user_stories/c.md'] });
});
