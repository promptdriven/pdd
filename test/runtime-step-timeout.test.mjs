import test from 'node:test';
import assert from 'node:assert/strict';
import { runCheck, runTry, runDoorCall } from '../src/runtime-client.mjs';
import { projectAnswer, renderText, exitCodeFor } from '../src/runtime-output.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

const advice = 'Make the step smaller, for example split 30 moves into 3 steps of 10.';
function timeout(f, id, command = 'check', { seconds = 180, detail = 'timeout', state = 'unknown' } = {}) {
  const refusal = { code: 'graph-provider-failure', section: 'samples[0].steps[0]', engine_message: `Provider timeout after ${seconds} seconds`,
    failure_cause: { kind: 'transport_unknown', detail }, details: { timeout_seconds: seconds } };
  return f.job(id, command, state, { refusals: [refusal], report: { samples: [{ refusal }], refusal } }, 3);
}
async function check(t, options = {}, variant = {}) {
  const setup = harbor(t), fake = await fakeRuntime(t, (e, f) => e.method === 'GET' ? { status: 200, json: timeout(f, e.url.split('/').at(-1), 'check', variant) } : f.normal(e));
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const code = await runCheck({ cwd: setup.repo, words: ['place-order'], options }, ports);
  return { code, fake, setup, ports };
}

test('STEP-TIME1: check names the timed-out authored step, reports minutes and small-step advice, never an expectation failure', async t => {
  const r = await check(t);
  assert.equal(r.code, 3);
  assert.match(r.ports.stdout.text, /Step sam-orders-espressos-and-a-muffin took more than 3 minutes and was stopped\./);
  assert.ok(r.ports.stdout.text.includes(advice)); assert.doesNotMatch(r.ports.stdout.text, /FAILED|expected.*got|the AI provider failed/);
  assert.equal(r.fake.posts.filter(p => p.command === 'check').length, 1);
  const batch = /pdd check --read (\S+)/.exec(r.ports.stderr.text)[1], count = r.fake.posts.length;
  const ports = portsFor({ HOME: r.setup.home, PDD_STATE_DIR: r.setup.state, PDD_RUNTIME_URL: r.fake.origin }).ports;
  assert.equal(await runCheck({ cwd: r.setup.repo, words: [batch], options: { '--read': true, '--json': true } }, ports), 3);
  const row = JSON.parse(ports.stdout.text).rows[0]; assert.equal(row.time_limit.minutes, 3); assert.equal(row.calls, 3);
  assert.ok(row.reason.message.includes(advice)); assert.equal(r.fake.posts.length, count);
});

test('STEP-TIME2: a server failed label for time remains inconclusive and explicit ten-minute limit wins over total elapsed', async t => {
  const r = await check(t, { '--json': true }, { seconds: 600, state: 'failed' });
  assert.equal(r.code, 3); const row = JSON.parse(r.ports.stdout.text).rows[0];
  assert.equal(row.state, 'unknown'); assert.equal(row.time_limit.minutes, 10);
  assert.match(row.reason.message, /10 minutes/); assert.equal(row.failed_checks.length, 0);
});

test('STEP-TIME3: a Try setup timeout retains usage and prints the same step guidance', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (e, f) => e.command === 'try' ? { status: 200, json: timeout(f, e.request.requestId, 'try', { seconds: 600 }) } : f.normal(e));
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true, '--no-wait': true } }, ports), 3);
  assert.match(ports.stdout.text + ports.stderr.text, /Step sam-orders-espressos-and-a-muffin took more than 10 minutes and was stopped\./);
  assert.ok((ports.stdout.text + ports.stderr.text).includes(advice)); assert.doesNotMatch(ports.stdout.text + ports.stderr.text, /used no AI calls|FAILED/);
  assert.equal(fake.posts.filter(p => p.command === 'try').length, 1);
});

test('STEP-TIME4: CLI/HTTP owner calls surface timeout advice with known usage and never replay', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (e, f) => e.json ? { status: 202, json: f.job(e.json.requestId, 'call', 'queued') }
    : { status: 200, json: { ...timeout(f, e.url.split('/').at(-1), 'call'), session_id: 'session' } });
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  await assert.rejects(runDoorCall({ root: setup.repo, origin: fake.origin, sessionId: 'session', login: 'octo', prompt: 'prompts/place_order.prompt.md', operation: 'replay' }, {}, ports), error => {
    assert.equal(error.exitCode, 125); assert.match(error.message, /took more than 3 minutes and was stopped/); assert.ok(error.message.includes(advice)); assert.equal(error.tryUsage.calls, 3); return true;
  });
  assert.equal(fake.jsonPosts.length, 1);
});

test('STEP-TIME5: unrelated provider errors, client deadlines and queue waits are not step-time refusals', () => {
  for (const code of ['graph-provider-failure','check-queue-timeout']) {
    const answer = { state: 'unknown', result: { refusals: [{ code, message: code === 'graph-provider-failure' ? 'The answer was lost.' : 'Queue timeout after 20 seconds.' }], report: {} } };
    assert.equal(projectAnswer(answer).time_limit, null);
  }
});

test('STEP-TIME6: legacy typed timeout uses the companion refusal section to name the authored step', () => {
  const answer = { state: 'unknown', result: { refusals: [{ code: 'graph-provider-failure', section: 'samples[0].steps[1]', engine_message: 'step execution refused' }],
    report: { samples: [{ refusal: { code: 'graph-provider-failure', failure_cause: { kind: 'timeout', detail: 'provider' } } }] } } };
  const row = projectAnswer(answer, { steps: [{ step_id: 'prepare' }, { step_id: 'replay-last-10' }] });
  assert.equal(row.time_limit.step, 'replay-last-10'); assert.equal(row.time_limit.minutes, 3);
});

test('STEP-TIME7: typed step timeout without a duration uses ten minutes and sanitizes the reported name', () => {
  const row = projectAnswer({ state: 'refused', result: { refusals: [{ code: 'synthetic-future-refusal', step_id: 'step-secret-value\n', failure_cause: { kind: 'step_timeout' } }] } }, { secrets: ['secret-value'] });
  assert.equal(row.time_limit.minutes, 10); assert.equal(row.time_limit.step, 'step-[secret]'); assert.equal(row.state, 'unknown');
});

for (const mode of ['--cli','--serve']) test(`STEP-TIME8: Try ${mode} setup preserves specific timeout guidance`, async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (e, f) => e.command === 'try' ? { status: 200, json: timeout(f, e.request.requestId, 'try', { seconds: 600 }) } : f.normal(e));
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { [mode]: mode === '--cli' ? true : '8080' } }, ports), 125);
  assert.match(ports.stderr.text, /Step sam-orders-espressos-and-a-muffin took more than 10 minutes and was stopped\./);
  assert.ok(ports.stderr.text.includes(advice)); assert.equal(fake.posts.filter(p => p.command === 'try').length, 1);
});
