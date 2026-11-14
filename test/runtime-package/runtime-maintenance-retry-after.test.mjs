// prompt-runtime#865: During a fake maintenance window, the batch answer
// (summary.json / --json stdout and batch.json) and GET /v1/capacity both carry
// the exact same planned end time (`until`) and machine-readable `retry_after`.
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { checkRuntimeHealth, runCheck } from '../../src/runtime-seam.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

const STORY = 'user_stories/place-order.md';

test('during a fake maintenance window, batch answers and /v1/capacity carry the same end time and retry_after', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, runtime) => runtime.normal(entry));
  const made = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const untilMs = made.clock.now + 600_000;
  const until = new Date(untilMs).toISOString().replace('.000Z', 'Z');
  const reason = 'Runtime upgrade';
  let lastCapacity = null;
  fake.capacity = () => {
    if (made.clock.now >= untilMs) return { status: 200, json: { maintenance: null } };
    const remaining = Math.max(5, Math.min(3600, Math.ceil((untilMs - made.clock.now) / 1000)));
    lastCapacity = {
      slots: { check: { running: 0, limit: 4, waiting: 0 }, lint: { running: 0, limit: 4, waiting: 0 } },
      tries: { open: 0, limit: 30, yours: 0, per_account: null },
      maintenance: { until, reason, retry_after: remaining },
      retry_after: remaining,
      pool: null,
      features: ['lint-tests', 'lint-call-preflight'],
    };
    return { status: 200, json: lastCapacity };
  };

  // Stop while waiting in maintenance (at the same clock instant as /v1/capacity).
  made.ports.sleep = async () => { made.clock.interrupt(); };
  const exitCode = await runCheck({ words: [STORY], cwd: setup.repo, options: { '--json': true } }, made.ports);
  assert.equal(exitCode, 3);
  assert.equal(fake.posts.length, 0);

  const summary = JSON.parse(made.ports.stdout.text);
  const batchRecord = JSON.parse(readFileSync(join(setup.state, 'batches', summary.batch, 'batch.json'), 'utf8'));
  const savedSummary = JSON.parse(readFileSync(join(setup.state, 'batches', summary.batch, 'summary.json'), 'utf8'));

  assert.equal(summary.maintenance.until, lastCapacity.maintenance.until);
  assert.equal(summary.maintenance.retry_after, lastCapacity.maintenance.retry_after);
  assert.equal(summary.retry_after, lastCapacity.retry_after);
  assert.deepEqual(savedSummary.maintenance, summary.maintenance);
  assert.deepEqual(batchRecord.maintenance, summary.maintenance);
  assert.equal(batchRecord.retry_after, summary.retry_after);

  // Free health check also exposes `until` and `retry_after`.
  const health = await checkRuntimeHealth(
    { env: { PDD_RUNTIME_URL: fake.origin } },
    { ...made.ports, gh: () => ({ status: 0, stdout: 'gho_health_token' }) },
  );
  assert.equal(health.state, 'unavailable');
  assert.equal(health.detail, 'maintenance');
  assert.equal(Date.parse(health.until), Date.parse(lastCapacity.maintenance.until));
  assert.equal(health.retry_after, lastCapacity.maintenance.retry_after);

  // Explicit `pdd lint --json` during the same maintenance window carries the same `until` and `retry_after`.
  const lintMade = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  lintMade.clock.now = made.clock.now;
  lintMade.ports.sleep = async () => { lintMade.clock.interrupt(); };
  const lintExit = await runCheck({ words: [STORY], cwd: setup.repo, options: { '--lint': true, '--json': true } }, lintMade.ports);
  assert.equal(lintExit, 5);
  const lintSummary = JSON.parse(lintMade.ports.stdout.text);
  assert.equal(lintSummary.maintenance.until, lastCapacity.maintenance.until);
  assert.equal(lintSummary.maintenance.retry_after, lastCapacity.maintenance.retry_after);
  assert.equal(lintSummary.retry_after, lastCapacity.retry_after);
});

test('503 maintenance on POST /v1/check preserves zero-call accounting, batch end time, and pdd test --read / --retry recovery', async t => {
  const setup = harbor(t);
  let inMaintenance = true;
  let until = '';
  const reason = 'Planned upgrade';
  const seenRunning = new Set();
  const fake = await fakeRuntime(t, (entry, runtime) => {
    if (entry.command === 'check' && inMaintenance) {
      return {
        status: 503,
        headers: { 'retry-after': '600' },
        json: {
          requestId: entry.request.requestId,
          command: 'check',
          state: 'refused',
          job_created: false,
          dispatch: 'not_started',
          provider_calls: 0,
          accounting_complete: true,
          usage: { calls: 0, known_calls: 0, unknown_calls: 0, provider_calls: 0, accounting_complete: true },
          maintenance: { until, reason, retry_after: 600 },
          retry_after: 600,
          error: { code: 'maintenance', message: `The runtime is undergoing maintenance: ${reason}`, details: { until, reason, retryable: true, retry_after: 600 } },
        },
      };
    }
    if (entry.command === 'check' && !inMaintenance) {
      return { status: 202, json: runtime.job(entry.request.requestId, 'check', 'queued') };
    }
    if (entry.method === 'GET' && entry.url.startsWith('/v1/jobs/')) {
      const jobId = entry.url.split('/').at(-1);
      const checkPost = runtime.posts.find(p => p.command === 'check' && p.request.requestId === jobId);
      if (checkPost && !seenRunning.has(jobId)) {
        seenRunning.add(jobId);
        return {
          status: 200,
          json: {
            ...runtime.job(jobId, 'check', 'running'),
            usage: { calls: 'unknown', model: 'unknown', requested_model: 'unknown', seconds: 'unknown', input_tokens: 'unknown', output_tokens: 'unknown', reported_calls: 'unknown', accounting_complete: false },
          },
        };
      }
    }
    return runtime.normal(entry);
  });
  const made = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const untilMs = made.clock.now + 600_000;
  until = new Date(untilMs).toISOString();
  // Capacity initially clear so lint passes, then 503 maintenance hits POST /v1/check.
  let checkRefused = false;
  fake.capacity = () => ({
    status: 200,
    json: {
      maintenance: inMaintenance && checkRefused
        ? { until, reason, retry_after: Math.max(5, Math.min(3600, Math.ceil((untilMs - made.clock.now) / 1000))) }
        : null,
    },
  });
  const origSleep = made.ports.sleep;
  made.ports.sleep = async ms => {
    if (fake.posts.some(p => p.command === 'check')) {
      checkRefused = true;
      made.clock.interrupt();
      return;
    }
    await origSleep(ms);
  };

  const firstExit = await runCheck({ words: [STORY], cwd: setup.repo, options: { '--json': true } }, made.ports);
  assert.equal(firstExit, 3);
  const firstSummary = JSON.parse(made.ports.stdout.text);
  assert.equal(firstSummary.maintenance.until, until);
  assert.equal(firstSummary.retry_after, 600);
  assert.equal(firstSummary.rows[0].calls, 0);
  assert.equal(firstSummary.rows[0].accounting_complete, true);
  assert.equal(firstSummary.rows[0].can_retry, true);

  // `pdd test --read <batch> --json` during maintenance preserves busy/can_retry and maintenance end time!
  const readPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  readPorts.clock.now = made.clock.now + 30_000;
  const readExit = await runCheck({ words: [], cwd: setup.repo, options: { '--read': firstSummary.batch, '--json': true } }, readPorts.ports);
  assert.equal(readExit, 5);
  const readSummary = JSON.parse(readPorts.ports.stdout.text);
  assert.equal(readSummary.maintenance.until, until);
  assert.equal(readSummary.retry_after, 570);
  assert.equal(readSummary.rows[0].calls, 0);
  assert.equal(readSummary.rows[0].can_retry, true);

  // After maintenance ends, `pdd test --retry <batch> --json` succeeds and clears `maintenance`!
  inMaintenance = false;
  const retryPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  retryPorts.clock.now = untilMs + 1000;
  const retryExit = await runCheck({ words: [], cwd: setup.repo, options: { '--retry': firstSummary.batch, '--json': true } }, retryPorts.ports);
  assert.equal(retryExit, 0, retryPorts.ports.stderr.text);
  const retrySummary = JSON.parse(retryPorts.ports.stdout.text);
  assert.equal(retrySummary.maintenance, undefined);
  assert.equal(retrySummary.retry_after, undefined);
  assert.equal(retrySummary.rows[0].state, 'passed');
});
