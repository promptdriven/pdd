import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { listRuntimeJobs } from '../src/runtime-slots.mjs';
import { fakeRuntime, filesUnder, harbor, portsFor, TOKEN } from './runtime-fake.mjs';

const execute = promisify(execFile);
const cases = JSON.parse(readFileSync(new URL('runtime-admission/runtime-maintenance-wait.json', import.meta.url))).cases;
// Synthetic inputs and expected local observations approved with the native cases.
const localCases = [
  { id: 'summer-local-end', zone: 'America/Los_Angeles', until: '2026-07-02T02:25:00.000Z', time: /\b19:25\b/, zoneName: /\bPDT\b/ },
  { id: 'winter-local-end', zone: 'America/Los_Angeles', until: '2026-12-01T03:25:00.000Z', time: /\b19:25\b/, zoneName: /\bPST\b/ },
  { id: 'end-instant-zone', zone: 'America/Los_Angeles', now: '2026-11-01T08:59:50.000Z', until: '2026-11-01T09:00:10.000Z', time: /\b0?1:00\b/, zoneName: /\bPST\b/ },
  { id: 'configured-local-zone', zone: 'Asia/Tokyo', until: '2026-07-02T02:25:00.000Z', time: /\b11:25\b/, zoneName: /\b(?:JST|GMT\+0?9(?::00)?|Japan Standard Time)\b/ },
];

// A child owns TZ, a real temporary Git repo/state directory and a loopback fake
// runtime. Intl itself is not mocked; no external authentication or service runs.
async function observe(t, input) {
  const setup = harbor(t), end = Date.parse(input.until), reason = 'synthetic maintenance deploy';
  let made, refused = false;
  const submissions = [], capacityReads = [];
  const fake = await fakeRuntime(t, (entry, runtime) => {
    if (entry.command) {
      submissions.push({ kind: entry.command, at: made.clock.now, id: entry.request.requestId, maxCalls: entry.request.max_calls });
      if (input.source === 'capacity') assert.ok(made.clock.now >= end, 'no job POST during announced maintenance');
      if (input.source === '503' && entry.command === input.kind) {
        if (!refused) {
          refused = true;
          return { status: 503, headers: { 'retry-after': '7' }, json: {
            dispatch: 'not_started', error: { code: 'maintenance', details: { until: input.until, reason } },
          } };
        }
        assert.ok(made.clock.now >= end, 'no replacement POST before the UTC maintenance end');
      }
    }
    if (entry.command === 'try') return { status: 200, json: runtime.tryJob(entry.request.requestId) };
    if (entry.url.endsWith('/tests')) return { status: 200, json: { tests: [] } };
    if (entry.url.endsWith('/approvals')) return { status: 200, json: { approvals: [] } };
    return runtime.normal(entry);
  });
  made = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin, TZ: input.zone });
  made.clock.now = input.now ? Date.parse(input.now) : end - 20_000;
  const started = made.clock.now;
  fake.capacity = entry => {
    assert.equal(entry.headers.authorization, `Bearer ${TOKEN}`);
    capacityReads.push(made.clock.now);
    return input.source === 'capacity'
      ? { status: 200, json: { maintenance: made.clock.now < end ? { until: input.until, reason } : null } }
      : { status: 404, json: { error: { code: 'not-found' } } };
  };
  const options = input.kind === 'try' ? { '--no-open': true, '--no-wait': true, '--max-calls': '400' }
    : { '--json': true, ...(input.kind === 'lint' ? { '--lint': true } : { '--max-calls': '9' }) };
  const code = await (input.kind === 'try' ? runTry : runCheck)({ words: ['place-order'], cwd: setup.repo, options }, made.ports);
  assert.equal(code, 0, made.ports.stderr.text + made.ports.stdout.text);
  assert.ok(made.clock.now >= end && made.clock.now - started < 90_000, 'maintenance obeys the UTC instant and caller budget');
  assert.ok(capacityReads.some(at => at >= end), 'capacity is rechecked after maintenance');
  const attempts = submissions.filter(item => item.kind === input.kind);
  assert.equal(attempts.length, input.source === '503' ? 2 : 1, 'only confirmed not-started work gets a new POST');
  assert.equal(new Set(attempts.map(item => item.id)).size, attempts.length);
  assert.ok(fake.posts.every(entry => entry.tar.equals(fake.posts[0].tar)), 'maintenance preserves the source archive');
  if (input.kind !== 'lint') assert.ok(attempts.every(item => item.maxCalls === (input.kind === 'try' ? 400 : 9)), 'maintenance preserves call ceilings');
  assert.equal((await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs.length, 0);
  const admissions = filesUnder(setup.state).filter(path => path.endsWith('.admission.json')).map(path => JSON.parse(readFileSync(path)));
  const json = input.kind === 'try' ? null : JSON.parse(made.ports.stdout.text);
  if (input.kind === 'lint') {
    const receipt = filesUnder(setup.state).find(path => path.endsWith(`/${attempts.at(-1).id}.json`));
    assert.equal(JSON.parse(readFileSync(receipt)).usage.calls, 0, 'lint maintenance consumes no AI calls');
  } else if (json) assert.equal(json.rows[0].calls, 1, 'unstarted maintenance consumes no calls');
  else assert.match(made.ports.stdout.text, /400 calls; 400 remaining/, 'Try keeps its confirmed budget');
  return { notice: made.ports.stderr.text.split('\n').find(line => line.includes(reason)), stdout: made.ports.stdout.text, admissions };
}

if (process.argv[2] === '--maintenance-zone-worker') {
  const cleanup = [];
  try {
    const result = await observe({ after: callback => cleanup.push(callback) }, JSON.parse(process.argv[3]));
    process.stdout.write(JSON.stringify(result));
  } finally {
    for (const callback of cleanup.reverse()) await callback();
  }
} else {
  for (const local of localCases) {
    const nativeCase = cases.find(item => item.id === local.id);
    for (const source of ['capacity', '503']) test(`maintenance local time: ${nativeCase.id} via ${source}`, async () => {
      await checkNotice(local, source, 'check');
    });
  }
  for (const kind of ['lint', 'try']) test(`maintenance local time: summer-local-end via ${kind} 503`, async () => {
    await checkNotice(localCases[0], '503', kind);
  });
}

async function checkNotice(local, source, kind) {
  const input = { id: local.id, zone: local.zone, now: local.now, until: local.until, source, kind };
  const child = await execute(process.execPath, [fileURLToPath(import.meta.url), '--maintenance-zone-worker', JSON.stringify(input)], {
    env: { ...process.env, TZ: local.zone, LANG: 'en_US.UTF-8', LC_ALL: 'en_US.UTF-8' }, timeout: 20_000,
  });
  const observed = JSON.parse(child.stdout);
  assert.equal(typeof observed.notice, 'string', 'notice includes the supplied reason');
  assert.match(observed.notice, local.time, 'notice uses the configured local end hour/minute');
  assert.match(observed.notice, local.zoneName, 'notice uses the zone at the end instant');
  assert.ok(!observed.notice.includes(local.until), 'UTC is not substituted for the human local time');
  if (local.zone === 'Asia/Tokyo') assert.doesNotMatch(observed.notice, /\bP[DS]T\b/);
  if (source === '503') {
    assert.equal(observed.admissions.length, 1);
    assert.equal(observed.admissions[0].error.details.until, local.until, 'saved machine receipt retains the exact original UTC until');
  }
  // stdout stays machine-readable for Check/lint; maintenance progress stays on stderr.
  if (kind !== 'try') {
    assert.equal(JSON.parse(observed.stdout).exit_code, 0);
    assert.ok(!observed.stdout.includes('synthetic maintenance deploy'));
    assert.doesNotMatch(observed.stdout, local.zoneName, 'human zone formatting does not leak into machine JSON');
  }
}
