import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { parseArgv, CommandInputError } from '../../src/argument-parser.mjs';
import { PUBLIC_COMMAND_ROUTES, PUBLIC_COMMAND_MANIFEST } from '../../src/command-catalog.mjs';
import { runCheck } from '../../src/runtime-seam.mjs';
import { harbor, storyTest, fakeRuntime, portsFor, root } from './runtime-fake.mjs';

const envFor = (setup, fake, extra = {}) => ({
  HOME: setup.home,
  XDG_CONFIG_HOME: join(setup.home, 'config'),
  PDD_STATE_DIR: setup.state,
  PDD_RUNTIME_URL: fake.origin,
  ...extra
});

function restartedJob(fake, id, { calls = 'unknown', known = 4, unknown = 1, complete = false } = {}) {
  const job = fake.check(id, 'unknown', [], [{ code: 'service-restarted', message: 'The interpreter restarted during execution.' }]);
  job.usage = { calls, known_calls: known, unknown_calls: unknown, requested_model: 'gpt-6.1-sol', seconds: 3.2, input_tokens: 'unknown', output_tokens: 'unknown' };
  job.accounting_complete = complete;
  job.result.report.refusal = { code: 'service-restarted', message: 'The interpreter restarted during execution.' };
  return job;
}

function settledPassedJob(fake, id, calls) {
  const job = fake.check(id, 'passed');
  job.usage = { calls, known_calls: calls, unknown_calls: 0, provider_calls: calls, requested_model: 'gpt-6.1-sol', seconds: 2.1, input_tokens: 1000, output_tokens: 50 };
  job.accounting_complete = true;
  return job;
}

test('793 CLI catalog, parser, help, completion and early mode rejection', () => {
  const parsed = parseArgv(['test', 'place-order', '--max-calls', '18', '--max-total-calls', '36', '--no-restart-replacement', '--json'], PUBLIC_COMMAND_ROUTES);
  assert.equal(parsed.commandId, 'check');
  assert.deepEqual(parsed.operands, ['place-order']);
  assert.equal(parsed.options['--max-calls'], '18');
  assert.equal(parsed.options['--max-total-calls'], '36');
  assert.equal(parsed.options['--no-restart-replacement'], true);

  for (const bad of ['0', '-5', '1000000', 'abc']) {
    assert.throws(() => parseArgv(['test', '--max-total-calls', bad], PUBLIC_COMMAND_ROUTES), error => {
      assert.ok(error instanceof CommandInputError, `expected CommandInputError for ${bad}`);
      assert.equal(error.exitCode, 2);
      return true;
    });
  }

  assert.ok(PUBLIC_COMMAND_MANIFEST.some(item => item.form.includes('--max-total-calls N') && item.form.includes('--no-restart-replacement')));
  const completion = spawnSync(process.execPath, [join(root, 'bin/pdd.mjs'), 'completion', 'bash'], { encoding: 'utf8' });
  assert.equal(completion.status, 0);
  assert.match(completion.stdout, /--max-total-calls/);
  assert.match(completion.stdout, /--no-restart-replacement/);
});

test('793 incompatible modes and invalid direct options fail with exit 2 before sign-in, state writes or network', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const cases = [
    { options: { '--lint': true, '--max-total-calls': 20 } },
    { options: { '--lint': true, '--no-restart-replacement': true } },
    { options: { '--files': true, '--max-total-calls': 20 } },
    { options: { '--read': true, '--max-total-calls': 20 } },
    { options: { '--retry': '20261027-162747-aaaa', '--no-restart-replacement': true } },
    { options: { '--fill-hash': true, '--max-total-calls': 20 } },
    { options: { '--explain-bindings': true, '--no-restart-replacement': true } },
    { options: { '--max-total-calls': 0 } },
    { options: { '--no-restart-replacement': 'false' } }
  ];
  for (const item of cases) {
    const { ports, clock } = portsFor(envFor(setup, fake));
    const code = await runCheck({ cwd: setup.repo, options: item.options }, ports);
    assert.equal(code, 2, JSON.stringify(item.options));
    assert.equal(clock.gh.length, 0);
    assert.equal(fake.posts.length, 0);
    assert.equal(existsSync(setup.state), false);
  }
});

test('793 AC1: ceiling 18 with unresolved 18-call service-restarted check blocks replacement and retains unknown receipt', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.method === 'POST' && entry.command === 'check') {
      return { status: 200, json: restartedJob(f, entry.request.requestId, { calls: 'unknown', known: 5, unknown: 1, complete: false }) };
    }
    return f.normal(entry);
  });
  const { ports } = portsFor(envFor(setup, fake));
  const code = await runCheck({
    cwd: setup.repo,
    words: ['place-order'],
    options: { '--json': true, '--max-calls': 18, '--max-total-calls': 18 }
  }, ports);
  const report = JSON.parse(ports.stdout.text);
  const checkPosts = fake.posts.filter(p => p.command === 'check');
  assert.equal(checkPosts.length, 1, 'must not send a replacement when 18-call ceiling is retained by unresolved original');
  assert.equal(checkPosts[0].request.max_calls, 18);
  assert.notEqual(code, 0);
  assert.equal(report.rows[0].state, 'partial');
  assert.equal(report.rows[0].calls, 'unknown');
  assert.equal(report.rows[0].reason?.code, 'call-budget-exhausted');
  assert.match(ports.stderr.text, /No restart replacement was sent: --max-total-calls 18 has 0 remaining calls/);

  const saved = JSON.parse(readFileSync(join(setup.state, 'batches', report.batch, 'batch.json'), 'utf8'));
  assert.equal(saved.max_total_calls, 18);
  assert.equal(saved.rows[0].recovery_state, 'unknown');
  assert.equal(saved.rows[0].note?.code, 'call-budget-exhausted');
  assert.deepEqual(saved.rows[0].request_ids, [checkPosts[0].request.requestId]);
});

test('793 AC2: ceiling 36 with 18-call cap permits exactly one replacement at 18 and fuse blocks any second restart even at ceiling 60', async t => {
  const setup = harbor(t);
  let checkCount = 0;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.method === 'POST' && entry.command === 'check') {
      checkCount += 1;
      if (checkCount === 1) return { status: 200, json: restartedJob(f, entry.request.requestId) };
      return { status: 200, json: settledPassedJob(f, entry.request.requestId, 3) };
    }
    return f.normal(entry);
  });
  const { ports } = portsFor(envFor(setup, fake));
  const code = await runCheck({
    cwd: setup.repo,
    words: ['place-order'],
    options: { '--json': true, '--max-calls': 18, '--max-total-calls': 36 }
  }, ports);
  const report = JSON.parse(ports.stdout.text);
  const checkPosts = fake.posts.filter(p => p.command === 'check');
  assert.equal(code, 0, ports.stderr.text);
  assert.equal(checkPosts.length, 2);
  assert.deepEqual(checkPosts.map(p => p.request.max_calls), [18, 18]);
  assert.equal(report.rows[0].state, 'passed');
  assert.equal(report.rows[0].calls, 'unknown', 'prior unresolved attempt keeps total calls unknown');

  // Even with ceiling 60, a second service-restarted on the replacement never triggers a 3rd POST.
  const setup2 = harbor(t);
  const fake2 = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.method === 'POST' && entry.command === 'check') return { status: 200, json: restartedJob(f, entry.request.requestId) };
    return f.normal(entry);
  });
  const run2 = portsFor(envFor(setup2, fake2));
  const code2 = await runCheck({
    cwd: setup2.repo,
    words: ['place-order'],
    options: { '--json': true, '--max-calls': 18, '--max-total-calls': 60 }
  }, run2.ports);
  assert.notEqual(code2, 0);
  assert.equal(fake2.posts.filter(p => p.command === 'check').length, 2, 'at most 1 restart replacement per test');
});

test('793 AC3: multi-Story conserved pool waits for in-flight settlement, releases unused calls, clamps remaining allowance and blocks at 0', async t => {
  const setup = harbor(t, repo => {
    storyTest(repo, 'story-c');
    storyTest(repo, 'story-d');
  });
  const git = (...args) => spawnSync('git', args, { cwd: setup.repo, encoding: 'utf8' });
  git('add', '-A'); git('-c', 'user.email=t@example.com', '-c', 'user.name=t', 'commit', '-qm', 'four-stories');

  let capacityRefusedOnce = false;
  const openPolls = new Map();
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.method === 'POST' && entry.command === 'check') {
      const { requestId, scenario } = entry.request;
      if (scenario === 'tests/place-order.json' && !capacityRefusedOnce) {
        capacityRefusedOnce = true;
        return {
          status: 429,
          headers: { 'retry-after': '1' },
          json: {
            requestId,
            dispatch: 'not_started',
            accounting_complete: true,
            usage: { calls: 0, known_calls: 0, unknown_calls: 0, provider_calls: 0 },
            error: { code: 'check-capacity', message: 'Check slots full.', details: { retryable: true, retry_after: 1 } }
          }
        };
      }
      openPolls.set(requestId, scenario);
      return { status: 202, json: f.check(requestId, 'queued') };
    }
    if (entry.method === 'GET') {
      const id = entry.url.split('/').at(-1);
      const scenario = openPolls.get(id);
      if (scenario === 'tests/unknown-item.json') return { status: 200, json: settledPassedJob(f, id, 16) };
      if (scenario === 'tests/place-order.json') return { status: 200, json: settledPassedJob(f, id, 4) };
      return { status: 200, json: settledPassedJob(f, id, 10) };
    }
    return f.normal(entry);
  });

  const { ports } = portsFor(envFor(setup, fake));
  const code = await runCheck({
    cwd: setup.repo,
    options: { '--json': true, '--max-calls': 18, '--max-total-calls': 30 }
  }, ports);
  const report = JSON.parse(ports.stdout.text);
  const checkPosts = fake.posts.filter(p => p.command === 'check');

  // 1 zero-work capacity refusal (0 calls) + 3 executed checks (4 + 16 + clamped 10 = 30 calls); 4th Story blocked at 0 remaining!
  assert.equal(checkPosts.length, 4);
  const acceptedPosts = checkPosts.slice(1);
  assert.deepEqual(acceptedPosts.map(p => p.request.max_calls), [18, 18, 10]);
  assert.notEqual(code, 0, 'blocked Story keeps batch non-passing');
  const blocked = report.rows.filter(r => r.reason?.code === 'call-budget-exhausted');
  assert.equal(blocked.length, 1);
  assert.equal(blocked[0].state, 'not run');
  assert.equal(blocked[0].calls, 0);
  assert.match(ports.stderr.text, /Capping .* to 10 AI calls \(remaining from --max-total-calls 30\)/);
});

test('793 AC4 & AC5: --no-restart-replacement disables replacement across fresh, --read and --retry; Check plan discloses policy and prior unresolved reservations', async t => {
  const setup = harbor(t);
  // Seed a prior batch with an unresolved reservation in the same repo.
  const priorBatch = '20261027-160000-prio';
  const priorDir = join(setup.state, 'batches', priorBatch);
  mkdirSync(priorDir, { recursive: true });
  writeFileSync(join(priorDir, 'batch.json'), JSON.stringify({
    version: 1,
    batch: priorBatch,
    intent: 'check',
    root: setup.repo,
    rows: [{ test: 'tests/place-order.json', request_ids: ['11111111-1111-4111-8111-111111111111'], recovery_state: 'unknown', state: 'unknown', calls: 'unknown', max_calls: 15, known_calls: 3, unknown_calls: 1, accounting_complete: false }]
  }, null, 2));

  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.method === 'POST' && entry.command === 'check') return { status: 200, json: restartedJob(f, entry.request.requestId) };
    if (entry.method === 'GET') {
      const id = entry.url.split('/').at(-1);
      return { status: 200, json: restartedJob(f, id) };
    }
    return f.normal(entry);
  });

  const run1 = portsFor(envFor(setup, fake));
  const code1 = await runCheck({
    cwd: setup.repo,
    words: ['place-order'],
    options: { '--json': true, '--max-calls': 18, '--max-total-calls': 50, '--no-restart-replacement': true }
  }, run1.ports);
  const report1 = JSON.parse(run1.ports.stdout.text);
  assert.notEqual(code1, 0);
  assert.equal(fake.posts.filter(p => p.command === 'check').length, 1);
  assert.deepEqual(report1.check_plan.calls, { estimated: 1, maximum: 18, check_requests: 1, lint_model_calls: 0 });
  assert.deepEqual(report1.check_plan.call_policy, {
    max_calls_override: 18,
    per_request_max_calls: [18],
    max_total_calls: 50,
    restart_replacement: 'disabled',
    unbounded_maximum: 18,
    planned_maximum: 18,
    unresolved_reservations: { count: 1, reserved_calls: 15, batches: [priorBatch] },
    accounting_scope: 'logical-interpreter-calls'
  });
  assert.match(run1.ports.stderr.text, /Call policy: per-request cap 18; invocation ceiling 50 \(--max-total-calls\); restart replacement disabled; unresolved prior reservations 1 \(15 calls reserved in 20261027-160000-prio\)/);
  assert.match(run1.ports.stderr.text, /restart replacement is disabled, so pdd kept the original unknown result/);

  // Later --read and --retry without flags or PDD_CHECK_SINGLE_ATTEMPT still honor saved single_attempt: true.
  const cleanEnv = envFor(setup, fake);
  delete cleanEnv.PDD_CHECK_SINGLE_ATTEMPT;
  for (const options of [{ '--read': true, '--json': true }, { '--retry': report1.batch, '--json': true }]) {
    const words = options['--read'] ? [report1.batch] : [];
    const next = portsFor(cleanEnv);
    const nextCode = await runCheck({ cwd: setup.repo, words, options }, next.ports);
    assert.notEqual(nextCode, 0);
    assert.equal(fake.posts.filter(p => p.command === 'check').length, 1, 'saved single_attempt must block replacement on read/retry');
  }
});

test('793 unproved capacity refusal (missing accounting_complete: true) retains budget reservation and blocks sibling dispatch at ceiling 1', async t => {
  const setup = harbor(t);
  const openPolls = new Map();
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.method === 'POST' && entry.command === 'check') {
      openPolls.set(entry.request.requestId, entry.request.scenario);
      return { status: 202, json: f.check(entry.request.requestId, 'queued') };
    }
    if (entry.method === 'GET') {
      const id = entry.url.split('/').at(-1);
      const job = f.check(id, 'refused', [], [{
        code: 'login-queue-timeout',
        message: 'Not run: PDD stayed busy.',
        details: { retryable: true, reason: 'status-unavailable', max_wait_seconds: 2 }
      }]);
      job.result.report.dispatch = 'not_started';
      job.result.report.provider_calls = 0;
      job.result.report.refusal = {
        code: 'login-queue-timeout',
        message: 'Not run: PDD stayed busy.',
        details: { retryable: true, reason: 'status-unavailable', max_wait_seconds: 2 }
      };
      // Deliberately omit accounting_complete: true (matching live unproved login-queue-timeout receipts).
      job.usage = { calls: 0, requested_model: 'unknown', seconds: 0, input_tokens: 'unknown', output_tokens: 'unknown' };
      return { status: 200, json: job };
    }
    return f.normal(entry);
  });

  const { ports } = portsFor(envFor(setup, fake));
  const code = await runCheck({
    cwd: setup.repo,
    options: { '--json': true, '--max-calls': 5, '--max-total-calls': 1 }
  }, ports);
  const report = JSON.parse(ports.stdout.text);
  const checkPosts = fake.posts.filter(p => p.command === 'check');
  assert.notEqual(code, 0);
  assert.equal(checkPosts.length, 1, 'unproved capacity refusal must retain its 1-call reservation and block sibling Story');
  assert.equal(checkPosts[0].request.max_calls, 1);
  const blocked = report.rows.filter(r => r.reason?.code === 'call-budget-exhausted');
  assert.equal(blocked.length, 1);
  assert.equal(blocked[0].state, 'not run');
  assert.equal(blocked[0].calls, 0);
});
