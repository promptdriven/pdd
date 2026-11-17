import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  exhaustCloudPoolLogin,
  isAuthFailureMessage,
  isQuotaExhaustionMessage,
  listCloudAccounts,
  readCloudAccountsState,
  selectPoolLogin,
  writeCloudAccountsState,
} from '../src/login-pool.mjs';
import { coreWorld } from './helpers/core-world.mjs';

const MIN = 60_000, HOUR = 60 * MIN;
const jobFile = (w, n) => { try { return JSON.parse(readFileSync(join(w.root, 'jobs', `${n}.json`), 'utf8')); } catch { return null; } };
const machine = w => { try { return JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8')); } catch { return { streak: 0, pausedUntil: null }; } };

function scriptedPool(w, entries) {
  const cooldowns = new Map();
  const exhaustedCalls = [];
  const select = async () => {
    const now = w.now();
    const cooling = [];
    for (const entry of entries) {
      const cd = cooldowns.get(entry.id);
      if (cd && cd.until > now) {
        cooling.push({ id: entry.id, until: cd.until, resetAt: cd.until, reason: cd.reason });
        continue;
      }
      return {
        state: 'ready',
        configured: true,
        poolPath: join(w.dir, 'pool.json'),
        poolSize: entries.length,
        login: { id: entry.id, kind: entry.kind, command: entry.command },
        agent: { id: entry.id, kind: entry.kind, command: entry.command },
        env: { ...process.env, ...entry.env },
      };
    }
    const resetAt = cooling.length ? Math.min(...cooling.map(r => r.until)) : null;
    return { state: 'exhausted', configured: true, poolPath: join(w.dir, 'pool.json'), poolSize: entries.length, resetAt, cooling, unavailable: [] };
  };
  const exhaust = async ({ loginId, resetAt, reason }) => {
    exhaustedCalls.push({ loginId, reason });
    const spec = entries.find(e => e.id === loginId);
    const until = Number.isFinite(resetAt) && resetAt > w.now() ? resetAt : w.now() + (spec?.cooldownMs ?? 30 * MIN);
    if (loginId) cooldowns.set(loginId, { until, reason });
    return select();
  };
  return { exhaustedCalls, ports: { selectLogin: select, exhaustLogin: exhaust } };
}

test('#3491 selectPoolLogin skips Claude login with expired .credentials.json and empty refreshToken even when claude auth status says loggedIn:true', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-3491-pool-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const home = join(root, 'home'), cwd = join(root, 'repo'), stateRoot = join(root, 'state');
  const claudeExpiredDir = join(home, '.claude-expired');
  const claudeRefreshDir = join(home, '.claude-refreshable');
  const codexDir = join(home, '.codex-cx2');
  mkdirSync(claudeExpiredDir, { recursive: true });
  mkdirSync(claudeRefreshDir, { recursive: true });
  mkdirSync(codexDir, { recursive: true });
  mkdirSync(cwd, { recursive: true });

  const now = Date.parse('2026-11-17T13:45:00Z');
  writeFileSync(join(claudeExpiredDir, '.credentials.json'), JSON.stringify({
    claudeAiOauth: {
      accessToken: 'sk-ant-oat01-expired-token',
      refreshToken: '',
      expiresAt: now - 86_400_000,
    },
  }));
  writeFileSync(join(claudeRefreshDir, '.credentials.json'), JSON.stringify({
    claudeAiOauth: {
      accessToken: 'sk-ant-oat01-expired-but-refreshable',
      refreshToken: 'sk-ant-ort01-valid-refresh',
      expiresAt: now - 3600_000,
    },
  }));

  const poolPath = join(root, 'pool.json');
  writeFileSync(poolPath, JSON.stringify({
    reset: 'never',
    weeklyStopPercent: 97,
    logins: [
      { id: 'claude-expired', kind: 'claude', claudeConfigDir: '~/.claude-expired' },
      { id: 'codex-cx2', kind: 'codex', plan: 'team', credits: false, codexHome: '~/.codex-cx2' },
    ],
  }));

  const first = await selectPoolLogin(
    { cwd, env: { HOME: home }, poolPath, stateRoot },
    {
      now: () => now,
      run: async (_cmd, args) => {
        if (args[0] === 'auth') return { code: 0, stdout: JSON.stringify({ loggedIn: true }), stderr: '' };
        return { code: 0, stdout: 'Logged in using ChatGPT\n', stderr: '' };
      },
      readCodexLimits: async () => ({ state: 'healthy', resetAt: null, usedPercent: 30 }),
    },
  );
  assert.equal(first.state, 'ready');
  assert.equal(first.login.id, 'codex-cx2', 'expired Claude .credentials.json without refreshToken is skipped');

  // Verify refreshable Claude .credentials.json is NOT falsely marked expired.
  const refreshPoolPath = join(root, 'pool-refresh.json');
  writeFileSync(refreshPoolPath, JSON.stringify({
    reset: 'never',
    logins: [{ id: 'claude-refresh', kind: 'claude', claudeConfigDir: '~/.claude-refreshable' }],
  }));
  const second = await selectPoolLogin(
    { cwd, env: { HOME: home }, poolPath: refreshPoolPath, stateRoot },
    {
      now: () => now,
      run: async () => ({ code: 0, stdout: JSON.stringify({ loggedIn: true }), stderr: '' }),
    },
  );
  assert.equal(second.state, 'ready');
  assert.equal(second.login.id, 'claude-refresh');
});

test('#3491 isAuthFailureMessage matches 401 and refresh-token failures while ignoring test diagnostics, and exhaustCloudPoolLogin marks local reauth instead of reporting 100% quota', async t => {
  for (const sample of [
    'Failed to authenticate. API Error: 401 OAuth access token is invalid.',
    '2026-11-17T14:00:12Z ERROR codex_login::auth::manager: Failed to refresh token status=400 Bad Request',
    'HTTP 401 Unauthorized',
    'Error: authentication_error: invalid_api_key',
    'Not logged in · Please run /login',
  ]) {
    assert.equal(isAuthFailureMessage(sample), true, sample);
    assert.equal(isQuotaExhaustionMessage(sample), false, sample);
  }
  assert.equal(isAuthFailureMessage('AssertionError: expected "401 Unauthorized" in test/auth.spec.mjs to fail'), false);
  assert.equal(isAuthFailureMessage('502 Bad Gateway'), false);

  const root = mkdtempSync(join(tmpdir(), 'pdd-3491-cloud-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const env = { HOME: root, PDD_STATE_DIR: join(root, 'state'), PDD_TOKEN: 'tok_test_3491', PDD_ACCOUNTS_URL: 'http://127.0.0.1:9999' };
  writeCloudAccountsState({
    enrolled: true,
    providers: ['claude'],
    active: { claude: { account_id: 'acc_cl_1', label: 'cl1', provider: 'claude', state: 'ready' } },
  }, { env });

  const fetchCalls = [];
  await exhaustCloudPoolLogin(
    { cwd: root, env, fallbackAgent: { id: 'claude', kind: 'claude', command: 'claude' }, loginId: 'acc_cl_1', reason: 'Failed to authenticate. API Error: 401 OAuth access token is invalid.' },
    {
      now: () => Date.parse('2026-11-17T14:00:00Z'),
      fetch: async (url, init) => {
        fetchCalls.push({ url: String(url), method: init?.method ?? 'GET' });
        return new Response(JSON.stringify({ state: 'all_cooling', wake_at: '2026-11-17T17:24:00Z' }), { status: 200 });
      },
    },
  );
  assert.equal(fetchCalls.some(c => c.url.includes('/usage-report')), false, 'auth failure must not send 100% usage-report');
  const state = readCloudAccountsState({ env });
  assert.ok(state.reauth?.acc_cl_1?.marked_at, 'auth failure marks cloud account in local reauth map');

  // Verify cold-start token timeout budget (>= 10_000ms) and 30s listCloudAccounts window.
  let observedTokenTimeout = 0;
  await listCloudAccounts(
    { cwd: root, env: { HOME: root, PDD_ACCOUNTS_URL: 'http://127.0.0.1:9999' } },
    {
      run: async (_cmd, _args, opts) => { observedTokenTimeout = opts?.timeoutMs ?? 0; return { code: 0, stdout: 'ghs_tok_cold\n', stderr: '' }; },
      fetch: async () => new Response(JSON.stringify({ accounts: [] }), { status: 200 }),
    },
  );
  assert.equal(observedTokenTimeout, 10_000, 'gh auth token receives 10s cold-start budget');
});

test('#3491 autopilot-core preserves clean build commits across pool rotation, rotates past 401/refresh errors without streak, and pauses open PR cleanly when pool exhausts', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  const pool = scriptedPool(w, [
    { id: 'codex-cx4', kind: 'codex', command: '/bin/codex', env: { CODEX_HOME: '/Users/pool/.cx4' }, cooldownMs: 2 * HOUR },
    { id: 'claude-max', kind: 'claude', command: '/bin/claude', env: { CLAUDE_CONFIG_DIR: '/Users/pool/.claude-max' }, cooldownMs: 2 * HOUR },
    { id: 'codex-work2', kind: 'codex', command: '/bin/codex', env: { CODEX_HOME: '/Users/pool/.work2' }, cooldownMs: 2 * HOUR },
  ]);
  const alerts = [], tick = () => w.tick({ ...pool.ports, alert: async a => alerts.push(a) });

  w.issue(17);
  await tick();
  const build1 = w.job(17, 'build');
  assert.equal(build1.env.CODEX_HOME, '/Users/pool/.cx4');

  // Simulate builder 1 committing clean work AND leaving dirty untracked/modified wreckage right before hitting 5H quota.
  writeFileSync(join(build1.cwd, 'phone-slice.js'), 'export const phone = "P01..P06";\n');
  w.git(build1.cwd, 'add', 'phone-slice.js');
  w.git(build1.cwd, 'commit', '-qm', 'feat(phone): implement P01-P06');
  const committedSha = w.git(build1.cwd, 'rev-parse', 'HEAD');
  writeFileSync(join(build1.cwd, 'phone-slice.js'), 'HALF WRITTEN CORRUPT EDIT\n');
  writeFileSync(join(build1.cwd, 'scratch.tmp'), 'dirty scratch\n');

  w.say(17, 'build', JSON.stringify({ type: 'error', message: 'You have hit your usage limit.' }));
  w.finish(17, 'build', { code: 1 });
  await tick();

  const build2 = w.job(17, 'build');
  assert.equal(build2.command, '/bin/claude', 'rotated from cx4 to claude-max');
  assert.equal(w.git(build2.cwd, 'rev-parse', 'HEAD'), committedSha, 'clean build commit preserved across pool rotation');
  assert.equal(readFileSync(join(build2.cwd, 'phone-slice.js'), 'utf8'), 'export const phone = "P01..P06";\n', 'dirty tracked edit reset to committed HEAD');
  assert.equal(existsSync(join(build2.cwd, 'scratch.tmp')), false, 'untracked scratch cleaned');

  // Now claude-max fails online with 401 OAuth access token is invalid -> cools down claude-max and rotates to codex-work2!
  w.say(17, 'build', JSON.stringify({ type: 'result', is_error: true, result: 'Failed to authenticate. API Error: 401 OAuth access token is invalid.' }));
  w.finish(17, 'build', { code: 1 });
  await tick();

  assert.ok(pool.exhaustedCalls.some(c => c.loginId === 'claude-max'), 'claude-max marked exhausted on 401');
  const build3 = w.job(17, 'build');
  assert.equal(build3.env.CODEX_HOME, '/Users/pool/.work2', 'rotated past 401 claude-max onto codex-work2');
  assert.equal(w.git(build3.cwd, 'rev-parse', 'HEAD'), committedSha, 'committed build progress still intact');
  assert.equal(machine(w).streak, 0, 'zero machine streak on 401 rotation');

  // Builder 3 opens PR, then fails during repair with Codex refresh-token 400 -> pool exhausts, PR pauses OPEN via pausePrForPool!
  const { pr, head } = w.build(17);
  await tick();
  w.finish(17, 'review', { result: { verdict: 'FAIL', head, summary: 'Read: phone-slice.js', mustFix: ['P2 phone-slice.js:1 add export'] } });
  w.suite(17, 0);
  await tick();
  assert.ok(w.job(17, 'repair'), 'repair started on codex-work2');
  w.say(17, 'repair', '2026-11-17T14:00:12Z ERROR codex_login::auth::manager: Failed to refresh token status=400 Bad Request');
  w.finish(17, 'repair', { code: 1 });
  await tick();

  assert.equal(pr.state, 'open', 'open PR is preserved via pausePrForPool instead of closed');
  assert.equal(jobFile(w, 17)?.stepStop?.code, 'pool-exhausted');
  assert.equal(jobFile(w, 17)?.repairs, 0, 'failed auth repair attempt rolled back');
  assert.equal(machine(w).streak, 0, 'zero machine pause streak');
});

test('#3491 un-pooled job that adopted a pre-existing PR (job.resumed === true) keeps it open as a draft on no-result release instead of closing it', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, repairs: 0 } });
  w.issue(17);
  await w.tick();
  const { pr, head } = w.build(17);
  await w.tick();
  // End run 1 on repair cap so PR stays open as an ended draft PR.
  w.finish(17, 'review', { result: { verdict: 'FAIL', head, summary: 'Read: x', mustFix: ['P2 fix x'] } });
  w.suite(17, 0);
  await w.tick();
  assert.equal(pr.state, 'open');
  assert.equal(pr.draft, true);

  // Person removes pdd:stuck to let run 2 adopt the draft PR (job.resumed = true).
  const labels = w.github.issues.get(17).labels;
  w.github.issues.get(17).labels = labels.filter(l => l !== 'pdd:stuck');
  w.settings.repairs = 2;
  await w.tick();
  assert.equal(jobFile(w, 17)?.resumed, true, 'run 2 adopted existing PR');
  assert.equal(pr.draft, false, 'marked ready on adoption');
  await w.tick();
  assert.ok(w.job(17, 'review'), 'review attempt 1 started');

  // Reviewer dies twice with no result -> run 2 releases with no-result, keeping the resumed PR OPEN as draft!
  w.finish(17, 'review', { code: 1 });
  w.suite(17, 0);
  await w.tick();
  w.finish(17, 'review', { code: 1 });
  await w.tick();

  assert.equal(jobFile(w, 17), null, 'issue released cleanly');
  assert.equal(pr.state, 'open', 'pre-existing resumed PR was NOT closed on release');
  assert.equal(pr.draft, true, 'pre-existing resumed PR converted back to draft');
});
