import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  POOL_FALLBACK_COOLDOWN_MS,
  clearPoolCooldowns,
  isQuotaExhaustionMessage,
  loadLoginPool,
  loginEnvironment,
  markLoginExhausted,
  readPoolCooldowns,
  resolvePoolPath,
  selectPoolLogin,
} from '../src/login-pool.mjs';

function makeTemp(t) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-login-pool-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const home = join(dir, 'home'), cwd = join(dir, 'repo'), stateRoot = join(dir, 'state');
  mkdirSync(home, { recursive: true });
  mkdirSync(cwd, { recursive: true });
  return { dir, home, cwd, stateRoot };
}

test('#3252 pool discovery checks explicit path, XDG_CONFIG_HOME/pdd/pool.json, ~/.pdd/pool.json, and off', t => {
  const { home, cwd } = makeTemp(t);
  const env = { HOME: home };
  assert.equal(resolvePoolPath({ cwd, env }), null);

  const fallback = loadLoginPool({ cwd, env, fallbackAgent: { id: 'codex', kind: 'codex', command: 'codex' } });
  assert.equal(fallback.configured, false);
  assert.equal(fallback.logins.length, 1);

  const pddPool = join(home, '.pdd', 'pool.json');
  mkdirSync(join(home, '.pdd'), { recursive: true });
  writeFileSync(pddPool, JSON.stringify({ logins: [{ id: 'gemini-main', kind: 'gemini', geminiCliHome: '~/.gemini-main' }] }));
  assert.equal(resolvePoolPath({ cwd, env }), pddPool);

  const xdgPool = join(home, '.config', 'pdd', 'pool.json');
  mkdirSync(join(home, '.config', 'pdd'), { recursive: true });
  writeFileSync(xdgPool, JSON.stringify({ logins: [{ id: 'codex-plus', kind: 'codex', codexHome: '~/.codex-plus' }] }));
  assert.equal(resolvePoolPath({ cwd, env }), xdgPool, 'XDG_CONFIG_HOME/pdd/pool.json takes precedence over ~/.pdd/pool.json');
  assert.equal(resolvePoolPath({ cwd, env, poolPath: 'off' }), null);
});

test('#3252 pool validation refuses reset credits, inline secrets, provider-home env keys and symlinks', t => {
  const { dir, home, cwd } = makeTemp(t);
  const env = { HOME: home };
  const writePool = (name, obj) => {
    const p = join(dir, name);
    writeFileSync(p, JSON.stringify(obj));
    return p;
  };

  assert.throws(
    () => loadLoginPool({ cwd, env, poolPath: writePool('reset.json', { reset: 'auto', logins: [{ kind: 'codex' }] }) }),
    /reset must be "never"/,
  );
  for (const badEnv of [
    { OPENAI_API_KEY: 'sk-synthetic' },
    { ANTHROPIC_API_KEY: 'sk-ant-synthetic' },
    { GEMINI_API_KEY: 'gm-synthetic' },
    { CUSTOM_TOKEN: 'tok' },
    { CODEX_HOME: '/tmp/other' },
  ]) {
    assert.throws(
      () => loadLoginPool({ cwd, env, poolPath: writePool('secret.json', { logins: [{ kind: 'codex', env: badEnv }] }) }),
      /not permitted in pool\.json/,
    );
  }
  const real = writePool('real.json', { logins: [{ kind: 'codex' }] });
  const link = join(dir, 'link.json');
  symlinkSync(real, link);
  assert.throws(() => loadLoginPool({ cwd, env, poolPath: link }), /not a symlink/);
});

test('#3252 loginEnvironment isolates provider config folders across Codex, Gemini, Claude and agy', () => {
  const baseEnv = {
    HOME: '/Users/alice',
    PATH: '/usr/bin',
    CODEX_HOME: '/Users/alice/.codex-old',
    CLAUDE_CONFIG_DIR: '/Users/alice/.claude-old',
    GEMINI_CLI_HOME: '/Users/alice/.gemini-old',
    ANTIGRAVITY_APP_DATA_DIR: '/Users/alice/.agy-old',
    CLAUDECODE: '1',
  };
  const geminiEnv = loginEnvironment(baseEnv, {
    id: 'gemini-main',
    kind: 'gemini',
    configVar: 'GEMINI_CLI_HOME',
    configDir: '/Users/alice/.gemini-work',
    env: { NO_COLOR: '1' },
  });
  assert.equal(geminiEnv.GEMINI_CLI_HOME, '/Users/alice/.gemini-work');
  assert.equal(geminiEnv.CODEX_HOME, undefined);
  assert.equal(geminiEnv.CLAUDE_CONFIG_DIR, undefined);
  assert.equal(geminiEnv.ANTIGRAVITY_APP_DATA_DIR, undefined);
  assert.equal(geminiEnv.CLAUDECODE, undefined);
  assert.equal(geminiEnv.NO_COLOR, '1');
});

test('#3252 selectPoolLogin rotates Codex -> Gemini -> Claude on 97% weekly stop, protects Pro accounts on unknown limits, and re-probes after cooldown', async t => {
  const { home, cwd, stateRoot } = makeTemp(t);
  const poolPath = join(home, '.pdd', 'pool.json');
  mkdirSync(join(home, '.pdd'), { recursive: true });
  writeFileSync(poolPath, JSON.stringify({
    reset: 'never',
    weeklyStopPercent: 97,
    logins: [
      { id: 'codex-pro', kind: 'codex', plan: 'pro', credits: true, codexHome: '~/.codex-pro' },
      { id: 'codex-plus', kind: 'codex', plan: 'plus', codexHome: '~/.codex-plus' },
      { id: 'gemini-main', kind: 'gemini', geminiCliHome: '~/.gemini-main' },
      { id: 'claude-team', kind: 'claude', claudeConfigDir: '~/.claude-team' },
    ],
  }));

  let now = Date.parse('2026-11-13T12:00:00Z');
  const codexState = {
    'codex-pro': { state: 'unknown', resetAt: null, usedPercent: null },
    'codex-plus': { state: 'limited', resetAt: now + 2 * 3600_000, usedPercent: 97.2 },
  };
  const select = () => selectPoolLogin(
    { cwd, env: { HOME: home, CODEX_HOME: '/stale/codex' }, poolPath, stateRoot },
    {
      now: () => now,
      probeLogin: async login => ({ ok: true, id: login.id }),
      readCodexLimits: async ({ env }) => env.CODEX_HOME?.endsWith('.codex-pro') ? codexState['codex-pro'] : codexState['codex-plus'],
    },
  );

  // 1. codex-pro fails closed on unknown limits (protecting paid credits), codex-plus stops at 97.2% weekly limit -> selects gemini-main!
  const first = await select();
  assert.equal(first.state, 'ready');
  assert.equal(first.login.id, 'gemini-main');
  assert.equal(first.env.GEMINI_CLI_HOME, join(home, '.gemini-main'));
  assert.equal(first.env.CODEX_HOME, undefined);

  const cds1 = readPoolCooldowns({ stateRoot, now });
  assert.equal(cds1['codex-pro'].reason, 'pro-limits-unverified');
  assert.equal(cds1['codex-pro'].until, now + POOL_FALLBACK_COOLDOWN_MS);
  assert.equal(cds1['codex-plus'].until, now + 2 * 3600_000);

  // 2. Mark gemini-main exhausted without resetAt -> bounded 30m cooldown, rotates to claude-team!
  markLoginExhausted({ stateRoot, loginId: 'gemini-main', resetAt: null, reason: '429 RESOURCE_EXHAUSTED', now });
  const second = await select();
  assert.equal(second.state, 'ready');
  assert.equal(second.login.id, 'claude-team');
  assert.equal(second.env.CLAUDE_CONFIG_DIR, join(home, '.claude-team'));

  // 3. Mark claude-team exhausted with resetAt in 1h -> all logins exhausted, earliest resetAt is 30m (pro/gemini bounded window).
  markLoginExhausted({ stateRoot, loginId: 'claude-team', resetAt: now + 3600_000, reason: 'hit your usage limit', now });
  const third = await select();
  assert.equal(third.state, 'exhausted');
  assert.equal(third.resetAt, now + POOL_FALLBACK_COOLDOWN_MS);

  // 4. Advance past 30m bounded window and let codex-pro report healthy 42% -> codex-pro resumes!
  now += POOL_FALLBACK_COOLDOWN_MS + 1000;
  codexState['codex-pro'] = { state: 'healthy', resetAt: null, usedPercent: 42 };
  const fourth = await select();
  assert.equal(fourth.state, 'ready');
  assert.equal(fourth.login.id, 'codex-pro');

  clearPoolCooldowns({ stateRoot });
  assert.deepEqual(readPoolCooldowns({ stateRoot, now }), {});
});

test('#3252 isQuotaExhaustionMessage matches provider quota/rate messages and ignores test assertion output', () => {
  for (const msg of [
    'You are out of credits.',
    'exceeded your current quota',
    '429 RESOURCE_EXHAUSTED: Quota has been exhausted',
    'You have hit your usage limit. Try again at 3pm.',
    'Error: spend_control reached for this workspace',
  ]) {
    assert.equal(isQuotaExhaustionMessage(msg), true, msg);
  }
  assert.equal(isQuotaExhaustionMessage('AssertionError: expected "rate_limit" in test/quota.spec.mjs to fail'), false);
  assert.equal(isQuotaExhaustionMessage('502 Bad Gateway'), false);
});

test('selectPoolLogin filters by allowedKinds so sandboxed intake only selects codex or claude and rotates past exhausted codex', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-pool-kinds-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const stateRoot = join(root, 'state');
  const poolPath = join(root, 'pool.json');
  writeFileSync(poolPath, JSON.stringify({
    reset: 'never',
    logins: [
      { id: 'gemini-main', kind: 'gemini', geminiCliHome: join(root, '.gemini-main') },
      { id: 'codex-1', kind: 'codex', codexHome: join(root, '.codex-1'), plan: 'pro' },
      { id: 'codex-2', kind: 'codex', codexHome: join(root, '.codex-2'), plan: 'pro' },
    ],
  }));

  const codexLimitsByHome = {
    [join(root, '.codex-1')]: { state: 'limited', resetAt: 1_800_000_000_000, usedPercent: 97 },
    [join(root, '.codex-2')]: { state: 'healthy', resetAt: null, usedPercent: 25 },
  };
  const ports = {
    now: () => 1_799_990_000_000,
    probeLogin: async () => ({ ok: true }),
    readCodexLimits: async ({ env }) => codexLimitsByHome[env.CODEX_HOME],
  };

  // Unfiltered build selection chooses gemini-main first.
  const buildPick = await selectPoolLogin({ cwd: root, env: { HOME: root }, poolPath, stateRoot }, ports);
  assert.equal(buildPick.state, 'ready');
  assert.equal(buildPick.login.id, 'gemini-main');

  // Sandboxed intake selection (`allowedKinds: ['codex', 'claude']`) skips gemini-main, sees codex-1 at 97% weekly limit, and rotates to codex-2!
  const intakePick = await selectPoolLogin(
    { cwd: root, env: { HOME: root }, poolPath, stateRoot, allowedKinds: ['codex', 'claude'] },
    ports,
  );
  assert.equal(intakePick.state, 'ready');
  assert.equal(intakePick.login.id, 'codex-2');
  assert.equal(intakePick.poolSize, 2);

  // Pool with only gemini/agy returns state: 'unavailable', poolSize: 0 when allowedKinds: ['codex', 'claude'].
  const geminiOnlyPath = join(root, 'gemini-only.json');
  writeFileSync(geminiOnlyPath, JSON.stringify({
    reset: 'never',
    logins: [{ id: 'gemini-only', kind: 'gemini', geminiCliHome: join(root, '.gemini-main') }],
  }));
  const nonePick = await selectPoolLogin(
    { cwd: root, env: { HOME: root }, poolPath: geminiOnlyPath, stateRoot, allowedKinds: ['codex', 'claude'] },
    ports,
  );
  assert.equal(nonePick.state, 'unavailable');
  assert.equal(nonePick.poolSize, 0);
});
