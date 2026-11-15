import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import http from 'node:http';
import {
  chmodSync,
  existsSync,
  lstatSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  realpathSync,
  rmSync,
  statSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { basename, join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { runStepAgentProcess } from '../src/agent-adapters.mjs';
import { cleanupAgentJob, jobEnvironment } from '../src/agent-job.mjs';
import { parseCodexUsageWindows } from '../src/codex-limits.mjs';
import {
  CloudAccountsError,
  DEFAULT_CLOUD_URL,
  cloudAccountsRequest,
  createCodexStepOverlay,
  loginEnvironment,
  materializeLocalClaudeAuth,
  normalizeUsagePercentInt,
  prepareCloudStepExecution,
  reportCloudAccountUsage,
  resolveCloudAccountsEndpoint,
  sweepActiveCodexOverlays,
} from '../src/login-pool.mjs';
import { redactSecrets } from '../src/secret-redaction.mjs';
import { coreWorld } from './helpers/core-world.mjs';
import { tickAutopilot, runAutopilotLauncher } from '../src/autopilot-launcher.mjs';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';

function makeJwt(payload) {
  const header = Buffer.from(JSON.stringify({ alg: 'none', typ: 'JWT' })).toString('base64url');
  const body = Buffer.from(JSON.stringify(payload)).toString('base64url');
  return `${header}.${body}.sig`;
}

function sink() {
  return {
    text: '',
    write(chunk) {
      this.text += String(chunk);
      return true;
    },
  };
}

async function createMockCloudServer(t, initial = {}) {
  const state = {
    bearerToken: initial.bearerToken ?? 'ghu_mockCloudBearerToken123456',
    nowMs: initial.nowMs ?? Date.parse('2026-11-14T22:00:00Z'),
    accounts: structuredClone(initial.accounts ?? []),
    vaultBundles: new Map(),
    pendingInvites: structuredClone(initial.pendingInvites ?? []),
    auditLogs: new Map(),
    requests: [],
    delayLeaseMs: 0,
    nextSeq: 1,
  };

  const logAudit = (accountId, event, machineLabel, detail = '') => {
    const list = state.auditLogs.get(accountId) ?? [];
    list.push({
      created_at: new Date(state.nowMs).toISOString(),
      event,
      machine_label: machineLabel || 'unknown-machine',
      actor_login: 'Serhan-Asad',
      detail,
    });
    state.auditLogs.set(accountId, list);
  };

  const refreshAccountState = acc => {
    if (acc.state === 'paused') return;
    if (acc.cooling_until) {
      const untilMs = Date.parse(acc.cooling_until);
      if (Number.isFinite(untilMs) && untilMs <= state.nowMs) {
        acc.cooling_until = null;
        if ((acc.five_hour_used_percent ?? 0) >= 100 && (!acc.five_hour_reset_at || Date.parse(acc.five_hour_reset_at) <= state.nowMs)) {
          acc.five_hour_used_percent = 0;
        }
        if ((acc.weekly_used_percent ?? 0) >= 100 && (!acc.weekly_reset_at || Date.parse(acc.weekly_reset_at) <= state.nowMs)) {
          acc.weekly_used_percent = 0;
        }
        acc.state = 'ready';
      } else {
        acc.state = 'cooling';
      }
    }
  };

  const isReady = acc => {
    refreshAccountState(acc);
    return acc.state === 'ready'
      && (acc.five_hour_used_percent ?? 0) < 100
      && (acc.weekly_used_percent ?? 0) < 100;
  };

  const server = http.createServer(async (req, res) => {
    const chunks = [];
    for await (const chunk of req) chunks.push(chunk);
    const rawBody = Buffer.concat(chunks).toString('utf8');
    let body = null;
    try { body = rawBody ? JSON.parse(rawBody) : null; } catch {}

    const url = new URL(req.url, 'http://127.0.0.1');
    const machineId = req.headers['x-pdd-machine-id'] ?? '';
    state.requests.push({
      method: req.method,
      path: url.pathname,
      auth: req.headers.authorization ?? '',
      machineId,
      body,
    });

    if (req.headers.authorization !== `Bearer ${state.bearerToken}`) {
      res.writeHead(401, { 'content-type': 'application/json' });
      res.end(JSON.stringify({ detail: { error: 'unauthorized', message: 'Unauthorized' } }));
      return;
    }

    const send = (status, payload) => {
      res.writeHead(status, { 'content-type': 'application/json' });
      res.end(JSON.stringify(payload));
    };

    if (req.method === 'GET' && url.pathname === '/v1/accounts') {
      for (const acc of state.accounts) refreshAccountState(acc);
      return send(200, {
        accounts: state.accounts.filter(a => !a.revoked),
        pending_invites: state.pendingInvites,
      });
    }

    if (req.method === 'POST' && url.pathname === '/v1/accounts') {
      if (body?.provider === 'codex') {
        const tok = body?.bundle?.auth_json?.tokens;
        const missing = ['access_token', 'refresh_token', 'id_token', 'account_id'].filter(
          k => typeof tok?.[k] !== 'string' || !tok[k].trim(),
        );
        if (missing.length > 0) {
          return send(422, { detail: missing.map(k => ({ loc: ['body', 'bundle', 'auth_json', 'tokens', k], msg: `Field required: ${k}` })) });
        }
      }
      const id = `acc_${state.nextSeq++}`;
      const acc = {
        account_id: id,
        label: body.label,
        provider: body.provider,
        plan: body.plan ?? 'pro',
        owner_github_id: 95069916,
        owner_login: 'Serhan-Asad',
        shared: false,
        state: 'ready',
        five_hour_used_percent: 8,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 22,
        weekly_reset_at: '2026-11-18T17:00:00Z',
        cooling_until: null,
        created_at: new Date(state.nowMs + state.nextSeq).toISOString(),
      };
      state.vaultBundles.set(id, structuredClone(body.bundle));
      state.accounts.push(acc);
      logAudit(id, 'enrolled', machineId, `provider=${acc.provider}`);
      return send(201, { account: acc });
    }

    if (req.method === 'POST' && url.pathname === '/v1/accounts/lease') {
      if (state.delayLeaseMs > 0) {
        await new Promise(r => setTimeout(r, state.delayLeaseMs));
      }
      const provider = body?.provider ?? 'codex';
      const skip = new Set(Array.isArray(body?.skip_account_ids) ? body.skip_account_ids : []);
      const accessible = state.accounts.filter(a => !a.revoked && a.provider === provider);
      for (const acc of accessible) refreshAccountState(acc);

      let chosen = null;
      let switched = false;
      if (body?.preferred_label) {
        const target = accessible.find(a => a.label === body.preferred_label || a.account_id === body.preferred_label);
        if (!target) return send(404, { detail: { error: 'not_found', message: `Account ${body.preferred_label} not found` } });
        if (!isReady(target)) return send(409, { detail: { error: 'account_not_ready', message: `Account ${target.label} is ${target.state}` } });
        chosen = target;
        switched = body.current_account_id !== target.account_id;
      } else {
        const current = body?.current_account_id
          ? accessible.find(a => a.account_id === body.current_account_id)
          : null;
        if (current && !skip.has(current.account_id) && isReady(current)) {
          chosen = current;
          switched = false;
        } else {
          const readyPool = accessible
            .filter(a => !skip.has(a.account_id) && isReady(a))
            .sort((a, b) => {
              const wa = a.weekly_reset_at ? Date.parse(a.weekly_reset_at) : Number.MAX_SAFE_INTEGER;
              const wb = b.weekly_reset_at ? Date.parse(b.weekly_reset_at) : Number.MAX_SAFE_INTEGER;
              if (wa !== wb) return wa - wb;
              return Date.parse(a.created_at ?? 0) - Date.parse(b.created_at ?? 0);
            });
          chosen = readyPool[0] ?? null;
          switched = Boolean(chosen && body?.current_account_id && chosen.account_id !== body.current_account_id);
        }
      }

      if (!chosen) {
        const coolingTimes = accessible
          .map(a => a.cooling_until)
          .filter(Boolean)
          .sort((a, b) => Date.parse(a) - Date.parse(b));
        return send(200, {
          state: 'all_cooling',
          wake_at: coolingTimes[0] ?? new Date(state.nowMs + 3600_000).toISOString(),
          lease: null,
        });
      }

      logAudit(chosen.account_id, 'leased', body?.machine_label || machineId, `holder=${body?.holder_id ?? ''}`);
      const expiresAt = new Date(state.nowMs + 50 * 60 * 1000).toISOString();
      let lease;
      if (provider === 'codex') {
        lease = {
          lease_id: `lse_${state.nextSeq++}`,
          expires_at: expiresAt,
          delivery_mode: 'direct_stripped',
          codex_auth_json: {
            auth_mode: 'chatgpt',
            OPENAI_API_KEY: null,
            tokens: {
              access_token: `acc_tok_${chosen.label}_secret12345`,
              refresh_token: '',
              id_token: makeJwt({ email: `${chosen.label}@example.com`, 'https://api.openai.com/auth': { chatgpt_plan_type: chosen.plan ?? 'pro' } }),
              account_id: `org_${chosen.account_id}`,
            },
            last_refresh: new Date(state.nowMs).toISOString(),
          },
        };
      } else if (chosen.shared) {
        const leaseId = `lse_${state.nextSeq++}`;
        lease = {
          lease_id: leaseId,
          expires_at: expiresAt,
          delivery_mode: 'gateway_grant',
          anthropic_base_url: `${serverUrl}/v1/accounts/claude-gateway/${leaseId}`,
          claude_oauth_token: `pddg_${chosen.label.replace(/[^A-Za-z0-9_-]/g, '_')}_shortlived9999`,
        };
      } else {
        lease = {
          lease_id: `lse_${state.nextSeq++}`,
          expires_at: expiresAt,
          delivery_mode: 'direct_oauth',
          claude_oauth_token: `sk-ant-oat01-${chosen.label}-personalSecretToken888`,
        };
      }

      return send(200, {
        state: 'leased',
        switched,
        account: chosen,
        lease,
      });
    }

    const usageMatch = /^\/v1\/accounts\/([^/]+)\/usage-report$/.exec(url.pathname);
    if (req.method === 'POST' && usageMatch) {
      const id = decodeURIComponent(usageMatch[1]);
      const acc = state.accounts.find(a => a.account_id === id);
      if (!acc) return send(404, { detail: { error: 'not_found', message: 'Not found' } });
      for (const field of ['five_hour_used_percent', 'weekly_used_percent']) {
        const val = body?.[field];
        if (val !== null && val !== undefined && (!Number.isInteger(val) || val < 0 || val > 100)) {
          return send(422, { detail: [{ loc: ['body', field], msg: 'Input should be a valid integer between 0 and 100' }] });
        }
      }
      if (typeof body?.five_hour_used_percent === 'number') acc.five_hour_used_percent = body.five_hour_used_percent;
      if (body?.five_hour_reset_at) acc.five_hour_reset_at = body.five_hour_reset_at;
      if (typeof body?.weekly_used_percent === 'number') acc.weekly_used_percent = body.weekly_used_percent;
      if (body?.weekly_reset_at) acc.weekly_reset_at = body.weekly_reset_at;
      if (body?.limit_reached || (acc.five_hour_used_percent ?? 0) >= 100 || (acc.weekly_used_percent ?? 0) >= 100) {
        acc.state = 'cooling';
        if ((acc.weekly_used_percent ?? 0) >= 100 && acc.weekly_reset_at) {
          acc.cooling_until = acc.weekly_reset_at;
        } else {
          acc.cooling_until = acc.five_hour_reset_at ?? acc.weekly_reset_at ?? new Date(state.nowMs + 3600_000).toISOString();
        }
      }
      logAudit(id, 'usage_report', machineId, `state=${acc.state}`);
      return send(200, { account: acc });
    }

    const actionMatch = /^\/v1\/accounts\/([^/]+)\/(pause|unpause|share|unshare|leave|log)$/.exec(url.pathname);
    if (actionMatch) {
      const id = decodeURIComponent(actionMatch[1]);
      const action = actionMatch[2];
      const acc = state.accounts.find(a => a.account_id === id);
      if (!acc) return send(404, { detail: 'Not found' });
      if (req.method === 'POST' && action === 'pause') {
        acc.state = 'paused';
        logAudit(id, 'paused', machineId);
        return send(200, { account: acc });
      }
      if (req.method === 'POST' && action === 'unpause') {
        acc.state = 'ready';
        acc.cooling_until = null;
        logAudit(id, 'unpaused', machineId);
        return send(200, { account: acc });
      }
      if (req.method === 'POST' && action === 'share') {
        const invId = `inv_${state.nextSeq++}`;
        logAudit(id, 'shared', machineId, body?.github_login ? `user=${body.github_login}` : `team=${body?.org}/${body?.team}`);
        return send(200, { account: acc, invite: { invite_id: invId, account_id: id, shared: body } });
      }
      if (req.method === 'POST' && action === 'unshare') {
        logAudit(id, 'unshared', machineId, `user=${body?.github_login}`);
        return send(200, { revoked: true });
      }
      if (req.method === 'POST' && action === 'leave') {
        acc.revoked = true;
        logAudit(id, 'left', machineId);
        return send(200, { left: true });
      }
      if (req.method === 'GET' && action === 'log') {
        return send(200, { entries: state.auditLogs.get(id) ?? [] });
      }
    }

    const acceptMatch = /^\/v1\/accounts\/invites\/([^/]+)\/accept$/.exec(url.pathname);
    if (req.method === 'POST' && acceptMatch) {
      const invId = decodeURIComponent(acceptMatch[1]);
      const idx = state.pendingInvites.findIndex(i => i.invite_id === invId);
      if (idx === -1) return send(404, { detail: 'Invite not found' });
      const [inv] = state.pendingInvites.splice(idx, 1);
      const sharedAcc = {
        account_id: inv.account_id,
        label: inv.label,
        provider: inv.provider,
        plan: 'max',
        owner_github_id: 111,
        owner_login: inv.owner_login,
        shared: true,
        state: 'ready',
        five_hour_used_percent: 15,
        five_hour_reset_at: '2026-11-15T01:00:00Z',
        weekly_used_percent: 30,
        weekly_reset_at: '2026-11-17T12:00:00Z',
        cooling_until: null,
        created_at: new Date(state.nowMs).toISOString(),
      };
      state.accounts.push(sharedAcc);
      logAudit(sharedAcc.account_id, 'invite_accepted', machineId);
      return send(200, { account: sharedAcc });
    }

    const deleteMatch = /^\/v1\/accounts\/([^/]+)$/.exec(url.pathname);
    if (req.method === 'DELETE' && deleteMatch) {
      const id = decodeURIComponent(deleteMatch[1]);
      const idx = state.accounts.findIndex(a => a.account_id === id);
      if (idx === -1) return send(404, { detail: 'Not found' });
      state.accounts.splice(idx, 1);
      state.vaultBundles.delete(id);
      return send(200, { deleted: true });
    }

    send(404, { detail: `Unhandled ${req.method} ${url.pathname}` });
  });

  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const address = server.address();
  const serverUrl = `http://127.0.0.1:${address.port}`;
  t.after(() => {
    server.closeAllConnections?.();
    server.close();
  });
  return { serverUrl, state };
}

function makeTempSandbox(t, cloudUrl, bearerToken = 'ghu_mockCloudBearerToken123456') {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-cloud-acc-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const home = join(root, 'home');
  const stateDir = join(root, 'state');
  const cwd = join(root, 'work');
  mkdirSync(home, { recursive: true });
  mkdirSync(stateDir, { recursive: true });
  mkdirSync(cwd, { recursive: true });
  const env = {
    HOME: home,
    PDD_STATE_DIR: stateDir,
    PDD_CLOUD_URL: cloudUrl,
    GH_TOKEN: bearerToken,
    PATH: process.env.PATH,
  };
  return { root, home, stateDir, cwd, env };
}

async function invokeCli(argv, sandbox, accountsPorts = {}) {
  const stdout = sink();
  const stderr = sink();
  const exit = await runPdd(argv, {
    cwd: sandbox.cwd,
    env: sandbox.env,
    stdout,
    stderr,
    accountsPorts,
  });
  return { exit, stdout: stdout.text, stderr: stderr.text };
}

test('3252 T1: pdd accounts add, import, and list enroll Codex & Claude bundles, strip local refresh tokens (0600), and leak zero secrets', async t => {
  const cloud = await createMockCloudServer(t, {
    pendingInvites: [
      { invite_id: 'inv_team1', account_id: 'acc_shared_claude', label: 'team-claude', provider: 'claude', owner_login: 'team-lead' },
    ],
  });
  const sb = makeTempSandbox(t, cloud.serverUrl);

  const rawRefresh = 'rt_superSecretSingleUseRefreshToken_99999';
  const rawAccess = 'at_initialLocalAccessToken_88888';
  const rawClaudeOauth = 'sk-ant-oat01-enrolledClaudeSecretToken77777';

  // 1. pdd accounts add --provider codex --label plus-1
  const addCodex = await invokeCli(['accounts', 'add', '--provider', 'codex', '--label', 'plus-1'], sb, {
    runLogin: async (provider, { env }) => {
      assert.equal(provider, 'codex');
      const codexDir = join(env.HOME, '.codex');
      mkdirSync(codexDir, { recursive: true });
      writeFileSync(join(codexDir, 'auth.json'), JSON.stringify({
        auth_mode: 'chatgpt',
        OPENAI_API_KEY: null,
        tokens: {
          access_token: rawAccess,
          refresh_token: rawRefresh,
          id_token: makeJwt({ email: 'plus1@example.com', 'https://api.openai.com/auth': { chatgpt_plan_type: 'plus' } }),
          account_id: 'acct_plus1',
        },
      }));
      return { code: 0, stdout: 'Logged in\n', stderr: '' };
    },
  });
  assert.equal(addCodex.exit, 0, addCodex.stderr);
  assert.match(addCodex.stdout, /Enrolled Codex account "plus-1"/);

  // Server received the full refresh_token in POST /v1/accounts.
  const enrollReq = cloud.state.requests.find(r => r.method === 'POST' && r.path === '/v1/accounts' && r.body?.provider === 'codex');
  assert.ok(enrollReq, 'POST /v1/accounts sent');
  assert.ok(enrollReq.machineId.length > 0, 'X-PDD-Machine-Id header sent');
  assert.equal(enrollReq.body.plan, 'plus');
  assert.equal(enrollReq.body.bundle.auth_json.tokens.refresh_token, rawRefresh);

  // Local ~/.codex/auth.json is mode 0600 and has refresh_token === "".
  const localCodexPath = join(sb.home, '.codex', 'auth.json');
  assert.equal(statSync(localCodexPath).mode & 0o777, 0o600);
  const localCodex = JSON.parse(readFileSync(localCodexPath, 'utf8'));
  assert.equal(localCodex.tokens.refresh_token, '');
  assert.equal(localCodex.auth_mode, 'chatgpt');

  // Re-importing an already-stripped local auth.json refuses cleanly instead of overwriting Cloud with "".
  const reimportStripped = await invokeCli(['accounts', 'import', '--provider', 'codex', '--label', 'dup'], sb);
  assert.equal(reimportStripped.exit, 1);
  assert.match(reimportStripped.stderr, /already has a stripped refresh token/);

  // 2. pdd accounts import --provider claude --label max-1 (preserving unrelated ~/.claude/settings.json keys)
  const claudeDir = join(sb.home, '.claude');
  mkdirSync(claudeDir, { recursive: true });
  writeFileSync(join(claudeDir, 'settings.json'), JSON.stringify({
    theme: 'dark',
    env: { CUSTOM_USER_FLAG: 'keep-me', CLAUDE_CODE_OAUTH_TOKEN: rawClaudeOauth },
  }));
  const importClaude = await invokeCli(['accounts', 'import', '--provider', 'claude', '--label', 'max-1'], sb);
  assert.equal(importClaude.exit, 0, importClaude.stderr);

  const claudeSettingsPath = join(sb.home, '.claude', 'settings.json');
  const claudeJsonPath = join(sb.home, '.claude.json');
  assert.equal(statSync(claudeSettingsPath).mode & 0o777, 0o600);
  const claudeSettings = JSON.parse(readFileSync(claudeSettingsPath, 'utf8'));
  assert.equal(claudeSettings.theme, 'dark');
  assert.equal(claudeSettings.env.CUSTOM_USER_FLAG, 'keep-me');
  assert.match(claudeSettings.env.CLAUDE_CODE_OAUTH_TOKEN, /^sk-ant-oat01-max-1-/);
  assert.equal(JSON.parse(readFileSync(claudeJsonPath, 'utf8')).hasCompletedOnboarding, true);

  // 3. pdd accounts list & --json
  const listTable = await invokeCli(['accounts', 'list'], sb);
  assert.equal(listTable.exit, 0);
  assert.match(listTable.stdout, /LABEL\s+PROVIDER\s+ACCESS\s+5H\s+7D\s+STATE/);
  assert.match(listTable.stdout, /\*\s+plus-1\s+codex/);
  assert.match(listTable.stdout, /\*\s+max-1\s+claude/);
  assert.match(listTable.stdout, /Pending share invites:/);
  assert.match(listTable.stdout, /inv_team1\s+team-claude\s+claude\s+from team-lead/);

  const listJson = await invokeCli(['accounts', '--json'], sb);
  assert.equal(listJson.exit, 0);
  const parsedList = JSON.parse(listJson.stdout);
  assert.equal(parsedList.accounts.length, 2);
  assert.equal(parsedList.pending_invites.length, 1);

  // 4. Zero secrets stored in accounts-state.json or printed anywhere.
  const statePath = join(sb.stateDir, 'accounts-state.json');
  assert.equal(statSync(statePath).mode & 0o777, 0o600);
  const stateRaw = readFileSync(statePath, 'utf8');
  for (const secret of [rawRefresh, rawAccess, rawClaudeOauth, 'acc_tok_', 'personalSecretToken888']) {
    assert.ok(!stateRaw.includes(secret), `accounts-state.json must not contain ${secret}`);
    assert.ok(!addCodex.stdout.includes(secret) && !addCodex.stderr.includes(secret));
    assert.ok(!importClaude.stdout.includes(secret) && !importClaude.stderr.includes(secret));
    assert.ok(!listTable.stdout.includes(secret) && !listJson.stdout.includes(secret));
  }
});

test('3252 T2: use, next, shared Claude gateway_grant, share/accept/unshare/leave/pause/unpause/remove/log match exact contract', async t => {
  const cloud = await createMockCloudServer(t, {
    accounts: [
      {
        account_id: 'acc_cx_later',
        label: 'cx-later',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        shared: false,
        state: 'ready',
        five_hour_used_percent: 10,
        five_hour_reset_at: '2026-11-15T01:00:00Z',
        weekly_used_percent: 20,
        weekly_reset_at: '2026-11-20T00:00:00Z',
        cooling_until: null,
        created_at: '2026-11-01T00:00:00Z',
      },
      {
        account_id: 'acc_cx_sooner',
        label: 'cx-sooner',
        provider: 'codex',
        plan: 'plus',
        owner_login: 'Serhan-Asad',
        shared: false,
        state: 'ready',
        five_hour_used_percent: 45,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 70,
        weekly_reset_at: '2026-11-16T08:00:00Z',
        cooling_until: null,
        created_at: '2026-11-02T00:00:00Z',
      },
      {
        account_id: 'acc_cl_own',
        label: 'cl-own',
        provider: 'claude',
        plan: 'max',
        owner_login: 'Serhan-Asad',
        shared: false,
        state: 'ready',
        five_hour_used_percent: 5,
        five_hour_reset_at: '2026-11-15T01:00:00Z',
        weekly_used_percent: 10,
        weekly_reset_at: '2026-11-19T00:00:00Z',
        cooling_until: null,
        created_at: '2026-11-01T00:00:00Z',
      },
    ],
    pendingInvites: [
      { invite_id: 'inv_shared_cl', account_id: 'acc_cl_shared', label: 'cl-shared', provider: 'claude', owner_login: 'org-owner' },
    ],
  });
  const sb = makeTempSandbox(t, cloud.serverUrl);

  // Pin cx-later first, then run `pdd accounts next --provider codex` -> switches to cx-sooner (soonest weekly reset).
  assert.equal((await invokeCli(['accounts', 'use', 'cx-later'], sb)).exit, 0);
  const nextRes = await invokeCli(['accounts', 'next', '--provider', 'codex'], sb);
  assert.equal(nextRes.exit, 0);
  assert.match(nextRes.stdout, /Switched codex account to "cx-sooner"/);
  const codexAuth = JSON.parse(readFileSync(join(sb.home, '.codex', 'auth.json'), 'utf8'));
  assert.equal(codexAuth.tokens.access_token, 'acc_tok_cx-sooner_secret12345');
  assert.equal(codexAuth.tokens.refresh_token, '');

  // Accept shared Claude invite -> `use cl-shared` writes gateway_grant ANTHROPIC_BASE_URL + short-lived grant token.
  const acceptRes = await invokeCli(['accounts', 'accept', 'inv_shared_cl'], sb);
  assert.equal(acceptRes.exit, 0);
  assert.match(acceptRes.stdout, /Accepted shared account "cl-shared"/);

  assert.equal((await invokeCli(['accounts', 'use', 'cl-shared'], sb)).exit, 0);
  const sharedSettings = JSON.parse(readFileSync(join(sb.home, '.claude', 'settings.json'), 'utf8'));
  assert.equal(sharedSettings.env.CLAUDE_CODE_OAUTH_TOKEN, 'pddg_cl-shared_shortlived9999');
  assert.match(sharedSettings.env.ANTHROPIC_BASE_URL, new RegExp(`^${cloud.serverUrl.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}/v1/accounts/claude-gateway/lse_`));

  // Switching back to personal `cl-own` (`direct_oauth`) clears managed ANTHROPIC_BASE_URL cleanly!
  assert.equal((await invokeCli(['accounts', 'use', 'cl-own'], sb)).exit, 0);
  const ownSettings = JSON.parse(readFileSync(join(sb.home, '.claude', 'settings.json'), 'utf8'));
  assert.equal(ownSettings.env.CLAUDE_CODE_OAUTH_TOKEN, 'sk-ant-oat01-cl-own-personalSecretToken888');
  assert.equal(ownSettings.env.ANTHROPIC_BASE_URL, undefined);

  // Share with user (resolving numeric github_user_id via gh) and with org/team.
  const shareUser = await invokeCli(['accounts', 'share', 'cx-sooner', '--with', 'octocat'], sb, {
    run: async (cmd, args) => {
      assert.equal(cmd, 'gh');
      assert.deepEqual(args, ['api', 'users/octocat']);
      return { code: 0, stdout: JSON.stringify({ id: 583231, login: 'octocat', type: 'User' }), stderr: '' };
    },
  });
  assert.equal(shareUser.exit, 0, shareUser.stderr);
  assert.match(shareUser.stdout, /\(invite inv_\d+\)/);
  const shareReq = cloud.state.requests.findLast(r => r.path === '/v1/accounts/acc_cx_sooner/share');
  assert.deepEqual(shareReq.body, { github_login: 'octocat', github_user_id: 583231 });

  const shareTeam = await invokeCli(['accounts', 'share', 'cx-sooner', '--with', 'promptdriven/builders'], sb);
  assert.equal(shareTeam.exit, 0);
  const shareTeamReq = cloud.state.requests.findLast(r => r.path === '/v1/accounts/acc_cx_sooner/share');
  assert.deepEqual(shareTeamReq.body, { org: 'promptdriven', team: 'builders' });

  // pause, unpause, unshare, log, leave, remove
  assert.equal((await invokeCli(['accounts', 'pause', 'cx-later'], sb)).exit, 0);
  assert.equal(cloud.state.accounts.find(a => a.account_id === 'acc_cx_later').state, 'paused');
  assert.equal((await invokeCli(['accounts', 'unpause', 'cx-later'], sb)).exit, 0);
  assert.equal(cloud.state.accounts.find(a => a.account_id === 'acc_cx_later').state, 'ready');

  assert.equal((await invokeCli(['accounts', 'unshare', 'cx-sooner', '--user', 'octocat'], sb)).exit, 0);

  const logRes = await invokeCli(['accounts', 'log', 'cx-sooner'], sb);
  assert.equal(logRes.exit, 0);
  assert.match(logRes.stdout, /leased/);
  assert.match(logRes.stdout, /shared/);
  assert.doesNotMatch(logRes.stdout, /secret12345/);

  assert.equal((await invokeCli(['accounts', 'leave', 'cl-shared'], sb)).exit, 0);
  assert.equal((await invokeCli(['accounts', 'remove', 'cx-later'], sb)).exit, 0);
  assert.equal(cloud.state.accounts.some(a => a.account_id === 'acc_cx_later'), false);
});

test('3252 T3 & T4: sync 0ms cache hit, offline 1.2s fail-open, opt-in auto on|off|status idempotence, no reset command, and --pool hidden from help', async t => {
  const cloud = await createMockCloudServer(t, {
    accounts: [
      {
        account_id: 'acc_sync_1',
        label: 'sync-1',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        shared: false,
        state: 'ready',
        five_hour_used_percent: 25,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 40,
        weekly_reset_at: '2026-11-18T17:00:00Z',
        cooling_until: null,
        created_at: '2026-11-01T00:00:00Z',
      },
      {
        account_id: 'acc_sync_2',
        label: 'sync-2',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        shared: false,
        state: 'ready',
        five_hour_used_percent: 5,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 10,
        weekly_reset_at: '2026-11-17T17:00:00Z',
        cooling_until: null,
        created_at: '2026-11-02T00:00:00Z',
      },
    ],
  });
  const sb = makeTempSandbox(t, cloud.serverUrl);

  // Materialize sync-1 first.
  assert.equal((await invokeCli(['accounts', 'use', 'sync-1'], sb, { now: () => cloud.state.nowMs })).exit, 0);
  const requestsBefore = cloud.state.requests.length;

  // 1. Fast cached sync (< 100% on both windows and > 15m from expiry): 0 HTTP requests, empty stdout with --quiet!
  const fastStart = performance.now();
  const fastSync = await invokeCli(['accounts', 'sync', '--provider', 'codex', '--quiet'], sb, { now: () => cloud.state.nowMs });
  const fastElapsed = performance.now() - fastStart;
  assert.equal(fastSync.exit, 0);
  assert.equal(fastSync.stdout, '');
  assert.equal(fastSync.stderr, '');
  assert.equal(cloud.state.requests.length, requestsBefore, 'cached healthy lease makes zero HTTP requests');
  assert.ok(fastElapsed < 250, `expected fast local no-op, took ${fastElapsed}ms`);

  // 2. Advance clock to within 10 minutes of lease expiry -> sync refreshes lease via POST /v1/accounts/lease.
  cloud.state.nowMs += 42 * 60 * 1000;
  const refreshSync = await invokeCli(['accounts', 'sync', '--provider', 'codex'], sb, { now: () => cloud.state.nowMs });
  assert.equal(refreshSync.exit, 0);
  assert.match(refreshSync.stdout, /Synced codex account "sync-1"/);
  assert.equal(cloud.state.requests.length, requestsBefore + 1);

  // 3. Offline / slow Cloud server (> timeout-ms) fails open cleanly without touching local auth.json!
  const authBeforeTimeout = readFileSync(join(sb.home, '.codex', 'auth.json'), 'utf8');
  cloud.state.nowMs += 45 * 60 * 1000;
  cloud.state.delayLeaseMs = 600;
  const timeoutStart = performance.now();
  const failOpen = await invokeCli(['accounts', 'sync', '--provider', 'codex', '--quiet', '--timeout-ms', '120'], sb, { now: () => cloud.state.nowMs });
  const timeoutElapsed = performance.now() - timeoutStart;
  cloud.state.delayLeaseMs = 0;
  assert.equal(failOpen.exit, 0, 'sync always fails open on timeout');
  assert.equal(failOpen.stdout, '');
  assert.equal(failOpen.stderr, '');
  assert.ok(timeoutElapsed < 550, `timeout respected within budget: ${timeoutElapsed}ms`);
  assert.equal(readFileSync(join(sb.home, '.codex', 'auth.json'), 'utf8'), authBeforeTimeout);

  // 4. Opt-in terminal auto-switch: off by default, idempotent `on`, zero-trace `off`.
  const zshrc = join(sb.home, '.zshrc');
  const bashrc = join(sb.home, '.bashrc');
  writeFileSync(zshrc, 'export EDITOR=vim\n');
  assert.match((await invokeCli(['accounts', 'auto', 'status'], sb)).stdout, /Terminal auto-switch: off \(default\)/);

  assert.equal((await invokeCli(['accounts', 'auto', 'on'], sb)).exit, 0);
  assert.equal((await invokeCli(['accounts', 'auto', 'on'], sb)).exit, 0); // idempotent
  const zshWithAuto = readFileSync(zshrc, 'utf8');
  assert.equal(zshWithAuto.match(/# >>> pdd accounts auto >>>/g)?.length, 1);
  assert.match(zshWithAuto, /unalias codex claude 2>\/dev\/null \|\| true/);
  assert.match(zshWithAuto, /pdd accounts sync --provider codex --quiet --timeout-ms 1200 2>\/dev\/null \|\| true/);
  assert.match(zshWithAuto, /command codex "\$@"/);
  assert.match(zshWithAuto, /command claude "\$@"/);
  assert.match((await invokeCli(['accounts', 'auto', 'status'], sb)).stdout, /Terminal auto-switch: on/);

  assert.equal((await invokeCli(['accounts', 'auto', 'off'], sb)).exit, 0);
  assert.equal(readFileSync(zshrc, 'utf8'), 'export EDITOR=vim\n');
  assert.equal(readFileSync(bashrc, 'utf8'), '');
  assert.doesNotMatch(readFileSync(zshrc, 'utf8'), /pdd accounts auto/);

  // 5. Zero reset-credit commands and --pool hidden from public help.
  const resetAttempt = await invokeCli(['accounts', 'reset'], sb);
  assert.equal(resetAttempt.exit, 2);
  const rootHelp = await invokeCli(['--help'], sb);
  const autopilotHelp = await invokeCli(['autopilot', '--help'], sb);
  const accountsHelp = await invokeCli(['accounts', '--help'], sb);
  assert.doesNotMatch(rootHelp.stdout, /--pool/);
  assert.doesNotMatch(autopilotHelp.stdout, /--pool/);
  assert.doesNotMatch(accountsHelp.stdout, /accounts reset/i);
});

test('3252 T5: runStepAgentProcess enforces Stick-Until-100%, burst-429 same-account retry, 5h/7d failover by soonest weekly reset, and disposable 0700 Codex overlay', async t => {
  const cloud = await createMockCloudServer(t, {
    accounts: [
      {
        account_id: 'acc_a',
        label: 'acct-a',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        shared: false,
        state: 'ready',
        five_hour_used_percent: 82,
        five_hour_reset_at: '2026-11-15T01:30:00Z',
        weekly_used_percent: 98, // 98% > old 97% line: must NOT switch early!
        weekly_reset_at: '2026-11-19T00:00:00Z',
        cooling_until: null,
        created_at: '2026-11-01T00:00:00Z',
      },
      {
        account_id: 'acc_b_later',
        label: 'acct-b-later',
        provider: 'codex',
        plan: 'plus',
        owner_login: 'Serhan-Asad',
        shared: false,
        state: 'ready',
        five_hour_used_percent: 20,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 30,
        weekly_reset_at: '2026-11-20T12:00:00Z',
        cooling_until: null,
        created_at: '2026-11-02T00:00:00Z',
      },
      {
        account_id: 'acc_c_sooner',
        label: 'acct-c-sooner',
        provider: 'codex',
        plan: 'plus',
        owner_login: 'Serhan-Asad',
        shared: false,
        state: 'ready',
        five_hour_used_percent: 40,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 60,
        weekly_reset_at: '2026-11-16T06:00:00Z', // soonest weekly reset!
        cooling_until: null,
        created_at: '2026-11-03T00:00:00Z',
      },
      {
        account_id: 'acc_cl_shared',
        label: 'cl-shared-step',
        provider: 'claude',
        plan: 'max',
        owner_login: 'org-owner',
        shared: true,
        state: 'ready',
        five_hour_used_percent: 10,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 25,
        weekly_reset_at: '2026-11-17T00:00:00Z',
        cooling_until: null,
        created_at: '2026-11-01T00:00:00Z',
      },
    ],
  });
  const sb = makeTempSandbox(t, cloud.serverUrl);

  // Prepare user's ~/.codex with config.toml, skills, memories, sessions, rules, and a concurrent terminal auth.json.
  const userCodex = join(sb.home, '.codex');
  mkdirSync(userCodex, { recursive: true });
  writeFileSync(join(userCodex, 'config.toml'), 'model = "gpt-5"\n');
  for (const dirName of ['skills', 'memories', 'sessions', 'rules']) {
    mkdirSync(join(userCodex, dirName), { recursive: true });
    writeFileSync(join(userCodex, dirName, 'marker.txt'), dirName);
  }
  const concurrentTerminalAuth = JSON.stringify({ auth_mode: 'chatgpt', tokens: { access_token: 'terminal_session_untouched', refresh_token: '' } });
  writeFileSync(join(userCodex, 'auth.json'), concurrentTerminalAuth, { mode: 0o600 });

  // Enroll local state on acct-a first (then restore concurrentTerminalAuth to prove step overlays never touch ~/.codex/auth.json).
  assert.equal((await invokeCli(['accounts', 'use', 'acct-a'], sb)).exit, 0);
  writeFileSync(join(userCodex, 'auth.json'), concurrentTerminalAuth, { mode: 0o600 });

  // 1. Stick-Until-Out across 3 consecutive steps at 98% / 99% weekly usage -> stays on acct-a (0 switches)!
  const observedOverlays = [];
  for (const pct of [98, 99, 99]) {
    cloud.state.accounts[0].weekly_used_percent = pct;
    const stepRes = await runStepAgentProcess({
      agent: 'codex',
      step: 'build',
      cwd: sb.cwd,
      env: sb.env,
      accountsPorts: { burstRetryMs: 5 },
      run: async (_cmd, _args, opts) => {
        const overlay = opts.env.CODEX_HOME;
        observedOverlays.push(overlay);
        assert.notEqual(overlay, userCodex);
        assert.match(basename(overlay), /^pdd-cx-/);
        assert.equal(statSync(overlay).mode & 0o777, 0o700);
        assert.equal(statSync(join(overlay, 'auth.json')).mode & 0o777, 0o600);
        for (const item of ['config.toml', 'skills', 'memories', 'sessions', 'rules']) {
          assert.equal(lstatSync(join(overlay, item)).isSymbolicLink(), true, `${item} symlinked in overlay`);
        }
        const overlayAuth = JSON.parse(readFileSync(join(overlay, 'auth.json'), 'utf8'));
        assert.equal(overlayAuth.tokens.access_token, 'acc_tok_acct-a_secret12345');
        assert.equal(overlayAuth.tokens.refresh_token, '');
        return { code: 0, stdout: 'ok\n', stderr: '' };
      },
    });
    assert.equal(stepRes.account.label, 'acct-a');
  }
  for (const ov of observedOverlays) {
    assert.equal(existsSync(ov), false, `overlay ${ov} wiped on step exit`);
  }
  assert.equal(readFileSync(join(userCodex, 'auth.json'), 'utf8'), concurrentTerminalAuth, 'concurrent ~/.codex/auth.json untouched');

  // 2. Brief burst 429 while 5h < 100% and 7d < 100% retries on the SAME account (acct-a) so prompt cache stays warm!
  let burstCalls = 0;
  const burstRes = await runStepAgentProcess({
    agent: 'codex',
    step: 'build',
    cwd: sb.cwd,
    env: sb.env,
    accountsPorts: { burstRetryMs: 5 },
    run: async (_cmd, _args, opts) => {
      burstCalls++;
      const auth = JSON.parse(readFileSync(join(opts.env.CODEX_HOME, 'auth.json'), 'utf8'));
      assert.equal(auth.tokens.access_token, 'acc_tok_acct-a_secret12345');
      if (burstCalls === 1) return { code: 1, stdout: '', stderr: '429 Too Many Requests: rate limit exceeded' };
      return { code: 0, stdout: 'warm cache success\n', stderr: '' };
    },
  });
  assert.equal(burstCalls, 2);
  assert.equal(burstRes.account.label, 'acct-a', 'stayed on acct-a after transient burst 429');

  // 3. 5h == 100% (`usage_limit_reached`) -> reports usage to Cloud, cools acct-a, and switches to acct-c-sooner (soonest weekly reset)!
  let failoverCalls = 0;
  const failoverStart = performance.now();
  const failoverRes = await runStepAgentProcess({
    agent: 'codex',
    step: 'build',
    cwd: sb.cwd,
    env: sb.env,
    accountsPorts: { burstRetryMs: 5 },
    run: async (_cmd, _args, opts) => {
      failoverCalls++;
      const auth = JSON.parse(readFileSync(join(opts.env.CODEX_HOME, 'auth.json'), 'utf8'));
      if (failoverCalls === 1) {
        assert.equal(auth.tokens.access_token, 'acc_tok_acct-a_secret12345');
        return { code: 1, stdout: '', stderr: 'Error 429: usage_limit_reached (resets at 2026-11-15T01:30:00Z)' };
      }
      assert.equal(auth.tokens.access_token, 'acc_tok_acct-c-sooner_secret12345');
      return { code: 0, stdout: 'completed on acct-c-sooner\n', stderr: '' };
    },
  });
  assert.ok(performance.now() - failoverStart < 2000, 'failover completed in < 2s');
  assert.equal(failoverCalls, 2);
  assert.equal(failoverRes.account.label, 'acct-c-sooner');
  assert.equal(cloud.state.accounts.find(a => a.account_id === 'acc_a').state, 'cooling');

  // 4. 7d == 100% (`weekly usage limit reached`) on acct-c-sooner -> cools for full multi-day weekly_reset_at and switches to acct-b-later!
  let weeklyCalls = 0;
  const weeklyRes = await runStepAgentProcess({
    agent: 'codex',
    step: 'review',
    cwd: sb.cwd,
    env: sb.env,
    accountsPorts: { burstRetryMs: 5 },
    run: async (_cmd, _args, opts) => {
      weeklyCalls++;
      const auth = JSON.parse(readFileSync(join(opts.env.CODEX_HOME, 'auth.json'), 'utf8'));
      if (weeklyCalls === 1) {
        assert.equal(auth.tokens.access_token, 'acc_tok_acct-c-sooner_secret12345');
        return { code: 1, stdout: '', stderr: 'You have hit your weekly usage limit (usage_limit_reached until 2026-11-16T06:00:00Z)' };
      }
      assert.equal(auth.tokens.access_token, 'acc_tok_acct-b-later_secret12345');
      return { code: 0, stdout: 'completed on acct-b-later\n', stderr: '' };
    },
  });
  assert.equal(weeklyCalls, 2);
  assert.equal(weeklyRes.account.label, 'acct-b-later');
  const cooledC = cloud.state.accounts.find(a => a.account_id === 'acc_c_sooner');
  assert.equal(cooledC.state, 'cooling');
  assert.equal(cooledC.cooling_until, '2026-11-16T06:00:00Z');

  // 5. Shared Claude step isolation: passes CLAUDE_CODE_OAUTH_TOKEN + ANTHROPIC_BASE_URL through jobEnvironment!
  assert.equal((await invokeCli(['accounts', 'list'], sb)).exit, 0);
  const claudeStep = await runStepAgentProcess({
    agent: 'claude',
    step: 'build',
    cwd: sb.cwd,
    env: { ...sb.env, CLAUDECODE: '1', CLAUDE_CODE_ENTRYPOINT: 'cli' },
    run: async (_cmd, _args, opts) => {
      const sanitized = jobEnvironment(opts.env);
      assert.equal(sanitized.CLAUDE_CODE_OAUTH_TOKEN, 'pddg_cl-shared-step_shortlived9999');
      assert.match(sanitized.ANTHROPIC_BASE_URL, new RegExp(`^${cloud.serverUrl.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}/v1/accounts/claude-gateway/lse_`));
      assert.equal(sanitized.CLAUDECODE, undefined);
      assert.equal(sanitized.CLAUDE_CODE_ENTRYPOINT, undefined);
      return { code: 0, stdout: 'claude ok\n', stderr: '' };
    },
  });
  assert.equal(claudeStep.account.label, 'cl-shared-step');

  // 6. parseCodexUsageWindows respects weeklyStopPercent = 100 for Cloud accounts.
  const windows98 = parseCodexUsageWindows({
    rateLimits: {
      primary: { usedPercent: 50, resetsAt: 1794700000 },
      secondary: { usedPercent: 98, resetsAt: 1795000000 },
    },
  }, { weeklyStopPercent: 100 });
  assert.equal(windows98.state, 'healthy');
  assert.equal(windows98.weekly_used_percent, 98);
});

test('3252 T6: Autopilot Cloud rotation switches on 100% with zero strikes, pauses with "Waiting on AI quota until <wake_at>" on all_cooling, and auto-wakes', async t => {
  const baseMs = Date.parse('2026-11-10T12:00:00Z');
  const wakeIso = '2026-11-10T14:00:00.000Z';
  const cloud = await createMockCloudServer(t, {
    nowMs: baseMs,
    accounts: [
      {
        account_id: 'acc_ap_1',
        label: 'ap-1',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        shared: false,
        state: 'ready',
        five_hour_used_percent: 90,
        five_hour_reset_at: wakeIso,
        weekly_used_percent: 98,
        weekly_reset_at: '2026-11-15T00:00:00.000Z',
        cooling_until: null,
        created_at: '2026-11-01T00:00:00Z',
      },
      {
        account_id: 'acc_ap_2',
        label: 'ap-2',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        shared: false,
        state: 'ready',
        five_hour_used_percent: 30,
        five_hour_reset_at: '2026-11-10T15:00:00.000Z',
        weekly_used_percent: 50,
        weekly_reset_at: '2026-11-14T00:00:00.000Z',
        cooling_until: null,
        created_at: '2026-11-02T00:00:00Z',
      },
    ],
  });

  const w = await coreWorld(t, { settings: { runs: 1 } });
  cloud.state.nowMs = w.now();
  const sb = makeTempSandbox(t, cloud.serverUrl);
  assert.equal((await invokeCli(['accounts', 'use', 'ap-1'], sb, { now: () => w.now() })).exit, 0);

  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], testCommand: 'npm test', runs: 1 } }));
  w.issue(17, { labels: ['pdd:autopilot'] });
  w.issue(18, { labels: ['pdd:autopilot'] });

  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel');
  const stateRoot = join(w.dir, 'launcher-state');
  mkdirSync(stateRoot, { recursive: true });
  const stateFile = join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`);
  writeFileSync(stateFile, JSON.stringify({
    enabled: true,
    cwd,
    repo: 'acme/widgets',
    defaultBranch: 'main',
    coordinatorId: 'coord-cloud',
    machine: 'machine-cloud',
    engine: 'core',
    label: 'pdd:autopilot',
    agent: { id: 'codex', kind: 'codex', command: 'codex' },
    packageRoot: join(w.dir, 'pkg'),
  }));

  const alerts = [];
  const ports = {
    stateRoot,
    now: () => { cloud.state.nowMs = w.now(); return w.now(); },
    env: sb.env,
    timer: async () => true,
    warn: () => {},
    sendAlert: async input => { alerts.push(input); return { exitCode: 0, message: 'sent' }; },
    run: async (command, args, options = {}) => {
      if (command === 'gh') return w.gh(args, options);
      if (command !== 'git') assert.fail(`unexpected program ${command}`);
      const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' });
      return { code: r.status, stdout: r.stdout, stderr: r.stderr };
    },
    machineGuard: w.machineGuard,
    corePorts: {
      jobs: w.jobs,
      checkBase: async () => ({ exitCode: 0, message: 'ok' }),
    },
  };

  // 1. Tick 1 starts Issue #17 on ap-1 (at 98% weekly — Stick-Until-100%) inside a 0700 pdd-cx-* overlay!
  const t1 = await tickAutopilot(stateFile, ports);
  assert.match(t1.message, /1 started/);
  const build1 = w.job(17, 'build');
  assert.ok(build1);
  assert.match(basename(build1.env.CODEX_HOME), /^pdd-cx-/);
  assert.equal(statSync(build1.env.CODEX_HOME).mode & 0o777, 0o700);
  const build1Overlay = build1.env.CODEX_HOME;

  // 2. Build 1 hits 100% quota (`usage_limit_reached`) -> rotates in-place to ap-2 with 0 strikes and cleans up build1's overlay!
  writeFileSync(build1.log, `Error 429: usage_limit_reached (resets at ${wakeIso})\n`);
  w.finish(17, 'build', { code: 1 });
  for (const dir of build1.cleanupDirs ?? []) rmSync(dir, { recursive: true, force: true });

  const t2 = await tickAutopilot(stateFile, ports);
  assert.equal(existsSync(build1Overlay), false);
  const savedJobAfterRotate = JSON.parse(readFileSync(join(stateFile.replace(/\.json$/, '-core'), 'jobs', '17.json'), 'utf8'));
  assert.equal(savedJobAfterRotate.agent.loginId, 'acc_ap_2', `expected rotation to acc_ap_2, got ${savedJobAfterRotate.agent?.loginId} (${t2.message})`);
  assert.ok(!w.labels(17).includes('pdd:stuck'), 'zero strikes on quota failover');

  // Finish Issue #17 build, review, and suite -> merges cleanly!
  const { pr } = w.build(17);
  await tickAutopilot(stateFile, ports);
  w.review(17, 'PASS');
  w.suite(17, 0);
  await tickAutopilot(stateFile, ports);
  assert.deepEqual(w.github.merges, [pr.number]);

  // 3. Now ap-2 also hits 100% on Issue #18 -> all accounts cooling -> "Waiting on AI quota until <wakeIso>"!
  await tickAutopilot(stateFile, ports); // claims #18 on ap-2
  const build18 = w.job(18, 'build');
  assert.ok(build18);
  cloud.state.accounts[1].five_hour_reset_at = '2026-11-10T15:00:00.000Z';
  writeFileSync(build18.log, 'Error 429: usage_limit_reached (resets at 2026-11-10T15:00:00.000Z)\n');
  w.finish(18, 'build', { code: 1 });

  const allCoolingTick = await tickAutopilot(stateFile, ports);
  assert.match(allCoolingTick.message, /Waiting on AI quota until 2026-11-10T14:00:00\.000Z/);
  assert.equal(alerts.length, 1, 'one deduplicated usage-limit alert sent');

  const statusWhileCooling = await runAutopilotLauncher({ command: 'status', cwd, packageRoot: join(w.dir, 'pkg'), env: sb.env }, ports);
  assert.match(statusWhileCooling.message, /Waiting on AI quota until 2026-11-10T14:00:00\.000Z/);

  // 4. Advance clock past wakeIso (2h + 1m) -> ap-1 auto-wakes and Autopilot claims Issue #18 automatically!
  w.advance(121 * 60 * 1000);
  const wokeTick = await tickAutopilot(stateFile, ports);
  assert.match(wokeTick.message, /1 started/);
  assert.ok(w.job(18, 'build'), 'Autopilot auto-woke at wake_at and resumed Issue #18');
});

test('3252 T7: Round 1 security, FastAPI contract, overlay cleanup, env isolation, alias safety, and burst rotation invariants', async t => {
  const cloud = await createMockCloudServer(t, {
    accounts: [
      {
        account_id: 'acc_r1_1',
        label: 'r1-1',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        shared: false,
        state: 'ready',
        five_hour_used_percent: 12,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 34,
        weekly_reset_at: '2026-11-18T17:00:00Z',
        cooling_until: null,
        created_at: '2026-11-01T00:00:00Z',
      },
      {
        account_id: 'acc_r1_2',
        label: 'r1-2',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        shared: false,
        state: 'ready',
        five_hour_used_percent: 5,
        five_hour_reset_at: '2026-11-15T03:00:00Z',
        weekly_used_percent: 15,
        weekly_reset_at: '2026-11-17T17:00:00Z',
        cooling_until: null,
        created_at: '2026-11-02T00:00:00Z',
      },
    ],
  });
  const sb = makeTempSandbox(t, cloud.serverUrl);

  // 1. Cross-process regex redaction scrubs pddg_ grants, rt_ refresh tokens, and 3-segment eyJ JWTs without rememberSecrets!
  const unrememberedJwt = 'eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiJ1c2VyXzEyMyIsImVtYWlsIjoidGVzdEBleGFtcGxlLmNvbSJ9.SflKxwRJSMeKKF2QT4fwpMeJf36POk6yJV_adQssw5c';
  const unrememberedGrant = 'pddg_unrememberedGatewayGrant987654321';
  const unrememberedRefresh = 'rt_unrememberedRefreshToken_abcdef123456';
  const scrubbed = redactSecrets(`grant=${unrememberedGrant} refresh=${unrememberedRefresh} jwt=${unrememberedJwt}`);
  assert.doesNotMatch(scrubbed, /pddg_unremembered/);
  assert.doesNotMatch(scrubbed, /rt_unremembered/);
  assert.doesNotMatch(scrubbed, /eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCJ9/);
  assert.equal(scrubbed, 'grant=[redacted] refresh=[redacted] jwt=[redacted]');

  // 2. Overlay mkdtempSync + 0700 + signal/exit sweep + cleanupAgentJob when !alive && !processManifest(saved)
  const sigintBefore = process.listenerCount('SIGINT');
  const sigtermBefore = process.listenerCount('SIGTERM');
  const ov = createCodexStepOverlay(
    { tokens: { access_token: 'acc_tok_ov_test12345', refresh_token: 'rt_stripme_1234567890', id_token: 'id_1', account_id: 'acct_1' } },
    { env: sb.env, tmpRoot: sb.root },
  );
  assert.equal(statSync(ov.overlayDir).mode & 0o777, 0o700);
  assert.equal(process.listenerCount('SIGINT'), sigintBefore + 1);
  sweepActiveCodexOverlays();
  assert.equal(existsSync(ov.overlayDir), false, 'sweepActiveCodexOverlays wipes active overlay');
  assert.equal(process.listenerCount('SIGINT'), sigintBefore, 'signal listeners restored to exact baseline');
  assert.equal(process.listenerCount('SIGTERM'), sigtermBefore, 'SIGTERM listeners restored to exact baseline');

  const deadJobOverlay = mkdtempSync(join(sb.root, 'pdd-cx-'));
  chmodSync(deadJobOverlay, 0o700);
  writeFileSync(join(deadJobOverlay, 'auth.json'), '{"tokens":{"access_token":"x"}}', { mode: 0o600 });
  const deadSpec = join(sb.root, 'dead-job.spec.json');
  writeFileSync(deadSpec, JSON.stringify({ command: 'codex', args: [], cwd: sb.cwd, cleanupDirs: [deadJobOverlay] }));
  await cleanupAgentJob({ pid: 999991, token: deadSpec }, { alive: () => false, list: () => [] });
  assert.equal(existsSync(deadJobOverlay), false, 'cleanupAgentJob removes pdd-cx-* even when !alive && !processManifest(saved)');

  // 3 & 6. Strip ambient CLAUDE_CODE_OAUTH_TOKEN & managed /v1/accounts/claude-gateway ANTHROPIC_BASE_URL
  const dirtyAmbient = {
    HOME: sb.home,
    PATH: sb.env.PATH,
    CLAUDE_CODE_OAUTH_TOKEN: 'pddg_ambientLeakedToken12345678',
    ANTHROPIC_BASE_URL: 'https://api.promptdriven.ai/v1/accounts/claude-gateway/lse_99',
  };
  const cleanLocal = loginEnvironment(dirtyAmbient, { kind: 'codex', configVar: 'CODEX_HOME', configDir: '/tmp/custom-codex', env: {} });
  assert.equal(cleanLocal.CLAUDE_CODE_OAUTH_TOKEN, undefined);
  assert.equal(cleanLocal.ANTHROPIC_BASE_URL, undefined);

  const codexStep = prepareCloudStepExecution({
    account: { account_id: 'acc_r1_1', provider: 'codex' },
    lease: { codex_auth_json: { tokens: { access_token: 'at_12345678', refresh_token: '', id_token: 'id_1', account_id: 'acct_1' } } },
  }, dirtyAmbient, { tmpRoot: sb.root });
  try {
    assert.equal(codexStep.env.CLAUDE_CODE_OAUTH_TOKEN, undefined);
    assert.equal(codexStep.env.ANTHROPIC_BASE_URL, undefined);
  } finally {
    codexStep.cleanup();
  }

  // Switching Claude settings.json from /v1/accounts/claude-gateway/<lease> to direct_oauth removes ANTHROPIC_BASE_URL even if previousManagedBaseUrl is false!
  mkdirSync(join(sb.home, '.claude'), { recursive: true });
  writeFileSync(join(sb.home, '.claude', 'settings.json'), JSON.stringify({
    env: { ANTHROPIC_BASE_URL: 'https://api.promptdriven.ai/v1/accounts/claude-gateway/lse_old' },
  }));
  materializeLocalClaudeAuth({ delivery_mode: 'direct_oauth', claude_oauth_token: 'sk-ant-oat01-directToken123456' }, { env: sb.env, previousManagedBaseUrl: false });
  const afterDirect = JSON.parse(readFileSync(join(sb.home, '.claude', 'settings.json'), 'utf8'));
  assert.equal(afterDirect.env.ANTHROPIC_BASE_URL, undefined);

  // 4. Production URL defaults to https://api.promptdriven.ai and ignores PDD_RUNTIME_URL!
  assert.equal(DEFAULT_CLOUD_URL, 'https://api.promptdriven.ai');
  assert.equal(resolveCloudAccountsEndpoint({ PDD_RUNTIME_URL: 'https://interpreter.example.com' }), 'https://api.promptdriven.ai');
  assert.equal(resolveCloudAccountsEndpoint({ PDD_CLOUD_URL: 'https://cloud.example.com/' }), 'https://cloud.example.com');
  assert.equal(resolveCloudAccountsEndpoint({ PDD_ACCOUNTS_URL: 'https://accounts.example.com/', PDD_CLOUD_URL: 'https://cloud.example.com' }), 'https://accounts.example.com');

  // 5. FastAPI HTTPException detail envelope unwrapping ({"detail": {"error": ..., "message": ...}})
  await assert.rejects(
    () => cloudAccountsRequest('GET', '/v1/accounts', { env: sb.env }, {
      fetch: async () => new Response(JSON.stringify({
        detail: { error: 'github_not_linked', message: 'Link your GitHub account in PDD Cloud first.' },
      }), { status: 403, headers: { 'content-type': 'application/json' } }),
    }),
    err => {
      assert.ok(err instanceof CloudAccountsError);
      assert.equal(err.code, 'github_not_linked');
      assert.match(err.message, /Link your GitHub account in PDD Cloud first/);
      return true;
    },
  );

  // 7. Clamp/floor usage percents to strict int 0..100 without rounding 99.9 up to 100!
  assert.equal(normalizeUsagePercentInt(99.9), 99);
  assert.equal(normalizeUsagePercentInt(42.7), 42);
  assert.equal(normalizeUsagePercentInt(-3.5), 0);
  assert.equal(normalizeUsagePercentInt(100.4), 100);
  assert.equal(normalizeUsagePercentInt(null), null);
  const reportReply = await reportCloudAccountUsage('acc_r1_1', {
    five_hour_used_percent: 42.8,
    weekly_used_percent: 99.9,
    limit_reached: false,
  }, { cwd: sb.cwd, env: sb.env });
  assert.equal(reportReply.account.five_hour_used_percent, 42);
  assert.equal(reportReply.account.weekly_used_percent, 99);

  // 8. Validate all 4 Codex token fields locally before upload!
  mkdirSync(join(sb.home, '.codex'), { recursive: true });
  writeFileSync(join(sb.home, '.codex', 'auth.json'), JSON.stringify({
    tokens: { access_token: 'at_12345678', refresh_token: 'rt_123456789012', id_token: '', account_id: '' },
  }));
  const reqCountBeforeBadImport = cloud.state.requests.length;
  const badImport = await invokeCli(['accounts', 'import', '--provider', 'codex', '--label', 'bad-codex'], sb);
  assert.equal(badImport.exit, 1);
  assert.match(badImport.stderr, /missing required OAuth token fields: id_token, account_id/);
  assert.equal(cloud.state.requests.length, reqCountBeforeBadImport, 'invalid Codex bundle rejected before network upload');

  // 9. Reject GitHub organization without /team on `pdd accounts share`!
  const orgShare = await invokeCli(['accounts', 'share', 'r1-1', '--with', 'promptdriven'], sb, {
    run: async () => ({ code: 0, stdout: JSON.stringify({ id: 777, login: 'promptdriven', type: 'Organization' }), stderr: '' }),
  });
  assert.equal(orgShare.exit, 1);
  assert.match(orgShare.stderr, /is a GitHub organization\. Pass --with promptdriven\/<team>/);

  // 10. `unalias codex claude` in shell block prevents zsh/bash syntax errors when user has prior `alias codex=...`!
  const aliasZsh = join(sb.home, '.zshrc');
  writeFileSync(aliasZsh, "alias codex='codex --full-auto'\nalias claude='claude --verbose'\n");
  assert.equal((await invokeCli(['accounts', 'auto', 'on'], sb)).exit, 0);
  for (const sh of ['/bin/bash', '/bin/zsh']) {
    if (existsSync(sh)) {
      const parseCheck = spawnSync(sh, ['-c', `source ${JSON.stringify(aliasZsh)}`], { encoding: 'utf8' });
      assert.equal(parseCheck.status, 0, `${sh} sourced profile with prior aliases cleanly: ${parseCheck.stderr}`);
    }
  }

  // 11 & 12. Autopilot keepEnv preserves PDD_STATE_DIR/PDD_CLOUD_URL/PDD_ACCOUNTS_URL/XDG_STATE_HOME, and burst 429 retry counts rotation when /lease switches accounts!
  const w = await coreWorld(t, { settings: { runs: 1 } });
  cloud.state.nowMs = w.now();
  assert.equal((await invokeCli(['accounts', 'use', 'r1-1'], sb, { now: () => w.now() })).exit, 0);
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], testCommand: 'npm test', runs: 1 } }));
  w.issue(31, { labels: ['pdd:autopilot'] });
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel');
  const stateRoot = join(w.dir, 'launcher-state-r1');
  mkdirSync(stateRoot, { recursive: true });
  const launcherEnv = {
    ...sb.env,
    XDG_STATE_HOME: join(sb.root, 'xdg-state'),
    PDD_ACCOUNTS_URL: cloud.serverUrl,
    PDD_TOKEN: cloud.state.bearerToken,
  };
  const basePorts = {
    stateRoot,
    now: () => { cloud.state.nowMs = w.now(); return w.now(); },
    env: launcherEnv,
    timer: async () => true,
    warn: () => {},
    sendAlert: async () => ({ exitCode: 0, message: 'sent' }),
    doctor: async () => ({ exitCode: 0, ok: true, message: 'ok', warnings: [] }),
    run: async (command, args, options = {}) => {
      if (command === 'codex' && args[0] === 'login') return { code: 0, stdout: 'Logged in using ChatGPT\n', stderr: '' };
      if (command === 'codex' && args[0] === '--help') return { code: 0, stdout: '--sandbox\n', stderr: '' };
      if (command === 'gh') return w.gh(args, options);
      if (command !== 'git') assert.fail(`unexpected program ${command}`);
      const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' });
      return { code: r.status, stdout: r.stdout, stderr: r.stderr };
    },
    machineGuard: w.machineGuard,
    corePorts: {
      jobs: w.jobs,
      burstRetryMs: 1,
      checkBase: async () => ({ exitCode: 0, message: 'ok' }),
    },
  };
  const startedRes = await runAutopilotLauncher({
    command: 'start',
    cwd,
    packageRoot: process.cwd(),
    label: 'pdd:autopilot',
    mode: 'auto',
    agent: 'codex',
    env: launcherEnv,
  }, basePorts);
  assert.equal(startedRes.exitCode, 0, startedRes.message);
  const stateFile = join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`);
  const savedLauncherState = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.equal(savedLauncherState.environment.PDD_STATE_DIR, sb.stateDir);
  assert.equal(savedLauncherState.environment.XDG_STATE_HOME, launcherEnv.XDG_STATE_HOME);
  assert.equal(savedLauncherState.environment.PDD_ACCOUNTS_URL, cloud.serverUrl);
  assert.equal(savedLauncherState.environment.PDD_CLOUD_URL, cloud.serverUrl);
  assert.equal(savedLauncherState.environment.PDD_TOKEN, undefined, 'never persist secret tokens in launcher state');
  assert.equal(savedLauncherState.environment.GH_TOKEN, undefined, 'never persist GH_TOKEN in launcher state');

  // Issue #31 started on acc_r1_1. Simulate server pausing acc_r1_1 right before burst-429 retry so /lease switches to acc_r1_2!
  const build31 = w.job(31, 'build');
  assert.equal(build31.loginId, 'acc_r1_1');
  cloud.state.accounts[0].state = 'paused';
  writeFileSync(build31.log, '429 Too Many Requests: rate limit exceeded\n');
  w.finish(31, 'build', { code: 1 });
  await tickAutopilot(stateFile, basePorts);
  const job31 = JSON.parse(readFileSync(join(stateFile.replace(/\.json$/, '-core'), 'jobs', '31.json'), 'utf8'));
  assert.equal(job31.agent.loginId, 'acc_r1_2', 'burst retry switched to acc_r1_2 when acc_r1_1 paused');
  assert.equal(job31.poolRotations, 1, 'server-switched burst retry counted as a pool rotation');
  assert.equal(job31.agent.burstRetried, undefined, 'fresh account retains its own burst-retry budget');
});
