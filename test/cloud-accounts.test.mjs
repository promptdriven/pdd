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
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { basename, join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { parseAgentAuthStatus, runStepAgentProcess } from '../src/agent-adapters.mjs';
import { cleanupAgentJob, jobEnvironment } from '../src/agent-job.mjs';
import { parseCodexUsageWindows } from '../src/codex-limits.mjs';
import {
  CloudAccountsError,
  DEFAULT_CLOUD_URL,
  cloudAccountsRequest,
  createCodexStepOverlay,
  localCodexAuthPath,
  localCodexConfigPath,
  loginEnvironment,
  materializeLocalClaudeAuth,
  materializeLocalCodexAuth,
  normalizeUsagePercentInt,
  prepareCloudStepExecution,
  reportCloudAccountUsage,
  resolveCloudAccountsEndpoint,
  restoreLocalCodexGatewayConfig,
  selectCloudPoolLogin,
  sweepActiveCodexOverlays,
} from '../src/login-pool.mjs';
import { parse as parseToml } from '../src/vendor/smol-toml/parse.js';
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
    activeLeases: new Map(),
    requests: [],
    delayLeaseMs: 0,
    dedupEnroll: Boolean(initial.dedupEnroll),
    zeroInitialUsage: Boolean(initial.zeroInitialUsage),
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
      query: url.search,
      headers: { ...req.headers },
      auth: req.headers.authorization ?? '',
      machineId,
      body,
    });

    const send = (status, payload) => {
      res.writeHead(status, { 'content-type': 'application/json' });
      res.end(JSON.stringify(payload));
    };

    const codexGatewayMatch = /^\/v1\/codex-gateway\/([^/]+)\/responses$/.exec(url.pathname);
    if (req.method === 'POST' && codexGatewayMatch) {
      const leaseId = decodeURIComponent(codexGatewayMatch[1]);
      const grantHeader = req.headers['x-pdd-gateway-grant'] ?? '';
      const leaseRecord = state.activeLeases.get(leaseId);
      if (!leaseRecord || leaseRecord.grantToken !== grantHeader) {
        return send(401, { error: { message: 'Invalid gateway grant' } });
      }
      const acc = state.accounts.find(a => a.account_id === leaseRecord.accountId);
      if (!acc || acc.revoked || acc.state === 'paused' || leaseRecord.revoked) {
        return send(403, { error: { message: 'Gateway grant revoked' } });
      }
      return send(200, { id: 'resp_gateway_ok', object: 'response', status: 'completed' });
    }

    if (req.headers.authorization !== `Bearer ${state.bearerToken}`) {
      res.writeHead(401, { 'content-type': 'application/json' });
      res.end(JSON.stringify({ detail: { error: 'unauthorized', message: 'Unauthorized' } }));
      return;
    }

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
      if (state.dedupEnroll) {
        const subjectKey = body?.provider === 'codex'
          ? `codex:${body?.bundle?.auth_json?.tokens?.account_id}`
          : `claude:${body?.bundle?.oauth_token}`;
        const existing = state.accounts.find(a => !a.revoked && a.provider === body.provider && a._subjectKey === subjectKey);
        if (existing) {
          state.vaultBundles.set(existing.account_id, structuredClone(body.bundle));
          logAudit(existing.account_id, 'refreshed', machineId, `provider=${existing.provider}`);
          return send(200, { account: existing, already_enrolled: true });
        }
      }
      const id = `acc_${state.nextSeq++}`;
      const coolingInit = state.enrollCoolingUntil ?? null;
      const zeroUsage = state.zeroInitialUsage && !coolingInit;
      const acc = {
        account_id: id,
        label: body.label,
        provider: body.provider,
        plan: body.plan ?? 'pro',
        owner_github_id: 95069916,
        owner_login: 'Serhan-Asad',
        is_owner: true,
        shared: false,
        state: coolingInit ? 'cooling' : 'ready',
        five_hour_used_percent: coolingInit ? 100 : (zeroUsage ? 0 : 8),
        five_hour_reset_at: coolingInit ?? (zeroUsage ? null : '2026-11-15T02:00:00Z'),
        weekly_used_percent: zeroUsage ? 0 : 22,
        weekly_reset_at: zeroUsage ? null : '2026-11-18T17:00:00Z',
        cooling_until: coolingInit,
        created_at: new Date(state.nowMs + state.nextSeq).toISOString(),
        _subjectKey: body?.provider === 'codex'
          ? `codex:${body?.bundle?.auth_json?.tokens?.account_id}`
          : `claude:${body?.bundle?.oauth_token}`,
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
        if (isReady(target)) {
          chosen = target;
          switched = body.current_account_id !== target.account_id;
        } else if (accessible.some(a => isReady(a))) {
          return send(409, { detail: { error: 'account_not_ready', message: `Account ${target.label} is ${target.state}` } });
        }
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
          wake_at: coolingTimes[0] ?? null,
          lease: null,
        });
      }

      logAudit(chosen.account_id, 'leased', body?.machine_label || machineId, `holder=${body?.holder_id ?? ''}`);
      const expiresAt = new Date(state.nowMs + 50 * 60 * 1000).toISOString();
      let lease;
      const isBorrowerShared = typeof chosen.is_owner === 'boolean' ? !chosen.is_owner : Boolean(chosen.shared);
      if (provider === 'codex' && isBorrowerShared) {
        const leaseId = `lse_${state.nextSeq++}`;
        const grantToken = `pddg_${chosen.label.replace(/[^A-Za-z0-9_-]/g, '_')}_codexGrant7777`;
        state.activeLeases.set(leaseId, { accountId: chosen.account_id, grantToken, revoked: false });
        lease = {
          lease_id: leaseId,
          expires_at: expiresAt,
          delivery_mode: 'gateway_grant',
          codex_gateway_url: `${serverUrl}/v1/codex-gateway/${leaseId}`,
          codex_gateway_token: grantToken,
          gateway_bearer_token: grantToken,
        };
      } else if (provider === 'codex') {
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
      } else if (isBorrowerShared) {
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
        for (const leaseRec of state.activeLeases.values()) {
          if (leaseRec.accountId === id) leaseRec.revoked = true;
        }
        logAudit(id, 'unshared', machineId, `user=${body?.github_login ?? body?.team ?? body?.org ?? body?.machine_id}`);
        return send(200, { revoked: true });
      }
      if (req.method === 'POST' && action === 'leave') {
        acc.revoked = true;
        for (const leaseRec of state.activeLeases.values()) {
          if (leaseRec.accountId === id) leaseRec.revoked = true;
        }
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
        plan: inv.provider === 'codex' ? 'pro' : 'max',
        owner_github_id: 111,
        owner_login: inv.owner_login,
        is_owner: false,
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

  // 4. Production URL defaults to https://pdd-byok-api-c437voydwa-uc.a.run.app and ignores PDD_RUNTIME_URL!
  assert.equal(DEFAULT_CLOUD_URL, 'https://pdd-byok-api-c437voydwa-uc.a.run.app');
  assert.equal(resolveCloudAccountsEndpoint({ PDD_RUNTIME_URL: 'https://interpreter.example.com' }), 'https://pdd-byok-api-c437voydwa-uc.a.run.app');
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

test('3252 T8: Round 2 single-provider Cloud enrollment preserves un-enrolled local agents, heals leave/list state, and runs --agent agy with Cloud active intake', async t => {
  const baseMs = Date.parse('2026-11-14T18:00:00Z');
  const cloud = await createMockCloudServer(t, {
    nowMs: baseMs,
    pendingInvites: [
      { invite_id: 'inv_only_cl', account_id: 'acc_shared_cl_r2', label: 'cl-team', provider: 'claude', owner_login: 'Serhan-Asad' },
    ],
  });
  const sb = makeTempSandbox(t, cloud.serverUrl);

  // 1. Accept shared Claude invite, then `leave` it -> accounts-state.json flips back to enrolled: false, providers: []!
  assert.equal((await invokeCli(['accounts', 'accept', 'inv_only_cl'], sb)).exit, 0);
  assert.equal((await invokeCli(['accounts', 'use', 'cl-team'], sb)).exit, 0);
  let stateAfterAccept = JSON.parse(readFileSync(join(sb.stateDir, 'accounts-state.json'), 'utf8'));
  assert.equal(stateAfterAccept.enrolled, true);
  assert.deepEqual(stateAfterAccept.providers, ['claude']);

  assert.equal((await invokeCli(['accounts', 'leave', 'cl-team'], sb)).exit, 0);
  let stateAfterLeave = JSON.parse(readFileSync(join(sb.stateDir, 'accounts-state.json'), 'utf8'));
  assert.equal(stateAfterLeave.enrolled, false, 'leaving last shared account sets enrolled: false');
  assert.deepEqual(stateAfterLeave.providers, []);
  assert.deepEqual(stateAfterLeave.active, {});

  // Also verify `pdd accounts list` keeps enrolled: false when 0 accessible accounts exist even if state was stale!
  writeFileSync(join(sb.stateDir, 'accounts-state.json'), JSON.stringify({ enrolled: true, providers: ['claude'], active: {}, cooling: {} }));
  assert.equal((await invokeCli(['accounts', 'list'], sb)).exit, 0);
  let stateAfterEmptyList = JSON.parse(readFileSync(join(sb.stateDir, 'accounts-state.json'), 'utf8'));
  assert.equal(stateAfterEmptyList.enrolled, false, 'list clears stale enrolled: true when 0 accessible accounts remain');
  assert.deepEqual(stateAfterEmptyList.providers, []);

  // 2. Enroll ONLY Codex (`providers: ["codex"]`):
  mkdirSync(join(sb.home, '.codex'), { recursive: true });
  writeFileSync(join(sb.home, '.codex', 'auth.json'), JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'at_cx_only_r2_secret8888',
      refresh_token: 'rt_cx_only_r2_secret1234',
      id_token: makeJwt({ email: 'cx-only@example.com', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
      account_id: 'acct_cx_only_r2',
    },
  }));
  assert.equal((await invokeCli(['accounts', 'import', '--provider', 'codex', '--label', 'cx-only'], sb)).exit, 0);
  const stateCodexOnly = JSON.parse(readFileSync(join(sb.stateDir, 'accounts-state.json'), 'utf8'));
  assert.equal(stateCodexOnly.enrolled, true);
  assert.deepEqual(stateCodexOnly.providers, ['codex']);

  // 2a. `pdd accounts sync --provider claude --quiet` (shell auto-wrapper) exits 0 with ZERO HTTP requests!
  const reqBeforeQuietSync = cloud.state.requests.length;
  const quietClaudeSync = await invokeCli(['accounts', 'sync', '--provider', 'claude', '--quiet'], sb);
  assert.equal(quietClaudeSync.exit, 0);
  assert.equal(cloud.state.requests.length, reqBeforeQuietSync, 'quiet sync for un-enrolled provider makes zero network calls');

  // 2b. `runStepAgentProcess` for un-enrolled `claude` runs local `claude` directly without calling /v1/accounts/lease!
  let localClaudeRuns = 0;
  const localClaudeRes = await runStepAgentProcess({
    agent: 'claude',
    step: 'build',
    args: ['-p', 'hi'],
    cwd: sb.root,
    env: { ...sb.env, CLAUDE_CODE_OAUTH_TOKEN: 'local-user-claude-token' },
    run: async (cmd, _args, opts) => {
      localClaudeRuns++;
      assert.equal(cmd, 'claude');
      assert.equal(opts.env.CLAUDE_CODE_OAUTH_TOKEN, 'local-user-claude-token', 'local Claude token preserved when Claude is not enrolled in Cloud');
      return { code: 0, stdout: 'ok', stderr: '' };
    },
  });
  assert.equal(localClaudeRes.code, 0);
  assert.equal(localClaudeRuns, 1);
  assert.equal(cloud.state.requests.length, reqBeforeQuietSync, 'un-enrolled claude step did not call Cloud /lease');

  // 2c. Even if accounts-state.json has stale `providers: ["codex", "claude"]` while Cloud has 0 Claude accounts,
  // `runStepAgentProcess` falls back to local `claude` and heals `accounts-state.json` (never throwing "until null")!
  writeFileSync(join(sb.stateDir, 'accounts-state.json'), JSON.stringify({
    ...stateCodexOnly,
    providers: ['codex', 'claude'],
  }));
  const healedClaudeRes = await runStepAgentProcess({
    agent: 'claude',
    step: 'build',
    args: ['-p', 'hi'],
    cwd: sb.root,
    env: sb.env,
    run: async cmd => {
      localClaudeRuns++;
      assert.equal(cmd, 'claude');
      return { code: 0, stdout: 'healed-ok', stderr: '' };
    },
  });
  assert.equal(healedClaudeRes.code, 0);
  assert.equal(localClaudeRuns, 2);
  const healedState = JSON.parse(readFileSync(join(sb.stateDir, 'accounts-state.json'), 'utf8'));
  assert.deepEqual(healedState.providers, ['codex'], 'stale claude provider healed out of accounts-state.json');

  // 2d. When `codex` IS enrolled in Cloud and its only account is paused (`wake_at: null`), message never says "until null"!
  const cxAcc = cloud.state.accounts.find(a => a.label === 'cx-only');
  cxAcc.state = 'paused';
  await assert.rejects(
    () => runStepAgentProcess({
      agent: 'codex',
      step: 'build',
      args: ['exec', 'hi'],
      cwd: sb.root,
      env: sb.env,
      run: async () => ({ code: 0, stdout: 'ok', stderr: '' }),
    }),
    err => {
      assert.equal(err.code, 'all_cooling');
      assert.equal(err.wakeAt, null);
      assert.match(err.message, /All codex Cloud accounts are paused or cooling\./);
      assert.doesNotMatch(err.message, /until null/);
      return true;
    },
  );
  cxAcc.state = 'ready';

  // 3. Autopilot with `--agent agy --intake active` while `codex` is enrolled in Cloud:
  //    - Active intake card job leases Cloud `codex` inside a disposable `0700` `pdd-cx-*` overlay!
  //    - Main `build` job runs on `agy` (NEVER hijacked onto `codex`)!
  const w = await coreWorld(t, { settings: { runs: 1, intake: 'active' } });
  cloud.state.nowMs = w.now();
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', intake: 'active', trust: [], testCommand: 'npm test', runs: 1 } }));
  w.issue(41, { title: 'Fix typo in help text', body: 'Change teh to the in src/help.mjs.', labels: [] });
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel');
  const stateRoot = join(w.dir, 'launcher-state-r2');
  mkdirSync(stateRoot, { recursive: true });
  const fakeBin = join(sb.root, 'fake-bin');
  mkdirSync(fakeBin, { recursive: true });
  writeFileSync(join(fakeBin, 'agy'), '#!/bin/sh\necho "agy ready"\n', { mode: 0o755 });
  const agyEnv = { ...sb.env, PATH: `${fakeBin}:${sb.env.PATH}` };
  const ports = {
    stateRoot,
    now: () => { cloud.state.nowMs = w.now(); return w.now(); },
    env: agyEnv,
    timer: async () => true,
    warn: () => {},
    sendAlert: async () => ({ exitCode: 0, message: 'sent' }),
    run: async (command, args, options = {}) => {
      if (command === 'agy' || command.endsWith('/agy')) return { code: 0, stdout: 'agy models\n', stderr: '' };
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

  const agyStart = await runAutopilotLauncher({
    command: 'start',
    cwd,
    packageRoot: process.cwd(),
    mode: 'auto',
    intake: 'active',
    agent: 'agy',
    env: agyEnv,
  }, ports);
  assert.equal(agyStart.exitCode, 0, agyStart.message);
  const stateFile = join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`);

  // First tick started an intake card job for #41 using the leased Cloud `codex` account inside a `pdd-cx-*` overlay!
  const cardJob41 = w.started.find(j => j.role === 'intake' && j.issue === 41);
  assert.ok(cardJob41, 'active intake started card job for #41');
  assert.equal(cardJob41.command, 'codex', 'intake card job uses enrolled Cloud codex');
  assert.match(cardJob41.env.CODEX_HOME ?? '', /pdd-cx-/, 'intake card job runs inside disposable 0700 pdd-cx-* overlay');

  // Complete card job #41 as `ready`, then tick again -> main `build` job starts on `agy`, NOT hijacked to `codex`!
  const cardOutPath = cardJob41.args[cardJob41.args.indexOf('--output-last-message') + 1];
  writeFileSync(cardOutPath, JSON.stringify({
    class: 'ready',
    reason: 'Clear one-line fix.',
    confidence: 0.95,
    canonical: null,
    suggested_links: [],
    question: null,
    area_hint: ['src/help.mjs'],
    model: 'gpt-test',
  }));
  writeFileSync(cardJob41.exit, JSON.stringify({ code: 0, signal: null, at: w.now() }));
  w.alive.delete(cardJob41.pid);

  const buildTick = await tickAutopilot(stateFile, ports);
  assert.match(buildTick.message, /1 started/);
  const buildJob41 = w.job(41, 'build');
  assert.ok(buildJob41, 'main build job started for #41');
  assert.equal(buildJob41.command, 'agy', 'main build job uses --agent agy and is NOT hijacked onto Cloud codex');
  assert.equal(buildJob41.agentKind, 'agy');

  // 4. Importing an already-exhausted (100%) Codex or Claude login when initial `/v1/accounts/lease` returns `all_cooling`
  //    STILL records `enrolled: true`, `providers`, and `cooling.<provider>.wake_at` in `accounts-state.json`!
  const coolingCloud = await createMockCloudServer(t, { nowMs: baseMs });
  coolingCloud.state.enrollCoolingUntil = '2026-11-14T22:30:00Z';
  const sbCooling = makeTempSandbox(t, coolingCloud.serverUrl);
  mkdirSync(join(sbCooling.home, '.codex'), { recursive: true });
  writeFileSync(join(sbCooling.home, '.codex', 'auth.json'), JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'at_exhausted_cx_secret1111',
      refresh_token: 'rt_exhausted_cx_secret2222',
      id_token: makeJwt({ email: 'exhausted@example.com', 'https://api.openai.com/auth': { chatgpt_plan_type: 'plus' } }),
      account_id: 'acct_exhausted_cx',
    },
  }));
  const impCoolingCx = await invokeCli(['accounts', 'import', '--provider', 'codex', '--label', 'cx-cooling'], sbCooling);
  assert.equal(impCoolingCx.exit, 0, impCoolingCx.stderr);
  let coolingState = JSON.parse(readFileSync(join(sbCooling.stateDir, 'accounts-state.json'), 'utf8'));
  assert.equal(coolingState.enrolled, true, 'all_cooling on initial Codex import still marks enrolled: true');
  assert.deepEqual(coolingState.providers, ['codex']);
  assert.equal(coolingState.cooling?.codex?.wake_at, '2026-11-14T22:30:00Z');

  mkdirSync(join(sbCooling.home, '.claude'), { recursive: true });
  writeFileSync(join(sbCooling.home, '.claude', 'settings.json'), JSON.stringify({
    env: { CLAUDE_CODE_OAUTH_TOKEN: 'sk-ant-oat01-exhaustedClaudeTokenSecret3333' },
  }));
  const impCoolingCl = await invokeCli(['accounts', 'import', '--provider', 'claude', '--label', 'cl-cooling'], sbCooling);
  assert.equal(impCoolingCl.exit, 0, impCoolingCl.stderr);
  coolingState = JSON.parse(readFileSync(join(sbCooling.stateDir, 'accounts-state.json'), 'utf8'));
  assert.equal(coolingState.enrolled, true);
  assert.deepEqual(coolingState.providers, ['codex', 'claude']);
  assert.equal(coolingState.cooling?.claude?.wake_at, '2026-11-14T22:30:00Z');
});

test('3426: shared Codex gateway_grant materializes tokenless step overlays & local ~/.codex/, skips local usage probes, refuses symlinks, and clean-restores config', async t => {
  const cloud = await createMockCloudServer(t, {
    accounts: [
      {
        account_id: 'acc_cx_owner',
        label: 'cx-owner',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        is_owner: true,
        shared: true, // owner shared this account with a team — still owned!
        state: 'ready',
        five_hour_used_percent: 12,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 24,
        weekly_reset_at: '2026-11-21T12:00:00Z',
        cooling_until: null,
        created_at: '2026-11-01T00:00:00Z',
      },
      {
        account_id: 'acc_cx_backup_shared',
        label: 'cx-shared-2',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'team-owner',
        is_owner: false,
        shared: true,
        state: 'ready',
        five_hour_used_percent: 18,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 35,
        weekly_reset_at: '2026-11-20T12:00:00Z',
        cooling_until: null,
        created_at: '2026-11-02T00:00:00Z',
      },
    ],
    pendingInvites: [
      { invite_id: 'inv_cx_shared_1', account_id: 'acc_cx_shared_1', label: 'cx-shared-1', provider: 'codex', owner_login: 'team-owner' },
    ],
  });
  const sb = makeTempSandbox(t, cloud.serverUrl);

  // Seed user's ~/.codex/ with custom model_provider, [mcp_servers.pdd], real skills/rules, and a symlinked sessions folder.
  const codexDir = join(sb.home, '.codex');
  mkdirSync(join(codexDir, 'skills', 'pdd-prompting'), { recursive: true });
  writeFileSync(join(codexDir, 'skills', 'pdd-prompting', 'SKILL.md'), '# Skill\n');
  mkdirSync(join(codexDir, 'rules'), { recursive: true });
  writeFileSync(join(codexDir, 'rules', 'base.md'), '# Rule\n');
  const extSessions = join(sb.root, 'ext-sessions');
  mkdirSync(extSessions, { recursive: true });
  symlinkSync(extSessions, join(codexDir, 'sessions'));
  writeFileSync(join(codexDir, 'config.toml'), [
    'model = "gpt-5.4"',
    'model_provider = "custom_upstream"',
    '',
    '[mcp_servers.pdd]',
    'command = "node"',
    'args = ["bin/pdd.mjs", "mcp"]',
    'default_tools_approval_mode = "approve"',
    'tool_timeout_sec = 600',
    '',
  ].join('\n'), { mode: 0o600 });

  // 1. Accept shared Codex invite -> immediately materializes tokenless gateway_grant into ~/.codex/{auth.json,config.toml}!
  const accRes = await invokeCli(['accounts', 'accept', 'inv_cx_shared_1'], sb);
  assert.equal(accRes.exit, 0, accRes.stderr);
  assert.match(accRes.stdout, /Accepted shared account "cx-shared-1"/);

  const authPath = localCodexAuthPath(sb.env);
  const configPath = localCodexConfigPath(sb.env);
  assert.equal(statSync(authPath).mode & 0o777, 0o600);
  assert.equal(statSync(configPath).mode & 0o777, 0o600);

  const localAuthRaw = readFileSync(authPath, 'utf8');
  const localAuth = JSON.parse(localAuthRaw);
  assert.equal(localAuth.auth_mode, 'apikey');
  assert.match(localAuth.OPENAI_API_KEY, /^pddg_cx-shared-1_/);
  assert.equal(localAuth.tokens, undefined, 'zero OpenAI access_token, id_token, or refresh_token on borrower disk');
  assert.doesNotMatch(localAuthRaw, /access_token|refresh_token|id_token/);

  const localCfg = parseToml(readFileSync(configPath, 'utf8'));
  assert.equal(localCfg.model, 'gpt-5.4', 'preserved top-level model');
  assert.equal(localCfg.model_provider, 'pdd_codex_gateway');
  assert.deepEqual({ ...localCfg.mcp_servers?.pdd }, {
    command: 'node',
    args: ['bin/pdd.mjs', 'mcp'],
    default_tools_approval_mode: 'approve',
    tool_timeout_sec: 600,
  }, 'preserved [mcp_servers.pdd]');
  assert.equal(localCfg.model_providers?.pdd_codex_gateway?.wire_api, 'responses');
  assert.equal(localCfg.model_providers?.pdd_codex_gateway?.requires_openai_auth, false);
  assert.equal(localCfg.model_providers?.pdd_codex_gateway?.supports_websockets, false);
  assert.equal(localCfg.model_providers?.pdd_codex_gateway?.http_headers?.['x-pdd-gateway-grant'], localAuth.OPENAI_API_KEY);

  const savedState = JSON.parse(readFileSync(join(sb.stateDir, 'accounts-state.json'), 'utf8'));
  assert.equal(savedState.active.codex.delivery_mode, 'gateway_grant');
  assert.equal(savedState.active.codex.managed_codex_gateway, true);
  assert.equal(savedState.active.codex.previous_codex_model_provider, 'custom_upstream');
  assert.doesNotMatch(JSON.stringify(savedState), /pddg_/, 'zero grant tokens persisted in accounts-state.json');

  // Verify real codex-cli (if installed) parses local ~/.codex/{auth.json,config.toml} with exit 0 and zero TOML warnings!
  const codexWhich = spawnSync('codex', ['--version'], { encoding: 'utf8' });
  const hasRealCodex = codexWhich.status === 0;
  if (hasRealCodex) {
    const statusCheck = spawnSync('codex', ['login', 'status'], {
      env: { ...sb.env, CODEX_HOME: codexDir },
      encoding: 'utf8',
    });
    assert.equal(statusCheck.status, 0, `codex login status failed: ${statusCheck.stderr}`);
    assert.equal(
      parseAgentAuthStatus({ agent: 'codex', result: { code: statusCheck.status, stdout: statusCheck.stdout, stderr: statusCheck.stderr } }),
      'ready',
    );
    const featCheck = spawnSync('codex', ['features', 'list'], {
      env: { ...sb.env, CODEX_HOME: codexDir },
      encoding: 'utf8',
    });
    assert.equal(featCheck.status, 0, `codex features list failed on local config.toml: ${featCheck.stderr}`);
    assert.doesNotMatch(featCheck.stderr, /parse|invalid|unknown field|toml/i);
  }

  // 2. Per-step overlay (`selectCloudPoolLogin` + `runStepAgentProcess`):
  //    - NO auth.json inside /tmp/pdd-cx-*
  //    - Symlinks non-symlink skills & rules only (never auth.json, config.toml, or symlinked sessions)
  //    - Scrubs ambient OPENAI_API_KEY / CODEX_API_KEY / CODEX_ACCESS_TOKEN / OPENAI_BASE_URL
  //    - Skips local readCodexUsageWindows on gateway_grant!
  let usageProbeCalls = 0;
  const poolSel = await selectCloudPoolLogin(
    { cwd: sb.cwd, env: sb.env, fallbackAgent: { kind: 'codex', command: 'codex' } },
    {
      tmpRoot: sb.root,
      readCodexUsageWindows: async () => {
        usageProbeCalls += 1;
        return { state: 'ok' };
      },
    },
  );
  assert.equal(poolSel.state, 'ready');
  assert.equal(poolSel.lease.delivery_mode, 'gateway_grant');
  assert.equal(usageProbeCalls, 0, 'selectCloudPoolLogin skips local readCodexUsageWindows on gateway_grant');

  const dirtyEnv = {
    ...sb.env,
    OPENAI_API_KEY: 'sk-ambient-personal-key',
    CODEX_API_KEY: 'sk-ambient-codex-key',
    CODEX_ACCESS_TOKEN: 'at-ambient-codex-token',
    OPENAI_BASE_URL: 'https://evil-override.example.com/v1',
  };
  let stepAttempts = 0;
  let capturedOverlayDir = null;
  const stepRes = await runStepAgentProcess({
    agent: 'codex',
    step: 'build',
    args: ['exec', 'hello'],
    cwd: sb.cwd,
    env: dirtyEnv,
    accountsPorts: {
      tmpRoot: sb.root,
      readCodexUsageWindows: async () => {
        usageProbeCalls += 1;
        return { five_hour_used_percent: 100 };
      },
    },
    run: async (_cmd, _args, opts) => {
      stepAttempts += 1;
      const ovDir = opts.env.CODEX_HOME;
      capturedOverlayDir = ovDir;
      assert.notEqual(ovDir, codexDir);
      assert.equal(statSync(ovDir).mode & 0o777, 0o700);
      assert.equal(existsSync(join(ovDir, 'auth.json')), false, 'NO auth.json inside shared Codex step overlay');
      assert.equal(lstatSync(join(ovDir, 'config.toml')).isSymbolicLink(), false, 'config.toml is a dedicated 0600 file, never symlinked');
      assert.equal(statSync(join(ovDir, 'config.toml')).mode & 0o777, 0o600);
      assert.equal(lstatSync(join(ovDir, 'skills')).isSymbolicLink(), true, 'skills dir symlinked');
      assert.equal(lstatSync(join(ovDir, 'rules')).isSymbolicLink(), true, 'rules dir symlinked');
      assert.equal(existsSync(join(ovDir, 'sessions')), false, 'symlinked source sessions dir is NOT symlinked');

      assert.match(opts.env.PDD_CODEX_GATEWAY_GRANT ?? '', /^pddg_/);
      assert.equal(opts.env.OPENAI_API_KEY, undefined);
      assert.equal(opts.env.CODEX_API_KEY, undefined);
      assert.equal(opts.env.CODEX_ACCESS_TOKEN, undefined);
      assert.equal(opts.env.OPENAI_BASE_URL, undefined);

      const ovCfg = parseToml(readFileSync(join(ovDir, 'config.toml'), 'utf8'));
      assert.equal(ovCfg.model_provider, 'pdd_codex_gateway');
      assert.equal(ovCfg.features?.shell_snapshot, false);
      assert.equal(ovCfg.shell_environment_policy?.filters?.PDD_CODEX_GATEWAY_GRANT, 'exclude');
      assert.deepEqual(ovCfg.mcp_servers?.pdd, localCfg.mcp_servers.pdd, 'step overlay preserved [mcp_servers.pdd]');
      const gwBlock = ovCfg.model_providers?.pdd_codex_gateway;
      assert.equal(gwBlock?.http_headers, undefined, 'no static http_headers leaked into step overlay');
      assert.deepEqual({ ...gwBlock?.env_http_headers }, { 'x-pdd-gateway-grant': 'PDD_CODEX_GATEWAY_GRANT' });

      if (hasRealCodex && stepAttempts === 1) {
        const ovFeat = spawnSync('codex', ['features', 'list'], {
          env: { ...sb.env, CODEX_HOME: ovDir, PDD_CODEX_GATEWAY_GRANT: opts.env.PDD_CODEX_GATEWAY_GRANT },
          encoding: 'utf8',
        });
        assert.equal(ovFeat.status, 0, `codex features list failed on step overlay config.toml: ${ovFeat.stderr}`);
        assert.doesNotMatch(ovFeat.stderr, /parse|invalid|unknown field|toml/i);
      }

      // Verify live gateway call succeeds before revocation.
      const gwResp = await fetch(`${gwBlock.base_url}/responses`, {
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-pdd-gateway-grant': opts.env.PDD_CODEX_GATEWAY_GRANT },
        body: JSON.stringify({ model: 'gpt-5.4', input: 'ping' }),
      });
      assert.equal(gwResp.status, 200);

      if (stepAttempts === 1) {
        // Trigger quota exhaustion on cx-shared-1 -> rotates to cx-shared-2 WITHOUT calling local readCodexUsageWindows!
        return { code: 1, stdout: '', stderr: 'You have hit your usage limit (5-hour limit). resets at 2026-11-15T03:00:00Z' };
      }
      return { code: 0, stdout: 'gateway-step-ok', stderr: '' };
    },
  });
  assert.equal(stepRes.code, 0);
  assert.equal(stepAttempts, 2);
  assert.equal(stepRes.account?.label, 'cx-shared-2');
  assert.equal(usageProbeCalls, 0, 'runStepAgentProcess skips local readCodexUsageWindows on gateway_grant failover');
  assert.equal(existsSync(capturedOverlayDir), false, 'step overlay wiped in finally');

  // Revoking access (`unshare`) invalidates existing gateway grant immediately on the server!
  const activeLeaseEntry = [...cloud.state.activeLeases.entries()].find(([, v]) => v.accountId === 'acc_cx_shared_1');
  assert.ok(activeLeaseEntry);
  await invokeCli(['accounts', 'unshare', 'cx-shared-1', '--user', 'borrower'], sb);
  const afterRevokeResp = await fetch(`${cloud.serverUrl}/v1/codex-gateway/${activeLeaseEntry[0]}/responses`, {
    method: 'POST',
    headers: { 'content-type': 'application/json', 'x-pdd-gateway-grant': activeLeaseEntry[1].grantToken },
    body: JSON.stringify({ model: 'gpt-5.4', input: 'ping' }),
  });
  assert.equal(afterRevokeResp.status, 403, 'revoked shared Codex grant fails immediately without waiting for expiry');

  // 3. Clean Restore A: Switching to owner `direct_stripped` account strips [model_providers.pdd_codex_gateway] & restores model_provider!
  assert.equal((await invokeCli(['accounts', 'use', 'cx-owner'], sb)).exit, 0);
  const ownerAuth = JSON.parse(readFileSync(authPath, 'utf8'));
  assert.equal(ownerAuth.auth_mode, 'chatgpt');
  assert.equal(ownerAuth.tokens.refresh_token, '');
  const ownerCfg = parseToml(readFileSync(configPath, 'utf8'));
  assert.equal(ownerCfg.model_provider, 'custom_upstream', 'previous model_provider restored cleanly');
  assert.equal(ownerCfg.model_providers, undefined, '[model_providers.pdd_codex_gateway] stripped cleanly');
  assert.deepEqual(ownerCfg.mcp_servers?.pdd, localCfg.mcp_servers.pdd, '[mcp_servers.pdd] preserved');
  const ownerState = JSON.parse(readFileSync(join(sb.stateDir, 'accounts-state.json'), 'utf8'));
  assert.equal(ownerState.active.codex.managed_codex_gateway, false);
  assert.equal(ownerState.active.codex.previous_codex_model_provider, null);

  // 4. Clean Restore B: Switching to shared `cx-shared-2`, removing remaining accounts, and running `leave cx-shared-2`
  //    strips gateway config AND removes the pddg_* auth.json!
  assert.equal((await invokeCli(['accounts', 'use', 'cx-shared-2'], sb)).exit, 0);
  assert.equal((await invokeCli(['accounts', 'remove', 'cx-owner'], sb)).exit, 0);
  assert.equal((await invokeCli(['accounts', 'leave', 'cx-shared-1'], sb)).exit, 0);
  assert.equal((await invokeCli(['accounts', 'leave', 'cx-shared-2'], sb)).exit, 0);

  assert.equal(existsSync(authPath), false, 'pddg_* auth.json removed when leaving shared Codex account with no replacement');
  const leftCfg = parseToml(readFileSync(configPath, 'utf8'));
  assert.equal(leftCfg.model_provider, 'custom_upstream', 'model_provider restored on leave');
  assert.equal(leftCfg.model_providers, undefined, 'pdd_codex_gateway removed on leave');
  assert.deepEqual(leftCfg.mcp_servers?.pdd, localCfg.mcp_servers.pdd, '[mcp_servers.pdd] still intact after leave');

  // 5. Symlink refusal: symlinking ~/.codex/config.toml or ~/.codex/auth.json is refused without touching target!
  const victimFile = join(sb.root, 'victim.txt');
  writeFileSync(victimFile, 'DO_NOT_OVERWRITE');
  rmSync(configPath, { force: true });
  symlinkSync(victimFile, configPath);
  assert.throws(
    () => materializeLocalCodexAuth({
      delivery_mode: 'gateway_grant',
      codex_gateway_url: 'https://cloud.example.com/v1/codex-gateway/lse_test',
      codex_gateway_token: 'pddg_symlink_test_token',
    }, { env: sb.env }),
    err => err instanceof CloudAccountsError && err.code === 'symlink_refused',
  );
  assert.throws(
    () => restoreLocalCodexGatewayConfig({ env: sb.env, removeAuthFile: true }),
    err => err instanceof CloudAccountsError && err.code === 'symlink_refused',
  );
  assert.equal(readFileSync(victimFile, 'utf8'), 'DO_NOT_OVERWRITE');
});

test('3427: isolated temp CODEX_HOME on add, --device-auth, --loop auto-labels & duplicate detection, inline --with, import --from, bulk share --all, and symmetric unshare', async t => {
  const cloud = await createMockCloudServer(t, {
    dedupEnroll: true,
    accounts: [
      {
        account_id: 'acc_existing_1',
        label: 'team-cx-1',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        is_owner: true,
        shared: false,
        state: 'ready',
        five_hour_used_percent: 5,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 10,
        weekly_reset_at: '2026-11-18T17:00:00Z',
        cooling_until: null,
        created_at: '2026-11-01T00:00:00Z',
        _subjectKey: 'codex:acct_existing_server',
      },
      {
        account_id: 'acc_borrowed_cx',
        label: 'borrowed-cx',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'other-owner',
        is_owner: false,
        shared: true,
        state: 'ready',
        five_hour_used_percent: 5,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 10,
        weekly_reset_at: '2026-11-18T17:00:00Z',
        cooling_until: null,
        created_at: '2026-11-01T00:00:00Z',
      },
      {
        account_id: 'acc_owned_cl',
        label: 'owned-claude',
        provider: 'claude',
        plan: 'max',
        owner_login: 'Serhan-Asad',
        is_owner: true,
        shared: false,
        state: 'ready',
        five_hour_used_percent: 5,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 10,
        weekly_reset_at: '2026-11-18T17:00:00Z',
        cooling_until: null,
        created_at: '2026-11-01T00:00:00Z',
      },
    ],
  });
  const sb = makeTempSandbox(t, cloud.serverUrl);

  // 1. Reject --device-auth for Claude with exit 2 BEFORE invoking claude!
  let claudeCalled = false;
  const badDeviceClaude = await invokeCli(['accounts', 'add', '--provider', 'claude', '--device-auth'], sb, {
    run: async () => {
      claudeCalled = true;
      return { code: 0, stdout: '', stderr: '' };
    },
  });
  assert.equal(badDeviceClaude.exit, 2);
  assert.match(badDeviceClaude.stderr, /--device-auth is only supported for Codex accounts/);
  assert.equal(claudeCalled, false);

  // 2. Isolated temp CODEX_HOME on Codex `add` + `--device-auth`: failed/cancelled login leaves ~/.codex/auth.json untouched and wipes temp dir!
  const localCodexDir = join(sb.home, '.codex');
  mkdirSync(localCodexDir, { recursive: true });
  const sentinelAuth = JSON.stringify({ sentinel: 'keep_untouched' });
  writeFileSync(join(localCodexDir, 'auth.json'), sentinelAuth, { mode: 0o600 });

  let seenTempLoginHome = null;
  const abortedAdd = await invokeCli(['accounts', 'add', '--provider', 'codex', '--device-auth'], sb, {
    tmpRoot: sb.root,
    run: async (cmd, args, opts) => {
      assert.equal(cmd, 'codex');
      assert.deepEqual(args, ['login', '-c', 'cli_auth_credentials_store="file"', '--device-auth']);
      seenTempLoginHome = opts.env.CODEX_HOME;
      assert.notEqual(seenTempLoginHome, localCodexDir);
      assert.equal(statSync(seenTempLoginHome).mode & 0o777, 0o700);
      writeFileSync(join(seenTempLoginHome, 'auth.json'), '{"partial":true}');
      return { code: 130, stdout: '', stderr: 'Interrupted' };
    },
  });
  assert.equal(abortedAdd.exit, 1);
  assert.equal(existsSync(seenTempLoginHome), false, 'disposable login CODEX_HOME removed in finally');
  assert.equal(readFileSync(join(localCodexDir, 'auth.json'), 'utf8'), sentinelAuth, 'local ~/.codex/auth.json untouched on failed login');

  // 3. Reject --loop in non-TTY without prompt port (exit 2).
  const nonTtyLoop = await invokeCli(['accounts', 'add', '--provider', 'codex', '--loop'], sb);
  assert.equal(nonTtyLoop.exit, 2);
  assert.match(nonTtyLoop.stderr, /--loop requires an interactive terminal/);

  // 4. Interactive `--loop` with collision-free auto-labels (team-cx-1 already taken -> starts at team-cx-2),
  //    session + server duplicate detection without advancing label counter, and inline comma-separated `--with`!
  const loopLogins = [
    { account_id: 'acct_loop_A', refresh: 'rt_loop_A_secret1111', email: 'a@example.com' },
    { account_id: 'acct_loop_A', refresh: 'rt_loop_A_refreshed2222', email: 'a@example.com' }, // session duplicate!
    { account_id: 'acct_existing_server', refresh: 'rt_server_dup_3333', email: 'existing@example.com' }, // server already_enrolled duplicate!
    { account_id: 'acct_loop_B', refresh: 'rt_loop_B_secret4444', email: 'b@example.com' },
  ];
  const promptAnswers = ['y', '', 'yes', 'n'];
  const seenPrompts = [];
  let loginIdx = 0;

  const loopRes = await invokeCli(
    ['accounts', 'add', '--provider', 'codex', '--label', 'team-cx', '--loop', '--with', 'octocat, promptdriven/builders, @promptdriven, octocat'],
    sb,
    {
      tmpRoot: sb.root,
      resolveGithubUser: async login => ({ id: 583231, login, type: 'User' }),
      prompt: async question => {
        seenPrompts.push(question);
        return promptAnswers.shift();
      },
      run: async (cmd, args, opts) => {
        assert.equal(cmd, 'codex');
        assert.deepEqual(args, ['login', '-c', 'cli_auth_credentials_store="file"']);
        const spec = loopLogins[loginIdx++];
        writeFileSync(join(opts.env.CODEX_HOME, 'auth.json'), JSON.stringify({
          auth_mode: 'chatgpt',
          OPENAI_API_KEY: null,
          tokens: {
            access_token: `at_${spec.account_id}_secret`,
            refresh_token: spec.refresh,
            id_token: makeJwt({ email: spec.email, 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
            account_id: spec.account_id,
          },
        }));
        return { code: 0, stdout: 'Logged in\n', stderr: '' };
      },
    },
  );
  assert.equal(loopRes.exit, 0, loopRes.stderr);
  assert.equal(seenPrompts.length, 4);
  assert.ok(seenPrompts.every(q => q === 'Enroll another codex account? [Y/n] '));
  assert.match(loopRes.stdout, /Enrolled Codex account "team-cx-2"/);
  assert.match(loopRes.stdout, /Already enrolled as team-cx-2 — refreshed credentials\./);
  assert.match(loopRes.stdout, /Already enrolled as team-cx-1 — refreshed credentials\./);
  assert.match(loopRes.stdout, /Enrolled Codex account "team-cx-3"/, 'duplicates did NOT increment label counter past team-cx-3');
  assert.match(loopRes.stdout, /Loop summary: enrolled 2 codex accounts \(team-cx-2, team-cx-3\); refreshed 1 existing \(team-cx-1\), shared with octocat, promptdriven\/builders, @promptdriven\./);

  // 5. `pdd accounts import --provider codex --from <path> --label cx-imported --with promptdriven/eng,@promptdriven`
  const extAuthPath = join(sb.root, 'external-codex-auth.json');
  const extRawJson = JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'at_ext_import_secret9999',
      refresh_token: 'rt_ext_import_secret8888',
      id_token: makeJwt({ email: 'ext@example.com', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
      account_id: 'acct_ext_import',
    },
  });
  writeFileSync(extAuthPath, extRawJson, { mode: 0o600 });
  const impFrom = await invokeCli(
    ['accounts', 'import', '--provider', 'codex', '--from', extAuthPath, '--label', 'cx-imported', '--with', 'promptdriven/eng,@promptdriven'],
    sb,
  );
  assert.equal(impFrom.exit, 0, impFrom.stderr);
  assert.match(impFrom.stdout, /Enrolled Codex account "cx-imported"/);
  assert.match(impFrom.stdout, /Shared with promptdriven\/eng \(invite inv_\d+\), @promptdriven \(invite inv_\d+\)/);
  assert.equal(readFileSync(extAuthPath, 'utf8'), extRawJson, 'external --from file left intact');

  // 6. Upfront validation on `share` & `unshare` BEFORE network mutations!
  const reqCountBeforeInvalid = cloud.state.requests.length;
  assert.equal((await invokeCli(['accounts', 'share', '--with', 'octocat'], sb)).exit, 2, 'missing both LABEL and --all');
  assert.equal((await invokeCli(['accounts', 'share', 'team-cx-1', '--all', '--with', 'octocat'], sb)).exit, 2, 'both LABEL and --all');
  assert.equal((await invokeCli(['accounts', 'share', 'team-cx-1', '--with', 'bad/team/extra'], sb)).exit, 2, 'malformed team');
  assert.equal((await invokeCli(['accounts', 'share', 'team-cx-1', '--with', '@'], sb)).exit, 2, 'empty @ORG');
  assert.equal((await invokeCli(['accounts', 'share', 'team-cx-1', '--with', 'octocat,'], sb)).exit, 2, 'empty trailing target');
  assert.equal((await invokeCli(['accounts', 'unshare', 'team-cx-1'], sb)).exit, 2, 'missing target on unshare');
  assert.equal((await invokeCli(['accounts', 'unshare', 'team-cx-1', '--all', '--user', 'octocat'], sb)).exit, 2, 'both LABEL and --all on unshare');
  assert.equal(cloud.state.requests.length, reqCountBeforeInvalid, 'invalid share/unshare syntax rejected before network calls');

  // 7. Bulk `share --all --provider codex` shares ONLY owned Codex accounts (skipping borrowed-cx and owned-claude)!
  const idxBeforeBulkShare = cloud.state.requests.length;
  const bulkShare = await invokeCli(
    ['accounts', 'share', '--all', '--provider', 'codex', '--with', 'alice,promptdriven/core,@promptdriven'],
    sb,
    { resolveGithubUser: async login => ({ id: 1001, login, type: 'User' }) },
  );
  assert.equal(bulkShare.exit, 0, bulkShare.stderr);
  const bulkShareReqs = cloud.state.requests.slice(idxBeforeBulkShare).filter(r => r.method === 'POST' && r.path.endsWith('/share'));
  const sharedAccountIds = [...new Set(bulkShareReqs.map(r => r.path.split('/')[3]))];
  const expectedOwnedCodexIds = cloud.state.accounts
    .filter(a => a.provider === 'codex' && a.is_owner === true)
    .map(a => a.account_id);
  assert.deepEqual(sharedAccountIds, expectedOwnedCodexIds, 'shared every owned Codex account and excluded borrowed/Claude accounts');
  const firstAcctShares = bulkShareReqs.filter(r => r.path === `/v1/accounts/${expectedOwnedCodexIds[0]}/share`).map(r => r.body);
  assert.deepEqual(firstAcctShares, [
    { github_login: 'alice', github_user_id: 1001 },
    { org: 'promptdriven', team: 'core' },
    { org: 'promptdriven' },
  ]);

  // 8. Symmetric `unshare --all --provider codex --user alice --with promptdriven/core,@promptdriven --machine old-laptop`!
  const idxBeforeBulkUnshare = cloud.state.requests.length;
  const bulkUnshare = await invokeCli(
    ['accounts', 'unshare', '--all', '--provider', 'codex', '--user', 'alice', '--with', 'promptdriven/core,@promptdriven,alice', '--machine', 'old-laptop'],
    sb,
  );
  assert.equal(bulkUnshare.exit, 0, bulkUnshare.stderr);
  const bulkUnshareReqs = cloud.state.requests.slice(idxBeforeBulkUnshare).filter(r => r.method === 'POST' && r.path.endsWith('/unshare'));
  const unsharedAccountIds = [...new Set(bulkUnshareReqs.map(r => r.path.split('/')[3]))];
  assert.deepEqual(unsharedAccountIds, expectedOwnedCodexIds);
  const firstAcctUnshares = bulkUnshareReqs.filter(r => r.path === `/v1/accounts/${expectedOwnedCodexIds[0]}/unshare`).map(r => r.body);
  assert.deepEqual(firstAcctUnshares, [
    { github_login: 'alice' },
    { org: 'promptdriven', team: 'core' },
    { org: 'promptdriven' },
    { machine_id: 'old-laptop' },
  ], 'deduplicated alice and sent symmetric user, team, org, and machine unshare payloads');
});

test('3428: pdd accounts list requests refresh=true while internal checks stay fast, and Codex add/import probes local usage when initial server windows are unpopulated', async t => {
  const cloud = await createMockCloudServer(t, { zeroInitialUsage: true });
  const sb = makeTempSandbox(t, cloud.serverUrl);

  // 1. Codex `add` when server returns 0%/0% & null resets: probes temp CODEX_HOME BEFORE cleanup and reports usage!
  let addProbeSawFullTokens = false;
  const addRes = await invokeCli(['accounts', 'add', '--provider', 'codex', '--label', 'probe-add'], sb, {
    tmpRoot: sb.root,
    run: async (_cmd, _args, opts) => {
      writeFileSync(join(opts.env.CODEX_HOME, 'auth.json'), JSON.stringify({
        auth_mode: 'chatgpt',
        OPENAI_API_KEY: null,
        tokens: {
          access_token: 'at_probe_add_secret1111',
          refresh_token: 'rt_probe_add_secret2222',
          id_token: makeJwt({ email: 'probe1@example.com', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
          account_id: 'acct_probe_add',
        },
      }));
      return { code: 0, stdout: 'Logged in\n', stderr: '' };
    },
    readCodexUsageWindows: async ({ env: probeEnv }) => {
      const raw = JSON.parse(readFileSync(join(probeEnv.CODEX_HOME, 'auth.json'), 'utf8'));
      addProbeSawFullTokens = raw.tokens?.refresh_token === 'rt_probe_add_secret2222';
      return {
        state: 'ok',
        five_hour_used_percent: 34,
        five_hour_reset_at: '2026-11-15T23:00:00Z',
        weekly_used_percent: 61,
        weekly_reset_at: '2026-11-20T00:00:00Z',
      };
    },
  });
  assert.equal(addRes.exit, 0, addRes.stderr);
  assert.equal(addProbeSawFullTokens, true, 'local usage probe ran against temp CODEX_HOME BEFORE temp dir was wiped');
  const addedAcc = cloud.state.accounts.find(a => a.label === 'probe-add');
  assert.equal(addedAcc.five_hour_used_percent, 34);
  assert.equal(addedAcc.weekly_used_percent, 61);
  assert.equal(addedAcc.weekly_reset_at, '2026-11-20T00:00:00Z');

  // 2. Codex `import` when server returns 0%/0% & null resets: probes BEFORE stripping ~/.codex/auth.json, and fails open on probe error!
  mkdirSync(join(sb.home, '.codex'), { recursive: true });
  writeFileSync(join(sb.home, '.codex', 'auth.json'), JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'at_probe_imp_secret3333',
      refresh_token: 'rt_probe_imp_secret4444',
      id_token: makeJwt({ email: 'probe2@example.com', 'https://api.openai.com/auth': { chatgpt_plan_type: 'plus' } }),
      account_id: 'acct_probe_imp',
    },
  }));
  let impProbeSawUnstripped = false;
  const impRes = await invokeCli(['accounts', 'import', '--provider', 'codex', '--label', 'probe-imp'], sb, {
    readCodexUsageWindows: async ({ env: probeEnv }) => {
      const raw = JSON.parse(readFileSync(join(probeEnv.CODEX_HOME, 'auth.json'), 'utf8'));
      impProbeSawUnstripped = raw.tokens?.refresh_token === 'rt_probe_imp_secret4444';
      return {
        state: 'ok',
        five_hour_used_percent: 19,
        five_hour_reset_at: '2026-11-15T21:00:00Z',
        weekly_used_percent: 48,
        weekly_reset_at: '2026-11-19T12:00:00Z',
      };
    },
  });
  assert.equal(impRes.exit, 0, impRes.stderr);
  assert.equal(impProbeSawUnstripped, true, 'import usage probe ran BEFORE stripping local ~/.codex/auth.json');
  const impAcc = cloud.state.accounts.find(a => a.label === 'probe-imp');
  assert.equal(impAcc.five_hour_used_percent, 19);
  assert.equal(impAcc.weekly_used_percent, 48);

  // Fail-open check when local usage probe throws
  const extProbeFail = join(sb.root, 'probe-fail-auth.json');
  writeFileSync(extProbeFail, JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'at_probe_fail_5555',
      refresh_token: 'rt_probe_fail_6666',
      id_token: makeJwt({ email: 'probe3@example.com', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
      account_id: 'acct_probe_fail',
    },
  }));
  const failOpenImp = await invokeCli(['accounts', 'import', '--provider', 'codex', '--from', extProbeFail, '--label', 'probe-fail-open'], sb, {
    readCodexUsageWindows: async () => {
      throw new Error('codex app-server timed out');
    },
  });
  assert.equal(failOpenImp.exit, 0, 'usage probe failure is strictly fail-open');

  // 3. `pdd accounts` and `pdd accounts list` pass `?refresh=true`, whereas internal lookups (`use`) omit `?refresh=true`!
  const idxBeforeList = cloud.state.requests.length;
  const listOut = await invokeCli(['accounts', 'list'], sb);
  assert.equal(listOut.exit, 0);
  assert.match(listOut.stdout, /probe-add\s+codex\s+owner \(Serhan-Asad\)\s+34%/);
  const rootListOut = await invokeCli(['accounts'], sb);
  assert.equal(rootListOut.exit, 0);
  const listReqs = cloud.state.requests.slice(idxBeforeList).filter(r => r.method === 'GET' && r.path === '/v1/accounts');
  assert.equal(listReqs.length, 2);
  assert.deepEqual(listReqs.map(r => r.query), ['?refresh=true', '?refresh=true']);

  const idxBeforeUse = cloud.state.requests.length;
  assert.equal((await invokeCli(['accounts', 'use', 'probe-add'], sb)).exit, 0);
  const internalListReqs = cloud.state.requests.slice(idxBeforeUse).filter(r => r.method === 'GET' && r.path === '/v1/accounts');
  assert.equal(internalListReqs.length, 1);
  assert.equal(internalListReqs[0].query, '', 'internal account resolution keeps refresh=false');
});
