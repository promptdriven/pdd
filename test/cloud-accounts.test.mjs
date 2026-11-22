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
  buildClaudeStepEnv,
  buildSyntheticGatewayIdToken,
  localClaudePaths,
  restoreLocalClaudeGatewayConfig,
  cloudAccountsRequest,
  createCodexStepOverlay,
  isIsolatedCodexHomeEntry,
  isSafeCodexSourceEntry,
  leaseCloudAccount,
  listCloudAccounts,
  localCodexAuthPath,
  localCodexConfigPath,
  localCodexHome,
  loginEnvironment,
  managedClaudeSettingsPath,
  managedCodexAuthPath,
  managedCodexConfigPath,
  materializeLocalClaudeAuth,
  materializeLocalCodexAuth,
  pddManagedClaudeHome,
  pddManagedCodexHome,
  normalizeUsagePercentInt,
  prepareCloudStepExecution,
  reportCloudAccountUsage,
  REQUIRED_CODEX_SUBSHELL_EXCLUDES,
  resolveCloudAccountsEndpoint,
  resolvePddStateBase,
  restoreLocalCodexGatewayConfig,
  selectCloudPoolLogin,
  stopCodexAppServerDaemon,
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
    if (acc.state === 'paused' || acc.state === 'reauth_required') return;
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

      if (chosen && chosen._leaseErrorStatus) {
        const status = chosen._leaseErrorStatus;
        const payload = chosen._leaseErrorBody ?? {
          detail: { error: 'token_revoked', message: 'Upstream OAuth refresh token revoked' },
          account_id: chosen.account_id,
        };
        if (chosen._markReauthOnLeaseError !== false) {
          chosen.state = 'reauth_required';
          chosen.last_refresh_error = 'token_revoked';
        }
        return send(status, payload);
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
      const codexDir = env.CODEX_HOME;
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

  // User ~/.codex/auth.json was NEVER created; managed codex-home/auth.json is mode 0600 with refresh_token === "".
  assert.equal(existsSync(join(sb.home, '.codex', 'auth.json')), false, '~/.codex/auth.json never touched');
  const localCodexPath = managedCodexAuthPath(sb.env);
  assert.equal(statSync(localCodexPath).mode & 0o777, 0o600);
  const localCodex = JSON.parse(readFileSync(localCodexPath, 'utf8'));
  assert.equal(localCodex.tokens.refresh_token, '');
  assert.equal(localCodex.auth_mode, 'chatgpt');

  // Re-importing an already-stripped auth.json refuses cleanly instead of overwriting Cloud with "".
  const reimportStripped = await invokeCli(['accounts', 'import', '--provider', 'codex', '--from', pddManagedCodexHome(sb.env), '--label', 'dup'], sb);
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
  const managedClPath = managedClaudeSettingsPath(sb.env);
  assert.equal(statSync(managedClPath).mode & 0o777, 0o600);
  const managedClSettings = JSON.parse(readFileSync(managedClPath, 'utf8'));
  assert.match(managedClSettings.env.CLAUDE_CODE_OAUTH_TOKEN, /^sk-ant-oat01-max-1-/);
  const personalSettings = JSON.parse(readFileSync(claudeSettingsPath, 'utf8'));
  assert.equal(personalSettings.theme, 'dark');
  assert.equal(personalSettings.env.CUSTOM_USER_FLAG, 'keep-me');
  assert.equal(personalSettings.env.CLAUDE_CODE_OAUTH_TOKEN, rawClaudeOauth, '~/.claude/settings.json must stay untouched on import');
  assert.equal(existsSync(claudeJsonPath), false, '~/.claude.json must stay untouched on import');

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
  assert.equal(existsSync(join(sb.home, '.codex', 'auth.json')), false, '~/.codex/auth.json untouched on use/next');
  const codexAuth = JSON.parse(readFileSync(managedCodexAuthPath(sb.env), 'utf8'));
  assert.equal(codexAuth.tokens.access_token, 'acc_tok_cx-sooner_secret12345');
  assert.equal(codexAuth.tokens.refresh_token, '');

  // Accept shared Claude invite -> `use cl-shared` writes gateway_grant ANTHROPIC_BASE_URL + short-lived grant token.
  const acceptRes = await invokeCli(['accounts', 'accept', 'inv_shared_cl'], sb);
  assert.equal(acceptRes.exit, 0);
  assert.match(acceptRes.stdout, /Accepted shared account "cl-shared"/);

  assert.equal((await invokeCli(['accounts', 'use', 'cl-shared'], sb)).exit, 0);
  assert.equal(existsSync(join(sb.home, '.claude', 'settings.json')), false, '~/.claude/settings.json untouched on use');
  const sharedSettings = JSON.parse(readFileSync(managedClaudeSettingsPath(sb.env), 'utf8'));
  assert.equal(sharedSettings.env.CLAUDE_CODE_OAUTH_TOKEN, 'pddg_cl-shared_shortlived9999');
  assert.match(sharedSettings.env.ANTHROPIC_BASE_URL, new RegExp(`^${cloud.serverUrl.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}/v1/accounts/claude-gateway/lse_`));

  // Switching back to personal `cl-own` (`direct_oauth`) clears managed ANTHROPIC_BASE_URL cleanly in isolated file!
  assert.equal((await invokeCli(['accounts', 'use', 'cl-own'], sb)).exit, 0);
  assert.equal(existsSync(join(sb.home, '.claude', 'settings.json')), false, '~/.claude/settings.json untouched on use cl-own');
  const ownSettings = JSON.parse(readFileSync(managedClaudeSettingsPath(sb.env), 'utf8'));
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
  const authBeforeTimeout = readFileSync(managedCodexAuthPath(sb.env), 'utf8');
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
  assert.equal(readFileSync(managedCodexAuthPath(sb.env), 'utf8'), authBeforeTimeout);
  assert.equal(existsSync(join(sb.home, '.codex', 'auth.json')), false);

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

  // Switching isolated Claude settings to direct_oauth overrides legacy managed gateway URL in ~/.claude/settings.json WITHOUT mutating ~/.claude/settings.json!
  mkdirSync(join(sb.home, '.claude'), { recursive: true });
  const personalBefore = JSON.stringify({
    env: { ANTHROPIC_BASE_URL: 'https://api.promptdriven.ai/v1/accounts/claude-gateway/lse_old' },
  });
  writeFileSync(join(sb.home, '.claude', 'settings.json'), personalBefore);
  materializeLocalClaudeAuth({ delivery_mode: 'direct_oauth', claude_oauth_token: 'sk-ant-oat01-directToken123456' }, { env: sb.env, previousManagedBaseUrl: false });
  assert.equal(readFileSync(join(sb.home, '.claude', 'settings.json'), 'utf8'), personalBefore, '~/.claude/settings.json stays untouched');
  const afterDirect = JSON.parse(readFileSync(managedClaudeSettingsPath(sb.env), 'utf8'));
  assert.equal(afterDirect.env.ANTHROPIC_BASE_URL, 'https://api.anthropic.com');

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
  symlinkSync(join(sb.root, 'missing-dangling-memories'), join(codexDir, 'memories'));
  symlinkSync(join(codexDir, 'config.toml'), join(codexDir, 'agents'));
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

  assert.equal(existsSync(localCodexAuthPath(sb.env)), false, '~/.codex/auth.json untouched on shared Codex accept');
  const managedHome = pddManagedCodexHome(sb.env);
  const authPath = managedCodexAuthPath(sb.env);
  const configPath = managedCodexConfigPath(sb.env);
  assert.equal(statSync(managedHome).mode & 0o777, 0o700);
  assert.equal(statSync(authPath).mode & 0o777, 0o600);
  assert.equal(statSync(configPath).mode & 0o777, 0o600);

  const localAuthRaw = readFileSync(authPath, 'utf8');
  const localAuth = JSON.parse(localAuthRaw);
  assert.equal(localAuth.auth_mode, 'chatgpt');
  assert.equal(localAuth.OPENAI_API_KEY, null);
  assert.match(localAuth.tokens?.access_token ?? '', /^pddg_cx-shared-1_/);
  assert.equal(localAuth.tokens?.refresh_token, '');
  assert.equal(localAuth.tokens?.account_id, 'acct_pdd_gateway');
  assert.equal(localAuth.tokens?.id_token, buildSyntheticGatewayIdToken({ planType: 'pro' }));
  assert.doesNotMatch(localAuthRaw, /oa_shared_secret|rt_shared_secret|id_shared_secret/, 'zero real OpenAI OAuth tokens on borrower disk');

  const localCfg = parseToml(readFileSync(configPath, 'utf8'));
  assert.equal(localCfg.model, 'gpt-5.4', 'preserved top-level model');
  assert.equal(localCfg.model_provider, undefined, 'native openai provider retained (no top-level model_provider)');
  assert.match(localCfg.openai_base_url ?? '', /\/v1\/codex-gateway\/lse_/);
  assert.equal(localCfg.chatgpt_base_url, localCfg.openai_base_url);
  assert.deepEqual({ ...localCfg.mcp_servers?.pdd }, {
    command: 'node',
    args: ['bin/pdd.mjs', 'mcp'],
    default_tools_approval_mode: 'approve',
    tool_timeout_sec: 600,
  }, 'preserved [mcp_servers.pdd]');
  assert.equal(localCfg.model_providers?.pdd_codex_gateway?.wire_api, 'responses');
  assert.equal(localCfg.model_providers?.pdd_codex_gateway?.requires_openai_auth, false);
  assert.equal(localCfg.model_providers?.pdd_codex_gateway?.supports_websockets, false);
  assert.equal(localCfg.model_providers?.pdd_codex_gateway?.http_headers?.['x-pdd-gateway-grant'], localAuth.tokens.access_token);

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
      env: { ...sb.env, CODEX_HOME: managedHome },
      encoding: 'utf8',
    });
    assert.equal(statusCheck.status, 0, `codex login status failed: ${statusCheck.stderr}`);
    assert.equal(
      parseAgentAuthStatus({ agent: 'codex', result: { code: statusCheck.status, stdout: statusCheck.stdout, stderr: statusCheck.stderr } }),
      'ready',
    );
    const featCheck = spawnSync('codex', ['features', 'list'], {
      env: { ...sb.env, CODEX_HOME: managedHome },
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
      assert.equal(lstatSync(join(ovDir, 'sessions')).isSymbolicLink(), true, 'valid external symlinked sessions dir IS symlinked');
      assert.equal(realpathSync(join(ovDir, 'sessions')), realpathSync(extSessions));
      assert.equal(existsSync(join(ovDir, 'memories')), false, 'dangling symlinked memories dir is NOT symlinked');
      assert.equal(existsSync(join(ovDir, 'agents')), false, 'symlink targeting config.toml is NOT symlinked');

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
  assert.equal(ownerCfg.openai_base_url, undefined, 'PDD-managed openai_base_url stripped cleanly');
  assert.equal(ownerCfg.chatgpt_base_url, undefined, 'PDD-managed chatgpt_base_url stripped cleanly');
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
  assert.equal(leftCfg.openai_base_url, undefined, 'openai_base_url removed on leave');
  assert.equal(leftCfg.chatgpt_base_url, undefined, 'chatgpt_base_url removed on leave');
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
  const scrubbedExtRaw = readFileSync(extAuthPath, 'utf8');
  assert.equal(scrubbedExtRaw.includes('rt_ext_import_secret8888'), false, 'single-use refresh_token scrubbed from --from source file');
  const scrubbedExtJson = JSON.parse(scrubbedExtRaw);
  assert.equal(scrubbedExtJson.tokens.refresh_token, '');
  assert.equal(scrubbedExtJson.tokens.account_id, 'acct_ext_import');
  assert.equal(statSync(extAuthPath).mode & 0o777, 0o600);

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

  // 8. Symmetric `unshare --all --provider codex --user alice --with promptdriven/core,@promptdriven`!
  const idxBeforeBulkUnshare = cloud.state.requests.length;
  const bulkUnshare = await invokeCli(
    ['accounts', 'unshare', '--all', '--provider', 'codex', '--user', 'alice', '--with', 'promptdriven/core,@promptdriven,alice'],
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
  ], 'deduplicated alice and sent symmetric user, team, and org unshare payloads');
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
      addProbeSawFullTokens = raw.tokens?.access_token === 'at_probe_add_secret1111' && raw.tokens?.refresh_token === '';
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
  assert.equal(addProbeSawFullTokens, true, 'local usage probe ran against disposable temp CODEX_HOME with refresh_token cleared');
  const addedAcc = cloud.state.accounts.find(a => a.label === 'probe-add');
  assert.equal(addedAcc.five_hour_used_percent, 34);
  assert.equal(addedAcc.weekly_used_percent, 61);
  assert.equal(addedAcc.weekly_reset_at, '2026-11-20T00:00:00Z');

  // 2. Codex `import` when server returns 0%/0% & null resets: probes with scrubbed refresh_token copy BEFORE scrubbing ~/.codex/auth.json, and fails open on probe error!
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
      const probeRaw = JSON.parse(readFileSync(join(probeEnv.CODEX_HOME, 'auth.json'), 'utf8'));
      const homeRawDuringProbe = JSON.parse(readFileSync(join(sb.home, '.codex', 'auth.json'), 'utf8'));
      impProbeSawUnstripped = probeRaw.tokens?.access_token === 'at_probe_imp_secret3333'
        && probeRaw.tokens?.refresh_token === ''
        && homeRawDuringProbe.tokens?.refresh_token === 'rt_probe_imp_secret4444';
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
  assert.equal(impProbeSawUnstripped, true, 'import usage probe used scrubbed temp copy before scrubbing ~/.codex/auth.json');
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
  assert.match(listOut.stdout, /probe-add\s+codex\s+owner \(Serhan-Asad\)\s+66% left/);
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

test('3426 & 3427 review regressions: shell_environment_policy migration, pddg_ prefix guard, revoked gateway config restore on list & step heal, and SIGINT/null-code login handling', async t => {
  const cloud = await createMockCloudServer(t, {
    accounts: [
      {
        account_id: 'acc_revokable_shared_1',
        label: 'cx-shared-rev1',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'team-owner',
        is_owner: false,
        shared: true,
        state: 'ready',
        five_hour_used_percent: 10,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 20,
        weekly_reset_at: '2026-11-20T12:00:00Z',
        cooling_until: null,
        created_at: '2026-11-01T00:00:00Z',
      },
    ],
  });
  const sb = makeTempSandbox(t, cloud.serverUrl);
  const codexDir = join(sb.home, '.codex');
  mkdirSync(codexDir, { recursive: true });
  const userConfigPath = localCodexConfigPath(sb.env);
  const authPath = managedCodexAuthPath(sb.env);
  const configPath = managedCodexConfigPath(sb.env);

  // 1. Legacy [shell_environment_policy] migration + case-insensitive grant scrub in `createCodexStepOverlay`!
  writeFileSync(userConfigPath, [
    'model = "gpt-5.4"',
    'model_provider = "custom_upstream"',
    '',
    '[shell_environment_policy]',
    'inherit = "all"',
    'exclude = ["AWS_*", "pdd_codex_gateway_grant"]',
    'include_only = ["PATH", "HOME", "pdd_Codex_Gateway_Grant"]',
    'filters = { CUSTOM_VAR = "exclude", pdd_codex_gateway_grant = "include" }',
    'set = { SAFE_KEY = "ok", pdd_codex_gateway_grant = "leaked_override" }',
    '',
    '[mcp_servers.pdd]',
    'command = "node"',
    'args = ["bin/pdd.mjs", "mcp"]',
    '',
  ].join('\n'), { mode: 0o600 });

  const ov = createCodexStepOverlay({
    delivery_mode: 'gateway_grant',
    codex_gateway_url: 'https://cloud.example.com/v1/codex-gateway/lse_policy_test',
    codex_gateway_token: 'pddg_policyTestGrant1234',
  }, { env: sb.env, tmpRoot: sb.root });
  try {
    const ovCfg = parseToml(readFileSync(ov.configPath, 'utf8'));
    assert.equal(ovCfg.shell_environment_policy?.exclude, undefined, 'legacy exclude array removed');
    assert.equal(ovCfg.shell_environment_policy?.include_only, undefined, 'legacy include_only array removed');
    assert.equal(ovCfg.shell_environment_policy?.inherit, 'all');
    assert.deepEqual({ ...ovCfg.shell_environment_policy?.filters }, {
      CUSTOM_VAR: 'exclude',
      'AWS_*': 'exclude',
      PATH: 'include',
      HOME: 'include',
      ...Object.fromEntries(REQUIRED_CODEX_SUBSHELL_EXCLUDES.map(k => [k, 'exclude'])),
    });
    assert.deepEqual({ ...ovCfg.shell_environment_policy?.set }, {
      SAFE_KEY: 'ok',
    });

    const codexWhich = spawnSync('codex', ['--version'], { encoding: 'utf8' });
    if (codexWhich.status === 0) {
      const featCheck = spawnSync('codex', ['features', 'list'], {
        env: { ...sb.env, CODEX_HOME: ov.overlayDir, PDD_CODEX_GATEWAY_GRANT: 'pddg_policyTestGrant1234' },
        encoding: 'utf8',
      });
      assert.equal(featCheck.status, 0, `codex features list failed on migrated shell_environment_policy: ${featCheck.stderr}`);
      assert.doesNotMatch(featCheck.stderr, /parse|invalid|unknown field|toml|conflict/i);
    }
  } finally {
    ov.cleanup();
  }

  // 2. Reject non-`pddg_` tokens in `resolveCodexGatewayGrant` while registering secret redaction!
  const badToken = 'sk-live-accidentalRawSecretToken_998877';
  assert.throws(
    () => materializeLocalCodexAuth({
      delivery_mode: 'gateway_grant',
      codex_gateway_url: 'https://cloud.example.com/v1/codex-gateway/lse_bad',
      codex_gateway_token: badToken,
    }, { env: sb.env }),
    err => err instanceof CloudAccountsError && err.code === 'invalid_lease',
  );
  assert.throws(
    () => createCodexStepOverlay({
      delivery_mode: 'gateway_grant',
      codex_gateway_url: 'https://cloud.example.com/v1/codex-gateway/lse_bad',
      gateway_bearer_token: badToken,
    }, { env: sb.env, tmpRoot: sb.root }),
    err => err instanceof CloudAccountsError && err.code === 'invalid_lease',
  );
  assert.equal(existsSync(authPath), false, 'non-pddg_ token never written to ~/.codex/auth.json');
  assert.doesNotMatch(redactSecrets(`err: ${badToken}`), new RegExp(badToken), 'rejected token registered in secret redaction');

  // 3A. Server-side revoke/unshare + borrower `pdd accounts list` restores `~/.codex/config.toml` & removes `pddg_*` `auth.json`!
  assert.equal((await invokeCli(['accounts', 'use', 'cx-shared-rev1'], sb)).exit, 0);
  const preRevokeListCfg = parseToml(readFileSync(configPath, 'utf8'));
  assert.equal(preRevokeListCfg.model_provider, undefined);
  assert.match(preRevokeListCfg.openai_base_url ?? '', /\/v1\/codex-gateway/);
  assert.equal(preRevokeListCfg.chatgpt_base_url, preRevokeListCfg.openai_base_url);
  assert.equal(existsSync(authPath), true);

  cloud.state.accounts[0].revoked = true;
  const healedList = await invokeCli(['accounts', 'list'], sb);
  assert.equal(healedList.exit, 0, healedList.stderr);
  assert.equal(existsSync(authPath), false, 'pddg_* auth.json removed when list prunes revoked shared Codex account');
  const healedListCfg = parseToml(readFileSync(configPath, 'utf8'));
  assert.equal(healedListCfg.model_provider, 'custom_upstream', 'previous model_provider restored when list prunes revoked shared account');
  assert.equal(healedListCfg.openai_base_url, undefined, 'openai_base_url stripped on list prune');
  assert.equal(healedListCfg.chatgpt_base_url, undefined, 'chatgpt_base_url stripped on list prune');
  assert.equal(healedListCfg.model_providers, undefined, '[model_providers.pdd_codex_gateway] stripped on list prune');
  assert.equal(healedListCfg.mcp_servers?.pdd?.command, 'node');

  // 3B. Server-side revoke/unshare + `runStepAgentProcess` zero-accounts heal restores `~/.codex/config.toml` & removes `pddg_*` `auth.json`!
  cloud.state.accounts[0].revoked = false;
  assert.equal((await invokeCli(['accounts', 'use', 'cx-shared-rev1'], sb)).exit, 0);
  const preRevokeStepCfg = parseToml(readFileSync(configPath, 'utf8'));
  assert.equal(preRevokeStepCfg.model_provider, undefined);
  assert.match(preRevokeStepCfg.openai_base_url ?? '', /\/v1\/codex-gateway/);
  assert.equal(existsSync(authPath), true);

  cloud.state.accounts[0].revoked = true;
  let localFallbackRan = false;
  const healStep = await runStepAgentProcess({
    agent: 'codex',
    step: 'build',
    args: ['exec', 'hi'],
    cwd: sb.cwd,
    env: sb.env,
    accountsPorts: { tmpRoot: sb.root },
    run: async (_cmd, _args, opts) => {
      localFallbackRan = true;
      assert.equal(opts.env.PDD_CLOUD_STEP_ISOLATED, undefined, 'fell back to local run after healing zero-account state');
      return { code: 0, stdout: 'local-ok', stderr: '' };
    },
  });
  assert.equal(healStep.code, 0);
  assert.equal(localFallbackRan, true);
  assert.equal(existsSync(authPath), false, 'pddg_* auth.json removed during runStepAgentProcess zero-accounts heal');
  const healedStepCfg = parseToml(readFileSync(configPath, 'utf8'));
  assert.equal(healedStepCfg.model_provider, 'custom_upstream', 'previous model_provider restored during runStepAgentProcess zero-accounts heal');
  assert.equal(healedStepCfg.openai_base_url, undefined);
  assert.equal(healedStepCfg.chatgpt_base_url, undefined);
  assert.equal(healedStepCfg.model_providers, undefined);

  // 4. `Ctrl-C` / `SIGINT` on `--loop` iteration 0 exits 0 cleanly, while non-`--loop` `{ code: null }` exits 1!
  const loopSigintFirst = await invokeCli(['accounts', 'add', '--provider', 'codex', '--loop'], sb, {
    tmpRoot: sb.root,
    prompt: async () => 'n',
    run: async () => ({ code: null, signal: 'SIGINT', stdout: '', stderr: '' }),
  });
  assert.equal(loopSigintFirst.exit, 0, loopSigintFirst.stderr);
  assert.match(loopSigintFirst.stdout, /Loop finished with 0 codex accounts enrolled\./);

  const singleNullCodeCodex = await invokeCli(['accounts', 'add', '--provider', 'codex'], sb, {
    tmpRoot: sb.root,
    run: async () => ({ code: null, signal: 'SIGTERM', stdout: '', stderr: '' }),
  });
  assert.equal(singleNullCodeCodex.exit, 1);
  assert.match(singleNullCodeCodex.stderr, /codex login did not complete\./);

  const singleNullCodeClaude = await invokeCli(['accounts', 'add', '--provider', 'claude'], sb, {
    run: async () => ({ code: null, signal: 'SIGTERM', stdout: '', stderr: '' }),
  });
  assert.equal(singleNullCodeClaude.exit, 1);
  assert.match(singleNullCodeClaude.stderr, /claude setup-token did not complete\./);
});


test('3445 T1: isolated pddManagedCodexHome never touches ~/.codex/auth.json, symlinks user dirs, cleans legacy gateway config, and guards zsh/bash/fish logout + fail-safe fallback', async t => {
  const { spawn } = await import('node:child_process');
  const execShellAsync = (bin, args, opts = {}) => new Promise((resolve, reject) => {
    const child = spawn(bin, args, { ...opts, stdio: ['ignore', 'pipe', 'pipe'] });
    let stdout = '';
    let stderr = '';
    child.stdout.on('data', d => { stdout += d.toString('utf8'); });
    child.stderr.on('data', d => { stderr += d.toString('utf8'); });
    child.on('error', reject);
    child.on('close', status => resolve({ status, stdout, stderr }));
  });

  const liveNow = Date.now();
  const future5h = new Date(liveNow + 4 * 3600_000).toISOString();
  const future7dA = new Date(liveNow + 5 * 86400_000).toISOString();
  const future7dB = new Date(liveNow + 3 * 86400_000).toISOString();

  const cloud = await createMockCloudServer(t, {
    nowMs: liveNow,
    accounts: [
      {
        account_id: 'acc_iso_1',
        label: 'iso-cx-1',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        is_owner: true,
        shared: false,
        state: 'ready',
        five_hour_used_percent: 12,
        five_hour_reset_at: future5h,
        weekly_used_percent: 25,
        weekly_reset_at: future7dA,
        cooling_until: null,
        last_refresh_at: new Date(liveNow - 60_000).toISOString(),
        created_at: '2026-11-01T00:00:00Z',
      },
      {
        account_id: 'acc_iso_2',
        label: 'iso-cx-2',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        is_owner: true,
        shared: false,
        state: 'ready',
        five_hour_used_percent: 4,
        five_hour_reset_at: future5h,
        weekly_used_percent: 9,
        weekly_reset_at: future7dB,
        cooling_until: null,
        last_refresh_at: new Date(liveNow - 30_000).toISOString(),
        created_at: '2026-11-02T00:00:00Z',
      },
    ],
  });
  const sb = makeTempSandbox(t, cloud.serverUrl);

  // Path resolution symmetry across PDD_STATE_DIR, XDG_STATE_HOME, and default HOME.
  assert.equal(pddManagedCodexHome({ HOME: '/tmp/h', PDD_STATE_DIR: '/tmp/s' }), '/tmp/s/codex-home');
  assert.equal(pddManagedCodexHome({ HOME: '/tmp/h', XDG_STATE_HOME: '/tmp/xdg' }), '/tmp/xdg/pdd/codex-home');
  assert.equal(pddManagedCodexHome({ HOME: '/tmp/h' }), '/tmp/h/.local/state/pdd/codex-home');
  assert.equal(
    localCodexHome({ ...sb.env, CODEX_HOME: pddManagedCodexHome(sb.env) }),
    join(sb.home, '.codex'),
    'localCodexHome ignores self-referential pddManagedCodexHome',
  );

  // Seed personal ~/.codex/auth.json sentinel, user directories/files, and legacy gateway block in ~/.codex/config.toml.
  const userCodexDir = join(sb.home, '.codex');
  mkdirSync(userCodexDir, { recursive: true, mode: 0o700 });
  const sentinelAuthRaw = JSON.stringify({
    auth_mode: 'chatgpt',
    tokens: {
      access_token: 'SENTINEL_PERSONAL_ACCESS_TOKEN_KEEP',
      refresh_token: 'SENTINEL_PERSONAL_REFRESH_TOKEN_KEEP',
      id_token: makeJwt({ email: 'personal@example.com' }),
      account_id: 'org_personal_sentinel',
    },
  }, null, 2) + '\n';
  const userAuthFile = join(userCodexDir, 'auth.json');
  writeFileSync(userAuthFile, sentinelAuthRaw, { mode: 0o600 });

  for (const dirName of ['skills', 'memories', 'sessions', 'archived_sessions', 'rules']) {
    mkdirSync(join(userCodexDir, dirName), { recursive: true });
    writeFileSync(join(userCodexDir, dirName, 'marker.txt'), dirName);
  }
  writeFileSync(join(userCodexDir, 'history.jsonl'), '{"ts":1}\n');
  writeFileSync(join(userCodexDir, 'session_index.jsonl'), '{"id":"s1"}\n');

  const userConfigFile = join(userCodexDir, 'config.toml');
  writeFileSync(userConfigFile, [
    'model = "gpt-5.4"',
    'model_provider = "pdd_codex_gateway"',
    '',
    '[mcp_servers.pdd]',
    'command = "node"',
    'args = ["bin/pdd.mjs", "mcp"]',
    '',
    '[model_providers.pdd_codex_gateway]',
    'name = "PDD Codex Gateway"',
    'base_url = "https://cloud.example.com/v1/codex-gateway/lse_old_legacy"',
    'wire_api = "responses"',
    'requires_openai_auth = false',
    '',
  ].join('\n'), { mode: 0o600 });

  // Materialize via use and next -> ~/.codex/auth.json MUST remain byte-for-byte identical!
  assert.equal((await invokeCli(['accounts', 'use', 'iso-cx-1'], sb, { now: () => cloud.state.nowMs })).exit, 0);
  assert.equal(readFileSync(userAuthFile, 'utf8'), sentinelAuthRaw, '~/.codex/auth.json untouched after use');

  // Legacy gateway block in ~/.codex/config.toml was cleaned safely without deleting ~/.codex/auth.json.
  const cleanedUserCfg = parseToml(readFileSync(userConfigFile, 'utf8'));
  assert.equal(cleanedUserCfg.model_provider, undefined, 'legacy pdd_codex_gateway stripped from ~/.codex/config.toml');
  assert.equal(cleanedUserCfg.model_providers, undefined);
  assert.equal(cleanedUserCfg.mcp_servers?.pdd?.command, 'node');

  // Managed CODEX_HOME has 0700 dir, 0600 auth.json, 0600 config.toml with cli_auth_credentials_store = "file", merged MCP config, and symlinks!
  const managedHome = pddManagedCodexHome(sb.env);
  assert.equal(statSync(managedHome).mode & 0o777, 0o700);
  assert.equal(statSync(managedCodexAuthPath(sb.env)).mode & 0o777, 0o600);
  assert.equal(statSync(managedCodexConfigPath(sb.env)).mode & 0o777, 0o600);

  const mCfg = parseToml(readFileSync(managedCodexConfigPath(sb.env), 'utf8'));
  assert.equal(mCfg.cli_auth_credentials_store, 'file');
  assert.equal(mCfg.model, 'gpt-5.4');
  assert.equal(mCfg.mcp_servers?.pdd?.command, 'node');

  for (const name of ['skills', 'memories', 'sessions', 'archived_sessions', 'history.jsonl', 'session_index.jsonl', 'rules']) {
    const linkPath = join(managedHome, name);
    assert.equal(lstatSync(linkPath).isSymbolicLink(), true, `${name} symlinked inside managed CODEX_HOME`);
    assert.equal(realpathSync(linkPath), realpathSync(join(userCodexDir, name)));
  }

  assert.equal((await invokeCli(['accounts', 'next', '--provider', 'codex'], sb, { now: () => cloud.state.nowMs })).exit, 0);
  assert.equal(readFileSync(userAuthFile, 'utf8'), sentinelAuthRaw, '~/.codex/auth.json untouched after next');
  assert.equal(JSON.parse(readFileSync(managedCodexAuthPath(sb.env), 'utf8')).tokens.access_token, 'acc_tok_iso-cx-2_secret12345');

  // Shell auto-switch across zsh, bash, AND fish (~/.config/fish/config.fish created automatically).
  const autoOn = await invokeCli(['accounts', 'auto', 'on'], sb);
  assert.equal(autoOn.exit, 0, autoOn.stderr);
  const autoOnRepeat = await invokeCli(['accounts', 'auto', 'on'], sb);
  assert.equal(autoOnRepeat.exit, 0);

  const zshrc = join(sb.home, '.zshrc');
  const bashrc = join(sb.home, '.bashrc');
  const fishCfg = join(sb.home, '.config', 'fish', 'config.fish');
  for (const rc of [zshrc, bashrc, fishCfg]) {
    assert.equal(existsSync(rc), true, `${rc} created by auto on`);
    assert.equal(readFileSync(rc, 'utf8').match(/# >>> pdd accounts auto >>>/g)?.length, 1);
  }
  const autoStatus = await invokeCli(['accounts', 'auto', 'status'], sb);
  assert.match(autoStatus.stdout, /Terminal auto-switch: on/);
  assert.match(autoStatus.stdout, /config\.fish/);

  // Create stub bin directory with spy codex and real CLI wrapper pdd.
  const binDir = join(sb.root, 'stub-bin');
  mkdirSync(binDir, { recursive: true });
  const nodeBin = process.execPath;
  const pddEntry = join(process.cwd(), 'bin', 'pdd.mjs');
  const spyCodex = join(binDir, 'codex');
  writeFileSync(spyCodex, [
    `#!${nodeBin}`,
    'console.log(JSON.stringify({ via: "codex", codexHome: process.env.CODEX_HOME ?? null, args: process.argv.slice(2) }));',
    '',
  ].join('\n'), { mode: 0o755 });
  const spyPddCodex = join(binDir, 'pdd-codex');
  writeFileSync(spyPddCodex, [
    `#!${nodeBin}`,
    'console.log(JSON.stringify({ via: "pdd-codex", failOpen: process.env.PDD_CODEX_AUTO_FAIL_OPEN ?? null, codexHome: process.env.CODEX_HOME ?? null, args: process.argv.slice(2) }));',
    '',
  ].join('\n'), { mode: 0o755 });
  const wrapperPdd = join(binDir, 'pdd');
  writeFileSync(wrapperPdd, [
    '#!/bin/sh',
    `exec ${JSON.stringify(nodeBin)} ${JSON.stringify(pddEntry)} "$@"`,
    '',
  ].join('\n'), { mode: 0o755 });

  const shellEnvBase = {
    ...sb.env,
    PATH: `${binDir}:${process.env.PATH ?? '/usr/bin:/bin'}`,
  };
  delete shellEnvBase.CODEX_HOME;
  const legacyShellEnv = { ...shellEnvBase, PDD_LEGACY_PTY_ROTATE: '1' };

  const shellsToTest = [
    { name: 'bash', bin: 'bash', runCmd: cmd => ['--norc', '--noprofile', '-c', `source ${JSON.stringify(bashrc)}; ${cmd}`] },
    { name: 'zsh', bin: 'zsh', runCmd: cmd => ['--no-rcs', '-c', `source ${JSON.stringify(zshrc)}; ${cmd}`] },
    { name: 'fish', bin: 'fish', runCmd: cmd => ['--no-config', '-c', `source ${JSON.stringify(fishCfg)}; ${cmd}`] },
  ].filter(s => spawnSync(s.bin, ['--version'], { encoding: 'utf8' }).status === 0);

  assert.ok(shellsToTest.some(sh => sh.name === 'bash'), 'bash shell available');
  if (spawnSync('fish', ['--version'], { encoding: 'utf8' }).status === 0) {
    assert.ok(shellsToTest.some(sh => sh.name === 'fish'), 'fish shell tested when installed');
  }

  const symlinkManagedHome = join(sb.root, 'symlink-codex-home');
  symlinkSync(managedHome, symlinkManagedHome);
  const dotAliasManagedHome = `${sb.stateDir}/./codex-home`;
  assert.equal(
    localCodexHome({ ...sb.env, CODEX_HOME: symlinkManagedHome }),
    join(sb.home, '.codex'),
    'localCodexHome ignores symlink pointing at pddManagedCodexHome',
  );
  assert.equal(
    localCodexHome({ ...sb.env, CODEX_HOME: dotAliasManagedHome }),
    join(sb.home, '.codex'),
    'localCodexHome ignores path alias pointing at pddManagedCodexHome',
  );

  for (const sh of shellsToTest) {
    // A0) Default unified mode delegates normal commands to `PDD_CODEX_AUTO_FAIL_OPEN=1 pdd-codex`!
    for (const [cmd, expectedArgs] of [
      ['codex exec "ship it"', ['exec', 'ship it']],
      ['codex exec logout', ['exec', 'logout']],
    ]) {
      const unifiedRun = await execShellAsync(sh.bin, sh.runCmd(cmd), { env: shellEnvBase });
      assert.equal(unifiedRun.status, 0, `${sh.name} default ${cmd} failed: ${unifiedRun.stderr}`);
      const unifiedParsed = JSON.parse(unifiedRun.stdout.trim());
      assert.equal(unifiedParsed.via, 'pdd-codex', `${sh.name} ${cmd} delegates to pdd-codex by default`);
      assert.equal(unifiedParsed.failOpen, '1', `${sh.name} ${cmd} sets PDD_CODEX_AUTO_FAIL_OPEN=1`);
      assert.deepEqual(unifiedParsed.args, expectedArgs);
    }

    // A) Legacy opt-in (`PDD_LEGACY_PTY_ROTATE=1`): healthy lease + normal command -> CODEX_HOME points to pddManagedCodexHome!
    for (const [cmd, expectedArgs] of [
      ['codex exec "ship it"', ['exec', 'ship it']],
      ['codex exec logout', ['exec', 'logout']],
    ]) {
      const execRun = await execShellAsync(sh.bin, sh.runCmd(cmd), { env: legacyShellEnv });
      assert.equal(execRun.status, 0, `${sh.name} ${cmd} failed: ${execRun.stderr}`);
      const execParsed = JSON.parse(execRun.stdout.trim());
      assert.equal(execParsed.codexHome, managedHome, `${sh.name} ${cmd} sets CODEX_HOME to managedHome`);
      assert.deepEqual(execParsed.args, expectedArgs);
    }

    // B) Logout & login guard with CODEX_HOME unset (including top-level value options like --add-dir) -> leaves CODEX_HOME unset!
    for (const cmd of ['codex logout', 'codex login', 'codex login --device-auth', 'codex -m gpt-5.4 logout', 'codex --add-dir /tmp logout']) {
      const guardUnset = await execShellAsync(sh.bin, sh.runCmd(cmd), { env: shellEnvBase });
      assert.equal(guardUnset.status, 0, `${sh.name} ${cmd} failed: ${guardUnset.stderr}`);
      const parsed = JSON.parse(guardUnset.stdout.trim());
      assert.equal(parsed.via, 'codex');
      assert.equal(parsed.codexHome, null, `${sh.name} ${cmd} does NOT point CODEX_HOME at managedHome`);
    }

    // C) Logout & login guard when CODEX_HOME points to managedHome directly, via /./ alias, or via symlink -> friendly refusal (exit 1)!
    for (const exportedHome of [managedHome, dotAliasManagedHome, symlinkManagedHome]) {
      for (const cmd of ['codex logout', 'codex --add-dir /tmp logout', 'codex login']) {
        const guardExported = await execShellAsync(sh.bin, sh.runCmd(cmd), {
          env: { ...shellEnvBase, CODEX_HOME: exportedHome },
        });
        assert.equal(guardExported.status, 1, `${sh.name} ${cmd} refuses when CODEX_HOME=${exportedHome}`);
        assert.equal(guardExported.stdout.trim(), '', `${sh.name} ${cmd} did not invoke codex binary`);
        assert.match(guardExported.stderr, /pdd accounts pause/);
        assert.match(guardExported.stderr, /pdd accounts remove/);
      }
    }
  }

  // D) Fail-safe fallback when no valid active lease exists or Cloud is unreachable (legacy mode) -> leaves/unsets CODEX_HOME so ~/.codex/auth.json works!
  const deadEnv = {
    ...legacyShellEnv,
    PDD_ACCOUNTS_URL: 'http://127.0.0.1:1',
    PDD_STATE_DIR: join(sb.root, 'offline-empty-state'),
  };
  mkdirSync(deadEnv.PDD_STATE_DIR, { recursive: true });
  const deadManagedHome = pddManagedCodexHome(deadEnv);
  for (const sh of shellsToTest) {
    const fallbackUnset = await execShellAsync(sh.bin, sh.runCmd('codex exec "offline work"'), { env: deadEnv });
    assert.equal(fallbackUnset.status, 0, `${sh.name} offline fallback failed: ${fallbackUnset.stderr}`);
    assert.equal(JSON.parse(fallbackUnset.stdout.trim()).codexHome, null, `${sh.name} leaves CODEX_HOME unset when Cloud unreachable`);

    const fallbackClearManaged = await execShellAsync(sh.bin, sh.runCmd('codex exec "offline work"'), {
      env: { ...deadEnv, CODEX_HOME: deadManagedHome },
    });
    assert.equal(fallbackClearManaged.status, 0);
    assert.equal(JSON.parse(fallbackClearManaged.stdout.trim()).codexHome, null, `${sh.name} clears stale managed CODEX_HOME on fail-safe fallback`);
  }

  // E) auto off cleans all three shell configs cleanly, and sentinel ~/.codex/auth.json is STILL untouched!
  assert.equal((await invokeCli(['accounts', 'auto', 'off'], sb)).exit, 0);
  for (const rc of [zshrc, bashrc, fishCfg]) {
    assert.doesNotMatch(readFileSync(rc, 'utf8'), /pdd accounts auto/);
  }
  assert.equal(readFileSync(userAuthFile, 'utf8'), sentinelAuthRaw, '~/.codex/auth.json untouched across entire lifecycle');
});

test('3445 T2: cold-start default timeouts (20s GET / 15s lease) and 1 bounded retry on timeout/abort for idempotent GET and /v1/accounts/lease', async t => {
  const sb = makeTempSandbox(t, 'https://cloud.example.com');

  // 1. GET /v1/accounts retries once on AbortError and succeeds on attempt 2.
  let getCalls = 0;
  const listRes = await listCloudAccounts({ cwd: sb.cwd, env: sb.env }, {
    fetch: async (_url, init) => {
      getCalls += 1;
      assert.ok(init.signal, 'AbortSignal passed to fetch');
      if (getCalls === 1) {
        const err = new Error('The operation was aborted');
        err.name = 'AbortError';
        throw err;
      }
      return new Response(JSON.stringify({ accounts: [{ account_id: 'acc_1', label: 'cx-1', provider: 'codex', state: 'ready' }], pending_invites: [] }), {
        status: 200,
        headers: { 'content-type': 'application/json' },
      });
    },
  });
  assert.equal(getCalls, 2, 'GET /v1/accounts retried once on cold-start abort');
  assert.equal(listRes.accounts.length, 1);

  // 2. POST /v1/accounts/lease retries once on TimeoutError, then throws timeout after 2 total attempts if still timing out.
  let leaseCalls = 0;
  const leasedRes = await leaseCloudAccount({ provider: 'codex', updateState: false }, { cwd: sb.cwd, env: sb.env }, {
    fetch: async () => {
      leaseCalls += 1;
      if (leaseCalls === 1) {
        const err = new Error('Timed out');
        err.name = 'TimeoutError';
        throw err;
      }
      return new Response(JSON.stringify({
        state: 'leased',
        account: { account_id: 'acc_1', label: 'cx-1', provider: 'codex', state: 'ready' },
        lease: { lease_id: 'lse_1', expires_at: '2026-11-16T22:00:00Z', delivery_mode: 'direct_stripped', codex_auth_json: { auth_mode: 'chatgpt', tokens: { access_token: 'tok', refresh_token: '', id_token: 'id', account_id: 'org_1' } } },
      }), { status: 200, headers: { 'content-type': 'application/json' } });
    },
  });
  assert.equal(leaseCalls, 2, 'POST /v1/accounts/lease retried once on cold-start timeout');
  assert.equal(leasedRes.state, 'leased');

  let doubleTimeoutCalls = 0;
  await assert.rejects(
    () => leaseCloudAccount({ provider: 'codex', updateState: false }, { cwd: sb.cwd, env: sb.env, timeoutMs: 50 }, {
      fetch: async () => {
        doubleTimeoutCalls += 1;
        const err = new Error('Aborted');
        err.name = 'AbortError';
        throw err;
      },
    }),
    err => err instanceof CloudAccountsError && err.code === 'timeout',
  );
  assert.equal(doubleTimeoutCalls, 2, 'bounded at 1 retry (2 total attempts)');

  // Real wall-clock budget check: 2 attempts under timeoutMs: 120 share one deadline and never take 2x (240ms)!
  let realTimerCalls = 0;
  const wallStart = performance.now();
  await assert.rejects(
    () => leaseCloudAccount({ provider: 'codex', updateState: false }, { cwd: sb.cwd, env: sb.env, timeoutMs: 120 }, {
      fetch: (_url, init) => new Promise((_resolve, reject) => {
        realTimerCalls += 1;
        init.signal.addEventListener('abort', () => {
          const err = new Error('Aborted');
          err.name = 'AbortError';
          reject(err);
        }, { once: true });
      }),
    }),
    err => err instanceof CloudAccountsError && err.code === 'timeout',
  );
  const wallElapsed = performance.now() - wallStart;
  assert.equal(realTimerCalls, 2, 'both transport attempts executed within shared deadline');
  assert.ok(wallElapsed < 210, 'shared deadline respected (<210ms)');

  // 3. Non-idempotent POST /v1/accounts does NOT retry on AbortError (1 attempt only).
  let enrollCalls = 0;
  await assert.rejects(
    () => cloudAccountsRequest('POST', '/v1/accounts', { body: { label: 'x' }, cwd: sb.cwd, env: sb.env, timeoutMs: 50 }, {
      fetch: async () => {
        enrollCalls += 1;
        const err = new Error('Aborted');
        err.name = 'AbortError';
        throw err;
      },
    }),
    err => err instanceof CloudAccountsError && err.code === 'timeout',
  );
  assert.equal(enrollCalls, 1, 'non-idempotent POST /v1/accounts makes 0 retries');
});

test('3445 T3: + -> - label lookup symmetry in resolveAccount across use, pause, unpause, and log', async t => {
  const cloud = await createMockCloudServer(t);
  const sb = makeTempSandbox(t, cloud.serverUrl);

  const addRes = await invokeCli(['accounts', 'add', '--provider', 'codex', '--label', 'glt+oai2'], sb, {
    runLogin: async (_provider, { env }) => {
      mkdirSync(env.CODEX_HOME, { recursive: true });
      writeFileSync(join(env.CODEX_HOME, 'auth.json'), JSON.stringify({
        auth_mode: 'chatgpt',
        tokens: {
          access_token: 'at_glt_oai2_secret',
          refresh_token: 'rt_glt_oai2_secret',
          id_token: makeJwt({ email: 'glt+oai2@example.com', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
          account_id: 'acct_glt_oai2',
        },
      }));
      return { code: 0, stdout: 'ok\n', stderr: '' };
    },
  });
  assert.equal(addRes.exit, 0, addRes.stderr);
  assert.match(addRes.stdout, /Enrolled Codex account "glt-oai2"/);

  // Lookup with '+' and mixed case resolves 'glt-oai2' across commands.
  const pausePlus = await invokeCli(['accounts', 'pause', 'glt+oai2'], sb);
  assert.equal(pausePlus.exit, 0, pausePlus.stderr);
  assert.match(pausePlus.stdout, /Paused account "glt-oai2"/);

  const unpausePlus = await invokeCli(['accounts', 'unpause', 'GLT+OAI2'], sb);
  assert.equal(unpausePlus.exit, 0, unpausePlus.stderr);
  assert.match(unpausePlus.stdout, /Unpaused account "glt-oai2"/);

  const usePlus = await invokeCli(['accounts', 'use', 'glt+oai2'], sb);
  assert.equal(usePlus.exit, 0, usePlus.stderr);
  assert.match(usePlus.stdout, /Active codex account set to "glt-oai2"/);

  const logPlus = await invokeCli(['accounts', 'log', 'glt+oai2'], sb);
  assert.equal(logPlus.exit, 0, logPlus.stderr);
});

test('3445 T4: reauth_required (401 / token_revoked / invalid_grant) visibility, rotation skip, and refresh/expiry status', async t => {
  const cloud = await createMockCloudServer(t, {
    accounts: [
      {
        account_id: 'acc_rev_1',
        label: 'revoked-cx',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        is_owner: true,
        shared: false,
        state: 'ready',
        _leaseErrorStatus: 401,
        _leaseErrorBody: {
          detail: { error: 'token_revoked', message: 'Your refresh token has already been used or revoked (invalid_grant).' },
          account_id: 'acc_rev_1',
        },
        five_hour_used_percent: 10,
        five_hour_reset_at: '2026-11-15T02:00:00Z',
        weekly_used_percent: 20,
        weekly_reset_at: '2026-11-16T12:00:00Z',
        cooling_until: null,
        last_refresh_at: '2026-11-14T22:00:00Z',
        created_at: '2026-11-01T00:00:00Z',
      },
      {
        account_id: 'acc_ok_2',
        label: 'healthy-cx',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        is_owner: true,
        shared: false,
        state: 'ready',
        five_hour_used_percent: 15,
        five_hour_reset_at: '2026-11-15T03:00:00Z',
        weekly_used_percent: 30,
        weekly_reset_at: '2026-11-19T12:00:00Z',
        cooling_until: null,
        last_refresh_at: '2026-11-15T00:45:00Z',
        token_expires_at: '2026-11-15T01:55:00Z',
        created_at: '2026-11-02T00:00:00Z',
      },
    ],
  });
  const sb = makeTempSandbox(t, cloud.serverUrl);

  // Seed state as enrolled with sticky acc_rev_1 so rotation must hit 401 token_revoked on acc_rev_1 and fall over to healthy-cx!
  writeFileSync(join(sb.stateDir, 'accounts-state.json'), JSON.stringify({
    version: 1,
    enrolled: true,
    providers: ['codex'],
    active: { codex: { account_id: 'acc_rev_1', label: 'revoked-cx', provider: 'codex' } },
    cooling: {},
  }));

  // 1. selectCloudPoolLogin & leaseCloudAccount automatically skip 401 token_revoked acc_rev_1 and lease healthy-cx!
  const sel = await selectCloudPoolLogin(
    { cwd: sb.cwd, env: sb.env, fallbackAgent: { kind: 'codex', command: 'codex' } },
    { tmpRoot: sb.root },
  );
  assert.equal(sel.state, 'ready');
  assert.equal(sel.account.label, 'healthy-cx');
  assert.equal(cloud.state.accounts[0].state, 'reauth_required');

  // 2. Pinning a reauth_required account explicitly refuses with actionable re-auth message.
  const useRevoked = await invokeCli(['accounts', 'use', 'revoked-cx'], sb, { now: () => cloud.state.nowMs });
  assert.equal(useRevoked.exit, 1);
  assert.match(useRevoked.stderr, /reauth_required|re-authentication/i);
  assert.match(useRevoked.stderr, /pdd accounts add --provider codex --label revoked-cx/);

  // 3. Pin healthy-cx, then verify pdd accounts list & pdd accounts status [--json] surface REFRESH timestamps and reauth_required!
  assert.equal((await invokeCli(['accounts', 'use', 'healthy-cx'], sb, { now: () => cloud.state.nowMs })).exit, 0);

  const listOut = await invokeCli(['accounts', 'list'], sb, { now: () => cloud.state.nowMs });
  assert.equal(listOut.exit, 0, listOut.stderr);
  assert.match(listOut.stdout, /LABEL\s+PROVIDER\s+ACCESS\s+5H\s+7D\s+STATE\s+REFRESH/);
  assert.match(listOut.stdout, /revoked-cx\s+codex[\s\S]*?reauth_required/);
  assert.doesNotMatch(listOut.stdout, /revoked-cx[^\n]*\bready\b/);
  assert.match(listOut.stdout, /2026-11-15T00:45Z/);
  assert.match(listOut.stdout, /Re-authentication required/);

  const statusHuman = await invokeCli(['accounts', 'status'], sb, { now: () => cloud.state.nowMs });
  assert.equal(statusHuman.exit, 0, statusHuman.stderr);
  assert.match(statusHuman.stdout, /Codex isolated home:/);
  assert.match(statusHuman.stdout, /codex-home/);
  assert.match(statusHuman.stdout, /Active codex: healthy-cx/);
  assert.match(statusHuman.stdout, /last refresh: 2026-11-15T00:45Z/);
  assert.match(statusHuman.stdout, /Re-authentication required: "revoked-cx"/);

  const statusJsonRes = await invokeCli(['accounts', 'status', '--json'], sb, { now: () => cloud.state.nowMs });
  assert.equal(statusJsonRes.exit, 0, statusJsonRes.stderr);
  const statusJson = JSON.parse(statusJsonRes.stdout);
  assert.equal(statusJson.codex_home.path, pddManagedCodexHome(sb.env));
  assert.equal(statusJson.codex_home.materialized, true);
  assert.deepEqual(statusJson.reauth_required, [{ account_id: 'acc_rev_1', label: 'revoked-cx', provider: 'codex' }]);
  const revEntry = statusJson.accounts.find(a => a.label === 'revoked-cx');
  const okEntry = statusJson.accounts.find(a => a.label === 'healthy-cx');
  assert.equal(revEntry.state, 'reauth_required');
  assert.equal(okEntry.state, 'ready');
  assert.equal(okEntry.last_refresh_at, '2026-11-15T00:45:00Z');

  // 4. Live mid-step 401 token_revoked failure during runStepAgentProcess marks account reauth_required and rotates to backup!
  cloud.state.accounts.push({
    account_id: 'acc_ok_3',
    label: 'backup-cx',
    provider: 'codex',
    plan: 'pro',
    owner_login: 'Serhan-Asad',
    is_owner: true,
    shared: false,
    state: 'ready',
    five_hour_used_percent: 5,
    five_hour_reset_at: '2026-11-15T04:00:00Z',
    weekly_used_percent: 10,
    weekly_reset_at: '2026-11-20T12:00:00Z',
    cooling_until: null,
    created_at: '2026-11-03T00:00:00Z',
  });
  let stepCalls = 0;
  const stepRotated = await runStepAgentProcess({
    agent: 'codex',
    step: 'build',
    args: ['exec', 'hi'],
    cwd: sb.cwd,
    env: sb.env,
    accountsPorts: { tmpRoot: sb.root },
    run: async () => {
      stepCalls += 1;
      if (stepCalls === 1) {
        return { code: 1, stdout: '', stderr: 'Error: 401 Unauthorized: token_revoked (refresh_token_reused)' };
      }
      return { code: 0, stdout: 'rotated-after-revoke-ok', stderr: '' };
    },
  });
  assert.equal(stepRotated.code, 0);
  assert.equal(stepCalls, 2);
  assert.equal(stepRotated.account.label, 'backup-cx');
});


test('3445 T5: sync guards paused/expiring/step-only leases, Cloud bearer 401 safety, persistent active & inactive reauth lifecycle, failed materialization atomicity, and cross-provider heal', async t => {
  const baseMs = Date.parse('2026-11-16T20:00:00Z');
  const cloud = await createMockCloudServer(t, {
    nowMs: baseMs,
    accounts: [
      {
        account_id: 'acc_sync_1',
        label: 'sync-cx',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        is_owner: true,
        shared: false,
        state: 'ready',
        five_hour_used_percent: 10,
        five_hour_reset_at: '2026-11-17T01:00:00Z',
        weekly_used_percent: 20,
        weekly_reset_at: '2026-11-22T00:00:00Z',
        cooling_until: null,
        last_refresh_at: '2026-11-16T19:55:00Z',
        created_at: '2026-11-01T00:00:00Z',
      },
      {
        account_id: 'acc_bare_401',
        label: 'bare-401-cx',
        provider: 'codex',
        plan: 'pro',
        owner_login: 'Serhan-Asad',
        is_owner: true,
        shared: false,
        state: 'ready',
        _leaseErrorStatus: 401,
        _leaseErrorBody: {
          detail: { message: 'Unauthorized' },
          account_id: 'acc_bare_401',
        },
        five_hour_used_percent: 5,
        five_hour_reset_at: '2026-11-17T01:00:00Z',
        weekly_used_percent: 10,
        weekly_reset_at: '2026-11-21T00:00:00Z',
        cooling_until: null,
        last_refresh_at: '2026-11-16T18:00:00Z',
        created_at: '2026-11-02T00:00:00Z',
      },
    ],
  });
  const sb = makeTempSandbox(t, cloud.serverUrl);
  const stateFile = join(sb.stateDir, 'accounts-state.json');

  // 1. Seed a healthy materialized lease first.
  assert.equal((await invokeCli(['accounts', 'use', 'sync-cx'], sb, { now: () => baseMs })).exit, 0);

  // 1a. Cached state: "paused" must NOT short-circuit sync --quiet as a valid cache hit!
  const pausedState = JSON.parse(readFileSync(stateFile, 'utf8'));
  pausedState.active.codex.state = 'paused';
  pausedState.active.codex.expires_at = new Date(baseMs + 3600_000).toISOString();
  writeFileSync(stateFile, JSON.stringify(pausedState));
  const reqBeforePausedSync = cloud.state.requests.length;
  assert.equal((await invokeCli(['accounts', 'sync', '--provider', 'codex', '--quiet'], sb, { now: () => baseMs })).exit, 0);
  assert.ok(cloud.state.requests.length > reqBeforePausedSync, 'paused cached entry did not bypass Cloud sync');

  // 1b. Cached state: "ready" with far expires_at but near-expiry access_token_expires_at (< 5m) must refresh from Cloud!
  const expiringTokState = JSON.parse(readFileSync(stateFile, 'utf8'));
  expiringTokState.active.codex.state = 'ready';
  expiringTokState.active.codex.expires_at = new Date(baseMs + 3600_000).toISOString();
  expiringTokState.active.codex.access_token_expires_at = new Date(baseMs + 60_000).toISOString();
  writeFileSync(stateFile, JSON.stringify(expiringTokState));
  const reqBeforeExpiringSync = cloud.state.requests.length;
  assert.equal((await invokeCli(['accounts', 'sync', '--provider', 'codex', '--quiet'], sb, { now: () => baseMs })).exit, 0);
  assert.ok(cloud.state.requests.length > reqBeforeExpiringSync, 'expiring access_token_expires_at triggered Cloud refresh');

  // 1c. Step-only lease rotation sets materialized_local: false so terminal sync updates codex-home!
  cloud.state.accounts.push({
    account_id: 'acc_step_b',
    label: 'step-b-cx',
    provider: 'codex',
    plan: 'pro',
    owner_login: 'Serhan-Asad',
    is_owner: true,
    shared: false,
    state: 'ready',
    five_hour_used_percent: 2,
    five_hour_reset_at: '2026-11-17T01:00:00Z',
    weekly_used_percent: 4,
    weekly_reset_at: '2026-11-18T00:00:00Z',
    cooling_until: null,
    last_refresh_at: '2026-11-16T19:58:00Z',
    created_at: '2026-11-03T00:00:00Z',
  });
  const stepLease = await leaseCloudAccount(
    { provider: 'codex', currentAccountId: null, skipAccountIds: ['acc_sync_1', 'acc_bare_401'], holderId: 'pdd-step' },
    { cwd: sb.cwd, env: sb.env, now: () => baseMs },
  );
  assert.equal(stepLease.account.account_id, 'acc_step_b');
  assert.equal(JSON.parse(readFileSync(managedCodexAuthPath(sb.env), 'utf8')).tokens.access_token, 'acc_tok_sync-cx_secret12345', 'step lease did not touch codex-home');
  assert.equal(JSON.parse(readFileSync(stateFile, 'utf8')).active.codex.materialized_local, false);

  const syncAfterStepRotate = await invokeCli(['accounts', 'sync', '--provider', 'codex', '--quiet'], sb, { now: () => baseMs });
  assert.equal(syncAfterStepRotate.exit, 0);
  assert.equal(
    JSON.parse(readFileSync(managedCodexAuthPath(sb.env), 'utf8')).tokens.access_token,
    'acc_tok_step-b-cx_secret12345',
    'sync detected materialized_local === false and materialized step-b-cx into codex-home',
  );
  cloud.state.accounts = cloud.state.accounts.filter(a => a.account_id !== 'acc_step_b');

  // 1d. Cloud bearer 401 (expired PDD_TOKEN, no account_id in response) must NEVER blacklist the active provider account!
  assert.equal((await invokeCli(['accounts', 'use', 'sync-cx'], sb, { now: () => baseMs })).exit, 0);
  await assert.rejects(
    () => leaseCloudAccount(
      { provider: 'codex' },
      { cwd: sb.cwd, env: { ...sb.env, PDD_TOKEN: 'expired-cloud-bearer-token' }, now: () => baseMs },
    ),
    err => err instanceof CloudAccountsError && err.status === 401,
  );
  const stateAfterCloud401 = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.equal(stateAfterCloud401.reauth, undefined, 'Cloud bearer 401 did not taint reauth map');
  assert.equal(stateAfterCloud401.active.codex.state, 'ready', 'active account stayed ready after Cloud bearer 401');

  // 2. Account-specific bare 401 + subsequent all_cooling preserves persistent local reauth_required,
  //    refuses stale "use", and recovers BOTH reauth map AND active.codex.state once a newer refresh arrives!
  cloud.state.accounts[0].state = 'cooling';
  cloud.state.accounts[0].cooling_until = '2026-11-16T22:00:00Z';
  writeFileSync(stateFile, JSON.stringify({
    version: 1,
    enrolled: true,
    providers: ['codex'],
    active: { codex: { account_id: 'acc_bare_401', label: 'bare-401-cx', provider: 'codex', state: 'ready' } },
    cooling: {},
  }));

  const leaseAllCool = await leaseCloudAccount({ provider: 'codex' }, { cwd: sb.cwd, env: sb.env, now: () => baseMs });
  assert.equal(leaseAllCool.state, 'all_cooling');
  const savedAfterAllCool = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.ok(savedAfterAllCool.reauth?.acc_bare_401?.marked_at, 'reauth marker survived all_cooling state write');
  assert.equal(savedAfterAllCool.active.codex.state, 'reauth_required');

  delete cloud.state.accounts[1]._leaseErrorStatus;
  delete cloud.state.accounts[1].last_refresh_error;
  cloud.state.accounts[1].state = 'ready';
  cloud.state.accounts[1].last_refresh_at = '2026-11-16T18:00:00Z';

  const staleUse = await invokeCli(['accounts', 'use', 'bare-401-cx'], sb, { now: () => baseMs });
  assert.equal(staleUse.exit, 1, 'stale lease without newer refresh cannot clear local reauth_required');
  assert.match(staleUse.stderr, /reauth_required|re-authentication/i);

  const statusStale = await invokeCli(['accounts', 'status', '--json'], sb, { now: () => baseMs });
  assert.equal(statusStale.exit, 0);
  const parsedStale = JSON.parse(statusStale.stdout);
  assert.equal(parsedStale.accounts.find(a => a.account_id === 'acc_bare_401').state, 'reauth_required');

  // Once Cloud reports a newer successful refresh after marked_at, BOTH reauth marker AND active.codex.state recover to ready!
  cloud.state.accounts[1].last_refresh_at = '2026-11-16T20:05:00Z';
  const listCleared = await invokeCli(['accounts', 'list'], sb, { now: () => baseMs + 10 * 60_000 });
  assert.equal(listCleared.exit, 0);
  const savedAfterHeal = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.equal(savedAfterHeal.reauth?.acc_bare_401, undefined, 'newer Cloud last_refresh_at cleared local reauth marker');
  assert.equal(savedAfterHeal.active.codex.state, 'ready', 'active entry recovered from reauth_required to ready');

  // 2b. Inactive Cloud-reported revocation is persisted on list so a subsequent stale ready read cannot flip it back!
  cloud.state.accounts.push({
    account_id: 'acc_inactive_rev',
    label: 'inactive-rev-cx',
    provider: 'codex',
    plan: 'pro',
    owner_login: 'Serhan-Asad',
    is_owner: true,
    shared: false,
    state: 'reauth_required',
    last_refresh_at: '2026-11-16T19:00:00Z',
    created_at: '2026-11-04T00:00:00Z',
  });
  assert.equal((await invokeCli(['accounts', 'list'], sb, { now: () => baseMs + 12 * 60_000 })).exit, 0);
  const savedInactiveRev = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.ok(savedInactiveRev.reauth?.acc_inactive_rev?.marked_at, 'inactive Cloud-reported revocation persisted locally');

  cloud.state.accounts.find(a => a.account_id === 'acc_inactive_rev').state = 'ready';
  const statusAfterStaleInactive = JSON.parse((await invokeCli(['accounts', 'status', '--json'], sb, { now: () => baseMs + 13 * 60_000 })).stdout);
  assert.equal(statusAfterStaleInactive.accounts.find(a => a.account_id === 'acc_inactive_rev').state, 'reauth_required');
  cloud.state.accounts = cloud.state.accounts.filter(a => a.account_id !== 'acc_inactive_rev');

  // Also verify last_refresh_error: "401 Unauthorized" on Cloud account record surfaces as reauth_required!
  cloud.state.accounts[1].last_refresh_error = 'HTTP 401 Unauthorized from auth.openai.com';
  const statusRefresh401 = JSON.parse((await invokeCli(['accounts', 'status', '--json'], sb, { now: () => baseMs + 14 * 60_000 })).stdout);
  assert.equal(statusRefresh401.accounts.find(a => a.account_id === 'acc_bare_401').state, 'reauth_required');
  delete cloud.state.accounts[1].last_refresh_error;

  // 3. Failed materialization (symlinked config.toml inside managed CODEX_HOME) does NOT write active lease metadata to accounts-state.json!
  cloud.state.accounts[0].state = 'ready';
  cloud.state.accounts[0].cooling_until = null;
  writeFileSync(stateFile, JSON.stringify({ version: 1, enrolled: true, providers: ['codex'], active: {}, cooling: {} }));
  const managedCfg = managedCodexConfigPath(sb.env);
  rmSync(managedCfg, { force: true });
  const dummyTarget = join(sb.root, 'dummy-cfg.toml');
  writeFileSync(dummyTarget, 'model = "gpt-5.4"\n');
  symlinkSync(dummyTarget, managedCfg);

  const failedUse = await invokeCli(['accounts', 'use', 'sync-cx'], sb, { now: () => baseMs });
  assert.equal(failedUse.exit, 1);
  const stateAfterFailedUse = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.equal(stateAfterFailedUse.active?.codex, undefined, 'active.codex not persisted when materialization fails');
  rmSync(managedCfg, { force: true });

  // 4. Cross-provider zero-account heal in runStepAgentProcess preserves unrelated Claude reauth markers!
  cloud.state.accounts = [
    {
      account_id: 'acc_cl_rev',
      label: 'revoked-claude',
      provider: 'claude',
      plan: 'max',
      owner_login: 'Serhan-Asad',
      is_owner: true,
      shared: false,
      state: 'reauth_required',
      created_at: '2026-11-05T00:00:00Z',
    },
  ];
  writeFileSync(stateFile, JSON.stringify({
    enrolled: true,
    providers: ['codex', 'claude'],
    active: { codex: { account_id: 'acc_deleted_cx', label: 'gone-cx', provider: 'codex', state: 'ready' } },
    cooling: {},
    reauth: { acc_cl_rev: { marked_at: '2026-11-16T20:00:00.000Z' } },
  }));
  const crossHeal = await runStepAgentProcess({
    agent: 'codex',
    step: 'build',
    args: ['exec', 'hi'],
    cwd: sb.cwd,
    env: sb.env,
    accountsPorts: { tmpRoot: sb.root },
    run: async () => ({ code: 0, stdout: 'local-codex-ok', stderr: '' }),
  });
  assert.equal(crossHeal.code, 0);
  const stateAfterCrossHeal = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.deepEqual(stateAfterCrossHeal.providers, ['claude']);
  assert.equal(
    stateAfterCrossHeal.reauth?.acc_cl_rev?.marked_at,
    '2026-11-16T20:00:00.000Z',
    'unrelated Claude reauth marker survived Codex zero-account heal',
  );
});

test('#3516: native openai provider gateway materialization, synthetic unsigned id_token, non-PDD base URL preservation, and hermetic stopCodexAppServerDaemon', t => {
  // 1. Deterministic synthetic unsigned metadata JWT (`alg: "none"`, `sig`, zero secrets)
  const defaultJwt = buildSyntheticGatewayIdToken();
  const [rawHeader, rawPayload, rawSig] = defaultJwt.split('.');
  assert.equal(rawSig, 'sig');
  assert.deepEqual(JSON.parse(Buffer.from(rawHeader, 'base64url').toString('utf8')), { alg: 'none', typ: 'JWT' });
  assert.deepEqual(JSON.parse(Buffer.from(rawPayload, 'base64url').toString('utf8')), {
    exp: 4102444800,
    iat: 1700000000,
    'https://api.openai.com/auth': {
      chatgpt_account_id: 'acct_pdd_gateway',
      chatgpt_plan_type: 'pro',
      chatgpt_user_id: 'user_pdd_gateway',
    },
  });
  const teamJwt = buildSyntheticGatewayIdToken({ planType: 'Team' });
  assert.equal(
    JSON.parse(Buffer.from(teamJwt.split('.')[1], 'base64url').toString('utf8'))['https://api.openai.com/auth'].chatgpt_plan_type,
    'team',
  );

  // 2. Preserving non-PDD user `openai_base_url` and `chatgpt_base_url` while stripping PDD-managed gateway URLs
  const sb = makeTempSandbox(t, 'https://cloud.example.com');
  const userCodexDir = localCodexHome(sb.env);
  mkdirSync(userCodexDir, { recursive: true, mode: 0o700 });
  const userCfgPath = localCodexConfigPath(sb.env);
  writeFileSync(userCfgPath, [
    'model = "gpt-5.4"',
    'openai_base_url = "https://corp-openai.example.com/v1"',
    'chatgpt_base_url = "https://corp-chatgpt.example.com/backend-api"',
    '',
  ].join('\n'), { mode: 0o600 });

  const daemonCalls = [];
  const spySpawnSync = (cmd, args, opts) => {
    daemonCalls.push({ cmd, args, codexHome: opts?.env?.CODEX_HOME, timeout: opts?.timeout });
    return { status: 0 };
  };

  const mat = materializeLocalCodexAuth({
    delivery_mode: 'gateway_grant',
    plan_type: 'team',
    codex_gateway_url: 'https://cloud.example.com/v1/codex-gateway/lse_01020304',
    codex_gateway_token: 'pddg_lse_01020304_grantTokenAbc',
  }, { env: sb.env }, { now: () => Date.parse('2026-11-18T00:00:00.000Z') });

  // User ~/.codex/config.toml keeps its custom non-PDD URLs untouched!
  const untouchedUserCfg = parseToml(readFileSync(userCfgPath, 'utf8'));
  assert.equal(untouchedUserCfg.openai_base_url, 'https://corp-openai.example.com/v1');
  assert.equal(untouchedUserCfg.chatgpt_base_url, 'https://corp-chatgpt.example.com/backend-api');

  // Managed config.toml routes native openai + chatgpt to normalized constant gateway URL with no top-level model_provider!
  const managedCfg = parseToml(readFileSync(mat.configPath, 'utf8'));
  assert.equal(managedCfg.model_provider, undefined);
  assert.equal(managedCfg.openai_base_url, 'https://cloud.example.com/v1/codex-gateway');
  assert.equal(managedCfg.chatgpt_base_url, 'https://cloud.example.com/v1/codex-gateway');
  assert.equal(managedCfg.cli_auth_credentials_store, 'file');
  assert.equal(managedCfg.model_providers?.pdd_codex_gateway?.base_url, 'https://cloud.example.com/v1/codex-gateway');
  assert.equal(managedCfg.model_providers?.pdd_codex_gateway?.requires_openai_auth, true);

  const managedAuth = JSON.parse(readFileSync(mat.authPath, 'utf8'));
  assert.deepEqual(managedAuth, {
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      id_token: teamJwt,
      access_token: 'pddg_lse_01020304_grantTokenAbc',
      refresh_token: '',
      account_id: 'acct_pdd_gateway',
    },
    last_refresh: '2026-11-18T00:00:00.000Z',
  });

  // Restoring gateway config removes PDD's /v1/codex-gateway URLs, restores user's non-PDD URLs, and stops stale daemon!
  const restored = restoreLocalCodexGatewayConfig(
    { env: sb.env, removeAuthFile: true },
    { spawnSync: spySpawnSync },
  );
  assert.equal(restored.restoredConfig, true);
  assert.equal(restored.removedAuth, true);
  assert.equal(existsSync(mat.authPath), false);
  const afterRestoreCfg = parseToml(readFileSync(mat.configPath, 'utf8'));
  assert.equal(afterRestoreCfg.model_providers, undefined);
  assert.equal(afterRestoreCfg.openai_base_url, 'https://corp-openai.example.com/v1');
  assert.equal(afterRestoreCfg.chatgpt_base_url, 'https://corp-chatgpt.example.com/backend-api');
  assert.equal(daemonCalls.length, 1);
  assert.deepEqual(daemonCalls[0], {
    cmd: 'codex',
    args: ['app-server', 'daemon', 'stop'],
    codexHome: pddManagedCodexHome(sb.env),
    timeout: 2500,
  });

  // Calling restore again when nothing is gateway-managed does NOT touch non-PDD URLs or spawn daemon stop!
  const noopRestore = restoreLocalCodexGatewayConfig(
    { env: sb.env, removeAuthFile: true },
    { spawnSync: spySpawnSync },
  );
  assert.equal(noopRestore.restoredConfig, false);
  assert.equal(noopRestore.removedAuth, false);
  assert.equal(daemonCalls.length, 1, 'no daemon stop spawned when neither config nor auth changed');

  // Switching from gateway_grant to direct_stripped also strips PDD gateway URLs while preserving non-PDD user URLs!
  materializeLocalCodexAuth({
    delivery_mode: 'gateway_grant',
    codex_gateway_url: 'https://cloud.example.com/v1/codex-gateway/lse_01020304',
    codex_gateway_token: 'pddg_lse_01020304_grantTokenAbc',
  }, { env: sb.env });
  materializeLocalCodexAuth({
    auth_mode: 'chatgpt',
    tokens: {
      access_token: 'direct_access',
      refresh_token: 'direct_refresh_to_strip',
      id_token: makeJwt({ email: 'owner@example.com' }),
      account_id: 'acct_owner_direct',
    },
  }, { env: sb.env, previousManagedCodexGateway: true });
  const directCfg = parseToml(readFileSync(mat.configPath, 'utf8'));
  assert.equal(directCfg.model_providers, undefined);
  assert.equal(directCfg.openai_base_url, 'https://corp-openai.example.com/v1');
  assert.equal(directCfg.chatgpt_base_url, 'https://corp-chatgpt.example.com/backend-api');

  // 3. Hermetic virtual-fs guard on stopCodexAppServerDaemon
  const fakeVirtualFs = {};
  assert.equal(stopCodexAppServerDaemon('/virtual/codex-home', { fs: fakeVirtualFs }), false);
  let virtualSpyCalled = false;
  assert.equal(
    stopCodexAppServerDaemon('/virtual/codex-home', {
      fs: fakeVirtualFs,
      spawnSync: () => {
        virtualSpyCalled = true;
        throw new Error('simulated codex missing');
      },
    }),
    false,
  );
  assert.equal(virtualSpyCalled, true, 'explicit spawnSync port is invoked and fail-open on error');
});

test('#3518: managed CODEX_HOME symlinks plugins, browser, chrome-native-hosts-v2.json, computer-use, and node_repl, and heals pre-existing partial non-symlink cache dirs without touching user sessions', t => {
  const sb = makeTempSandbox(t, 'https://cloud.example.com');
  const userCodexDir = localCodexHome(sb.env);
  const managedHome = pddManagedCodexHome(sb.env);
  mkdirSync(userCodexDir, { recursive: true, mode: 0o700 });

  // Populate `~/.codex` with full bundled plugins/browser/native-host/computer-use/node_repl state.
  mkdirSync(join(userCodexDir, 'plugins', 'cache', 'openai-bundled', 'browser'), { recursive: true });
  mkdirSync(join(userCodexDir, 'plugins', 'cache', 'openai-primary-runtime'), { recursive: true });
  writeFileSync(join(userCodexDir, 'plugins', 'cache', 'openai-bundled', 'browser', 'manifest.json'), '{"name":"browser"}');
  mkdirSync(join(userCodexDir, 'browser'), { recursive: true });
  writeFileSync(join(userCodexDir, 'browser', 'state.json'), '{"ok":true}');
  mkdirSync(join(userCodexDir, 'computer-use'), { recursive: true });
  writeFileSync(join(userCodexDir, 'computer-use', 'helper.json'), '{"ok":true}');
  mkdirSync(join(userCodexDir, 'node_repl'), { recursive: true });
  writeFileSync(join(userCodexDir, 'node_repl', 'runtime.json'), '{"ok":true}');
  writeFileSync(join(userCodexDir, 'chrome-native-hosts-v2.json'), '{"hosts":["com.openai.codex"]}\n');
  mkdirSync(join(userCodexDir, 'sessions'), { recursive: true });
  mkdirSync(join(userCodexDir, 'memories'), { recursive: true });

  // 1. Fresh materialization symlinks all 5 new plugin/browser entries into managedHome!
  materializeLocalCodexAuth({
    delivery_mode: 'gateway_grant',
    codex_gateway_url: 'https://cloud.example.com/v1/codex-gateway/lse_3518a',
    codex_gateway_token: 'pddg_lse_3518a_grantTokenFresh',
  }, { env: sb.env }, { spawnSync: () => ({ status: 0 }) });

  for (const name of ['plugins', 'browser', 'chrome-native-hosts-v2.json', 'computer-use', 'node_repl']) {
    const linkPath = join(managedHome, name);
    assert.equal(lstatSync(linkPath).isSymbolicLink(), true, `${name} symlinked on fresh materialization`);
    assert.equal(realpathSync(linkPath), realpathSync(join(userCodexDir, name)));
  }

  // 2. Upgrade healing: simulate a machine from 0.1.35 where codex already created a real non-symlink
  //    `managedHome/plugins` (with only `cache/openai-curated-remote`), non-symlink `browser`, and
  //    non-symlink `chrome-native-hosts-v2.json`, PLUS a non-symlink `managedHome/sessions` containing
  //    user session data that MUST NOT be deleted!
  for (const name of ['plugins', 'browser', 'chrome-native-hosts-v2.json', 'computer-use', 'node_repl', 'sessions', 'memories']) {
    rmSync(join(managedHome, name), { recursive: true, force: true });
  }
  mkdirSync(join(managedHome, 'plugins', 'cache', 'openai-curated-remote'), { recursive: true });
  writeFileSync(join(managedHome, 'plugins', 'cache', 'openai-curated-remote', 'partial.json'), '{}');
  mkdirSync(join(managedHome, 'browser'), { recursive: true });
  writeFileSync(join(managedHome, 'chrome-native-hosts-v2.json'), '{"stale":true}\n');
  mkdirSync(join(managedHome, 'sessions'), { recursive: true });
  writeFileSync(join(managedHome, 'sessions', 'keep-user-rollout.jsonl'), '{"keep":true}\n');
  mkdirSync(join(managedHome, 'memories'), { recursive: true });
  writeFileSync(join(managedHome, 'memories', 'keep-memory.md'), 'important note\n');

  materializeLocalCodexAuth({
    delivery_mode: 'gateway_grant',
    codex_gateway_url: 'https://cloud.example.com/v1/codex-gateway/lse_3518b',
    codex_gateway_token: 'pddg_lse_3518b_grantTokenHeal',
  }, { env: sb.env }, { spawnSync: () => ({ status: 0 }) });

  // Incomplete auto-generated cache dirs + native-hosts file in managedHome were replaced with symlinks to ~/.codex!
  for (const name of ['plugins', 'browser', 'chrome-native-hosts-v2.json', 'computer-use', 'node_repl']) {
    const linkPath = join(managedHome, name);
    assert.equal(lstatSync(linkPath).isSymbolicLink(), true, `stale non-symlink ${name} replaced with symlink`);
    assert.equal(realpathSync(linkPath), realpathSync(join(userCodexDir, name)));
  }
  assert.equal(
    existsSync(join(managedHome, 'plugins', 'cache', 'openai-bundled', 'browser', 'manifest.json')),
    true,
    'managed CODEX_HOME now exposes ~/.codex/plugins/cache/openai-bundled',
  );
  assert.equal(
    existsSync(join(managedHome, 'plugins', 'cache', 'openai-primary-runtime')),
    true,
    'managed CODEX_HOME now exposes ~/.codex/plugins/cache/openai-primary-runtime',
  );
  assert.equal(
    readFileSync(join(managedHome, 'chrome-native-hosts-v2.json'), 'utf8'),
    '{"hosts":["com.openai.codex"]}\n',
  );

  // Non-symlink `sessions` and `memories` in managedHome were NOT deleted, and `~/.codex/plugins` is intact!
  assert.equal(lstatSync(join(managedHome, 'sessions')).isSymbolicLink(), false);
  assert.equal(readFileSync(join(managedHome, 'sessions', 'keep-user-rollout.jsonl'), 'utf8'), '{"keep":true}\n');
  assert.equal(lstatSync(join(managedHome, 'memories')).isSymbolicLink(), false);
  assert.equal(readFileSync(join(managedHome, 'memories', 'keep-memory.md'), 'utf8'), 'important note\n');
  assert.equal(lstatSync(join(userCodexDir, 'plugins')).isSymbolicLink(), false);
});

test('dynamic ~/.codex mirror + denylist + safe symlink support + pruning in managedHome and createCodexStepOverlay', t => {
  const sb = makeTempSandbox(t, 'https://cloud.example.com');
  const userCodexDir = localCodexHome(sb.env);
  const managedHome = pddManagedCodexHome(sb.env);
  mkdirSync(userCodexDir, { recursive: true, mode: 0o700 });
  mkdirSync(managedHome, { recursive: true, mode: 0o700 });

  // Direct classifier unit checks
  for (const denied of [
    '.', '..', '.DS_Store', 'auth.json', 'auth.lock', 'auth.json.bak',
    'auth.json~', 'auth.json-bak', 'auth.json_old',
    'config.toml', 'config.toml.bak', 'config.toml~', '.config.toml.merge-lock', 'model-switch-backups',
    '.codex-global-state.json', 'version.json', 'vendor_imports',
    'app-server-daemon', 'app-server-control', 'ipc', 'tmp', '.tmp', '.tmp_upload', 'draft.tmp', 'log',
    'logs_2.sqlite', 'logs_2.sqlite-wal', 'logs_2.sqlite-shm', 'logs_2.sqlite-journal',
    'logs_app.sqlite', 'logs_2.sqlite.corrupt', 'state_5.sqlite-wal',
    'state_5.sqlite-shm', 'state_5.sqlite-journal', 'models_cache.json', 'shell_snapshots', 'mcp-oauth-locks',
    '.sqlite-maintenance.lock', 'installation_id', 'custom.lock', 'sync-lock',
    'old.bak-20261115', 'partial.tmp.99',
  ]) {
    assert.equal(isIsolatedCodexHomeEntry(denied), true, `expected ${denied} to be denylisted`);
  }
  for (const allowed of [
    'AGENTS.md', 'agents', 'skills', 'hooks.json', '.hook-trust', 'review-prompts',
    'packages', 'herdr.config.toml', 'prompt.tmpl',
    'herdr-agent-state.sh', 'prompts', 'generated_images', 'state_5.sqlite',
    'thread_history_1.sqlite', 'future_codex_feature_2027',
  ]) {
    assert.equal(isIsolatedCodexHomeEntry(allowed), false, `expected ${allowed} to be allowed`);
  }

  // Seed external dotfiles targets (both relative and absolute symlinks in ~/.codex)
  const codexManagedDir = join(sb.home, '.codex-managed');
  mkdirSync(codexManagedDir, { recursive: true });
  writeFileSync(join(codexManagedDir, 'AGENTS.md'), '# Shared AGENTS instructions\n');
  const extSkillsDir = join(sb.home, '.agents', 'skills', 'demo-skill');
  mkdirSync(extSkillsDir, { recursive: true });
  writeFileSync(join(extSkillsDir, 'SKILL.md'), '# Demo skill\n');

  // Relative symlink `AGENTS.md -> ../.codex-managed/AGENTS.md` + absolute symlink `skills -> ~/.agents/skills`
  symlinkSync('../.codex-managed/AGENTS.md', join(userCodexDir, 'AGENTS.md'));
  symlinkSync(join(sb.home, '.agents', 'skills'), join(userCodexDir, 'skills'));

  // Seed future / custom / SQLite entries in ~/.codex
  mkdirSync(join(userCodexDir, 'future_codex_feature_2027'), { recursive: true });
  writeFileSync(join(userCodexDir, 'future_codex_feature_2027', 'spec.json'), '{"future":true}\n');
  mkdirSync(join(userCodexDir, 'agents'), { recursive: true });
  writeFileSync(join(userCodexDir, 'agents', 'fixer.toml'), 'name = "fixer"\n');
  writeFileSync(join(userCodexDir, 'hooks.json'), '{"hooks":[]}\n');
  mkdirSync(join(userCodexDir, '.hook-trust'), { recursive: true });
  writeFileSync(join(userCodexDir, '.hook-trust', 'allow.json'), '{}');
  mkdirSync(join(userCodexDir, 'packages'), { recursive: true });
  writeFileSync(join(userCodexDir, 'herdr.config.toml'), 'enabled = true\n');
  writeFileSync(join(userCodexDir, 'prompt.tmpl'), 'template-ok\n');
  writeFileSync(join(userCodexDir, 'state_5.sqlite'), 'sqlite-threads');
  writeFileSync(join(userCodexDir, 'thread_history_1.sqlite'), 'sqlite-history');

  // Seed denylisted entries in ~/.codex
  writeFileSync(join(userCodexDir, 'auth.json'), '{"secret":"user_oauth_never_link"}\n', { mode: 0o600 });
  writeFileSync(join(userCodexDir, 'auth.json~'), '{"secret":"editor_backup_never_link"}\n', { mode: 0o600 });
  writeFileSync(join(userCodexDir, 'config.toml'), 'model = "gpt-5.4"\n', { mode: 0o600 });
  writeFileSync(join(userCodexDir, 'config.toml~'), 'model = "gpt-5.4"\n', { mode: 0o600 });
  writeFileSync(join(userCodexDir, '.codex-global-state.json'), '{"installation":"mac"}');
  writeFileSync(join(userCodexDir, 'version.json'), '{"version":"0.169.1"}');
  mkdirSync(join(userCodexDir, 'vendor_imports'), { recursive: true });
  writeFileSync(join(userCodexDir, 'auth.lock'), '');
  writeFileSync(join(userCodexDir, '.config.toml.merge-lock'), '');
  mkdirSync(join(userCodexDir, 'model-switch-backups'), { recursive: true });
  mkdirSync(join(userCodexDir, 'app-server-daemon'), { recursive: true });
  mkdirSync(join(userCodexDir, 'app-server-control'), { recursive: true });
  mkdirSync(join(userCodexDir, 'ipc'), { recursive: true });
  mkdirSync(join(userCodexDir, 'tmp'), { recursive: true });
  mkdirSync(join(userCodexDir, '.tmp'), { recursive: true });
  mkdirSync(join(userCodexDir, 'log'), { recursive: true });
  mkdirSync(join(userCodexDir, 'shell_snapshots'), { recursive: true });
  mkdirSync(join(userCodexDir, 'mcp-oauth-locks'), { recursive: true });
  writeFileSync(join(userCodexDir, 'logs_2.sqlite'), 'logs-db');
  writeFileSync(join(userCodexDir, 'logs_app.sqlite'), 'logs-app-db');
  writeFileSync(join(userCodexDir, 'logs_2.sqlite.corrupt'), 'logs-corrupt');
  writeFileSync(join(userCodexDir, 'logs_2.sqlite-wal'), 'logs-wal');
  writeFileSync(join(userCodexDir, 'logs_2.sqlite-shm'), 'logs-shm');
  writeFileSync(join(userCodexDir, 'state_5.sqlite-wal'), 'state-wal');
  writeFileSync(join(userCodexDir, 'state_5.sqlite-shm'), 'state-shm');
  writeFileSync(join(userCodexDir, 'state_5.sqlite-journal'), 'state-journal');
  writeFileSync(join(userCodexDir, 'models_cache.json'), '{}');
  writeFileSync(join(userCodexDir, '.sqlite-maintenance.lock'), '');
  writeFileSync(join(userCodexDir, 'installation_id'), 'inst-user');
  writeFileSync(join(userCodexDir, '.DS_Store'), '');

  // Seed unsafe symlinks in ~/.codex: dangling, loop to managedHome, loop to subdir of managedHome, self/parent links, and symlink to auth.json~ / config.toml~
  mkdirSync(join(managedHome, 'inside-managed'), { recursive: true });
  symlinkSync(join(sb.root, 'does-not-exist'), join(userCodexDir, 'dangling_entry'));
  symlinkSync(managedHome, join(userCodexDir, 'loop_to_root'));
  symlinkSync(join(managedHome, 'inside-managed'), join(userCodexDir, 'loop_to_child'));
  symlinkSync('.', join(userCodexDir, 'self_link'));
  symlinkSync('..', join(userCodexDir, 'up_link'));
  symlinkSync(join(userCodexDir, 'auth.json'), join(userCodexDir, 'sneaky_auth_link'));
  symlinkSync(join(userCodexDir, 'auth.json~'), join(userCodexDir, 'sneaky_auth_tilde'));
  symlinkSync(join(userCodexDir, 'config.toml'), join(userCodexDir, 'sneaky_cfg_link'));
  symlinkSync(join(userCodexDir, 'config.toml~'), join(userCodexDir, 'sneaky_cfg_tilde'));

  // Pre-seed a stale denylisted symlink and a bootstrap non-symlink `packages` dir inside managedHome
  symlinkSync(join(userCodexDir, 'models_cache.json'), join(managedHome, 'models_cache.json'));
  mkdirSync(join(managedHome, 'packages'), { recursive: true });
  writeFileSync(join(managedHome, 'packages', 'stale.txt'), 'stale');

  materializeLocalCodexAuth({
    delivery_mode: 'gateway_grant',
    codex_gateway_url: 'https://cloud.example.com/v1/codex-gateway/lse_dyn1',
    codex_gateway_token: 'pddg_lse_dyn1_grantToken',
  }, { env: sb.env }, { spawnSync: () => ({ status: 0 }) });

  // 1. Allowed entries (including future folder + relative/absolute symlinks + .tmpl + SQLite thread DBs) ARE linked
  for (const name of [
    'AGENTS.md',
    'skills',
    'future_codex_feature_2027',
    'agents',
    'hooks.json',
    '.hook-trust',
    'packages',
    'herdr.config.toml',
    'prompt.tmpl',
    'state_5.sqlite',
    'thread_history_1.sqlite',
  ]) {
    const dst = join(managedHome, name);
    assert.equal(lstatSync(dst).isSymbolicLink(), true, `${name} should be symlinked into managedHome`);
  }
  assert.equal(readFileSync(join(managedHome, 'AGENTS.md'), 'utf8'), '# Shared AGENTS instructions\n');
  assert.equal(readFileSync(join(managedHome, 'skills', 'demo-skill', 'SKILL.md'), 'utf8'), '# Demo skill\n');
  assert.equal(readFileSync(join(managedHome, 'future_codex_feature_2027', 'spec.json'), 'utf8'), '{"future":true}\n');
  assert.equal(readFileSync(join(managedHome, 'prompt.tmpl'), 'utf8'), 'template-ok\n');
  assert.equal(readFileSync(join(managedHome, 'state_5.sqlite'), 'utf8'), 'sqlite-threads');

  // 2. Denylisted entries and unsafe symlinks are NOT symlinked into managedHome (and stale models_cache.json symlink was pruned!)
  assert.equal(lstatSync(join(managedHome, 'auth.json')).isSymbolicLink(), false, 'managed auth.json is an isolated 0600 file');
  assert.equal(lstatSync(join(managedHome, 'config.toml')).isSymbolicLink(), false, 'managed config.toml is an isolated 0600 file');
  for (const excluded of [
    'auth.lock', 'auth.json~', 'config.toml~', '.codex-global-state.json', 'version.json', 'vendor_imports',
    '.config.toml.merge-lock', 'model-switch-backups', 'app-server-daemon',
    'app-server-control', 'ipc', 'tmp', '.tmp', 'log', 'shell_snapshots', 'mcp-oauth-locks',
    'logs_2.sqlite', 'logs_app.sqlite', 'logs_2.sqlite.corrupt', 'logs_2.sqlite-wal', 'logs_2.sqlite-shm',
    'state_5.sqlite-wal', 'state_5.sqlite-shm', 'state_5.sqlite-journal', 'models_cache.json',
    '.sqlite-maintenance.lock', 'installation_id', '.DS_Store', 'dangling_entry',
    'loop_to_root', 'loop_to_child', 'self_link', 'up_link',
    'sneaky_auth_link', 'sneaky_auth_tilde', 'sneaky_cfg_link', 'sneaky_cfg_tilde',
  ]) {
    let dstStat = null;
    try { dstStat = lstatSync(join(managedHome, excluded)); } catch {}
    assert.equal(dstStat, null, `${excluded} must NOT exist or be symlinked in managedHome`);
  }

  // 3. Step overlay (`createCodexStepOverlay`) also supports safe symlinks (`AGENTS.md`, `skills`) and rejects loops into managedHome / sourceHome / overlay
  symlinkSync(join(userCodexDir, 'auth.json'), join(userCodexDir, 'browser'));
  symlinkSync(join(sb.root, 'missing-plugin-target'), join(userCodexDir, 'plugins'));
  const stepOverlay = createCodexStepOverlay({
    delivery_mode: 'gateway_grant',
    codex_gateway_url: 'https://cloud.example.com/v1/codex-gateway/lse_dyn1',
    codex_gateway_token: 'pddg_lse_dyn1_grantToken',
  }, { env: sb.env, tmpRoot: sb.root });
  try {
    assert.equal(lstatSync(join(stepOverlay.overlayDir, 'AGENTS.md')).isSymbolicLink(), true);
    assert.equal(readFileSync(join(stepOverlay.overlayDir, 'AGENTS.md'), 'utf8'), '# Shared AGENTS instructions\n');
    assert.equal(lstatSync(join(stepOverlay.overlayDir, 'skills')).isSymbolicLink(), true);
    assert.equal(lstatSync(join(stepOverlay.overlayDir, 'agents')).isSymbolicLink(), true);
    assert.equal(lstatSync(join(stepOverlay.overlayDir, 'hooks.json')).isSymbolicLink(), true);
    assert.equal(lstatSync(join(stepOverlay.overlayDir, '.hook-trust')).isSymbolicLink(), true);
    assert.equal(lstatSync(join(stepOverlay.overlayDir, 'prompt.tmpl')).isSymbolicLink(), true);
    assert.equal(existsSync(join(stepOverlay.overlayDir, 'browser')), false, 'symlink targeting auth.json rejected in step overlay');
    assert.equal(existsSync(join(stepOverlay.overlayDir, 'plugins')), false, 'dangling symlink rejected in step overlay');
    assert.equal(existsSync(join(stepOverlay.overlayDir, 'loop_to_root')), false, 'symlink pointing to managedHome rejected in step overlay');
    assert.equal(existsSync(join(stepOverlay.overlayDir, 'loop_to_child')), false, 'symlink pointing inside managedHome rejected in step overlay');
    assert.equal(existsSync(join(stepOverlay.overlayDir, 'self_link')), false, 'self -> . symlink rejected in step overlay');
    assert.equal(existsSync(join(stepOverlay.overlayDir, 'up_link')), false, 'up -> .. symlink rejected in step overlay');
    assert.equal(isSafeCodexSourceEntry({ lstatSync, realpathSync }, stepOverlay.overlayDir, stepOverlay.overlayDir), true);
    const loopInsideOverlay = join(userCodexDir, 'computer-use');
    symlinkSync(stepOverlay.overlayDir, loopInsideOverlay);
    assert.equal(isSafeCodexSourceEntry({ lstatSync, realpathSync }, loopInsideOverlay, stepOverlay.overlayDir), false);
  } finally {
    stepOverlay.cleanup();
  }

  // 4. Pruning removed and newly-dangling entries from managedHome on next sync
  rmSync(join(userCodexDir, 'future_codex_feature_2027'), { recursive: true, force: true });
  rmSync(join(codexManagedDir, 'AGENTS.md'), { force: true }); // makes userCodexDir/AGENTS.md dangling!
  materializeLocalCodexAuth({
    delivery_mode: 'gateway_grant',
    codex_gateway_url: 'https://cloud.example.com/v1/codex-gateway/lse_dyn2',
    codex_gateway_token: 'pddg_lse_dyn2_grantToken',
  }, { env: sb.env }, { spawnSync: () => ({ status: 0 }) });

  let removedStat = null;
  try { removedStat = lstatSync(join(managedHome, 'future_codex_feature_2027')); } catch {}
  assert.equal(removedStat, null, 'removed source folder symlink pruned from managedHome');
  let danglingAgentsStat = null;
  try { danglingAgentsStat = lstatSync(join(managedHome, 'AGENTS.md')); } catch {}
  assert.equal(danglingAgentsStat, null, 'newly-dangling symlink pruned from managedHome');
  assert.equal(lstatSync(join(managedHome, 'skills')).isSymbolicLink(), true, 'still-valid skills symlink retained');
});


test('P0 surface audit (#2, #3c, #4): unified createCodexStepOverlay native auth + responses_websockets=false, symlinked user ~/.codex/config.toml, empty dir replacement, buildClaudeStepEnv, and restoreLocalClaudeGatewayConfig', t => {
  const sb = makeTempSandbox(t, 'https://api.promptdriven.ai');
  const userCodexDir = join(sb.home, '.codex');
  mkdirSync(userCodexDir, { recursive: true });

  // 1. Dotfile-symlinked user ~/.codex/config.toml is read cleanly and preserved on restoreLocalCodexGatewayConfig
  const dotfilesDir = join(sb.root, 'dotfiles-codex');
  mkdirSync(dotfilesDir, { recursive: true });
  const realUserConfig = join(dotfilesDir, 'config.toml');
  writeFileSync(realUserConfig, [
    'model = "gpt-5.4"',
    'model_provider = "pdd_codex_gateway"',
    'openai_base_url = "https://api.promptdriven.ai/v1/codex-gateway"',
    '[model_providers.pdd_codex_gateway]',
    'base_url = "https://api.promptdriven.ai/v1/codex-gateway"',
    '[mcp_servers.demo]',
    'command = "echo"',
    '',
  ].join('\n'), { mode: 0o600 });
  symlinkSync(realUserConfig, join(userCodexDir, 'config.toml'));

  mkdirSync(join(userCodexDir, 'packages'), { recursive: true });
  writeFileSync(join(userCodexDir, 'packages', 'pkg.json'), '{"ok":true}\n');
  mkdirSync(join(userCodexDir, 'agents'), { recursive: true });
  writeFileSync(join(userCodexDir, 'agents', 'reviewer.md'), '# Reviewer\n');
  mkdirSync(join(userCodexDir, 'skills'), { recursive: true });
  writeFileSync(join(userCodexDir, 'skills', 's.md'), '# Skill\n');
  writeFileSync(join(userCodexDir, 'herdr.config.toml'), 'port = 7777\n');

  // Pre-seed empty auto-created directories AND a non-empty sessions dir in managedHome
  const managedHome = pddManagedCodexHome(sb.env);
  mkdirSync(join(managedHome, 'packages'), { recursive: true });
  mkdirSync(join(managedHome, 'agents'), { recursive: true });
  mkdirSync(join(managedHome, 'skills'), { recursive: true });
  mkdirSync(join(managedHome, 'sessions'), { recursive: true });
  writeFileSync(join(managedHome, 'sessions', 'keep.jsonl'), '{"keep":true}\n');
  mkdirSync(join(userCodexDir, 'sessions'), { recursive: true });

  const mat = materializeLocalCodexAuth({
    delivery_mode: 'gateway_grant',
    plan_type: 'pro',
    codex_gateway_url: 'https://api.promptdriven.ai/v1/codex-gateway/lse_uni1',
    codex_gateway_token: 'pddg_lse_uni1_tok123',
  }, { env: sb.env }, { spawnSync: () => ({ status: 0 }) });
  assert.equal(mat.managedCodexGateway, true);

  // Empty auto-created dirs were replaced with symlinks, while non-empty sessions dir was preserved!
  for (const dirName of ['packages', 'agents', 'skills']) {
    assert.equal(lstatSync(join(managedHome, dirName)).isSymbolicLink(), true, `empty ${dirName}/ replaced by symlink`);
  }
  assert.equal(lstatSync(join(managedHome, 'sessions')).isSymbolicLink(), false, 'non-empty sessions/ never deleted');
  assert.equal(readFileSync(join(managedHome, 'sessions', 'keep.jsonl'), 'utf8'), '{"keep":true}\n');

  const managedCfg = parseToml(readFileSync(managedCodexConfigPath(sb.env), 'utf8'));
  assert.equal(managedCfg.model_provider, undefined);
  assert.equal(managedCfg.openai_base_url, 'https://api.promptdriven.ai/v1/codex-gateway');
  assert.equal(managedCfg.chatgpt_base_url, 'https://api.promptdriven.ai/v1/codex-gateway');
  assert.equal(managedCfg.features?.responses_websockets, false, 'managed gateway config disables responses_websockets');
  assert.equal(managedCfg.mcp_servers?.demo?.command, 'echo', 'read mcp_servers from dotfile-symlinked user ~/.codex/config.toml');

  // Stale gateway keys in dotfile-symlinked user ~/.codex/config.toml were scrubbed through realpath while preserving symlink!
  assert.equal(lstatSync(join(userCodexDir, 'config.toml')).isSymbolicLink(), true, 'user config.toml symlink preserved');
  const cleanedUserCfg = parseToml(readFileSync(realUserConfig, 'utf8'));
  assert.equal(cleanedUserCfg.model_provider, undefined);
  assert.equal(cleanedUserCfg.openai_base_url, undefined);
  assert.equal(cleanedUserCfg.mcp_servers?.demo?.command, 'echo');

  // 2. Unified createCodexStepOverlay for embedded pddg_lse_ grant writes native openai_base_url + chatgpt_base_url + synthetic 0600 auth.json + dynamic mirror
  const overlay = createCodexStepOverlay({
    delivery_mode: 'gateway_grant',
    plan_type: 'team',
    codex_gateway_url: 'https://api.promptdriven.ai/v1/codex-gateway/lse_step_uni',
    codex_gateway_token: 'pddg_lse_step_uni_grant999',
  }, { env: sb.env, tmpRoot: sb.root });
  try {
    assert.ok(overlay.authPath, 'embedded pddg_lse_ step overlay writes synthetic 0600 auth.json');
    assert.equal(statSync(overlay.authPath).mode & 0o777, 0o600);
    const stepAuth = JSON.parse(readFileSync(overlay.authPath, 'utf8'));
    assert.equal(stepAuth.auth_mode, 'chatgpt');
    assert.equal(stepAuth.OPENAI_API_KEY, null);
    assert.equal(stepAuth.tokens?.access_token, 'pddg_lse_step_uni_grant999');
    assert.equal(stepAuth.tokens?.refresh_token, '');
    assert.equal(stepAuth.tokens?.account_id, 'acct_pdd_gateway');
    assert.equal(stepAuth.tokens?.id_token, buildSyntheticGatewayIdToken({ planType: 'team' }));

    const stepCfg = parseToml(readFileSync(overlay.configPath, 'utf8'));
    assert.equal(stepCfg.model_provider, undefined, 'step overlay uses native openai provider');
    assert.equal(stepCfg.openai_base_url, 'https://api.promptdriven.ai/v1/codex-gateway');
    assert.equal(stepCfg.chatgpt_base_url, 'https://api.promptdriven.ai/v1/codex-gateway');
    assert.equal(stepCfg.features?.responses_websockets, false);
    assert.equal(stepCfg.features?.shell_snapshot, false);
    assert.equal(stepCfg.model_providers?.pdd_codex_gateway?.base_url, 'https://api.promptdriven.ai/v1/codex-gateway');
    assert.equal(lstatSync(join(overlay.overlayDir, 'packages')).isSymbolicLink(), true);
    assert.equal(lstatSync(join(overlay.overlayDir, 'herdr.config.toml')).isSymbolicLink(), true);
  } finally {
    overlay.cleanup();
  }

  // 2b. prepareCloudStepExecution forwards account.plan into createCodexStepOverlay synthetic id_token when lease.plan_type is omitted
  const prepExec = prepareCloudStepExecution({
    account: { provider: 'codex', plan: 'team' },
    lease: {
      delivery_mode: 'gateway_grant',
      codex_gateway_url: 'https://api.promptdriven.ai/v1/codex-gateway/lse_prep_team',
      codex_gateway_token: 'pddg_lse_prep_team_grant888',
    },
  }, sb.env, { tmpRoot: sb.root });
  try {
    const prepAuth = JSON.parse(readFileSync(join(prepExec.overlayDir, 'auth.json'), 'utf8'));
    assert.equal(prepAuth.tokens?.id_token, buildSyntheticGatewayIdToken({ planType: 'team' }));
  } finally {
    prepExec.cleanup();
  }

  // 3. buildClaudeStepEnv strips ANTHROPIC_API_KEY and overrides stale gateway ANTHROPIC_BASE_URL in settings.json on direct_oauth
  materializeLocalClaudeAuth({
    delivery_mode: 'gateway_grant',
    anthropic_base_url: 'https://api.promptdriven.ai/v1/accounts/claude-gateway/lse_cl1',
    gateway_bearer_token: 'pddg_cl_grant_secret_111',
  }, { env: sb.env });

  // Seed legacy gateway settings in ~/.claude/settings.json to verify buildClaudeStepEnv override & restoreLocalClaudeGatewayConfig cleanup
  const claudeSettingsPath = localClaudePaths(sb.env).settingsPath;
  mkdirSync(join(sb.home, '.claude'), { recursive: true });
  writeFileSync(claudeSettingsPath, JSON.stringify({
    model: 'claude-sonnet-4-6',
    env: {
      CUSTOM_FLAG: '1',
      CLAUDE_CODE_OAUTH_TOKEN: 'pddg_cl_grant_secret_111',
      ANTHROPIC_BASE_URL: 'https://api.promptdriven.ai/v1/accounts/claude-gateway/lse_cl1',
    },
  }, null, 2));

  const gwStepEnv = buildClaudeStepEnv(
    { ...sb.env, ANTHROPIC_API_KEY: 'sk-ant-api03-SHOULD_BE_STRIPPED' },
    {
      delivery_mode: 'gateway_grant',
      anthropic_base_url: 'https://api.promptdriven.ai/v1/accounts/claude-gateway/lse_cl2',
      gateway_bearer_token: 'pddg_cl_grant_secret_222',
    },
  );
  assert.equal(Object.hasOwn(gwStepEnv, 'ANTHROPIC_API_KEY'), false, 'gateway_grant strips ambient ANTHROPIC_API_KEY');
  assert.equal(gwStepEnv.CLAUDE_CODE_OAUTH_TOKEN, 'pddg_cl_grant_secret_222');

  const directStepEnv = buildClaudeStepEnv(
    { ...sb.env, ANTHROPIC_API_KEY: 'sk-ant-api03-SHOULD_BE_STRIPPED' },
    {
      delivery_mode: 'direct_oauth',
      claude_oauth_token: 'sk-ant-oat01-direct_secret_333',
    },
  );
  assert.equal(Object.hasOwn(directStepEnv, 'ANTHROPIC_API_KEY'), false, 'direct_oauth strips ambient ANTHROPIC_API_KEY');
  assert.equal(directStepEnv.ANTHROPIC_BASE_URL, 'https://api.anthropic.com', 'direct_oauth overrides managed gateway URL in ~/.claude/settings.json');

  // 4. restoreLocalClaudeGatewayConfig strips pddg_* token and gateway ANTHROPIC_BASE_URL while preserving custom settings
  const restored = restoreLocalClaudeGatewayConfig({ env: sb.env });
  assert.equal(restored.restoredSettings, true);
  assert.equal(restored.removedManagedSettings, true);
  assert.equal(existsSync(managedClaudeSettingsPath(sb.env)), false);
  const afterRestore = JSON.parse(readFileSync(claudeSettingsPath, 'utf8'));
  assert.equal(afterRestore.model, 'claude-sonnet-4-6');
  assert.equal(afterRestore.env?.CUSTOM_FLAG, '1');
  assert.equal(afterRestore.env?.CLAUDE_CODE_OAUTH_TOKEN, undefined);
  assert.equal(afterRestore.env?.ANTHROPIC_BASE_URL, undefined);

  // Non-pddg user OAuth token is never stripped by restoreLocalClaudeGatewayConfig
  writeFileSync(claudeSettingsPath, JSON.stringify({
    env: { CLAUDE_CODE_OAUTH_TOKEN: 'sk-ant-oat01-user_owned', ANTHROPIC_BASE_URL: 'https://custom-proxy.internal' },
  }, null, 2));
  assert.equal(restoreLocalClaudeGatewayConfig({ env: sb.env }).restoredSettings, false);
  const untouched = JSON.parse(readFileSync(claudeSettingsPath, 'utf8'));
  assert.equal(untouched.env.CLAUDE_CODE_OAUTH_TOKEN, 'sk-ant-oat01-user_owned');
  assert.equal(untouched.env.ANTHROPIC_BASE_URL, 'https://custom-proxy.internal');
});

test('#3426 borrower revocation: gateway_grant_revoked and borrowed generic 401 rotate without tainting reauth_required', async t => {
  const {
    exhaustCloudPoolLogin,
    isAuthFailureMessage,
    isExplicitReauthCodeFailure,
    isGatewayGrantRevokedFailure,
    isReauthRequiredFailure,
    readCloudAccountsState,
    writeCloudAccountsState,
  } = await import('../src/login-pool.mjs');

  // 1. Classifiers separate borrower share/grant revocations from upstream owner reauth_required,
  //    ignore test-assertion diagnostics, and never let grant-revoked text mask explicit upstream reauth codes.
  const revokedMsg = 'HTTP 403 {"error":{"code":"gateway_grant_revoked","message":"Shared account authorization epoch changed"}}';
  const revokedWith401 = 'HTTP 401 gateway_grant_revoked: Gateway grant was revoked';
  const noisyExplicitReauth = 'note: gateway_grant_revoked seen in source, real error: oauth_not_allowed_for_organization';
  const testAssertionNoise = 'AssertionError: expected "gateway_grant_revoked" in test/cloud-accounts.test.mjs to fail';
  assert.equal(isGatewayGrantRevokedFailure(revokedMsg), true);
  assert.equal(isGatewayGrantRevokedFailure(revokedWith401), true);
  assert.equal(isGatewayGrantRevokedFailure(testAssertionNoise), false, 'test diagnostics must never trigger revocation retries');
  assert.equal(isReauthRequiredFailure(revokedMsg), false, 'revoked borrower grant must never classify as reauth_required');
  assert.equal(isReauthRequiredFailure(revokedWith401), false, 'revoked borrower grant with 401 must never classify as reauth_required');
  assert.equal(isReauthRequiredFailure(noisyExplicitReauth), true, 'explicit upstream reauth code must never be masked by gateway_grant_revoked text');
  assert.equal(isAuthFailureMessage(revokedMsg), true, 'revoked borrower grant must still rotate cleanly with 0 issue strikes');
  assert.equal(isExplicitReauthCodeFailure('HTTP 401 Unauthorized'), false);
  assert.equal(isExplicitReauthCodeFailure('403 oauth_not_allowed_for_organization'), true);

  // 2. runStepAgentProcess rotates past borrowed gateway_grant_revoked and borrowed generic 401 without marking reauth_required.
  const sb = makeTempSandbox(t, 'https://cloud.example.com');
  writeCloudAccountsState({
    enrolled: true,
    providers: ['codex'],
    active: { codex: { account_id: 'acc_shared_1', label: 'shared-1', provider: 'codex', is_owner: false, state: 'ready' } },
  }, { env: sb.env });
  assert.equal(readCloudAccountsState({ env: sb.env }).active?.codex?.is_owner, false, 'is_owner must persist in accounts-state.json');
  const leaseCalls = [];
  const usageReports = [];
  const mockFetch = async (url, init) => {
    const u = String(url);
    const body = init?.body ? JSON.parse(init.body) : {};
    if (u.endsWith('/v1/accounts/lease')) {
      leaseCalls.push(body);
      const skip = new Set(body.skip_account_ids ?? []);
      if (!skip.has('acc_shared_1')) {
        return {
          ok: true,
          status: 200,
          text: async () => JSON.stringify({
            state: 'leased',
            account: { account_id: 'acc_shared_1', label: 'shared-1', provider: 'codex', is_owner: false, state: 'ready' },
            lease: {
              lease_id: 'lse_shared_1',
              delivery_mode: 'gateway_grant',
              codex_gateway_url: 'https://cloud.example.com/v1/codex-gateway/lse_shared_1',
              codex_gateway_token: 'pddg_lse_shared_1_tok',
            },
          }),
        };
      }
      if (!skip.has('acc_shared_2')) {
        return {
          ok: true,
          status: 200,
          text: async () => JSON.stringify({
            state: 'leased',
            account: { account_id: 'acc_shared_2', label: 'shared-2', provider: 'codex', is_owner: false, state: 'ready' },
            lease: {
              lease_id: 'lse_shared_2',
              delivery_mode: 'gateway_grant',
              codex_gateway_url: 'https://cloud.example.com/v1/codex-gateway/lse_shared_2',
              codex_gateway_token: 'pddg_lse_shared_2_tok',
            },
          }),
        };
      }
      return {
        ok: true,
        status: 200,
        text: async () => JSON.stringify({
          state: 'leased',
          account: { account_id: 'acc_backup_3', label: 'backup-3', provider: 'codex', is_owner: true, state: 'ready' },
          lease: {
            lease_id: 'lse_backup_3',
            delivery_mode: 'gateway_grant',
            codex_gateway_url: 'https://cloud.example.com/v1/codex-gateway/lse_backup_3',
            codex_gateway_token: 'pddg_lse_backup_3_tok',
          },
        }),
      };
    }
    if (u.includes('/usage-report')) {
      usageReports.push(body);
      return { ok: true, status: 200, text: async () => JSON.stringify({ ok: true }) };
    }
    return { ok: false, status: 404, text: async () => '{}' };
  };

  let runIdx = 0;
  const stepRes = await runStepAgentProcess({
    agent: 'codex',
    step: 'build',
    args: ['exec', '-'],
    cwd: sb.root,
    env: { ...sb.env, PDD_TOKEN: 'ghp_test_tok' },
    run: async () => {
      runIdx++;
      if (runIdx === 1) return { code: 1, stdout: '', stderr: revokedMsg };
      if (runIdx === 2) return { code: 1, stdout: '', stderr: 'HTTP 401 Unauthorized' };
      return { code: 0, stdout: 'DONE', stderr: '' };
    },
    accountsPorts: { fetch: mockFetch },
  });
  assert.equal(stepRes.code, 0);
  assert.equal(stepRes.stdout, 'DONE');
  assert.equal(runIdx, 3);
  assert.equal(usageReports.length, 0, 'revoked grants must not report fake quota exhaustion');
  const stateAfterStep = readCloudAccountsState({ env: sb.env });
  assert.equal(stateAfterStep.reauth?.acc_shared_1, undefined, 'gateway_grant_revoked must not mark account reauth_required');
  assert.equal(stateAfterStep.reauth?.acc_shared_2, undefined, 'borrowed generic 401 must not mark account reauth_required');

  // 3. exhaustCloudPoolLogin rotates past gateway_grant_revoked AND persisted borrowed generic 401 (accountWindows: null)
  //    without poisoning reauth or posting usage-report.
  writeCloudAccountsState({
    enrolled: true,
    providers: ['codex'],
    active: { codex: { account_id: 'acc_shared_1', label: 'shared-1', provider: 'codex', is_owner: false, state: 'ready' } },
  }, { env: sb.env });
  const exRes = await exhaustCloudPoolLogin({
    cwd: sb.root,
    env: { ...sb.env, PDD_TOKEN: 'ghp_test_tok' },
    loginId: 'acc_shared_1',
    accountWindows: null,
    reason: 'HTTP 401 Unauthorized',
    allowedKinds: ['codex'],
  }, { fetch: mockFetch });
  assert.equal(exRes.state, 'ready');
  assert.equal(exRes.login.id, 'acc_shared_2');
  assert.equal(usageReports.length, 0);
  assert.equal(readCloudAccountsState({ env: sb.env }).reauth?.acc_shared_1, undefined, 'persisted is_owner: false must prevent generic 401 from poisoning reauth');

  // 4. Real quota exhaustion in stderr must still report usage even if stdout mentions gateway_grant_revoked.
  let quotaRunIdx = 0;
  const quotaRes = await runStepAgentProcess({
    agent: 'codex',
    step: 'build',
    args: ['exec', '-'],
    cwd: sb.root,
    env: { ...sb.env, PDD_TOKEN: 'ghp_test_tok' },
    run: async () => {
      quotaRunIdx++;
      if (quotaRunIdx === 1) {
        return { code: 1, stdout: 'inspecting gateway_grant_revoked handler', stderr: 'You have hit your usage limit for today.' };
      }
      return { code: 0, stdout: 'QUOTA_OK', stderr: '' };
    },
    accountsPorts: { fetch: mockFetch },
  });
  assert.equal(quotaRes.code, 0);
  assert.equal(quotaRes.stdout, 'QUOTA_OK');
  assert.equal(usageReports.length, 1, 'quota exhaustion must still report usage when stdout mentions gateway_grant_revoked');
});

test('SEC-1, SEC-3, SEC-4, SEC-8 & REL-2: shared subshell excludes, no empty-subshell or /tmp root, unconditional codex env scrub, conditional grant env, and Claude symlink guard', t => {
  const sb = makeTempSandbox(t, 'https://api.promptdriven.ai');
  mkdirSync(join(sb.home, '.codex'), { recursive: true, mode: 0o700 });
  writeFileSync(join(sb.home, '.codex', 'config.toml'), [
    '[shell_environment_policy]',
    'filters = { pdd_token = "include", codex_home = "include", USER_VAR = "exclude" }',
    'set = { codex_home = "/evil/home", KEEP_ME = "1" }',
    '',
  ].join('\n'), { mode: 0o600 });

  // 1. SEC-1 & REL-2: createCodexStepOverlay defaults under resolvePddStateBase(env)/codex-runtime (never /tmp),
  //    enforces all REQUIRED_CODEX_SUBSHELL_EXCLUDES in filters, and does NOT create empty-subshell or set.CODEX_HOME.
  const embeddedLease = {
    delivery_mode: 'gateway_grant',
    codex_gateway_url: 'https://api.promptdriven.ai/v1/codex-gateway/lse_sec1',
    codex_backend_api_url: 'https://api.promptdriven.ai/v1/codex-gateway/backend-api',
    codex_gateway_token: 'pddg_lse_sec1_secret_token',
  };
  const envNoTmpRoot = { ...sb.env };
  delete envNoTmpRoot.PDD_CODEX_RUNTIME_ROOT;
  const ov = createCodexStepOverlay(embeddedLease, { env: envNoTmpRoot });
  try {
    const expectedRoot = join(resolvePddStateBase(envNoTmpRoot), 'codex-runtime');
    assert.ok(ov.overlayDir.startsWith(`${expectedRoot}/`), `overlay must live under ${expectedRoot}, got ${ov.overlayDir}`);
    assert.equal(existsSync(join(ov.overlayDir, 'empty-subshell')), false, 'must not create empty-subshell directory');
    const cfg = parseToml(readFileSync(ov.configPath, 'utf8'));
    assert.equal(cfg.shell_environment_policy?.set?.CODEX_HOME, undefined);
    assert.equal(cfg.shell_environment_policy?.set?.codex_home, undefined);
    assert.equal(cfg.shell_environment_policy?.set?.KEEP_ME, '1');
    for (const key of REQUIRED_CODEX_SUBSHELL_EXCLUDES) {
      assert.equal(cfg.shell_environment_policy?.filters?.[key], 'exclude', `missing required exclude ${key}`);
    }
    assert.equal(cfg.shell_environment_policy?.filters?.pdd_token, undefined);
    assert.equal(cfg.shell_environment_policy?.filters?.codex_home, undefined);
    assert.equal(cfg.shell_environment_policy?.filters?.USER_VAR, 'exclude');
  } finally {
    ov.cleanup();
  }

  // 2. SEC-3 & SEC-4: prepareCloudStepExecution unconditionally scrubs ambient Codex auth/base vars even on direct_stripped,
  //    omits PDD_CODEX_GATEWAY_GRANT for pddg_lse_* grants, and injects it only for legacy non-pddg_lse_* grants.
  const pollutedEnv = {
    ...envNoTmpRoot,
    OPENAI_API_KEY: 'sk-ambient-leak',
    CODEX_API_KEY: 'ck-ambient-leak',
    CODEX_ACCESS_TOKEN: 'at-ambient-leak',
    CODEX_CONNECTORS_TOKEN: 'ct-ambient-leak',
    OPENAI_BASE_URL: 'https://evil-proxy.example.com/v1',
    PDD_CODEX_GATEWAY_GRANT: 'pddg_stale_ambient',
  };

  const embeddedStep = prepareCloudStepExecution(
    { account: { provider: 'codex', plan_type: 'pro' }, lease: embeddedLease },
    pollutedEnv,
  );
  try {
    assert.equal(embeddedStep.env.OPENAI_API_KEY, undefined);
    assert.equal(embeddedStep.env.CODEX_API_KEY, undefined);
    assert.equal(embeddedStep.env.CODEX_ACCESS_TOKEN, undefined);
    assert.equal(embeddedStep.env.CODEX_CONNECTORS_TOKEN, undefined);
    assert.equal(embeddedStep.env.OPENAI_BASE_URL, undefined);
    assert.equal(embeddedStep.env.PDD_CODEX_GATEWAY_GRANT, undefined, 'pddg_lse_* grant must not be exported into child env');
  } finally {
    embeddedStep.cleanup?.();
  }

  const legacyStep = prepareCloudStepExecution(
    {
      account: { provider: 'codex' },
      lease: {
        delivery_mode: 'gateway_grant',
        codex_gateway_url: 'https://api.promptdriven.ai/v1/codex-gateway/lse_legacy',
        codex_gateway_token: 'pddg_legacyNonEmbeddedToken123',
      },
    },
    pollutedEnv,
  );
  try {
    assert.equal(legacyStep.env.OPENAI_API_KEY, undefined);
    assert.equal(legacyStep.env.CODEX_CONNECTORS_TOKEN, undefined);
    assert.equal(legacyStep.env.PDD_CODEX_GATEWAY_GRANT, 'pddg_legacyNonEmbeddedToken123', 'legacy non-pddg_lse_* grant keeps env header');
  } finally {
    legacyStep.cleanup?.();
  }

  const directStep = prepareCloudStepExecution(
    {
      account: { provider: 'codex' },
      lease: {
        delivery_mode: 'direct_stripped',
        codex_auth_json: {
          auth_mode: 'chatgpt',
          tokens: { access_token: 'tok-direct', id_token: makeJwt({ email: 'a@b.c' }), account_id: 'acct_1', refresh_token: 'must-strip' },
        },
      },
    },
    pollutedEnv,
  );
  try {
    assert.equal(directStep.env.OPENAI_API_KEY, undefined, 'SEC-3: direct_stripped must still scrub ambient OPENAI_API_KEY');
    assert.equal(directStep.env.CODEX_API_KEY, undefined, 'SEC-3: direct_stripped must still scrub ambient CODEX_API_KEY');
    assert.equal(directStep.env.CODEX_ACCESS_TOKEN, undefined, 'SEC-3: direct_stripped must still scrub ambient CODEX_ACCESS_TOKEN');
    assert.equal(directStep.env.CODEX_CONNECTORS_TOKEN, undefined, 'SEC-3: direct_stripped must still scrub ambient CODEX_CONNECTORS_TOKEN');
    assert.equal(directStep.env.OPENAI_BASE_URL, undefined, 'SEC-3: direct_stripped must still scrub ambient OPENAI_BASE_URL');
    assert.equal(directStep.env.PDD_CODEX_GATEWAY_GRANT, undefined);
  } finally {
    directStep.cleanup?.();
  }

  // 3. SEC-8: restoreLocalClaudeGatewayConfig refuses a ~/.claude/settings.json symlink pointing inside pddManagedClaudeHome(env),
  //    while allowing a valid dotfile symlink pointing to an external regular file.
  const managedClaudeDir = pddManagedClaudeHome(sb.env);
  mkdirSync(managedClaudeDir, { recursive: true, mode: 0o700 });
  const trapInsideManaged = join(managedClaudeDir, 'trap-settings.json');
  writeFileSync(trapInsideManaged, JSON.stringify({ env: { CLAUDE_CODE_OAUTH_TOKEN: 'pddg_should_not_touch' } }), { mode: 0o600 });
  mkdirSync(join(sb.home, '.claude'), { recursive: true, mode: 0o700 });
  const claudeSettings = join(sb.home, '.claude', 'settings.json');
  symlinkSync(trapInsideManaged, claudeSettings);

  assert.throws(
    () => restoreLocalClaudeGatewayConfig({ env: sb.env, removeManagedFile: false }),
    err => err instanceof CloudAccountsError && err.code === 'symlink_refused',
    'SEC-8: symlink targeting pddManagedClaudeHome must be refused',
  );
  assert.equal(JSON.parse(readFileSync(trapInsideManaged, 'utf8')).env.CLAUDE_CODE_OAUTH_TOKEN, 'pddg_should_not_touch');

  rmSync(claudeSettings);
  const externalDotfile = join(sb.root, 'dotfiles-claude-settings.json');
  writeFileSync(externalDotfile, JSON.stringify({ theme: 'dark', env: { CLAUDE_CODE_OAUTH_TOKEN: 'pddg_legacy_cleanme' } }), { mode: 0o600 });
  symlinkSync(externalDotfile, claudeSettings);

  const okRestore = restoreLocalClaudeGatewayConfig({ env: sb.env, removeManagedFile: false });
  assert.equal(okRestore.restoredSettings, true, 'valid external dotfile symlink is cleaned safely');
  assert.equal(lstatSync(claudeSettings).isSymbolicLink(), true, 'dotfile symlink itself is preserved');
  assert.deepEqual(JSON.parse(readFileSync(externalDotfile, 'utf8')), { theme: 'dark' });
});
