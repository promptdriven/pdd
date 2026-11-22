import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import { EventEmitter } from 'node:events';
import http from 'node:http';
import { PassThrough } from 'node:stream';
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
  utimesSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { detectImportProvider, refreshInstalledAutoSwitchBlocks, renderAutoSwitchBlock } from '../src/accounts-cli.mjs';
import { readCodexUsageWindows } from '../src/codex-limits.mjs';
import {
  accountsStatePath,
  buildSyntheticGatewayIdToken,
  CloudAccountsError,
  createCodexStepOverlay,
  managedClaudeSettingsPath,
  managedCodexAuthPath,
  managedCodexConfigPath,
  pddManagedCodexHome,
  prepareCloudStepExecution,
  readCloudAccountsState,
  resolvePddStateBase,
} from '../src/login-pool.mjs';
import { parse as parseToml } from '../src/shared/toml/parse.js';

function makeJwt(payload) {
  const header = Buffer.from(JSON.stringify({ alg: 'none', typ: 'JWT' })).toString('base64url');
  const body = Buffer.from(JSON.stringify(payload)).toString('base64url');
  return `${header}.${body}.sig`;
}

function sink(isTTY = false) {
  return {
    isTTY,
    columns: 120,
    rows: 36,
    text: '',
    write(chunk) {
      this.text += String(chunk);
      return true;
    },
  };
}

function makeSandbox(t, serverUrl, bearerToken = 'ghu_testCloudBearer999999') {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-acct-ux-sec-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const home = join(root, 'home');
  const stateDir = join(root, 'state');
  const configHome = join(root, 'config');
  mkdirSync(home, { recursive: true });
  mkdirSync(stateDir, { recursive: true });
  mkdirSync(configHome, { recursive: true });
  const env = {
    HOME: home,
    PDD_STATE_DIR: stateDir,
    XDG_CONFIG_HOME: configHome,
    PDD_CLOUD_URL: serverUrl,
    GH_TOKEN: bearerToken,
    PATH: process.env.PATH,
  };
  return { root, home, stateDir, configHome, env };
}

async function invokeCli(argv, sb, accountsPorts = {}, topOpts = {}) {
  const stdout = topOpts.stdout ?? sink(Boolean(topOpts.isTTY));
  const stderr = topOpts.stderr ?? sink(Boolean(topOpts.isTTY));
  const stdin = topOpts.stdin ?? '';
  const exit = await runPdd(argv, {
    cwd: sb.root,
    env: sb.env,
    stdin,
    stdout,
    stderr,
    pathDiagnostic: () => [],
    accountsPorts: {
      stdout,
      stderr,
      ...accountsPorts,
    },
  });
  return { exit, stdout: stdout.text, stderr: stderr.text };
}

async function createPoolGatewayServer(t, opts = {}) {
  const state = {
    bearerToken: 'ghu_testCloudBearer999999',
    nowMs: opts.nowMs ?? Date.now(),
    accounts: structuredClone(opts.accounts ?? []),
    pendingInvites: structuredClone(opts.pendingInvites ?? []),
    requests: [],
    nextSeq: 100,
    enforceUniqueLabel: opts.enforceUniqueLabel !== false,
    embeddedLeaseTokens: opts.embeddedLeaseTokens !== false,
    ownerGatewayGrant: opts.ownerGatewayGrant !== false,
    unpopulatedWindowsOnCreate: Boolean(opts.unpopulatedWindowsOnCreate),
    failNextPostAccountsStatus: 0,
    failPostAccountsAfterDeleteStatus: 0,
    leaseOverrideState: null,
  };

  let serverUrl = '';
  const server = http.createServer(async (req, res) => {
    const chunks = [];
    for await (const chunk of req) chunks.push(chunk);
    const rawBody = Buffer.concat(chunks).toString('utf8');
    let body = null;
    try { body = rawBody ? JSON.parse(rawBody) : null; } catch {}

    const url = new URL(req.url, 'http://127.0.0.1');
    state.requests.push({ method: req.method, path: url.pathname, query: url.search, body });

    const send = (status, payload) => {
      res.writeHead(status, { 'content-type': 'application/json' });
      res.end(JSON.stringify(payload));
    };

    if (req.headers.authorization !== `Bearer ${state.bearerToken}`) {
      return send(401, { detail: { error: 'unauthorized', message: 'Unauthorized' } });
    }

    if (req.method === 'GET' && url.pathname === '/v1/accounts') {
      return send(200, {
        accounts: state.accounts.filter(a => !a.revoked),
        pending_invites: state.pendingInvites,
      });
    }

    if (req.method === 'POST' && url.pathname === '/v1/accounts') {
      if (state.failNextPostAccountsStatus > 0) {
        const statusToFail = state.failNextPostAccountsStatus;
        state.failNextPostAccountsStatus = 0;
        return send(statusToFail, { detail: { error: 'service_unavailable', message: 'Upstream cold start timeout' } });
      }
      const subjectKey = body?.provider === 'codex'
        ? `codex:${body?.bundle?.auth_json?.tokens?.account_id}`
        : `claude:${body?.bundle?.oauth_token}`;

      const bySubject = state.accounts.find(a => !a.revoked && a.provider === body.provider && a._subjectKey && a._subjectKey === subjectKey);
      if (bySubject) {
        bySubject._bundle = structuredClone(body.bundle);
        return send(200, { account: bySubject, already_enrolled: true });
      }

      if (state.enforceUniqueLabel) {
        const dupLabel = state.accounts.find(
          a => !a.revoked && a.is_owner !== false && a.provider === body.provider && a.label.toLowerCase() === String(body.label ?? '').toLowerCase(),
        );
        if (dupLabel) {
          return send(409, {
            detail: {
              error: 'duplicate_label',
              message: `Account label "${body.label}" already exists for ${body.provider}.`,
            },
          });
        }
      }

      const id = `acc_${state.nextSeq++}`;
      const acc = {
        account_id: id,
        label: body.label,
        provider: body.provider,
        plan: body.plan ?? (body.provider === 'claude' ? 'max' : 'pro'),
        is_owner: true,
        shared: false,
        state: 'ready',
        five_hour_used_percent: state.unpopulatedWindowsOnCreate ? null : 5,
        five_hour_reset_at: state.unpopulatedWindowsOnCreate ? null : '2026-11-18T01:00:00Z',
        weekly_used_percent: state.unpopulatedWindowsOnCreate ? null : 12,
        weekly_reset_at: state.unpopulatedWindowsOnCreate ? null : '2026-11-22T00:00:00Z',
        shares: [],
        org_shares: [],
        team_shares: [],
        _subjectKey: subjectKey,
        _bundle: structuredClone(body.bundle),
      };
      state.accounts.push(acc);
      return send(200, { account: acc, already_enrolled: false });
    }

    if (req.method === 'POST' && url.pathname === '/v1/accounts/lease') {
      if (state.leaseOverrideState === 'all_cooling') {
        return send(200, { state: 'all_cooling', wake_at: '2026-11-18T03:00:00Z', lease: null });
      }
      if (state.leaseOverrideState === 'error_500') {
        return send(500, { detail: 'Temporary lease outage' });
      }
      if (state.leaseOverrideState === 'reauth_no_id') {
        return send(401, { detail: { error: 'reauth_required', message: 'refresh_token_reused' } });
      }
      const provider = body?.provider ?? 'codex';
      const skip = new Set(Array.isArray(body?.skip_account_ids) ? body.skip_account_ids : []);
      const candidates = state.accounts.filter(
        a => !a.revoked
          && a.provider === provider
          && a.state === 'ready'
          && (a.five_hour_used_percent ?? 0) < 100
          && (a.weekly_used_percent ?? 0) < 100
          && !skip.has(a.account_id),
      );
      let chosen = null;
      if (body?.preferred_label) {
        chosen = candidates.find(a => a.label === body.preferred_label) ?? null;
      }
      if (!chosen && body?.current_account_id) {
        chosen = candidates.find(a => a.account_id === body.current_account_id) ?? null;
      }
      if (!chosen) {
        chosen = candidates[0] ?? null;
      }
      if (!chosen) {
        const wakeAt = state.accounts
          .filter(a => !a.revoked && a.provider === provider && a.cooling_until)
          .map(a => a.cooling_until)
          .sort()[0] ?? '2026-11-18T04:00:00Z';
        return send(200, { state: 'all_cooling', wake_at: wakeAt, lease: null });
      }

      const seq = state.nextSeq++;
      const leaseHex = seq.toString(16).padStart(8, '0');
      const leaseId = `lse_${leaseHex}`;
      const expiresAt = new Date(state.nowMs + 50 * 60 * 1000).toISOString();

      if (provider === 'codex' && (state.ownerGatewayGrant || chosen.is_owner === false)) {
        const grantToken = state.embeddedLeaseTokens
          ? `pddg_lse_${leaseHex}_secretGrant${seq}`
          : `pddg_legacy_${chosen.label.replace(/[^A-Za-z0-9_-]/g, '_')}_${seq}`;
        return send(200, {
          state: 'leased',
          switched: chosen.account_id !== body?.current_account_id,
          account: chosen,
          lease: {
            lease_id: leaseId,
            expires_at: expiresAt,
            delivery_mode: 'gateway_grant',
            codex_gateway_url: `${serverUrl}/v1/codex-gateway/${leaseId}`,
            codex_gateway_token: grantToken,
            gateway_bearer_token: grantToken,
          },
        });
      }

      if (provider === 'claude' && chosen.is_owner === false) {
        const clGrant = `pddg_cl_shared_${seq}`;
        return send(200, {
          state: 'leased',
          switched: chosen.account_id !== body?.current_account_id,
          account: chosen,
          lease: {
            lease_id: leaseId,
            expires_at: expiresAt,
            delivery_mode: 'gateway_grant',
            gateway_bearer_token: clGrant,
            anthropic_base_url: `${serverUrl}/v1/accounts/claude-gateway/${leaseId}`,
          },
        });
      }

      if (provider === 'claude') {
        return send(200, {
          state: 'leased',
          switched: chosen.account_id !== body?.current_account_id,
          account: chosen,
          lease: {
            lease_id: leaseId,
            expires_at: expiresAt,
            delivery_mode: 'direct_oauth',
            claude_oauth_token: chosen._bundle?.oauth_token ?? `sk-ant-oat01-${chosen.label}-leasedToken123456`,
          },
        });
      }

      return send(200, {
        state: 'leased',
        switched: true,
        account: chosen,
        lease: {
          lease_id: leaseId,
          expires_at: expiresAt,
          delivery_mode: 'direct_stripped',
          codex_auth_json: {
            auth_mode: 'chatgpt',
            OPENAI_API_KEY: null,
            tokens: {
              access_token: `at_leased_${chosen.account_id}`,
              refresh_token: '',
              id_token: makeJwt({ email: `${chosen.label}@promptdriven.ai` }),
              account_id: `org_${chosen.account_id}`,
            },
          },
        },
      });
    }

    const usageMatch = /^\/v1\/accounts\/([^/]+)\/usage-report$/.exec(url.pathname);
    if (req.method === 'POST' && usageMatch) {
      const id = decodeURIComponent(usageMatch[1]);
      const acc = state.accounts.find(a => a.account_id === id);
      if (!acc) return send(404, { detail: 'Not found' });
      if (typeof body?.five_hour_used_percent === 'number') acc.five_hour_used_percent = body.five_hour_used_percent;
      if (body?.five_hour_reset_at) acc.five_hour_reset_at = body.five_hour_reset_at;
      if (typeof body?.weekly_used_percent === 'number') acc.weekly_used_percent = body.weekly_used_percent;
      if (body?.weekly_reset_at) acc.weekly_reset_at = body.weekly_reset_at;
      if (body?.limit_reached) {
        acc.state = 'cooling';
        acc.cooling_until = acc.five_hour_reset_at ?? acc.weekly_reset_at ?? '2026-11-18T04:00:00Z';
      }
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
        return send(200, { account: acc });
      }
      if (req.method === 'POST' && action === 'unpause') {
        acc.state = 'ready';
        return send(200, { account: acc });
      }
      if (req.method === 'POST' && action === 'share') {
        const invId = `inv_${state.nextSeq++}`;
        if (body?.github_login || Number.isSafeInteger(body?.github_user_id)) {
          acc.shares = acc.shares ?? [];
          acc.shares.push({
            github_login: body.github_login ?? null,
            github_user_id: body.github_user_id ?? null,
            state: 'pending',
          });
        } else if (body?.team && body?.org) {
          acc.team_shares = acc.team_shares ?? [];
          acc.team_shares.push(`${body.org}/${body.team}`);
        } else if (body?.org) {
          acc.org_shares = acc.org_shares ?? [];
          acc.org_shares.push(body.org);
        }
        return send(200, { account: acc, invite: { invite_id: invId, account_id: id, shared: body } });
      }
      if (req.method === 'POST' && action === 'unshare') {
        return send(200, { revoked: true });
      }
      if (req.method === 'POST' && action === 'leave') {
        acc.revoked = true;
        return send(200, { left: true });
      }
      if (req.method === 'GET' && action === 'log') {
        return send(200, { entries: [{ created_at: '2026-11-17T20:00:00Z', event: 'enrolled', actor_login: 'Serhan-Asad', detail: acc.provider }] });
      }
    }

    const acceptMatch = /^\/v1\/accounts\/invites\/([^/]+)\/accept$/.exec(url.pathname);
    if (req.method === 'POST' && acceptMatch) {
      const invId = decodeURIComponent(acceptMatch[1]);
      const invIdx = state.pendingInvites.findIndex(i => i.invite_id === invId);
      if (invIdx === -1) return send(404, { detail: 'Invite not found' });
      const inv = state.pendingInvites.splice(invIdx, 1)[0];
      const acc = state.accounts.find(a => a.account_id === inv.account_id) ?? inv.account;
      if (acc && !state.accounts.some(a => a.account_id === acc.account_id)) {
        state.accounts.push(acc);
      }
      return send(200, { accepted: true, account: acc, provider: acc?.provider ?? inv.provider ?? 'codex' });
    }

    const delMatch = /^\/v1\/accounts\/([^/]+)$/.exec(url.pathname);
    if (req.method === 'DELETE' && delMatch) {
      const id = decodeURIComponent(delMatch[1]);
      const acc = state.accounts.find(a => a.account_id === id);
      if (!acc) return send(404, { detail: 'Not found' });
      acc.revoked = true;
      if (state.failPostAccountsAfterDeleteStatus > 0) {
        state.failNextPostAccountsStatus = state.failPostAccountsAfterDeleteStatus;
        state.failPostAccountsAfterDeleteStatus = 0;
      }
      return send(200, { deleted: true });
    }

    return send(404, { detail: `Unhandled ${req.method} ${url.pathname}` });
  });

  await new Promise(r => server.listen(0, '127.0.0.1', r));
  t.after(() => {
    server.closeAllConnections?.();
    server.close();
  });
  const addr = server.address();
  serverUrl = `http://127.0.0.1:${addr.port}`;
  return { serverUrl, state };
}

test('#3495: interactive claude setup-token streams prompt with open TTY stdin, unwraps 80-col ANSI-wrapped ~108-char tokens, isolates CLAUDE_CONFIG_DIR, and fails fast on non-TTY', async t => {
  const cloud = await createPoolGatewayServer(t);
  const sb = makeSandbox(t, cloud.serverUrl);

  // Pre-seed ~/.claude/settings.json and ~/.claude/.credentials.json with an OLD personal token
  // to prove `pdd accounts add --provider claude` NEVER silently falls back to ~/.claude on disk!
  const userClaudeDir = join(sb.home, '.claude');
  mkdirSync(userClaudeDir, { recursive: true });
  const staleExistingToken = 'sk-ant-oat01-PREEXISTING_LOCAL_TOKEN_MUST_NEVER_BE_UPLOADED_BY_ADD_999999999999';
  writeFileSync(join(userClaudeDir, 'settings.json'), JSON.stringify({
    env: { CLAUDE_CODE_OAUTH_TOKEN: staleExistingToken },
  }));
  writeFileSync(join(userClaudeDir, '.credentials.json'), JSON.stringify({
    claudeAiOauth: {
      accessToken: staleExistingToken,
      expiresAt: Date.now() + 86_400_000,
    },
  }));
  sb.env.CLAUDE_CODE_OAUTH_TOKEN = staleExistingToken;

  // 1. Non-TTY stdin with no piped token fails immediately with actionable guidance instead of hanging 120s.
  const nonTtyStdin = new PassThrough();
  nonTtyStdin.isTTY = false;
  nonTtyStdin.end('');
  const t0 = Date.now();
  const nonTtyRes = await invokeCli(['accounts', 'add', '--provider', 'claude', '--label', 'glt-non-tty'], sb, {
    stdin: nonTtyStdin,
  }, { stdin: nonTtyStdin });
  const elapsedMs = Date.now() - t0;
  assert.equal(nonTtyRes.exit, 1);
  assert.ok(elapsedMs < 3000, `expected fast failure, took ${elapsedMs}ms`);
  assert.match(nonTtyRes.stderr, /interactive terminal|import --provider claude/i);
  assert.equal(cloud.state.requests.filter(r => r.method === 'POST' && r.path === '/v1/accounts').length, 0);

  // 2. Interactive TTY session keeps stdin open until user pastes OAuth code, streams prompt live,
  //    runs inside isolated 0700 CLAUDE_CONFIG_DIR with COLUMNS=500, and unwraps soft-wrapped + ANSI-colored 108-char token!
  const full108CharToken = `sk-ant-oat01-${'A1b2C3d4_E5f6-G7h8'.repeat(5)}Zz9988`;
  assert.ok(full108CharToken.length >= 108);
  const part1 = full108CharToken.slice(0, 68);
  const part2 = full108CharToken.slice(68);
  const inkWrappedAnsiOutput = [
    '\x1b[36mBrowser didn\'t open? Use the url below to sign in (c to copy)\x1b[0m',
    'https://claude.com/cai/oauth/authorize?code=true&redirect_uri=https%3A%2F%2Fplatform.claude.com%2Foauth%2Fcode%2Fcallback',
    '',
    '\x1b[1mPaste code here if prompted > \x1b[0m',
  ].join('\n');

  const ttyStdin = new PassThrough();
  ttyStdin.isTTY = true;
  const ttyStdout = sink(true);
  let sawTempClaudeDir = null;
  let sawColumns = null;
  let sawAmbientTokenInChild = 'not-checked';
  let childStdinClosedPrematurely = false;

  const interactiveRes = await invokeCli(['accounts', 'add', '--provider', 'claude', '--label', 'glt'], sb, {
    tmpRoot: sb.root,
    stdin: ttyStdin,
    stdout: ttyStdout,
    spawnInteractive(cmd, args, opts) {
      assert.equal(cmd, 'claude');
      assert.deepEqual(args, ['setup-token']);
      sawTempClaudeDir = opts.env.CLAUDE_CONFIG_DIR;
      sawColumns = opts.env.COLUMNS;
      sawAmbientTokenInChild = opts.env.CLAUDE_CODE_OAUTH_TOKEN;
      assert.notEqual(sawTempClaudeDir, userClaudeDir);
      assert.equal(statSync(sawTempClaudeDir).mode & 0o777, 0o700);

      const proc = new EventEmitter();
      proc.stdin = new PassThrough();
      proc.stdout = new PassThrough();
      proc.stderr = new PassThrough();
      proc.kill = () => {};

      proc.stdin.on('end', () => {
        if (!pastedCode) childStdinClosedPrematurely = true;
      });

      let pastedCode = false;
      setImmediate(() => {
        proc.stdout.write(inkWrappedAnsiOutput);
        // Verify prompt was streamed live BEFORE child exits, then simulate user pasting auth code!
        assert.match(ttyStdout.text, /Paste code here if prompted >/);
        assert.equal(childStdinClosedPrematurely, false, 'stdin must stay open for user paste-in');
        ttyStdin.write('oauth_auth_code_from_browser_12345\n');
      });

      proc.stdin.on('data', chunk => {
        if (String(chunk).includes('oauth_auth_code_from_browser_12345')) {
          pastedCode = true;
          // Emit soft-wrapped 80-col Ink output with ANSI sequences splitting the 108-char token across two lines!
          proc.stdout.write(`\n\x1b[32mYour OAuth token:\x1b[0m\n  \x1b[1m${part1}\x1b[0m\n  \x1b[1m${part2}\x1b[0m\n\nStore this token safely.\n`);
          proc.emit('close', 0, null);
        }
      });

      return proc;
    },
  }, { stdin: ttyStdin, stdout: ttyStdout, isTTY: true });

  assert.equal(interactiveRes.exit, 0, interactiveRes.stderr);
  assert.equal(sawColumns, '500');
  assert.equal(sawAmbientTokenInChild, undefined, 'ambient CLAUDE_CODE_OAUTH_TOKEN stripped from isolated setup-token child');
  assert.equal(existsSync(sawTempClaudeDir), false, 'isolated temp CLAUDE_CONFIG_DIR wiped after enrollment');
  const uploadedClaude = cloud.state.accounts.find(a => a.provider === 'claude' && a.label === 'glt');
  assert.ok(uploadedClaude);
  assert.equal(uploadedClaude._bundle.oauth_token, full108CharToken, 'unwrapped full 108-char token without 80-col truncation');

  // 3. Strict isolation check: if `claude setup-token` exits 0 without printing a token, `add` fails
  //    cleanly and NEVER uploads `staleExistingToken` from ~/.claude/settings.json or .credentials.json!
  const ttyStdinEmpty = new PassThrough();
  ttyStdinEmpty.isTTY = true;
  const noTokenRes = await invokeCli(['accounts', 'add', '--provider', 'claude', '--label', 'glt-empty'], sb, {
    tmpRoot: sb.root,
    stdin: ttyStdinEmpty,
    stdout: sink(true),
    spawnInteractive() {
      const proc = new EventEmitter();
      proc.stdin = new PassThrough();
      proc.stdout = new PassThrough();
      proc.stderr = new PassThrough();
      proc.kill = () => {};
      setImmediate(() => {
        proc.stdout.write('Setup cancelled before token generation.\n');
        proc.emit('close', 0, null);
      });
      return proc;
    },
  }, { stdin: ttyStdinEmpty, isTTY: true });

  assert.equal(noTokenRes.exit, 1);
  assert.match(noTokenRes.stderr, /No Claude OAuth token found/i);
  assert.equal(
    cloud.state.accounts.some(a => a._bundle?.oauth_token === staleExistingToken),
    false,
    'must never fall back to pre-existing ~/.claude token on add',
  );
  delete sb.env.CLAUDE_CODE_OAUTH_TOKEN;
});

test('#3494: --loop email-derived labels, --replace & interactive 409 recovery, --provider disambiguation, duplicate-share skip, and upload retry', async t => {
  const cloud = await createPoolGatewayServer(t);
  const sb = makeSandbox(t, cloud.serverUrl);

  const writeCodexBundle = (dir, { accountId, email, refresh }) => {
    const idPayload = email
      ? { email, 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }
      : { 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } };
    writeFileSync(join(dir, 'auth.json'), JSON.stringify({
      auth_mode: 'chatgpt',
      OPENAI_API_KEY: null,
      tokens: {
        access_token: `at_${accountId}_secret`,
        refresh_token: refresh,
        id_token: makeJwt(idPayload),
        account_id: accountId,
      },
    }));
  };

  // 1. `--loop` WITHOUT `--label` derives labels from authenticated email (`glt`, `glt-oai2`, collision `glt-2`, no-email fallback `codex-1`),
  //    prints iteration banners + `<email> -> "<label>"` confirmation, and recovers from transient 503 upload failure via `[R]etry` WITHOUT repeating `codex login`!
  const batchSpecs = [
    { accountId: 'acct_glt_1', email: 'glt@promptdriven.ai', refresh: 'rt_glt_1_sec' },
    { accountId: 'acct_glt_oai2', email: 'glt+oai2@promptdriven.ai', refresh: 'rt_glt_oai2_sec', failUploadOnce: 503 },
    { accountId: 'acct_glt_seat2', email: 'glt@secondary.org', refresh: 'rt_glt_seat2_sec' },
    { accountId: 'acct_no_email', email: null, refresh: 'rt_no_email_sec' },
  ];
  let loginCalls = 0;
  let specIdx = 0;
  const loopAnswers = ['y', 'R', 'y', 'y', 'n'];

  const loopRes = await invokeCli(
    ['accounts', 'add', '--provider', 'codex', '--loop', '--with', 'serhan-asad,@promptdriven'],
    sb,
    {
      tmpRoot: sb.root,
      resolveGithubUser: async login => ({ id: 4201, login, type: 'User' }),
      prompt: async () => loopAnswers.shift(),
      run: async (cmd, _args, opts) => {
        assert.equal(cmd, 'codex');
        loginCalls += 1;
        const spec = batchSpecs[specIdx++];
        if (spec.failUploadOnce) {
          cloud.state.failNextPostAccountsStatus = spec.failUploadOnce;
        }
        writeCodexBundle(opts.env.CODEX_HOME, spec);
        return { code: 0, stdout: 'Logged in\n', stderr: '' };
      },
    },
  );

  assert.equal(loopRes.exit, 0, loopRes.stderr);
  assert.equal(loginCalls, 4, 'transient 503 upload failure retried POST /v1/accounts without re-running codex login');
  assert.match(loopRes.stdout, /--- Account #1 \(codex, auto-label from account, 0 enrolled so far\) ---/);
  assert.match(loopRes.stdout, /glt@promptdriven\.ai -> "glt"/);
  assert.match(loopRes.stdout, /glt\+oai2@promptdriven\.ai -> "glt-oai2"/);
  assert.match(loopRes.stdout, /glt@secondary\.org -> "glt-2"/);
  assert.match(loopRes.stdout, /Enrolled Codex account "codex-1"/);
  assert.deepEqual(
    cloud.state.accounts.filter(a => !a.revoked && a.provider === 'codex').map(a => a.label),
    ['glt', 'glt-oai2', 'glt-2', 'codex-1'],
  );

  // 2. Skip duplicate share invites when `--with` targets already have active/pending shares!
  const shareReqsBeforeDup = cloud.state.requests.filter(r => r.method === 'POST' && r.path.endsWith('/share')).length;
  const dupSingleShare = await invokeCli(
    ['accounts', 'share', 'glt', '--with', 'serhan-asad'],
    sb,
    { resolveGithubUser: async login => ({ id: 4201, login, type: 'User' }) },
  );
  assert.equal(dupSingleShare.exit, 0, dupSingleShare.stderr);
  assert.match(dupSingleShare.stdout, /already shared/i);
  assert.equal(
    cloud.state.requests.filter(r => r.method === 'POST' && r.path.endsWith('/share')).length,
    shareReqsBeforeDup,
    'skipped duplicate invite creation for already-shared user',
  );

  // Mixed `--with` (`serhan-asad` already shared + `agarwal-ishaan` new) creates invite ONLY for `agarwal-ishaan`!
  const mixedShare = await invokeCli(
    ['accounts', 'share', 'glt', '--with', 'serhan-asad,agarwal-ishaan'],
    sb,
    { resolveGithubUser: async login => ({ id: login === 'serhan-asad' ? 4201 : 4202, login, type: 'User' }) },
  );
  assert.equal(mixedShare.exit, 0, mixedShare.stderr);
  const newShareCalls = cloud.state.requests.slice(-2).filter(r => r.method === 'POST' && r.path.endsWith('/share'));
  assert.equal(newShareCalls.length, 1);
  assert.equal(newShareCalls[0].body.github_login, 'agarwal-ishaan');

  // 3. `--replace` on `import` (and `add`) replaces an existing owned `(codex, glt)` label without 409 failure and preserves shares!
  const replacementFile = join(sb.root, 'replacement-glt.json');
  writeFileSync(replacementFile, JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'at_replaced_glt_secret',
      refresh_token: 'rt_replaced_glt_secret',
      id_token: makeJwt({ email: 'glt-new@promptdriven.ai', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
      account_id: 'acct_glt_replaced_999',
    },
  }));
  const replaceRes = await invokeCli(
    ['accounts', 'import', '--provider', 'codex', '--from', replacementFile, '--label', 'glt', '--replace'],
    sb,
    { resolveGithubUser: async login => ({ id: 4299, login, type: 'User' }) },
  );
  assert.equal(replaceRes.exit, 0, replaceRes.stderr);
  const activeGltCodex = cloud.state.accounts.filter(a => !a.revoked && a.provider === 'codex' && a.label === 'glt');
  assert.equal(activeGltCodex.length, 1, 'old glt replaced cleanly with single active glt row');
  assert.equal(activeGltCodex[0]._subjectKey, 'codex:acct_glt_replaced_999');
  assert.ok(activeGltCodex[0].shares.some(s => s.github_login === 'agarwal-ishaan'), 'preserved prior shares across --replace');

  // Interactive `409` prompt without `--replace`: choosing `2` disambiguates to `glt-3` (`glt` and `glt-2` exist) without redoing login!
  let conflictLoginRuns = 0;
  const interactive409 = await invokeCli(
    ['accounts', 'add', '--provider', 'codex', '--label', 'glt'],
    sb,
    {
      tmpRoot: sb.root,
      prompt: async q => {
        assert.match(q, /already exists for codex.*glt-3/i);
        return '2';
      },
      run: async (_cmd, _args, opts) => {
        conflictLoginRuns += 1;
        writeCodexBundle(opts.env.CODEX_HOME, {
          accountId: 'acct_interactive_409',
          email: 'glt3@promptdriven.ai',
          refresh: 'rt_interactive_409',
        });
        return { code: 0, stdout: 'Logged in\n', stderr: '' };
      },
    },
  );
  assert.equal(interactive409.exit, 0, interactive409.stderr);
  assert.equal(conflictLoginRuns, 1);
  assert.match(interactive409.stdout, /Enrolled Codex account "glt-3"/);

  // 4. Cross-provider `--provider codex|claude` disambiguation on `use`, `pause`, `unpause`, `log`, `share`, `unshare`, and `remove`!
  const claudeTokenFile = join(sb.root, 'claude-glt-token.txt');
  writeFileSync(claudeTokenFile, 'sk-ant-oat01-claudeGltSharedLabelToken_1234567890abcdef\n');
  const addClaudeGlt = await invokeCli(
    ['accounts', 'import', '--provider', 'claude', '--from', claudeTokenFile, '--label', 'glt'],
    sb,
  );
  assert.equal(addClaudeGlt.exit, 0, addClaudeGlt.stderr);

  for (const ambiguousArgv of [
    ['accounts', 'use', 'glt'],
    ['accounts', 'pause', 'glt'],
    ['accounts', 'unpause', 'glt'],
    ['accounts', 'log', 'glt'],
    ['accounts', 'share', 'glt', '--with', '@promptdriven'],
    ['accounts', 'unshare', 'glt', '--user', 'serhan-asad'],
    ['accounts', 'remove', 'glt'],
  ]) {
    const amb = await invokeCli(ambiguousArgv, sb);
    assert.equal(amb.exit, 2, `expected exit 2 for ambiguous ${ambiguousArgv.join(' ')}`);
    assert.match(amb.stderr, /multiple providers.*--provider codex.*--provider claude/i);
  }

  // Scoped commands succeed and touch ONLY the requested provider!
  assert.equal((await invokeCli(['accounts', 'pause', 'glt', '--provider', 'claude'], sb)).exit, 0);
  assert.equal(cloud.state.accounts.find(a => !a.revoked && a.provider === 'claude' && a.label === 'glt').state, 'paused');
  assert.equal(cloud.state.accounts.find(a => !a.revoked && a.provider === 'codex' && a.label === 'glt').state, 'ready');

  assert.equal((await invokeCli(['accounts', 'unpause', 'glt', '--provider', 'claude'], sb)).exit, 0);
  assert.equal((await invokeCli(['accounts', 'use', 'glt', '--provider', 'codex'], sb)).exit, 0);
  assert.equal((await invokeCli(['accounts', 'log', 'glt', '--provider', 'claude'], sb)).exit, 0);
  assert.equal((await invokeCli(['accounts', 'share', 'glt', '--provider', 'claude', '--with', '@promptdriven'], sb)).exit, 0);
  assert.equal((await invokeCli(['accounts', 'unshare', 'glt', '--provider', 'claude', '--with', '@promptdriven'], sb)).exit, 0);
  assert.equal((await invokeCli(['accounts', 'remove', 'glt', '--provider', 'claude'], sb)).exit, 0);

  assert.equal(
    cloud.state.accounts.some(a => !a.revoked && a.provider === 'claude' && a.label === 'glt'),
    false,
    'removed Claude "glt"',
  );
  assert.equal(
    cloud.state.accounts.some(a => !a.revoked && a.provider === 'codex' && a.label === 'glt'),
    true,
    'preserved Codex "glt"',
  );
});

test('#3497 Part 1: owner + shared gateway_grant zero-plaintext local Codex keys, constant /v1/codex-gateway URL across switches, and legacy grant compat', async t => {
  const cloud = await createPoolGatewayServer(t, {
    embeddedLeaseTokens: true,
    ownerGatewayGrant: true,
  });
  const sb = makeSandbox(t, cloud.serverUrl);

  // Enroll two owner Codex accounts (`glt` and `glt-oai2`) via `add` and verify:
  // - temp plaintext OAuth login directory is wiped immediately
  // - ZERO OpenAI access/refresh/id tokens exist anywhere on disk
  // - `config.toml` writes constant `<origin>/v1/codex-gateway` + `requires_openai_auth = true` (no `http_headers`)
  const seenTempLoginDirs = [];
  for (const [idx, email] of ['glt@promptdriven.ai', 'glt+oai2@promptdriven.ai'].entries()) {
    const res = await invokeCli(['accounts', 'add', '--provider', 'codex'], sb, {
      tmpRoot: sb.root,
      run: async (_cmd, _args, opts) => {
        seenTempLoginDirs.push(opts.env.CODEX_HOME);
        writeFileSync(join(opts.env.CODEX_HOME, 'auth.json'), JSON.stringify({
          auth_mode: 'chatgpt',
          OPENAI_API_KEY: null,
          tokens: {
            access_token: `raw_openai_access_${idx}_NEVER_ON_DISK`,
            refresh_token: `raw_openai_refresh_${idx}_NEVER_ON_DISK`,
            id_token: makeJwt({ email, 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
            account_id: `acct_zero_plain_${idx}`,
          },
        }));
        return { code: 0, stdout: 'Logged in\n', stderr: '' };
      },
    });
    assert.equal(res.exit, 0, res.stderr);
  }

  for (const dir of seenTempLoginDirs) {
    assert.equal(existsSync(dir), false, 'temporary plaintext login directory deleted immediately');
  }
  assert.equal(existsSync(join(sb.home, '.codex', 'auth.json')), false, '~/.codex/auth.json untouched');

  const authPath = managedCodexAuthPath(sb.env);
  const configPath = managedCodexConfigPath(sb.env);
  assert.equal(statSync(authPath).mode & 0o777, 0o600);
  assert.equal(statSync(configPath).mode & 0o777, 0o600);

  // Pin `glt`, inspect `auth.json` + `config.toml`, then switch to `glt-oai2` via `next` and verify `config.toml` NEVER changes!
  assert.equal((await invokeCli(['accounts', 'use', 'glt'], sb)).exit, 0);
  const auth1Raw = readFileSync(authPath, 'utf8');
  const auth1 = JSON.parse(auth1Raw);
  assert.equal(auth1.auth_mode, 'chatgpt');
  assert.equal(auth1.OPENAI_API_KEY, null);
  assert.match(auth1.tokens?.access_token ?? '', /^pddg_lse_[0-9a-f]+_/);
  assert.equal(auth1.tokens?.refresh_token, '');
  assert.equal(auth1.tokens?.account_id, 'acct_pdd_gateway');
  assert.equal(auth1.tokens?.id_token, buildSyntheticGatewayIdToken({ planType: 'pro' }));
  assert.doesNotMatch(auth1Raw, /raw_access_|raw_refresh_|@promptdriven\.ai/, 'zero raw OAuth tokens in auth.json');

  const configTextBeforeSwitch = readFileSync(configPath, 'utf8');
  const configInodeBeforeSwitch = statSync(configPath).ino;
  const parsedCfg = parseToml(configTextBeforeSwitch);
  assert.equal(parsedCfg.model_provider, undefined, 'native openai provider kept at top level');
  assert.equal(parsedCfg.openai_base_url, `${cloud.serverUrl}/v1/codex-gateway`);
  assert.equal(parsedCfg.chatgpt_base_url, `${cloud.serverUrl}/v1/codex-gateway`);
  assert.equal(parsedCfg.model_providers.pdd_codex_gateway.base_url, `${cloud.serverUrl}/v1/codex-gateway`);
  assert.equal(parsedCfg.model_providers.pdd_codex_gateway.model_catalog_url, `${cloud.serverUrl}/v1/codex-gateway/models`);
  assert.equal(parsedCfg.model_providers.pdd_codex_gateway.requires_openai_auth, true);
  assert.equal(parsedCfg.model_providers.pdd_codex_gateway.http_headers, undefined);

  // Also verify step overlay (`createCodexStepOverlay` / `prepareCloudStepExecution`) writes `model_catalog_url`!
  const stepExec = prepareCloudStepExecution({
    account: { account_id: 'acc_step_1', label: 'glt', provider: 'codex' },
    lease: {
      lease_id: 'lse_00aabbcc',
      delivery_mode: 'gateway_grant',
      codex_gateway_url: `${cloud.serverUrl}/v1/codex-gateway/lse_00aabbcc`,
      codex_gateway_token: 'pddg_lse_00aabbcc_stepSecret123',
    },
  }, sb.env, { tmpRoot: sb.root });
  try {
    const stepCfg = parseToml(readFileSync(join(stepExec.overlayDir, 'config.toml'), 'utf8'));
    assert.equal(stepCfg.model_providers.pdd_codex_gateway.base_url, `${cloud.serverUrl}/v1/codex-gateway`);
    assert.equal(stepCfg.model_providers.pdd_codex_gateway.model_catalog_url, `${cloud.serverUrl}/v1/codex-gateway/models`);
  } finally {
    stepExec.cleanup();
  }

  const legacyOverlay = createCodexStepOverlay({
    delivery_mode: 'gateway_grant',
    codex_gateway_url: `${cloud.serverUrl}/v1/codex-gateway/lse_legacy99`,
    codex_gateway_token: 'pddg_legacy_stepToken99',
  }, {
    env: sb.env,
    tmpRoot: sb.root,
  });
  try {
    const legacyStepCfg = parseToml(readFileSync(join(legacyOverlay.overlayDir, 'config.toml'), 'utf8'));
    assert.equal(legacyStepCfg.model_providers.pdd_codex_gateway.base_url, `${cloud.serverUrl}/v1/codex-gateway/lse_legacy99`);
    assert.equal(legacyStepCfg.model_providers.pdd_codex_gateway.model_catalog_url, `${cloud.serverUrl}/v1/codex-gateway/lse_legacy99/models`);
  } finally {
    legacyOverlay.cleanup();
  }

  const nextRes = await invokeCli(['accounts', 'next', '--provider', 'codex'], sb);
  assert.equal(nextRes.exit, 0, nextRes.stderr);
  const auth2 = JSON.parse(readFileSync(authPath, 'utf8'));
  assert.equal(auth2.auth_mode, 'chatgpt');
  assert.equal(auth2.OPENAI_API_KEY, null);
  assert.notEqual(auth2.tokens?.access_token, auth1.tokens?.access_token, 'auth.json rotated to new lease grant token');
  assert.match(auth2.tokens?.access_token ?? '', /^pddg_lse_[0-9a-f]+_/);
  assert.equal(readFileSync(configPath, 'utf8'), configTextBeforeSwitch, 'config.toml bytes remain 100% constant across switches');
  assert.equal(statSync(configPath).ino, configInodeBeforeSwitch, 'config.toml was not rewritten when unchanged');

  // Verify zero-plaintext fallback AND `null` (never `0` / `100% left`) quota state when post-enroll `/v1/accounts/lease` fails!
  const sbCooling = makeSandbox(t, cloud.serverUrl);
  cloud.state.leaseOverrideState = 'error_500';
  cloud.state.unpopulatedWindowsOnCreate = true;
  const coolingEnroll = await invokeCli(['accounts', 'add', '--provider', 'codex', '--label', 'glt-offline-lease'], sbCooling, {
    tmpRoot: sbCooling.root,
    readCodexUsageWindows: async () => null,
    run: async (_cmd, _args, opts) => {
      writeFileSync(join(opts.env.CODEX_HOME, 'auth.json'), JSON.stringify({
        auth_mode: 'chatgpt',
        OPENAI_API_KEY: null,
        tokens: {
          access_token: 'raw_fallback_access_MUST_NOT_WRITE',
          refresh_token: 'raw_fallback_refresh_MUST_NOT_WRITE',
          id_token: makeJwt({ email: 'fallback@promptdriven.ai', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
          account_id: 'acct_fallback_guard',
        },
      }));
      return { code: 0, stdout: 'Logged in\n', stderr: '' };
    },
  });
  cloud.state.leaseOverrideState = null;
  cloud.state.unpopulatedWindowsOnCreate = false;
  assert.equal(coolingEnroll.exit, 0, coolingEnroll.stderr);
  assert.equal(existsSync(managedCodexAuthPath(sbCooling.env)), false, 'must never fall back to writing raw OAuth auth.json when lease fails');
  const coolingSavedState = readCloudAccountsState({ env: sbCooling.env });
  assert.equal(coolingSavedState.active.codex.five_hour_used_percent, null, 'unprobed 5h window stays null, never 0');
  assert.equal(coolingSavedState.active.codex.weekly_used_percent, null, 'unprobed 7d window stays null, never 0');
  const sbCoolingOffline = { ...sbCooling, env: { ...sbCooling.env, PDD_CLOUD_URL: 'http://127.0.0.1:1' } };
  const offlineStatus = await invokeCli(['accounts', 'status'], sbCoolingOffline);
  assert.equal(offlineStatus.exit, 0);
  assert.match(offlineStatus.stdout, /5h: -, 7d: -/, 'offline status displays "-" rather than misleading 100% left');

  // Backward compatibility: legacy server returning non-`pddg_lse_` token keeps lease-scoped URL + `http_headers` + `model_catalog_url`!
  cloud.state.embeddedLeaseTokens = false;
  const legacyUse = await invokeCli(['accounts', 'use', 'glt'], sb);
  assert.equal(legacyUse.exit, 0, legacyUse.stderr);
  const legacyCfg = parseToml(readFileSync(configPath, 'utf8'));
  assert.equal(legacyCfg.model_provider, undefined);
  assert.match(legacyCfg.openai_base_url ?? '', /\/v1\/codex-gateway\/lse_[0-9a-f]+$/);
  assert.equal(legacyCfg.chatgpt_base_url, legacyCfg.openai_base_url);
  assert.match(legacyCfg.model_providers.pdd_codex_gateway.base_url, /\/v1\/codex-gateway\/lse_[0-9a-f]+$/);
  assert.match(legacyCfg.model_providers.pdd_codex_gateway.model_catalog_url, /\/v1\/codex-gateway\/lse_[0-9a-f]+\/models$/);
  assert.equal(legacyCfg.model_providers.pdd_codex_gateway.requires_openai_auth, false);
  assert.match(legacyCfg.model_providers.pdd_codex_gateway.http_headers['x-pdd-gateway-grant'], /^pddg_legacy_/);
});

test('#3497 Part 2: pdd accounts codex & shell auto wrapper perform structured live mid-session quota rotation without PTY stdout false positives', async t => {
  // 1. Shell wrapper blocks (`sh` and `fish`) delegate `codex` to `pdd-codex` with fail-open by default
  //    and preserve `pdd accounts codex --` behind the `PDD_LEGACY_PTY_ROTATE=1` opt-in switch!
  const shWrapper = renderAutoSwitchBlock('sh');
  const fishWrapper = renderAutoSwitchBlock('fish');
  assert.match(shWrapper, /PDD_CODEX_AUTO_FAIL_OPEN=1 command pdd-codex "\$@"/);
  assert.match(fishWrapper, /PDD_CODEX_AUTO_FAIL_OPEN=1 command pdd-codex \$argv/);
  assert.match(shWrapper, /PDD_LEGACY_PTY_ROTATE/);
  assert.match(fishWrapper, /PDD_LEGACY_PTY_ROTATE/);
  assert.match(shWrapper, /pdd accounts codex -- "\$@"/);
  assert.match(fishWrapper, /pdd accounts codex -- \$argv/);

  // 2. Live mid-session quota exhaustion from structured rollout JSONL rotates `auth.json` to next ready account and relaunches `codex resume <session-id>`!
  const cloud = await createPoolGatewayServer(t, {
    accounts: [
      {
        account_id: 'acc_live_1',
        label: 'glt',
        provider: 'codex',
        plan: 'pro',
        is_owner: true,
        shared: false,
        state: 'ready',
        five_hour_used_percent: 88,
        five_hour_reset_at: '2026-11-18T01:00:00Z',
        weekly_used_percent: 30,
        weekly_reset_at: '2026-11-22T00:00:00Z',
      },
      {
        account_id: 'acc_live_2',
        label: 'glt-oai2',
        provider: 'codex',
        plan: 'pro',
        is_owner: true,
        shared: false,
        state: 'ready',
        five_hour_used_percent: 10,
        five_hour_reset_at: '2026-11-18T02:00:00Z',
        weekly_used_percent: 15,
        weekly_reset_at: '2026-11-23T00:00:00Z',
      },
    ],
  });
  const sb = makeSandbox(t, cloud.serverUrl);
  const useInitial = await invokeCli(['accounts', 'use', 'glt'], sb);
  assert.equal(useInitial.exit, 0);
  assert.match(useInitial.stdout, /Active codex account set to "glt" \(5h: 12% left \(2026-11-18T01:00Z\), 7d: 70% left \(2026-11-22T00:00Z\)\)\./);

  // Verify `pdd accounts list`, `pdd accounts status`, and `--json` surface remaining `XX% left` clearly!
  const listHuman = await invokeCli(['accounts', 'list'], sb);
  assert.equal(listHuman.exit, 0);
  assert.match(listHuman.stdout, /12% left \(2026-11-18T01:00Z\)/);
  assert.match(listHuman.stdout, /70% left \(2026-11-22T00:00Z\)/);
  assert.match(listHuman.stdout, /90% left \(2026-11-18T02:00Z\)/);
  assert.match(listHuman.stdout, /85% left \(2026-11-23T00:00Z\)/);

  const listJson = JSON.parse((await invokeCli(['accounts', 'list', '--json'], sb)).stdout);
  const gltRow = listJson.accounts.find(a => a.label === 'glt');
  assert.equal(gltRow.five_hour_used_percent, 88);
  assert.equal(gltRow.five_hour_left_percent, 12);
  assert.equal(gltRow.weekly_used_percent, 30);
  assert.equal(gltRow.weekly_left_percent, 70);
  assert.equal(listJson.active.codex.five_hour_left_percent, 12);
  assert.equal(listJson.active.codex.weekly_left_percent, 70);

  const statusHuman = await invokeCli(['accounts', 'status'], sb);
  assert.equal(statusHuman.exit, 0);
  assert.match(statusHuman.stdout, /5h: 12% left \(2026-11-18T01:00Z\), 7d: 70% left \(2026-11-22T00:00Z\)/);

  const authPath = managedCodexAuthPath(sb.env);
  const configPath = managedCodexConfigPath(sb.env);
  const configSnapshot = readFileSync(configPath, 'utf8');
  const firstGrant = JSON.parse(readFileSync(authPath, 'utf8')).tokens.access_token;

  // 2a. CRITICAL negative guard: raw PTY stdout/stderr & rollout tool outputs containing quota keywords MUST NEVER kill interactive codex or poison Cloud `/usage-report`!
  const safeSessionUuid = '019a5555-6666-7000-8000-112233445566';
  let safeSignalAborted = false;
  const safeRes = await invokeCli(
    ['accounts', 'codex', '-m', 'gpt-5.4', 'inspect login-pool'],
    sb,
    {
      quotaSettleMs: 0,
      rolloutPollIntervalMs: 15,
      async spawnCodexPty({ env, signal, onOutput }) {
        const nowIso = new Date().toISOString();
        const dayDir = join(env.CODEX_HOME, 'sessions', '2026', '11', '17');
        mkdirSync(dayDir, { recursive: true });
        const rolloutFile = join(dayDir, `rollout-2026-11-17T20-00-00-${safeSessionUuid}.jsonl`);
        writeFileSync(
          rolloutFile,
          [
            JSON.stringify({ timestamp: nowIso, type: 'session_meta', payload: { id: safeSessionUuid, cwd: sb.root, timestamp: nowIso } }),
            JSON.stringify({
              timestamp: nowIso,
              type: 'response_item',
              payload: {
                type: 'function_call_output',
                output: 'src/login-pool.mjs: "You\'ve hit your usage limit (usage_limit_reached) and exceeded your current quota (insufficient_quota)"',
              },
            }),
          ].join('\n') + '\n',
        );
        onOutput('rg "exceeded your current quota"\nError: You\'ve hit your usage limit (usage_limit_reached). insufficient_quota\n');
        await new Promise(r => setTimeout(r, 50));
        safeSignalAborted = signal.aborted;
        return { code: 1, signal: null };
      },
    },
    { isTTY: true },
  );
  assert.equal(safeSignalAborted, false, 'raw PTY stdout quota substrings NEVER abort live interactive codex');
  assert.equal(safeRes.exit, 1, 'propagates codex exit code without false-positive quota rotation');
  assert.equal(
    cloud.state.requests.filter(r => r.method === 'POST' && r.path.endsWith('/usage-report')).length,
    0,
    'zero false-positive /usage-report requests sent to Cloud',
  );

  // 2b. Structured rollout `task_complete` quota error aborts live turn, reports usage, rotates `auth.json`, and resumes pinned UUID without re-triggering on Turn 0's error line!
  const capturedSessionUuid = '019a7777-8888-7000-9000-abcdef123456';
  const seenTurns = [];

  const liveRes = await invokeCli(
    ['accounts', 'codex', '--', '-m', 'gpt-5.4', 'refactor parser'],
    sb,
    {
      quotaSettleMs: 0,
      rolloutPollIntervalMs: 15,
      async spawnCodexPty({ args, env, turn, signal, onOutput }) {
        const activeGrantOnDisk = JSON.parse(readFileSync(join(env.CODEX_HOME, 'auth.json'), 'utf8')).tokens.access_token;
        seenTurns.push({ turn, args, codexHome: env.CODEX_HOME, grant: activeGrantOnDisk });
        const dayDir = join(env.CODEX_HOME, 'sessions', '2026', '11', '17');
        mkdirSync(dayDir, { recursive: true });
        const rolloutFile = join(dayDir, `rollout-2026-11-17T20-05-00-${capturedSessionUuid}.jsonl`);
        if (turn === 0) {
          const nowIso = new Date().toISOString();
          writeFileSync(
            rolloutFile,
            `${JSON.stringify({ timestamp: nowIso, type: 'session_meta', payload: { id: capturedSessionUuid, cwd: sb.root, timestamp: nowIso } })}\n`,
          );
          onOutput('Working on refactor...\n');
          writeFileSync(
            rolloutFile,
            `${JSON.stringify({
              timestamp: new Date().toISOString(),
              type: 'event_msg',
              payload: {
                type: 'task_complete',
                error: {
                  message: 'You\'ve hit your usage limit (usage_limit_reached). Resets at 2026-11-18T01:30:00Z.',
                  codex_error_info: 'usage_limit_exceeded',
                },
              },
            })}\n`,
            { flag: 'a' },
          );
          await new Promise(resolveAbort => {
            if (signal.aborted) return resolveAbort();
            signal.addEventListener('abort', resolveAbort, { once: true });
          });
          assert.equal(signal.aborted, true, 'supervisor aborts turn when structured rollout quota error arrives');
          return { code: 1, signal: 'SIGTERM' };
        }
        // Wait >2 poll cycles on Turn 1 while the same rollout file still has Turn 0's error line prior to `initialRolloutOffset`!
        await new Promise(r => setTimeout(r, 45));
        assert.equal(signal.aborted, false, 'Turn 1 starts at end-of-file offset and does not re-trigger on Turn 0 error');
        onOutput('Resumed conversation seamlessly on rotated account!\nDone.\n');
        return { code: 0, signal: null };
      },
    },
    { isTTY: true },
  );

  assert.equal(liveRes.exit, 0, liveRes.stderr);
  assert.equal(seenTurns.length, 2);
  assert.deepEqual(seenTurns[0].args, ['-m', 'gpt-5.4', 'refactor parser']);
  assert.equal(seenTurns[0].codexHome, pddManagedCodexHome(sb.env));
  assert.equal(seenTurns[0].grant, firstGrant);

  // Turn 1 resumed the exact captured session UUID with preserved `-m gpt-5.4` flag and rotated grant token!
  assert.deepEqual(seenTurns[1].args, ['resume', '-m', 'gpt-5.4', capturedSessionUuid]);
  assert.notEqual(seenTurns[1].grant, firstGrant, 'rotated auth.json to second account grant before resuming');
  assert.equal(readFileSync(configPath, 'utf8'), configSnapshot, 'config.toml stayed constant across live PTY rotation');
  assert.match(
    liveRes.stderr,
    /Quota reached on "glt"; switched active Codex account to "glt-oai2" \(5h: 90% left \(2026-11-18T02:00Z\), 7d: 85% left \(2026-11-23T00:00Z\)\) and resuming/,
  );

  const usageReports = cloud.state.requests.filter(r => r.method === 'POST' && r.path === '/v1/accounts/acc_live_1/usage-report');
  assert.equal(usageReports.length, 1);
  assert.equal(usageReports[0].body.limit_reached, true);
  assert.equal(usageReports[0].body.five_hour_used_percent, 100);
  assert.equal(usageReports[0].body.five_hour_reset_at, '2026-11-18T01:00:00Z');

  // 3. Structured Cloud gateway quota exhaustion (`cloudQuotaPollIntervalMs`) rotates and resumes pinned disk rollout UUID!
  cloud.state.accounts[0].state = 'ready';
  cloud.state.accounts[0].five_hour_used_percent = 5;
  assert.equal((await invokeCli(['accounts', 'use', 'glt'], sb)).exit, 0);

  const rolloutUuid = '019a9999-1111-7222-8333-fedcba654321';
  const rolloutTurns = [];
  const rolloutRes = await invokeCli(['accounts', 'codex'], sb, {
    quotaSettleMs: 0,
    rolloutPollIntervalMs: 15,
    cloudQuotaPollIntervalMs: 15,
    async spawnCodexPty({ args, env, turn, signal }) {
      rolloutTurns.push({ turn, args });
      if (turn === 0) {
        const nowIso = new Date().toISOString();
        const dayDir = join(env.CODEX_HOME, 'sessions', '2026', '11', '17');
        mkdirSync(dayDir, { recursive: true });
        writeFileSync(
          join(dayDir, `rollout-2026-11-17T20-10-00-${rolloutUuid}.jsonl`),
          `${JSON.stringify({ timestamp: nowIso, type: 'session_meta', payload: { id: rolloutUuid, cwd: sb.root, timestamp: nowIso } })}\n`,
        );
        // Cloud gateway marks active account 100% exhausted mid-turn:
        cloud.state.accounts[0].five_hour_used_percent = 100;
        cloud.state.accounts[0].limit_reached = true;
        await new Promise(resolveAbort => {
          if (signal.aborted) return resolveAbort();
          signal.addEventListener('abort', resolveAbort, { once: true });
        });
        return { code: 1, signal: 'SIGTERM' };
      }
      return { code: 0, signal: null };
    },
  }, { isTTY: true });

  assert.equal(rolloutRes.exit, 0, rolloutRes.stderr);
  assert.equal(rolloutTurns.length, 2);
  assert.deepEqual(rolloutTurns[1].args, ['resume', rolloutUuid], 'discovered active session UUID from sessions rollout file and rotated on Cloud exhaustion');

  // 4. Early startup failure `--last` fallback when codex exits non-zero on its own before creating any rollout file!
  rmSync(join(pddManagedCodexHome(sb.env), 'sessions'), { recursive: true, force: true });
  cloud.state.accounts[0].state = 'ready';
  cloud.state.accounts[0].five_hour_used_percent = 5;
  cloud.state.accounts[0].limit_reached = false;
  cloud.state.accounts[1].state = 'ready';
  cloud.state.accounts[1].five_hour_used_percent = 5;
  assert.equal((await invokeCli(['accounts', 'use', 'glt'], sb)).exit, 0);

  const fallbackTurns = [];
  const fallbackRes = await invokeCli(['accounts', 'codex', '--', '-i', 'diagram.png', '--search', 'fix turn zero prompt'], sb, {
    quotaSettleMs: 0,
    async spawnCodexPty({ args, turn, onOutput }) {
      fallbackTurns.push({ turn, args });
      if (turn === 0) {
        onOutput('Error: You\'ve hit your usage limit for this window.\n');
        return { code: 1, signal: 'SIGTERM' };
      }
      return { code: 0, signal: null };
    },
  }, { isTTY: true });

  assert.equal(fallbackRes.exit, 0, fallbackRes.stderr);
  assert.equal(fallbackTurns.length, 2);
  assert.deepEqual(
    fallbackTurns[1].args,
    ['-i', 'diagram.png', '--search', 'fix turn zero prompt'],
    'turn-0 quota exit before rollout creation keeps initial prompt & flags instead of discarding prompt for resume --last',
  );

  // Explicit `resume` without session UUID still falls back to `resume ... --last` preserving `-i`!
  cloud.state.accounts[0].state = 'ready';
  cloud.state.accounts[0].five_hour_used_percent = 5;
  cloud.state.accounts[1].state = 'ready';
  cloud.state.accounts[1].five_hour_used_percent = 5;
  assert.equal((await invokeCli(['accounts', 'use', 'glt'], sb)).exit, 0);
  const resumeFallbackTurns = [];
  const resumeFallbackRes = await invokeCli(['accounts', 'codex', '--', '-i', 'shot.png', '--search', 'resume'], sb, {
    quotaSettleMs: 0,
    async spawnCodexPty({ args, turn, onOutput }) {
      resumeFallbackTurns.push({ turn, args });
      if (turn === 0) {
        onOutput('Error: You\'ve hit your usage limit for this window.\n');
        return { code: 1, signal: 'SIGTERM' };
      }
      return { code: 0, signal: null };
    },
  }, { isTTY: true });
  assert.equal(resumeFallbackRes.exit, 0, resumeFallbackRes.stderr);
  assert.deepEqual(resumeFallbackTurns[1].args, ['resume', '-i', 'shot.png', '--search', '--last']);
});

test('R1 P0 & #3494/#3495/#3497: import refresh_token scrubbing, --replace pre-validation + uid shares + failure backup, multi-terminal rollout pinning, direct flag passthrough, and real Python PTY SIGWINCH/killpg', async t => {
  const cloud = await createPoolGatewayServer(t, {
    accounts: [
      {
        account_id: 'acc_existing_replace',
        label: 'cx-prod',
        provider: 'codex',
        plan: 'pro',
        is_owner: true,
        shared: true,
        state: 'ready',
        five_hour_used_percent: 20,
        five_hour_reset_at: '2026-11-18T01:00:00Z',
        weekly_used_percent: 35,
        weekly_reset_at: '2026-11-22T00:00:00Z',
        shares: [
          { github_user_id: 98765, state: 'active' },
          { github_login: 'octocat', github_user_id: 583231, state: 'active' },
        ],
        org_shares: ['promptdriven'],
        team_shares: [],
      },
    ],
  });
  const sb = makeSandbox(t, cloud.serverUrl);

  // 1. [P0] `pdd accounts import --provider codex` scrubs single-use `tokens.refresh_token` from `~/.codex/auth.json` after Cloud upload (and leaves it intact if upload fails)!
  const userCodexDir = join(sb.home, '.codex');
  mkdirSync(userCodexDir, { recursive: true });
  const homeAuthPath = join(userCodexDir, 'auth.json');
  const rawHomeRefreshToken = 'rt_single_use_family_MUST_BE_SCRUBBED_777777';
  const validImportPayload = {
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'at_home_import_111111',
      refresh_token: rawHomeRefreshToken,
      id_token: makeJwt({ email: 'home@promptdriven.ai', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
      account_id: 'acct_home_import_1',
    },
  };
  writeFileSync(homeAuthPath, JSON.stringify(validImportPayload, null, 2), { mode: 0o600 });

  cloud.state.failNextPostAccountsStatus = 500;
  const failedImport = await invokeCli(['accounts', 'import', '--provider', 'codex', '--label', 'home-cx'], sb);
  assert.equal(failedImport.exit, 1);
  assert.equal(
    JSON.parse(readFileSync(homeAuthPath, 'utf8')).tokens.refresh_token,
    rawHomeRefreshToken,
    'failed upload leaves local refresh_token unscrubbed so user does not lose credentials',
  );

  const okImport = await invokeCli(['accounts', 'import', '--provider', 'codex', '--label', 'home-cx'], sb);
  assert.equal(okImport.exit, 0, okImport.stderr);
  const scrubbedHomeText = readFileSync(homeAuthPath, 'utf8');
  assert.equal(scrubbedHomeText.includes(rawHomeRefreshToken), false, 'raw single-use refresh_token completely removed from ~/.codex/auth.json');
  assert.equal(JSON.parse(scrubbedHomeText).tokens.refresh_token, '');
  assert.equal(statSync(homeAuthPath).mode & 0o777, 0o600);

  // 2. [HIGH] Pre-validate local credentials BEFORE `DELETE` on `--replace`, preserve `uid:<id>` shares, and report backup summary on post-DELETE upload failure!
  const invalidFromPath = join(sb.root, 'invalid-codex-auth.json');
  writeFileSync(invalidFromPath, JSON.stringify({ auth_mode: 'chatgpt', tokens: { access_token: 'only_access', refresh_token: '' } }), { mode: 0o600 });
  const deletesBeforeInvalid = cloud.state.requests.filter(r => r.method === 'DELETE').length;
  const badReplace = await invokeCli(['accounts', 'import', '--provider', 'codex', '--from', invalidFromPath, '--label', 'cx-prod', '--replace'], sb);
  assert.equal(badReplace.exit, 1);
  assert.equal(
    cloud.state.requests.filter(r => r.method === 'DELETE').length,
    deletesBeforeInvalid,
    'invalid/stripped local credential rejected BEFORE sending any DELETE on --replace',
  );

  // Preserve `uid:98765` (`{ github_user_id: 98765 }` without `github_login`) across `--replace`!
  const replaceAuthPath = join(sb.root, 'replace-prod-auth.json');
  writeFileSync(replaceAuthPath, JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'at_replace_prod_222',
      refresh_token: 'rt_replace_prod_secret_222',
      id_token: makeJwt({ email: 'prod@promptdriven.ai', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
      account_id: 'acct_replace_prod_2',
    },
  }), { mode: 0o600 });

  const reqIdxBeforeReplace = cloud.state.requests.length;
  const okReplace = await invokeCli(['accounts', 'import', '--provider', 'codex', '--from', replaceAuthPath, '--label', 'cx-prod', '--replace'], sb);
  assert.equal(okReplace.exit, 0, okReplace.stderr);
  const replaceShareReqs = cloud.state.requests
    .slice(reqIdxBeforeReplace)
    .filter(r => r.method === 'POST' && r.path.endsWith('/share'));
  assert.equal(
    replaceShareReqs.some(r => r.body?.github_user_id === 98765 && !r.body?.github_login),
    true,
    're-shared uid-only share { github_user_id: 98765 } on replaced account',
  );
  assert.equal(replaceShareReqs.some(r => r.body?.github_login === 'octocat'), true);
  assert.equal(replaceShareReqs.some(r => r.body?.org === 'promptdriven'), true);
  assert.equal(JSON.parse(readFileSync(replaceAuthPath, 'utf8')).tokens.refresh_token, '', 'scrubbed after successful --replace');

  // Post-DELETE replacement `POST /v1/accounts` failure includes backup recovery summary AND leaves local credential file unscrubbed!
  const failAfterDeletePath = join(sb.root, 'fail-after-delete-auth.json');
  writeFileSync(failAfterDeletePath, JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'at_fail_after_del_333',
      refresh_token: 'rt_keep_me_for_recovery_333',
      id_token: makeJwt({ email: 'recover@promptdriven.ai', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
      account_id: 'acct_fail_after_del_3',
    },
  }), { mode: 0o600 });
  cloud.state.failPostAccountsAfterDeleteStatus = 502;
  const failedReplaceAfterDel = await invokeCli(
    ['accounts', 'import', '--provider', 'codex', '--from', failAfterDeletePath, '--label', 'cx-prod', '--replace'],
    sb,
  );
  assert.equal(failedReplaceAfterDel.exit, 1);
  assert.match(failedReplaceAfterDel.stderr, /Previous codex account "cx-prod" \(acc_\d+\) was removed before the replacement upload failed/);
  assert.match(failedReplaceAfterDel.stderr, /preserved shares: --with/);
  assert.match(failedReplaceAfterDel.stderr, /was left unscrubbed/);
  assert.equal(
    JSON.parse(readFileSync(failAfterDeletePath, 'utf8')).tokens.refresh_token,
    'rt_keep_me_for_recovery_333',
    'local credential file retained refresh_token when post-DELETE upload failed',
  );

  // Re-enroll a second ready Codex account so rotation tests have 2 healthy Codex accounts (`home-cx` + `cx-backup`).
  const backupAuthPath = join(sb.root, 'backup-codex-auth.json');
  writeFileSync(backupAuthPath, JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'at_backup_444',
      refresh_token: 'rt_backup_444',
      id_token: makeJwt({ email: 'backup@promptdriven.ai', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
      account_id: 'acct_backup_4',
    },
  }), { mode: 0o600 });
  assert.equal((await invokeCli(['accounts', 'import', '--provider', 'codex', '--from', backupAuthPath, '--label', 'cx-backup'], sb)).exit, 0);
  assert.equal((await invokeCli(['accounts', 'use', 'home-cx'], sb)).exit, 0);

  // 3. [HIGH] Multi-terminal rollout race & session pinning (`-C subproj`): ignores pre-existing, wrong-cwd, subagent, and later concurrent rollouts!
  const subprojDir = join(sb.root, 'subproj');
  mkdirSync(subprojDir, { recursive: true });
  const managedHome = pddManagedCodexHome(sb.env);
  const dayDir = join(managedHome, 'sessions', '2026', '11', '17');
  mkdirSync(dayDir, { recursive: true });

  const preExistingUuid = '019a0000-0000-7000-8000-000000000001';
  const wrongCwdUuid = '019a0000-0000-7000-8000-000000000002';
  const subagentUuid = '019a0000-0000-7000-8000-000000000003';
  const myPinnedUuid = '019a0000-0000-7000-8000-000000000004';
  const laterConcurrentUuid = '019a0000-0000-7000-8000-000000000005';

  const preIso = new Date(Date.now() - 60_000).toISOString();
  writeFileSync(
    join(dayDir, `rollout-2026-11-17T19-00-00-${preExistingUuid}.jsonl`),
    `${JSON.stringify({ timestamp: preIso, type: 'session_meta', payload: { id: preExistingUuid, cwd: subprojDir, timestamp: preIso } })}\n`,
  );
  writeFileSync(join(managedHome, 'session_index.jsonl'), `${JSON.stringify({ id: preExistingUuid })}\n`);

  const multiTermTurns = [];
  const multiTermRes = await invokeCli(
    // Direct flag passthrough WITHOUT `--` + full 0.169.0 flag preservation check (including `--color always` dropped on resume)!
    [
      'accounts', 'codex',
      '-C', 'subproj',
      '-m', 'gpt-5.4',
      '--enable', 'fast_apply',
      '--disable', 'telemetry',
      '--local-provider', 'ollama',
      '--remote', 'ws://127.0.0.1:9100',
      '--remote-auth-token-env', 'REMOTE_TOKEN',
      '--oss',
      '--approve-for-me',
      '--dangerously-bypass-hook-trust',
      '--no-daemon',
      '--strict-config',
      '--worktree',
      '--color', 'always',
      'implement feature',
    ],
    sb,
    {
      quotaSettleMs: 0,
      rolloutPollIntervalMs: 15,
      async spawnCodexPty({ args, turn, signal }) {
        multiTermTurns.push({ turn, args });
        if (turn === 0) {
          const t0 = new Date().toISOString();
          const wrongFile = join(dayDir, `rollout-2026-11-17T20-20-01-${wrongCwdUuid}.jsonl`);
          const subFile = join(dayDir, `rollout-2026-11-17T20-20-02-${subagentUuid}.jsonl`);
          const myFile = join(dayDir, `rollout-2026-11-17T20-20-03-${myPinnedUuid}.jsonl`);
          const laterFile = join(dayDir, `rollout-2026-11-17T20-20-04-${laterConcurrentUuid}.jsonl`);

          writeFileSync(wrongFile, `${JSON.stringify({ timestamp: t0, type: 'session_meta', payload: { id: wrongCwdUuid, cwd: sb.root, timestamp: t0 } })}\n`);
          writeFileSync(subFile, `${JSON.stringify({ timestamp: t0, type: 'session_meta', payload: { id: subagentUuid, cwd: subprojDir, timestamp: t0, thread_source: 'subagent' } })}\n`);
          writeFileSync(myFile, `${JSON.stringify({ timestamp: t0, type: 'session_meta', payload: { id: myPinnedUuid, cwd: subprojDir, timestamp: t0 } })}\n`);

          // Let monitor pin `myPinnedUuid`, then spawn a later concurrent session in the same cwd and hit quota in BOTH other terminals!
          await new Promise(r => setTimeout(r, 35));
          const t1 = new Date(Date.now() + 1000).toISOString();
          writeFileSync(laterFile, `${JSON.stringify({ timestamp: t1, type: 'session_meta', payload: { id: laterConcurrentUuid, cwd: subprojDir, timestamp: t1 } })}\n`);
          const otherQuotaErr = `${JSON.stringify({ timestamp: t1, type: 'error', error: { status: 429, code: 'insufficient_quota', message: 'You exceeded your current quota' } })}\n`;
          writeFileSync(wrongFile, otherQuotaErr, { flag: 'a' });
          writeFileSync(laterFile, otherQuotaErr, { flag: 'a' });
          await new Promise(r => setTimeout(r, 35));
          assert.equal(signal.aborted, false, 'quota errors in other terminals NEVER abort this pinned session');

          // Now append structured 429 quota error to THIS pinned session's rollout file!
          writeFileSync(myFile, otherQuotaErr, { flag: 'a' });
          await new Promise(resolveAbort => {
            if (signal.aborted) return resolveAbort();
            signal.addEventListener('abort', resolveAbort, { once: true });
          });
          return { code: 1, signal: 'SIGTERM' };
        }
        return { code: 0, signal: null };
      },
    },
    { isTTY: true },
  );

  assert.equal(multiTermRes.exit, 0, multiTermRes.stderr);
  assert.equal(multiTermTurns.length, 2);
  assert.deepEqual(multiTermTurns[1].args, [
    'resume',
    '-C', 'subproj',
    '-m', 'gpt-5.4',
    '--enable', 'fast_apply',
    '--disable', 'telemetry',
    '--local-provider', 'ollama',
    '--remote', 'ws://127.0.0.1:9100',
    '--remote-auth-token-env', 'REMOTE_TOKEN',
    '--oss',
    '--approve-for-me',
    '--dangerously-bypass-hook-trust',
    '--no-daemon',
    '--strict-config',
    '--worktree',
    myPinnedUuid,
  ], 'pinned exact session UUID and preserved all codex-resume-compatible 0.169.0 flags while dropping --color');

  // 4. [MEDIUM] Passthrough `--` handling: `pdd accounts codex --help` shows local help; `pdd accounts codex -- --help` and `pdd accounts codex -- -- -dash-prompt` strip at most one `--`!
  let spawnedHelp = false;
  const localHelp = await invokeCli(['accounts', 'codex', '--help'], sb, {
    async spawnCodexPty() {
      spawnedHelp = true;
      return { code: 0 };
    },
  });
  assert.equal(localHelp.exit, 0);
  assert.equal(spawnedHelp, false, '`pdd accounts codex --help` prints PDD help without spawning codex');
  assert.match(localHelp.stdout, /pdd accounts codex/);

  let forwardedDoubleDashArgs = null;
  const dashPromptRes = await invokeCli(['accounts', 'codex', '--', '--', '-dash-prompt'], sb, {
    async spawnCodexPty({ args }) {
      forwardedDoubleDashArgs = args;
      return { code: 0 };
    },
  });
  assert.equal(dashPromptRes.exit, 0);
  assert.deepEqual(forwardedDoubleDashArgs, ['--', '-dash-prompt'], 'strips at most one leading `--` so codex receives `-- -dash-prompt`');

  // 5. [MEDIUM] `OUT=$(pdd accounts add --provider claude)` (`stdin.isTTY === true` while `stdout.isTTY === false`) fails fast without spawning `claude`!
  let spawnedClaudeWhenStdoutPiped = false;
  const ttyIn = Object.assign(new PassThrough(), { isTTY: true });
  ttyIn.end();
  const pipedOut = sink(false);
  const ttyErr = sink(true);
  const subshellClaudeAdd = await invokeCli(
    ['accounts', 'add', '--provider', 'claude'],
    sb,
    {
      spawnInteractive() {
        spawnedClaudeWhenStdoutPiped = true;
        throw new Error('must not spawn claude when stdout is non-TTY');
      },
    },
    { stdin: ttyIn, stdout: pipedOut, stderr: ttyErr },
  );
  assert.equal(subshellClaudeAdd.exit, 1);
  assert.equal(spawnedClaudeWhenStdoutPiped, false);
  assert.match(subshellClaudeAdd.stderr, /requires an interactive terminal \(TTY\)/);

  // 6. [HIGH] Real Python PTY supervisor forwards `SIGWINCH` (`TIOCSWINSZ`) via fd 3 control pipe, restores TTY raw mode, and kills child process group (`os.killpg`) on close!
  const fakeBinDir = join(sb.root, 'fake-bin');
  mkdirSync(fakeBinDir, { recursive: true });
  const fakeCodexPath = join(fakeBinDir, 'codex');
  writeFileSync(
    fakeCodexPath,
    [
      '#!/usr/bin/env python3',
      'import fcntl, os, signal, struct, sys, termios, time',
      'bg_pid = os.fork()',
      'if bg_pid == 0:',
      '    time.sleep(30)',
      '    os._exit(0)',
      'def read_winsz():',
      '    r, c, _, _ = struct.unpack("HHHH", fcntl.ioctl(1, termios.TIOCGWINSZ, b"\\x00" * 8))',
      '    return f"{r}x{c}"',
      'def on_winch(_s, _f):',
      '    sys.stdout.write(f"RESIZED={read_winsz()}\\n")',
      '    sys.stdout.flush()',
      'signal.signal(signal.SIGWINCH, on_winch)',
      'sys.stdout.write(f"BG_PID={bg_pid} INIT_SIZE={read_winsz()}\\n")',
      'sys.stdout.flush()',
      'while True:',
      '    time.sleep(0.05)',
    ].join('\n') + '\n',
    { mode: 0o755 },
  );
  chmodSync(fakeCodexPath, 0o755);

  const ptyStdin = Object.assign(new PassThrough(), {
    isTTY: true,
    isRaw: false,
    rawCalls: [],
    setRawMode(flag) {
      this.isRaw = Boolean(flag);
      this.rawCalls.push(Boolean(flag));
    },
  });
  const ptyStdout = Object.assign(new EventEmitter(), {
    isTTY: true,
    rows: 30,
    columns: 100,
    text: '',
    write(chunk) {
      const s = String(chunk);
      this.text += s;
      this.emit('chunk', s);
      return true;
    },
  });

  const sbPty = {
    ...sb,
    env: {
      ...sb.env,
      PATH: `${fakeBinDir}:${sb.env.PATH}`,
    },
  };

  let bgGrandchildPid = 0;
  t.after(() => {
    if (bgGrandchildPid > 0) {
      try { process.kill(bgGrandchildPid, 'SIGKILL'); } catch {}
    }
  });

  const waitForPtyPattern = (re, timeoutMs = 12000) => new Promise((resolveMatch, rejectMatch) => {
    const existing = re.exec(ptyStdout.text);
    if (existing) return resolveMatch(existing);
    const timer = setTimeout(() => {
      ptyStdout.off('chunk', onChunk);
      rejectMatch(new Error(`Timed out waiting for ${re} in PTY output: ${JSON.stringify(ptyStdout.text)}`));
    }, timeoutMs);
    const onChunk = () => {
      const m = re.exec(ptyStdout.text);
      if (m) {
        clearTimeout(timer);
        ptyStdout.off('chunk', onChunk);
        resolveMatch(m);
      }
    };
    ptyStdout.on('chunk', onChunk);
  });

  const ptyRunPromise = invokeCli(['accounts', 'codex'], sbPty, {}, {
    stdin: ptyStdin,
    stdout: ptyStdout,
    stderr: sink(true),
  });

  const initMatch = await waitForPtyPattern(/BG_PID=(\d+)\s+INIT_SIZE=30x100/);
  bgGrandchildPid = Number(initMatch[1]);
  assert.ok(bgGrandchildPid > 0);
  assert.equal(ptyStdin.isRaw, true, 'TTY raw mode enabled while interactive PTY is active');

  ptyStdout.rows = 48;
  ptyStdout.columns = 140;
  ptyStdout.emit('resize');
  await waitForPtyPattern(/RESIZED=48x140/);

  // Closing stdin triggers Python PTY `_terminate_child_group()` (`os.killpg(pid, SIGTERM)`), reaping both `codex` and its `bg_pid` grandchild!
  ptyStdin.end();
  await ptyRunPromise;

  assert.equal(ptyStdin.isRaw, false, 'TTY raw mode restored to initial state on PTY exit');
  assert.deepEqual(ptyStdin.rawCalls, [true, false]);

  let grandchildAlive = true;
  for (let i = 0; i < 25; i += 1) {
    try {
      process.kill(bgGrandchildPid, 0);
      await new Promise(r => setTimeout(r, 20));
    } catch (err) {
      if (err?.code === 'ESRCH') {
        grandchildAlive = false;
        break;
      }
    }
  }
  assert.equal(grandchildAlive, false, 'Python PTY os.killpg terminated entire child process group with zero orphans');
});

test('R2 Blockers 1–5: 32 KiB session_meta + subagent parent_thread_id/source.subagent + 2.5 MiB JSONL line skip, conditional lease-materialized scrub, scrubbed-copy usage probe, and symlinked --from/parent guards', async t => {
  const cloud = await createPoolGatewayServer(t, {
    unpopulatedWindowsOnCreate: true,
    accounts: [
      {
        account_id: 'acc_r2_2',
        label: 'r2-backup',
        provider: 'codex',
        plan: 'pro',
        is_owner: true,
        shared: false,
        state: 'ready',
        five_hour_used_percent: 12,
        five_hour_reset_at: '2026-11-18T02:00:00Z',
        weekly_used_percent: 18,
        weekly_reset_at: '2026-11-23T00:00:00Z',
      },
    ],
  });
  const sb = makeSandbox(t, cloud.serverUrl);

  // Blocker 5: Reject symlinked `--from <dir>` AND symlinked parent `~/.codex` before reading/uploading or scrubbing!
  const realExternalDir = join(sb.root, 'real-ext-codex');
  mkdirSync(realExternalDir, { recursive: true });
  writeFileSync(join(realExternalDir, 'auth.json'), JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'at_sym_dir_111',
      refresh_token: 'rt_sym_dir_111',
      id_token: makeJwt({ email: 'sym@promptdriven.ai', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
      account_id: 'acct_sym_dir_1',
    },
  }), { mode: 0o600 });

  const symlinkFromDir = join(sb.root, 'symlink-from-dir');
  symlinkSync(realExternalDir, symlinkFromDir);
  const reqBeforeSym = cloud.state.requests.length;
  const symFromRes = await invokeCli(['accounts', 'import', '--provider', 'codex', '--from', symlinkFromDir, '--label', 'sym-cx'], sb);
  assert.equal(symFromRes.exit, 1);
  assert.match(symFromRes.stderr, /Refusing to import symlinked Codex credential path/);
  assert.equal(cloud.state.requests.length, reqBeforeSym, 'symlinked --from <dir> rejected before any network call');

  // Symlinked `~/.codex` parent directory is also rejected upfront!
  symlinkSync(realExternalDir, join(sb.home, '.codex'));
  const symHomeRes = await invokeCli(['accounts', 'import', '--provider', 'codex', '--label', 'sym-home'], sb);
  assert.equal(symHomeRes.exit, 1);
  assert.match(symHomeRes.stderr, /Refusing to import Codex credential file from symlinked directory/);
  assert.equal(cloud.state.requests.length, reqBeforeSym, 'symlinked ~/.codex parent directory rejected before any network call');
  rmSync(join(sb.home, '.codex'), { recursive: true, force: true });

  // Blocker 3 & Blocker 4:
  // - `probeInitialCodexUsageIfUnpopulated` ALWAYS passes a disposable 0700 probe CODEX_HOME with `tokens.refresh_token === ""`!
  // - When `/v1/accounts/lease` fails (`500`) or returns `all_cooling`, `pdd accounts import` MUST NOT scrub the source `auth.json`!
  const unleasedSourcePath = join(sb.root, 'unleased-import-auth.json');
  const unleasedRefreshToken = 'rt_must_remain_when_lease_fails_999';
  writeFileSync(unleasedSourcePath, JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'at_unleased_999',
      refresh_token: unleasedRefreshToken,
      id_token: makeJwt({ email: 'unleased@promptdriven.ai', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
      account_id: 'acct_unleased_999',
    },
  }), { mode: 0o600 });

  cloud.state.leaseOverrideState = 'error_500';
  let probeSawEmptyRefresh = false;
  let probeHomeWasIsolated = false;
  const leaseFailedImp = await invokeCli(
    ['accounts', 'import', '--provider', 'codex', '--from', unleasedSourcePath, '--label', 'r2-primary'],
    sb,
    {
      tmpRoot: sb.root,
      readCodexUsageWindows: async ({ env: probeEnv }) => {
        probeHomeWasIsolated = probeEnv.CODEX_HOME !== sb.root && (statSync(probeEnv.CODEX_HOME).mode & 0o777) === 0o700;
        const probeAuth = JSON.parse(readFileSync(join(probeEnv.CODEX_HOME, 'auth.json'), 'utf8'));
        probeSawEmptyRefresh = probeAuth.tokens?.access_token === 'at_unleased_999' && probeAuth.tokens?.refresh_token === '';
        return {
          state: 'ok',
          five_hour_used_percent: 25,
          five_hour_reset_at: '2026-11-18T01:00:00Z',
          weekly_used_percent: 40,
          weekly_reset_at: '2026-11-22T00:00:00Z',
        };
      },
    },
  );
  assert.equal(leaseFailedImp.exit, 0, leaseFailedImp.stderr);
  assert.equal(probeHomeWasIsolated, true, 'usage probe ran in an isolated 0700 temporary directory');
  assert.equal(probeSawEmptyRefresh, true, 'usage probe auth.json had single-use refresh_token scrubbed to ""');
  assert.equal(
    JSON.parse(readFileSync(unleasedSourcePath, 'utf8')).tokens.refresh_token,
    unleasedRefreshToken,
    'source auth.json refresh_token MUST NOT be scrubbed when /v1/accounts/lease fails (500)',
  );
  assert.match(leaseFailedImp.stdout, /lease pending/);
  assert.match(leaseFailedImp.stdout, /left .* unscrubbed/);

  // Also verify `all_cooling` lease state keeps source `auth.json` unscrubbed!
  const coolingSourcePath = join(sb.root, 'cooling-import-auth.json');
  writeFileSync(coolingSourcePath, JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'at_cooling_888',
      refresh_token: 'rt_must_remain_when_cooling_888',
      id_token: makeJwt({ email: 'cooling@promptdriven.ai', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
      account_id: 'acct_cooling_888',
    },
  }), { mode: 0o600 });
  cloud.state.leaseOverrideState = 'all_cooling';
  const coolingImp = await invokeCli(
    ['accounts', 'import', '--provider', 'codex', '--from', coolingSourcePath, '--label', 'r2-cooling'],
    sb,
    { readCodexUsageWindows: async () => null },
  );
  cloud.state.leaseOverrideState = null;
  assert.equal(coolingImp.exit, 0, coolingImp.stderr);
  assert.equal(
    JSON.parse(readFileSync(coolingSourcePath, 'utf8')).tokens.refresh_token,
    'rt_must_remain_when_cooling_888',
    'source auth.json refresh_token MUST NOT be scrubbed when /v1/accounts/lease returns all_cooling',
  );

  // Pin `r2-primary` so managed codex-home is leased and active for Blocker 1 & Blocker 2 live rollout tests!
  assert.equal((await invokeCli(['accounts', 'use', 'r2-primary'], sb)).exit, 0);

  // Blocker 1 & Blocker 2:
  // - Historical rollout file (`mtimeMs` in the past) is skipped before header reads.
  // - Subagent rollouts with `parent_thread_id` OR `source: { subagent: "review" }` are excluded.
  // - Partial unflushed >16 KiB `session_meta` (without `\n`) waits cleanly for `\n` flush, and 32 KiB `base_instructions` `session_meta` is parsed and pinned!
  // - A 2.5 MiB single-line `response_item` JSONL record does NOT wedge `rolloutOffset`; the structured quota error line immediately following it triggers live rotation and resumes the pinned UUID!
  const managedHome = pddManagedCodexHome(sb.env);
  const dayDir = join(managedHome, 'sessions', '2026', '11', '17');
  mkdirSync(dayDir, { recursive: true });

  const historicalUuid = '019b1111-0000-7000-8000-000000000001';
  const subParentUuid = '019b1111-0000-7000-8000-000000000002';
  const subSourceUuid = '019b1111-0000-7000-8000-000000000003';
  const bigMetaSessionUuid = '019b1111-0000-7000-8000-000000000004';

  const histFile = join(dayDir, `rollout-2026-11-17T10-00-00-${historicalUuid}.jsonl`);
  writeFileSync(histFile, '{"type":"session_meta","payload":{"id":"' + historicalUuid + '","cwd":' + JSON.stringify(sb.root) + '}}\n');
  const oldDate = new Date(Date.now() - 3600_000);
  utimesSync(histFile, oldDate, oldDate);

  const r2Turns = [];
  const r2LiveRes = await invokeCli(
    ['accounts', 'codex', '-m', 'gpt-5.4', 'audit large rollout'],
    sb,
    {
      quotaSettleMs: 0,
      rolloutPollIntervalMs: 15,
      async spawnCodexPty({ args, turn, signal }) {
        r2Turns.push({ turn, args });
        if (turn === 0) {
          const nowIso = new Date().toISOString();
          // Subagent 1 (`parent_thread_id`) and Subagent 2 (`source: { subagent: ... }`) in same cwd:
          writeFileSync(
            join(dayDir, `rollout-2026-11-17T23-30-01-${subParentUuid}.jsonl`),
            `${JSON.stringify({
              timestamp: nowIso,
              type: 'session_meta',
              payload: { id: subParentUuid, parent_thread_id: '019b0000-0000-7000-8000-999999999999', cwd: sb.root, timestamp: nowIso },
            })}\n`,
          );
          writeFileSync(
            join(dayDir, `rollout-2026-11-17T23-30-02-${subSourceUuid}.jsonl`),
            `${JSON.stringify({
              timestamp: nowIso,
              type: 'session_meta',
              payload: { id: subSourceUuid, source: { subagent: { type: 'explorer' } }, cwd: sb.root, timestamp: nowIso },
            })}\n`,
          );

          // Main session with a 32 KiB `base_instructions` string — write WITHOUT trailing `\n` first to test partial-flush retry!
          const bigFile = join(dayDir, `rollout-2026-11-17T23-30-03-${bigMetaSessionUuid}.jsonl`);
          const hugeBaseInstructions = 'You are Codex 0.169.0. '.repeat(1500); // ~34.5 KiB (> 32 KiB)
          assert.ok(Buffer.byteLength(hugeBaseInstructions, 'utf8') > 32 * 1024);
          const metaLineNoNewline = JSON.stringify({
            timestamp: nowIso,
            type: 'session_meta',
            payload: {
              id: bigMetaSessionUuid,
              cwd: sb.root,
              timestamp: nowIso,
              base_instructions: { text: hugeBaseInstructions },
            },
          });
          writeFileSync(bigFile, metaLineNoNewline);
          await new Promise(r => setTimeout(r, 30)); // poll fires while `\n` is not flushed yet
          writeFileSync(bigFile, '\n', { flag: 'a' }); // flush `\n`!
          await new Promise(r => setTimeout(r, 35)); // monitor pins `bigMetaSessionUuid`!

          // Now append a 2.5 MiB single-line `response_item` (exceeding the 2 MiB slice cap!) followed by a structured quota error line!
          const twoPointFiveMbBlob = 'A'.repeat(2_621_440); // 2.5 MiB
          const oversizedLine = JSON.stringify({
            timestamp: new Date().toISOString(),
            type: 'response_item',
            payload: { type: 'screenshot_base64', data: twoPointFiveMbBlob },
          });
          const quotaLine = JSON.stringify({
            timestamp: new Date().toISOString(),
            type: 'event_msg',
            payload: {
              type: 'task_complete',
              error: {
                message: 'You\'ve hit your usage limit (usage_limit_reached). Resets at 2026-11-18T03:00:00Z.',
                codex_error_info: 'usage_limit_exceeded',
              },
            },
          });
          writeFileSync(bigFile, `${oversizedLine}\n${quotaLine}\n`, { flag: 'a' });

          await new Promise(resolveAbort => {
            if (signal.aborted) return resolveAbort();
            signal.addEventListener('abort', resolveAbort, { once: true });
          });
          return { code: 1, signal: 'SIGTERM' };
        }
        return { code: 0, signal: null };
      },
    },
    { isTTY: true },
  );

  assert.equal(r2LiveRes.exit, 0, r2LiveRes.stderr);
  assert.equal(r2Turns.length, 2);
  assert.deepEqual(
    r2Turns[1].args,
    ['resume', '-m', 'gpt-5.4', bigMetaSessionUuid],
    'pinned 32 KiB session_meta UUID (ignoring subagent parent_thread_id/source.subagent), skipped 2.5 MiB line, and rotated on trailing quota error',
  );
});

test('#3516 Part 2: codex app-server daemon stop runs on import (managed + scrubbed source CODEX_HOME), use, next, remove/leave, and skips 0ms cached sync --quiet', async t => {
  const cloud = await createPoolGatewayServer(t, {
    accounts: [
      {
        account_id: 'acc_daemon_shared',
        label: 'shared-daemon',
        provider: 'codex',
        plan: 'pro',
        is_owner: false,
        shared: true,
        state: 'ready',
        five_hour_used_percent: 10,
        five_hour_reset_at: '2026-11-18T02:00:00Z',
        weekly_used_percent: 20,
        weekly_reset_at: '2026-11-23T00:00:00Z',
      },
    ],
  });
  const sb = makeSandbox(t, cloud.serverUrl);
  const managedHome = pddManagedCodexHome(sb.env);
  const userCodexHome = join(sb.home, '.codex');
  mkdirSync(userCodexHome, { recursive: true, mode: 0o700 });
  writeFileSync(join(userCodexHome, 'auth.json'), JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'oa_import_daemon_test',
      refresh_token: 'rt_single_use_import_daemon_test',
      id_token: makeJwt({ email: 'daemon-owner@example.com', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
      account_id: 'acct_import_daemon_1',
    },
  }), { mode: 0o600 });

  const daemonStops = [];
  const spyPorts = {
    tmpRoot: sb.root,
    readCodexUsageWindows: async () => null,
    spawnSync(cmd, args, opts) {
      daemonStops.push({ cmd, args, codexHome: opts?.env?.CODEX_HOME, stdio: opts?.stdio, timeout: opts?.timeout });
      return { status: 0 };
    },
  };

  // 1. `pdd accounts import`: stops daemon in BOTH `managedCodexHome` AND scrubbed `~/.codex`!
  const impRes = await invokeCli(['accounts', 'import', '--provider', 'codex', '--label', 'imported-daemon'], sb, spyPorts);
  assert.equal(impRes.exit, 0, impRes.stderr);
  assert.equal(JSON.parse(readFileSync(join(userCodexHome, 'auth.json'), 'utf8')).tokens.refresh_token, '');
  assert.deepEqual(
    daemonStops.map(c => ({ cmd: c.cmd, args: c.args, codexHome: c.codexHome, stdio: c.stdio, timeout: c.timeout })),
    [
      { cmd: 'codex', args: ['app-server', 'daemon', 'stop'], codexHome: managedHome, stdio: 'ignore', timeout: 2500 },
      { cmd: 'codex', args: ['app-server', 'daemon', 'stop'], codexHome: userCodexHome, stdio: 'ignore', timeout: 2500 },
    ],
    'import stops stale daemons in both managedCodexHome and scrubbed source CODEX_HOME',
  );

  // 2. Cached 0ms `sync --quiet` fast path MUST NOT spawn `codex app-server daemon stop`!
  daemonStops.length = 0;
  const cachedSync = await invokeCli(['accounts', 'sync', '--provider', 'codex', '--quiet'], sb, spyPorts);
  assert.equal(cachedSync.exit, 0, cachedSync.stderr);
  assert.equal(daemonStops.length, 0, 'cached 0ms sync --quiet fast path never spawns codex app-server daemon stop');

  // 3. Expired/stale `sync --quiet` that re-leases DOES stop stale daemon in `managedCodexHome`!
  const farFutureNow = Date.now() + 2 * 3600 * 1000;
  const refreshSync = await invokeCli(['accounts', 'sync', '--provider', 'codex', '--quiet'], sb, {
    ...spyPorts,
    now: () => farFutureNow,
  });
  assert.equal(refreshSync.exit, 0, refreshSync.stderr);
  assert.equal(daemonStops.length, 1, 're-materializing sync stops daemon in managedCodexHome');
  assert.equal(daemonStops[0].codexHome, managedHome);

  // 4. `use` and `next` each stop stale daemon in `managedCodexHome`!
  daemonStops.length = 0;
  assert.equal((await invokeCli(['accounts', 'use', 'shared-daemon'], sb, spyPorts)).exit, 0);
  assert.equal(daemonStops.length, 1);
  assert.equal(daemonStops[0].codexHome, managedHome);

  daemonStops.length = 0;
  assert.equal((await invokeCli(['accounts', 'next', '--provider', 'codex'], sb, spyPorts)).exit, 0);
  assert.equal(daemonStops.length, 1);
  assert.equal(daemonStops[0].codexHome, managedHome);

  // 5. `remove` + `leave` leaving zero active Codex accounts removes auth/gateway config and stops stale daemon!
  daemonStops.length = 0;
  assert.equal((await invokeCli(['accounts', 'remove', 'imported-daemon'], sb, spyPorts)).exit, 0);
  assert.equal(daemonStops.length, 1, 'removing active Codex account cleans managed home and stops daemon');
  assert.equal(daemonStops[0].codexHome, managedHome);

  assert.equal((await invokeCli(['accounts', 'use', 'shared-daemon'], sb, spyPorts)).exit, 0);
  daemonStops.length = 0;
  assert.equal((await invokeCli(['accounts', 'leave', 'shared-daemon'], sb, spyPorts)).exit, 0);
  assert.equal(daemonStops.length, 1, 'leaving last shared Codex account cleans managed home and stops daemon');
  assert.equal(daemonStops[0].codexHome, managedHome);
});

function findRolloutJsonlFiles(dir) {
  const out = [];
  if (!existsSync(dir)) return out;
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    const full = join(dir, entry.name);
    if (entry.isDirectory()) out.push(...findRolloutJsonlFiles(full));
    else if (entry.isFile() && entry.name.endsWith('.jsonl')) out.push(full);
  }
  return out;
}

function spawnAsync(cmd, args, { cwd, env, timeoutMs = 20_000 }) {
  return new Promise((resolvePromise, rejectPromise) => {
    const child = spawn(cmd, args, { cwd, env, stdio: ['ignore', 'pipe', 'pipe'] });
    let stdout = '';
    let stderr = '';
    const timer = setTimeout(() => {
      try { child.kill('SIGKILL'); } catch {}
      rejectPromise(new Error(`${cmd} ${args.join(' ')} timed out after ${timeoutMs}ms\nstdout: ${stdout}\nstderr: ${stderr}`));
    }, timeoutMs);
    child.stdout.on('data', chunk => { stdout += chunk.toString('utf8'); });
    child.stderr.on('data', chunk => { stderr += chunk.toString('utf8'); });
    child.on('error', err => {
      clearTimeout(timer);
      rejectPromise(err);
    });
    child.on('close', (code, signal) => {
      clearTimeout(timer);
      resolvePromise({ code, signal, stdout, stderr });
    });
  });
}

test('#3516 live codex-cli integration: app-server --strict-config rateLimits/read, codex exec on native openai provider, and codex exec resume across rotated grants with 0 external requests', async t => {
  const codexVersion = spawnSync('codex', ['--version'], { encoding: 'utf8' });
  if (codexVersion.status !== 0) {
    t.skip('codex binary is not installed in PATH');
    return;
  }

  const externalProxyTargets = [];
  const blockedProxy = http.createServer((req, res) => {
    externalProxyTargets.push(req.url);
    res.writeHead(502);
    res.end('External network blocked in test');
  });
  blockedProxy.on('connect', (req, clientSocket) => {
    externalProxyTargets.push(req.url);
    clientSocket.destroy();
  });
  await new Promise(resolveListen => blockedProxy.listen(0, '127.0.0.1', resolveListen));
  t.after(() => {
    blockedProxy.closeAllConnections?.();
    blockedProxy.close();
  });
  const blockedProxyUrl = `http://127.0.0.1:${blockedProxy.address().port}`;

  const issuedGrants = new Map();
  const gatewayHits = [];
  const accounts = [
    {
      account_id: 'acc_live_gw_1',
      label: 'gw-first',
      provider: 'codex',
      plan: 'pro',
      is_owner: true,
      shared: false,
      state: 'ready',
      five_hour_used_percent: 20,
      five_hour_reset_at: '2026-11-18T02:00:00Z',
      weekly_used_percent: 35,
      weekly_reset_at: '2026-11-23T00:00:00Z',
    },
    {
      account_id: 'acc_live_gw_2',
      label: 'gw-second',
      provider: 'codex',
      plan: 'team',
      is_owner: true,
      shared: false,
      state: 'ready',
      five_hour_used_percent: 5,
      five_hour_reset_at: '2026-11-18T03:00:00Z',
      weekly_used_percent: 10,
      weekly_reset_at: '2026-11-24T00:00:00Z',
    },
  ];
  let seq = 1;
  let mockUrl = '';

  const server = http.createServer(async (req, res) => {
    const chunks = [];
    for await (const chunk of req) chunks.push(chunk);
    const rawBody = Buffer.concat(chunks).toString('utf8');
    let body = null;
    try { body = rawBody ? JSON.parse(rawBody) : null; } catch {}
    const url = new URL(req.url, 'http://127.0.0.1');
    const sendJson = (status, payload) => {
      res.writeHead(status, { 'content-type': 'application/json' });
      res.end(JSON.stringify(payload));
    };

    if (url.pathname.startsWith('/v1/codex-gateway')) {
      const authHeader = String(req.headers.authorization ?? '');
      const bearerGrant = authHeader.startsWith('Bearer ') ? authHeader.slice(7).trim() : '';
      const headerGrant = String(req.headers['x-pdd-gateway-grant'] ?? '').trim();
      const grant = bearerGrant || headerGrant;
      gatewayHits.push({
        method: req.method,
        path: url.pathname,
        grant,
        accountLabel: issuedGrants.get(grant) ?? null,
      });
      if (!issuedGrants.has(grant)) {
        return sendJson(401, { error: { message: 'Invalid or revoked gateway grant' } });
      }
      if (req.method === 'GET' && /\/models$/.test(url.pathname)) {
        return sendJson(200, {
          models: [
            {
              slug: 'gpt-5.4',
              display_name: 'GPT-5.4',
              description: 'Mock GPT-5.4 via PDD Gateway',
              supported_reasoning_levels: [{ effort: 'medium', description: 'Medium' }],
              default_reasoning_level: 'medium',
              default_reasoning_summary: 'none',
              supports_reasoning_summaries: false,
              support_verbosity: false,
              default_verbosity: null,
              prefer_websockets: false,
              shell_type: 'unified_exec',
              visibility: 'list',
              minimal_client_version: '0.1.0',
              priority: 1,
              supported_in_api: true,
              availability_nux: null,
              upgrade: null,
              input_modalities: ['text'],
              apply_patch_tool_type: 'freeform',
              web_search_tool_type: 'text',
              truncation_policy: { mode: 'tokens', limit: 10000 },
              supports_parallel_tool_calls: true,
              context_window: 272000,
              effective_context_window_percent: 95,
              experimental_supported_tools: [],
              base_instructions: 'Reply directly without running tools.',
            },
          ],
        });
      }
      if (req.method === 'GET' && /\/usage$/.test(url.pathname)) {
        return sendJson(200, {
          plan_type: 'pro',
          rate_limit: {
            allowed: true,
            limit_reached: false,
            primary_window: {
              used_percent: 23,
              limit_window_seconds: 18000,
              reset_after_seconds: 3600,
              reset_at: 1800003600,
            },
            secondary_window: {
              used_percent: 41,
              limit_window_seconds: 604800,
              reset_after_seconds: 86400,
              reset_at: 1800086400,
            },
          },
        });
      }
      if (req.method === 'POST' && /\/responses$/.test(url.pathname)) {
        const label = issuedGrants.get(grant);
        const replyText = `GATEWAY_OK_${label}`;
        const model = body?.model || 'gpt-5.4';
        const respId = `resp_mock_${seq++}`;
        const msgId = `msg_mock_${seq++}`;
        res.writeHead(200, {
          'content-type': 'text/event-stream',
          'cache-control': 'no-cache',
          connection: 'keep-alive',
        });
        const events = [
          ['response.created', { type: 'response.created', response: { id: respId, object: 'response', status: 'in_progress', model, output: [] } }],
          ['response.output_item.added', { type: 'response.output_item.added', output_index: 0, item: { id: msgId, type: 'message', status: 'in_progress', role: 'assistant', content: [] } }],
          ['response.content_part.added', { type: 'response.content_part.added', item_id: msgId, output_index: 0, content_index: 0, part: { type: 'output_text', text: '' } }],
          ['response.output_text.delta', { type: 'response.output_text.delta', item_id: msgId, output_index: 0, content_index: 0, delta: replyText }],
          ['response.output_text.done', { type: 'response.output_text.done', item_id: msgId, output_index: 0, content_index: 0, text: replyText }],
          ['response.content_part.done', { type: 'response.content_part.done', item_id: msgId, output_index: 0, content_index: 0, part: { type: 'output_text', text: replyText } }],
          ['response.output_item.done', { type: 'response.output_item.done', output_index: 0, item: { id: msgId, type: 'message', status: 'completed', role: 'assistant', content: [{ type: 'output_text', text: replyText }] } }],
          ['response.completed', {
            type: 'response.completed',
            response: {
              id: respId,
              object: 'response',
              status: 'completed',
              model,
              output: [{ id: msgId, type: 'message', status: 'completed', role: 'assistant', content: [{ type: 'output_text', text: replyText }] }],
              usage: {
                input_tokens: 12,
                input_tokens_details: { cached_tokens: 0 },
                output_tokens: 4,
                output_tokens_details: { reasoning_tokens: 0 },
                total_tokens: 16,
              },
            },
          }],
        ];
        for (const [evt, data] of events) {
          res.write(`event: ${evt}\ndata: ${JSON.stringify(data)}\n\n`);
        }
        res.end();
        return;
      }
      return sendJson(404, { error: `Unhandled gateway route ${url.pathname}` });
    }

    if (req.headers.authorization !== 'Bearer ghu_testCloudBearer999999') {
      return sendJson(401, { detail: 'Unauthorized' });
    }
    if (req.method === 'GET' && url.pathname === '/v1/accounts') {
      return sendJson(200, { accounts, pending_invites: [] });
    }
    if (req.method === 'POST' && url.pathname === '/v1/accounts/lease') {
      const skip = new Set(Array.isArray(body?.skip_account_ids) ? body.skip_account_ids : []);
      const candidates = accounts.filter(a => !skip.has(a.account_id));
      const chosen = (body?.preferred_label && candidates.find(a => a.label === body.preferred_label))
        || (body?.current_account_id && candidates.find(a => a.account_id === body.current_account_id))
        || candidates[0];
      const leaseHex = (seq++).toString(16).padStart(8, '0');
      const leaseId = `lse_${leaseHex}`;
      const grantToken = `pddg_lse_${leaseHex}_liveGrantSecret${seq}`;
      issuedGrants.set(grantToken, chosen.label);
      return sendJson(200, {
        state: 'leased',
        switched: chosen.account_id !== body?.current_account_id,
        account: chosen,
        lease: {
          lease_id: leaseId,
          expires_at: new Date(Date.now() + 45 * 60 * 1000).toISOString(),
          delivery_mode: 'gateway_grant',
          codex_gateway_url: `${mockUrl}/v1/codex-gateway/${leaseId}`,
          codex_gateway_token: grantToken,
          gateway_bearer_token: grantToken,
        },
      });
    }
    return sendJson(404, { detail: 'Not found' });
  });

  await new Promise(resolveListen => server.listen(0, '127.0.0.1', resolveListen));
  t.after(() => {
    server.closeAllConnections?.();
    server.close();
  });
  mockUrl = `http://127.0.0.1:${server.address().port}`;

  const sb = makeSandbox(t, mockUrl);
  const managedHome = pddManagedCodexHome(sb.env);
  t.after(() => {
    try {
      spawnSync('codex', ['app-server', 'daemon', 'stop'], {
        env: { ...sb.env, CODEX_HOME: managedHome },
        stdio: 'ignore',
        timeout: 2500,
      });
    } catch {}
  });

  // Pin account 1 (`gw-first`)
  const useFirst = await invokeCli(['accounts', 'use', 'gw-first'], sb);
  assert.equal(useFirst.exit, 0, useFirst.stderr);
  const grantFirst = JSON.parse(readFileSync(managedCodexAuthPath(sb.env), 'utf8')).tokens.access_token;

  const codexEnv = {
    ...sb.env,
    CODEX_HOME: managedHome,
    HTTP_PROXY: blockedProxyUrl,
    HTTPS_PROXY: blockedProxyUrl,
    ALL_PROXY: blockedProxyUrl,
    NO_PROXY: '127.0.0.1,localhost',
  };

  // 1. `codex app-server --strict-config --listen stdio://` -> `account/rateLimits/read` succeeds via local mock gateway!
  const rateLimitsRes = await readCodexUsageWindows(
    { command: 'codex', cwd: sb.cwd, env: codexEnv, timeoutMs: 10_000 },
    {
      spawn(cmd, args, opts) {
        return spawn(cmd, [args[0], '--strict-config', ...args.slice(1)], opts);
      },
    },
  );
  assert.equal(rateLimitsRes?.state, 'healthy', `app-server rateLimits/read returned: ${JSON.stringify(rateLimitsRes)}`);
  assert.equal(rateLimitsRes?.five_hour_used_percent, 23);
  assert.equal(rateLimitsRes?.weekly_used_percent, 41);
  assert.ok(
    gatewayHits.some(h => /\/usage$/.test(h.path) && h.grant === grantFirst),
    'codex app-server account/rateLimits/read authenticated against local mock gateway with Bearer pddg_lse_*',
  );

  // 2. `codex exec` creates a session saved with `model_provider: "openai"` and completes via local mock gateway!
  const execRes = await spawnAsync(
    'codex',
    ['exec', '--skip-git-repo-check', '-m', 'gpt-5.4', 'say hello'],
    { cwd: sb.cwd, env: codexEnv, timeoutMs: 20_000 },
  );
  assert.equal(execRes.code, 0, `codex exec failed:\nstdout: ${execRes.stdout}\nstderr: ${execRes.stderr}`);
  assert.match(execRes.stdout, /GATEWAY_OK_gw-first/);

  const rolloutFiles = findRolloutJsonlFiles(join(managedHome, 'sessions'));
  assert.equal(rolloutFiles.length, 1, 'codex exec wrote session rollout JSONL');
  const rolloutLines = readFileSync(rolloutFiles[0], 'utf8').trim().split('\n');
  const sessionMeta = JSON.parse(rolloutLines[0]);
  assert.equal(sessionMeta.type, 'session_meta');
  assert.equal(sessionMeta.payload.model_provider, 'openai', 'session saved under native "openai" model_provider');
  const openaiThreadId = sessionMeta.payload.id;
  assert.ok(openaiThreadId);

  // 3. Rotate active account to `gw-second` and verify `codex exec resume <thread-id>` of the `"openai"` session succeeds on the rotated grant!
  const nextRes = await invokeCli(['accounts', 'next', '--provider', 'codex'], sb);
  assert.equal(nextRes.exit, 0, nextRes.stderr);
  const grantSecond = JSON.parse(readFileSync(managedCodexAuthPath(sb.env), 'utf8')).tokens.access_token;
  assert.notEqual(grantSecond, grantFirst);

  const resumeRes = await spawnAsync(
    'codex',
    ['exec', 'resume', '--skip-git-repo-check', openaiThreadId, 'continue session'],
    { cwd: sb.cwd, env: codexEnv, timeoutMs: 20_000 },
  );
  assert.equal(resumeRes.code, 0, `codex exec resume failed:\nstdout: ${resumeRes.stdout}\nstderr: ${resumeRes.stderr}`);
  assert.match(resumeRes.stdout, /GATEWAY_OK_gw-second/);
  assert.ok(
    gatewayHits.some(h => h.method === 'POST' && /\/responses$/.test(h.path) && h.grant === grantSecond),
    'resumed "openai" session sent rotated Bearer pddg_lse_* grant to local mock gateway',
  );

  // 4. Backward compatibility: an older session saved with `model_provider: "pdd_codex_gateway"` ALSO resumes cleanly!
  const legacyThreadId = '019a9999-aaaa-7000-8000-deadbeef1234';
  const legacyMeta = structuredClone(sessionMeta);
  legacyMeta.payload.id = legacyThreadId;
  legacyMeta.payload.model_provider = 'pdd_codex_gateway';
  const legacyRolloutPath = rolloutFiles[0].replace(openaiThreadId, legacyThreadId);
  writeFileSync(legacyRolloutPath, `${[JSON.stringify(legacyMeta), ...rolloutLines.slice(1)].join('\n')}\n`, { mode: 0o600 });

  const legacyResumeRes = await spawnAsync(
    'codex',
    ['-c', 'model_provider="pdd_codex_gateway"', 'exec', 'resume', '--skip-git-repo-check', legacyThreadId, 'continue legacy session'],
    { cwd: sb.cwd, env: codexEnv, timeoutMs: 20_000 },
  );
  assert.equal(
    legacyResumeRes.code,
    0,
    `legacy pdd_codex_gateway session resume failed:\nstdout: ${legacyResumeRes.stdout}\nstderr: ${legacyResumeRes.stderr}`,
  );
  assert.match(legacyResumeRes.stdout, /GATEWAY_OK_gw-second/);

  const openaiExternalHits = externalProxyTargets.filter(target => /^(?:https?:\/\/)?(?:api\.openai\.com|(?:www\.)?chatgpt\.com)(?::\d+)?(?:\/|$)/i.test(target));
  assert.deepEqual(openaiExternalHits, [], `expected 0 requests to api.openai.com or chatgpt.com, saw: ${JSON.stringify(externalProxyTargets)}`);
});

test('self-healing shell wrapper auto-upgrades stale 0.1.34 pdd accounts auto blocks in place while leaving unmarked profiles untouched', async t => {
  const cloud = await createPoolGatewayServer(t, {
    accounts: [
      {
        account_id: 'acc_auto_heal_1',
        provider: 'codex',
        label: 'auto-heal-1',
        is_owner: true,
        state: 'ready',
        plan_type: 'pro',
        five_hour_used_percent: 10,
        weekly_used_percent: 20,
        five_hour_reset_at: '2099-01-01T05:00:00Z',
        weekly_reset_at: '2099-01-07T00:00:00Z',
      },
    ],
  });
  const sb = makeSandbox(t, cloud.serverUrl);

  // Guard: missing HOME is a strict no-op
  assert.deepEqual(refreshInstalledAutoSwitchBlocks({ env: {} }), []);

  // Case 1: `.zshrc` WITHOUT `# >>> pdd accounts auto >>>` MUST remain 100% untouched (and missing `.bashrc` must NOT be created!)
  const zshrcPath = join(sb.home, '.zshrc');
  const bashrcPath = join(sb.home, '.bashrc');
  const fishPath = join(sb.configHome, 'fish', 'config.fish');
  const plainZshrc = 'export PATH="$HOME/.local/bin:$PATH"\nalias gs="git status"\n';
  writeFileSync(zshrcPath, plainZshrc, { mode: 0o600 });

  const useUnmarked = await invokeCli(['accounts', 'use', 'auto-heal-1', '--provider', 'codex'], sb);
  assert.equal(useUnmarked.exit, 0, useUnmarked.stderr);
  assert.equal(readFileSync(zshrcPath, 'utf8'), plainZshrc, 'unmarked .zshrc untouched');
  assert.equal(existsSync(bashrcPath), false, 'absent .bashrc not created unless auto on is run');
  assert.equal(existsSync(fishPath), false, 'absent config.fish not created unless auto on is run');

  // Case 2: Seed a stale 0.1.34 `# >>> pdd accounts auto >>>` block (missing PDD_PRINT_CODEX_HOME & CODEX_HOME="$_pdd_cx_home")
  // in a dotfiles-symlinked `.zshrc` (mode 0600) AND in `config.fish`, surrounded by custom user lines.
  rmSync(zshrcPath, { force: true });
  const dotfilesDir = join(sb.root, 'dotfiles');
  mkdirSync(dotfilesDir, { recursive: true });
  const dotfilesZshrc = join(dotfilesDir, 'zshrc');
  const staleZshBlock = [
    'export EDITOR="vim"',
    '',
    '# >>> pdd accounts auto >>>',
    'codex() {',
    '  command -v pdd >/dev/null 2>&1 && pdd accounts sync --provider codex --quiet --timeout-ms 1200 2>/dev/null || true',
    '  command codex "$@"',
    '}',
    '# <<< pdd accounts auto <<<',
    '',
    'alias ll="ls -la"',
    '',
  ].join('\n');
  writeFileSync(dotfilesZshrc, staleZshBlock, { mode: 0o600 });
  chmodSync(dotfilesZshrc, 0o600);
  symlinkSync(dotfilesZshrc, zshrcPath);

  mkdirSync(join(sb.configHome, 'fish'), { recursive: true });
  const staleFishBlock = [
    '# fish greeting',
    '# >>> pdd accounts auto >>>',
    'function codex --wraps codex',
    '  pdd accounts sync --provider codex --quiet 2>/dev/null; or true',
    '  command codex $argv',
    'end',
    '# <<< pdd accounts auto <<<',
    '',
  ].join('\n');
  writeFileSync(fishPath, staleFishBlock, { mode: 0o644 });

  // Running `pdd accounts sync --provider codex --quiet` (just like the old 0.1.34 shell hook does!) upgrades both blocks in place!
  const syncRes = await invokeCli(['accounts', 'sync', '--provider', 'codex', '--quiet'], sb);
  assert.equal(syncRes.exit, 0, syncRes.stderr);

  assert.equal(lstatSync(zshrcPath).isSymbolicLink(), true, 'dotfiles symlink on ~/.zshrc preserved');
  assert.equal(statSync(dotfilesZshrc).mode & 0o777, 0o600, 'target file mode 0600 preserved');
  const upgradedZsh = readFileSync(zshrcPath, 'utf8');
  assert.ok(upgradedZsh.includes(renderAutoSwitchBlock('zsh')), 'zsh auto block upgraded to current wrapper');
  assert.match(upgradedZsh, /PDD_PRINT_CODEX_HOME=1 pdd accounts sync/);
  assert.match(upgradedZsh, /CODEX_HOME="\$_pdd_cx_home"/);
  assert.match(upgradedZsh, /^export EDITOR="vim"\n\n# >>> pdd accounts auto >>>/);
  assert.match(upgradedZsh, /# <<< pdd accounts auto <<<\n\nalias ll="ls -la"\n$/);

  const upgradedFish = readFileSync(fishPath, 'utf8');
  assert.ok(upgradedFish.includes(renderAutoSwitchBlock('fish')), 'fish auto block upgraded to current wrapper');
  assert.match(upgradedFish, /PDD_PRINT_CODEX_HOME=1 pdd accounts sync/);
  assert.equal(existsSync(bashrcPath), false, 'still-absent .bashrc was not created');

  // Subsequent runs are idempotent no-ops
  assert.deepEqual(refreshInstalledAutoSwitchBlocks({ env: sb.env }), []);
});


test('P0 surface audit (#2, #3, #4, #5): symlinked ~/.codex/auth.json import+scrub, sync timeout resilience, bash shell wrapper (positional prompt, login status, claude ANTHROPIC_API_KEY), Claude remove/leave/list gateway cleanup, fork UUID, and accept activation + warning', async t => {
  const forkUuid = '019a8888-1111-7000-8000-123456789abc';
  const cloud = await createPoolGatewayServer(t, {
    accounts: [
      {
        account_id: 'acc_cx_audit_1',
        label: 'cx-audit-1',
        provider: 'codex',
        plan: 'pro',
        is_owner: true,
        shared: false,
        state: 'ready',
        five_hour_used_percent: 10,
        five_hour_reset_at: '2026-11-18T02:00:00Z',
        weekly_used_percent: 20,
        weekly_reset_at: '2026-11-23T00:00:00Z',
      },
      {
        account_id: 'acc_cx_audit_2',
        label: 'cx-audit-2',
        provider: 'codex',
        plan: 'pro',
        is_owner: true,
        shared: false,
        state: 'ready',
        five_hour_used_percent: 5,
        five_hour_reset_at: '2026-11-18T03:00:00Z',
        weekly_used_percent: 10,
        weekly_reset_at: '2026-11-24T00:00:00Z',
      },
      {
        account_id: 'acc_cl_shared_1',
        label: 'cl-shared-1',
        provider: 'claude',
        plan: 'max',
        is_owner: false,
        shared: true,
        state: 'ready',
        five_hour_used_percent: 15,
        five_hour_reset_at: '2026-11-18T02:00:00Z',
        weekly_used_percent: 25,
        weekly_reset_at: '2026-11-23T00:00:00Z',
      },
    ],
  });
  const sb = makeSandbox(t, cloud.serverUrl);

  // 1. Fix #2: Dotfile-symlinked `~/.codex/auth.json -> <dotfiles/auth.json>` imports cleanly and scrubs refresh_token while preserving symlink!
  const userCodexDir = join(sb.home, '.codex');
  mkdirSync(userCodexDir, { recursive: true });
  const dotAuthDir = join(sb.root, 'dotfiles-codex-auth');
  mkdirSync(dotAuthDir, { recursive: true });
  const realDotAuthPath = join(dotAuthDir, 'auth.json');
  writeFileSync(realDotAuthPath, JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: 'at_dotfile_symlink_777',
      refresh_token: 'rt_dotfile_symlink_SCRUB_ME_777',
      id_token: makeJwt({ email: 'dotfiles@promptdriven.ai', 'https://api.openai.com/auth': { chatgpt_plan_type: 'pro' } }),
      account_id: 'acct_dotfile_symlink_1',
    },
  }, null, 2), { mode: 0o600 });
  symlinkSync(realDotAuthPath, join(userCodexDir, 'auth.json'));

  const symImpRes = await invokeCli(['accounts', 'import', '--provider', 'codex', '--label', 'cx-dotfiles'], sb);
  assert.equal(symImpRes.exit, 0, symImpRes.stderr);
  assert.equal(lstatSync(join(userCodexDir, 'auth.json')).isSymbolicLink(), true, 'dotfile symlink at ~/.codex/auth.json preserved');
  assert.equal(JSON.parse(readFileSync(realDotAuthPath, 'utf8')).tokens.refresh_token, '', 'target dotfile auth.json had single-use refresh_token scrubbed');

  // Symlink pointing inside managedHome MUST STILL be refused!
  rmSync(join(userCodexDir, 'auth.json'), { force: true });
  symlinkSync(managedCodexAuthPath(sb.env), join(userCodexDir, 'auth.json'));
  const loopImpRes = await invokeCli(['accounts', 'import', '--provider', 'codex', '--label', 'cx-loop-refuse'], sb);
  assert.equal(loopImpRes.exit, 1);
  assert.match(loopImpRes.stderr, /Refusing to import symlinked Codex credential file/);
  rmSync(join(userCodexDir, 'auth.json'), { force: true });

  // 2. Fix #3a: `PDD_PRINT_CODEX_HOME=1 pdd accounts sync` keeps `pddManagedCodexHome` when Cloud times out / 500s and a valid lease is on disk!
  cloud.state.leaseOverrideState = 'error_500';
  const sbPrintHome = { ...sb, env: { ...sb.env, PDD_PRINT_CODEX_HOME: '1' } };
  // Expire near-renewal window (<15m left, still > now) to force runSyncCommand to hit `leaseCloudAccount` and enter catch block!
  const statePath = accountsStatePath(sb.env);
  const savedBeforeTimeout = JSON.parse(readFileSync(statePath, 'utf8'));
  savedBeforeTimeout.active.codex.expires_at = new Date(cloud.state.nowMs + 5 * 60 * 1000).toISOString();
  writeFileSync(statePath, JSON.stringify(savedBeforeTimeout, null, 2));

  const syncTimeoutRes = await invokeCli(['accounts', 'sync', '--provider', 'codex', '--quiet', '--timeout-ms', '1200'], sbPrintHome);
  cloud.state.leaseOverrideState = null;
  assert.equal(syncTimeoutRes.exit, 0);
  assert.equal(
    syncTimeoutRes.stdout.trim(),
    pddManagedCodexHome(sb.env),
    'transient sync failure keeps valid on-disk CODEX_HOME instead of returning empty string',
  );

  // Whereas an unattributed `reauth_required` lease failure MUST NOT keep `pddManagedCodexHome`!
  cloud.state.leaseOverrideState = 'reauth_no_id';
  const syncReauthRes = await invokeCli(['accounts', 'sync', '--provider', 'codex', '--quiet', '--timeout-ms', '1200'], sbPrintHome);
  cloud.state.leaseOverrideState = null;
  assert.equal(syncReauthRes.exit, 0);
  assert.equal(
    syncReauthRes.stdout.trim(),
    '',
    'reauth_required sync failure never keeps cached CODEX_HOME even without explicit account_id',
  );

  // 3. Fix #3b & #3c: Execute `renderAutoSwitchBlock('sh')` in real `bash`!
  assert.equal((await invokeCli(['accounts', 'use', 'cl-shared-1'], sb)).exit, 0);
  const clSettingsPath = join(sb.home, '.claude', 'settings.json');
  assert.equal(existsSync(clSettingsPath), false, 'use must never create or mutate ~/.claude/settings.json');
  const managedClSettingsPath = managedClaudeSettingsPath(sb.env);
  assert.match(JSON.parse(readFileSync(managedClSettingsPath, 'utf8')).env.CLAUDE_CODE_OAUTH_TOKEN, /^pddg_cl_shared_/);

  const fakeBin = join(sb.root, 'wrapper-bin');
  mkdirSync(fakeBin, { recursive: true });
  const managedHome = pddManagedCodexHome(sb.env);
  writeFileSync(join(fakeBin, 'pdd'), `#!/bin/sh\nif [ "\${PDD_PRINT_CODEX_HOME:-}" = "1" ]; then printf '%s\\n' ${JSON.stringify(managedHome)}; fi\nexit 0\n`, { mode: 0o755 });
  writeFileSync(join(fakeBin, 'pdd-codex'), `#!/bin/sh\nprintf 'VIA=pdd-codex FAIL_OPEN=%s CODEX_HOME=%s ARGS=%s\\n' "\${PDD_CODEX_AUTO_FAIL_OPEN:-UNSET}" "\${CODEX_HOME:-UNSET}" "$*"\n`, { mode: 0o755 });
  writeFileSync(join(fakeBin, 'codex'), `#!/bin/sh\nprintf 'CODEX_HOME=%s ARGS=%s\\n' "\${CODEX_HOME:-UNSET}" "$*"\n`, { mode: 0o755 });
  writeFileSync(join(fakeBin, 'pdd-claude'), `#!/bin/sh\nprintf 'VIA=pdd-claude ARGS=%s\\n' "$*"\n`, { mode: 0o755 });
  writeFileSync(join(fakeBin, 'claude'), `#!/bin/sh\nprintf 'VIA=stock-claude ARGS=%s\\n' "$*"\n`, { mode: 0o755 });
  chmodSync(join(fakeBin, 'pdd'), 0o755);
  chmodSync(join(fakeBin, 'pdd-codex'), 0o755);
  chmodSync(join(fakeBin, 'codex'), 0o755);
  chmodSync(join(fakeBin, 'pdd-claude'), 0o755);
  chmodSync(join(fakeBin, 'claude'), 0o755);

  const wrapperScript = join(sb.root, 'wrapper.sh');
  writeFileSync(wrapperScript, `${renderAutoSwitchBlock('sh')}\n`);

  const runBash = (cmd, extraEnv = {}) => spawnSync('bash', ['-c', `source ${JSON.stringify(wrapperScript)}\n${cmd}`], {
    env: {
      ...sb.env,
      PATH: `${fakeBin}:${sb.env.PATH}`,
      ...extraEnv,
    },
    encoding: 'utf8',
  });

  // 3b-i: Default unified auto-switch routes `codex "explain login" logout` and `codex login status` to `pdd-codex`
  // with `PDD_CODEX_AUTO_FAIL_OPEN=1` (clearing stale managed `CODEX_HOME`) and does NOT trip the logout guard!
  const defaultPromptWithLogoutWord = runBash('codex "explain login" logout', { CODEX_HOME: managedHome });
  assert.equal(defaultPromptWithLogoutWord.status, 0, defaultPromptWithLogoutWord.stderr);
  assert.match(defaultPromptWithLogoutWord.stdout, /VIA=pdd-codex FAIL_OPEN=1 CODEX_HOME=UNSET ARGS=explain login logout/);

  const defaultLoginStatusRun = runBash('codex login status');
  assert.equal(defaultLoginStatusRun.status, 0, defaultLoginStatusRun.stderr);
  assert.match(defaultLoginStatusRun.stdout, /VIA=pdd-codex FAIL_OPEN=1 CODEX_HOME=UNSET ARGS=login status/);

  // 3b-ii: Opt-in `PDD_LEGACY_PTY_ROTATE=1` preserves legacy `CODEX_HOME="$_pdd_cx_home"` routing!
  const legacyPromptWithLogoutWord = runBash('codex "explain login" logout', { CODEX_HOME: managedHome, PDD_LEGACY_PTY_ROTATE: '1' });
  assert.equal(legacyPromptWithLogoutWord.status, 0, legacyPromptWithLogoutWord.stderr);
  assert.match(legacyPromptWithLogoutWord.stdout, new RegExp(`CODEX_HOME=${managedHome.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')} ARGS=explain login logout`));

  const legacyLoginStatusRun = runBash('codex login status', { PDD_LEGACY_PTY_ROTATE: '1' });
  assert.equal(legacyLoginStatusRun.status, 0, legacyLoginStatusRun.stderr);
  assert.match(legacyLoginStatusRun.stdout, new RegExp(`CODEX_HOME=${managedHome.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')} ARGS=login status`));

  // While `codex logout` and `codex login` (without `status`) inside managedHome ARE still refused!
  assert.equal(runBash('codex logout', { CODEX_HOME: managedHome }).status, 1);
  assert.equal(runBash('codex login', { CODEX_HOME: managedHome }).status, 1);

  // 3c: `claude` delegates to `pdd-claude` when installed while parent shell keeps `ANTHROPIC_API_KEY`!
  const claudeRun = runBash('export ANTHROPIC_API_KEY="sk-ant-api03-ambient"; claude -p hi; printf "PARENT=%s\\n" "$ANTHROPIC_API_KEY"');
  assert.equal(claudeRun.status, 0, claudeRun.stderr);
  assert.match(claudeRun.stdout, /VIA=pdd-claude ARGS=-p hi/);
  assert.match(claudeRun.stdout, /PARENT=sk-ant-api03-ambient/);

  // 4. Fix #4: Leaving/removing the last Claude account cleans isolated managedClaudeSettingsPath AND legacy `pddg_*` & gateway `ANTHROPIC_BASE_URL` from `~/.claude/settings.json`!
  mkdirSync(join(sb.home, '.claude'), { recursive: true });
  writeFileSync(clSettingsPath, JSON.stringify({
    theme: 'dark',
    env: {
      CLAUDE_CODE_OAUTH_TOKEN: 'pddg_legacy_from_older_pdd',
      ANTHROPIC_BASE_URL: `${cloud.serverUrl}/v1/accounts/claude-gateway/lse_legacy`,
    },
  }, null, 2));
  const leaveClRes = await invokeCli(['accounts', 'leave', 'cl-shared-1'], sb);
  assert.equal(leaveClRes.exit, 0, leaveClRes.stderr);
  assert.equal(existsSync(managedClSettingsPath), false, 'leave removed isolated managed Claude settings file');
  const clAfterLeave = JSON.parse(readFileSync(clSettingsPath, 'utf8'));
  assert.equal(clAfterLeave.theme, 'dark');
  assert.equal(clAfterLeave.env, undefined, 'leave pruned empty env object after stripping legacy PDD entries');

  // Reconciling via `pdd accounts list` cleans lingering gateway settings whenever `!nextActive.claude`,
  // EVEN when another paused/inactive Claude account remains enrolled (`nextProviders.includes('claude')`)!
  cloud.state.accounts.push({
    account_id: 'acc_cl_paused_enrolled',
    label: 'cl-paused-other',
    provider: 'claude',
    plan: 'max',
    is_owner: true,
    shared: false,
    state: 'paused',
    five_hour_used_percent: 0,
    five_hour_reset_at: null,
    weekly_used_percent: 0,
    weekly_reset_at: null,
  });
  writeFileSync(clSettingsPath, JSON.stringify({
    env: {
      CLAUDE_CODE_OAUTH_TOKEN: 'pddg_stale_grant_after_revoke',
      ANTHROPIC_BASE_URL: `${cloud.serverUrl}/v1/accounts/claude-gateway/lse_stale`,
    },
  }, null, 2));
  assert.equal((await invokeCli(['accounts', 'list'], sb)).exit, 0);
  const clAfterList = JSON.parse(readFileSync(clSettingsPath, 'utf8'));
  assert.equal(clAfterList.env?.CLAUDE_CODE_OAUTH_TOKEN, undefined);
  assert.equal(clAfterList.env?.ANTHROPIC_BASE_URL, undefined);
  cloud.state.accounts = cloud.state.accounts.filter(a => a.account_id !== 'acc_cl_paused_enrolled');

  // 5. Fix #5a: `pdd accounts codex -- -i chart.png fork <parentUuid>` never pins pre-existing `<parentUuid>` rollout!
  // Seed a real pre-existing `<parentUuid>` rollout file on disk before launching `fork`:
  const sessionsDayDir = join(managedHome, 'sessions', '2026', '11', '17');
  mkdirSync(sessionsDayDir, { recursive: true });
  const parentRolloutPath = join(sessionsDayDir, `rollout-2026-11-17T00-00-00-${forkUuid}.jsonl`);
  writeFileSync(parentRolloutPath, `${JSON.stringify({
    timestamp: new Date().toISOString(),
    type: 'session_meta',
    payload: { id: forkUuid, cwd: sb.root, timestamp: new Date().toISOString() },
  })}\n`);

  // 5a-i: Turn-0 startup quota exit BEFORE child rollout creation re-runs `['-i', 'chart.png', 'fork', forkUuid]` (never mutating parent via `resume`)!
  assert.equal((await invokeCli(['accounts', 'use', 'cx-audit-1'], sb)).exit, 0);
  const forkTurn0Turns = [];
  const forkTurn0Res = await invokeCli(['accounts', 'codex', '--', '-i', 'chart.png', 'fork', forkUuid], sb, {
    quotaSettleMs: 0,
    async spawnCodexPty({ args, turn, onOutput }) {
      forkTurn0Turns.push({ turn, args });
      if (turn === 0) {
        onOutput(`Forking session ${forkUuid}...\nError: You've hit your usage limit for this window.\n`);
        return { code: 1, signal: 'SIGTERM' };
      }
      return { code: 0, signal: null };
    },
  }, { isTTY: true });
  assert.equal(forkTurn0Res.exit, 0, forkTurn0Res.stderr);
  assert.equal(forkTurn0Turns.length, 2);
  assert.deepEqual(forkTurn0Turns[0].args, ['-i', 'chart.png', 'fork', forkUuid]);
  assert.deepEqual(forkTurn0Turns[1].args, ['-i', 'chart.png', 'fork', forkUuid]);

  // 5a-ii: Mid-session quota rotation AFTER newly forked `<childUuid>` rollout is created ignores `<parentUuid>` and resumes `<childUuid>`!
  const cx1 = cloud.state.accounts.find(a => a.account_id === 'acc_cx_audit_1');
  cx1.state = 'ready';
  cx1.cooling_until = null;
  cx1.five_hour_used_percent = 10;
  assert.equal((await invokeCli(['accounts', 'use', 'cx-audit-1'], sb)).exit, 0);
  const childUuid = '019a9999-2222-7000-8000-abcdef012345';
  const forkMidTurns = [];
  const forkMidRes = await invokeCli(['accounts', 'codex', '--', '-i', 'chart.png', 'fork', forkUuid], sb, {
    rolloutPollIntervalMs: 15,
    quotaSettleMs: 0,
    async spawnCodexPty({ args, turn, cwd, signal }) {
      forkMidTurns.push({ turn, args });
      if (turn === 0) {
        const nowIso = new Date().toISOString();
        const childRolloutPath = join(sessionsDayDir, `rollout-2026-11-17T22-00-00-${childUuid}.jsonl`);
        writeFileSync(childRolloutPath, [
          JSON.stringify({
            timestamp: nowIso,
            type: 'session_meta',
            payload: { id: childUuid, forked_from_id: forkUuid, cwd, timestamp: nowIso },
          }),
          JSON.stringify({
            timestamp: nowIso,
            type: 'event_msg',
            payload: {
              type: 'error',
              codex_error_info: 'usage_limit_exceeded',
              message: 'Usage limit reached for this window.',
            },
          }),
          '',
        ].join('\n'));
        await new Promise(resolve => {
          if (signal.aborted) return resolve();
          signal.addEventListener('abort', resolve, { once: true });
        });
        return { code: 143, signal: 'SIGTERM' };
      }
      return { code: 0, signal: null };
    },
  }, { isTTY: true });
  assert.equal(forkMidRes.exit, 0, forkMidRes.stderr);
  assert.equal(forkMidTurns.length, 2);
  assert.deepEqual(forkMidTurns[0].args, ['-i', 'chart.png', 'fork', forkUuid]);
  assert.deepEqual(forkMidTurns[1].args, ['resume', '-i', 'chart.png', childUuid]);

  // 6. Fix #5b: `pdd accounts accept` leases/materializes when active pass is expired/missing, AND surfaces warning when lease sync fails!
  const sharedClaude2 = {
    account_id: 'acc_cl_shared_2',
    label: 'cl-invite-2',
    provider: 'claude',
    plan: 'max',
    is_owner: false,
    shared: true,
    state: 'ready',
    five_hour_used_percent: 5,
    five_hour_reset_at: '2026-11-18T02:00:00Z',
    weekly_used_percent: 10,
    weekly_reset_at: '2026-11-23T00:00:00Z',
  };
  cloud.state.pendingInvites.push({ invite_id: 'inv_warn_1', account_id: 'acc_cl_shared_2', provider: 'claude', account: sharedClaude2 });
  cloud.state.leaseOverrideState = 'error_500';
  const acceptWarnRes = await invokeCli(['accounts', 'accept', 'inv_warn_1'], sb);
  cloud.state.leaseOverrideState = null;
  assert.equal(acceptWarnRes.exit, 0);
  assert.match(acceptWarnRes.stdout, /Accepted shared account "cl-invite-2"\. Warning: initial local sync failed .* — run pdd accounts use cl-invite-2\./);

  // Now seed an EXPIRED active Claude entry in accounts-state.json with missing token on disk, and verify `accept` re-leases & materializes!
  const stExpired = JSON.parse(readFileSync(statePath, 'utf8'));
  stExpired.active.claude = {
    account_id: 'acc_cl_old_expired',
    label: 'cl-old',
    provider: 'claude',
    state: 'ready',
    expires_at: new Date(cloud.state.nowMs - 60_000).toISOString(),
  };
  writeFileSync(statePath, JSON.stringify(stExpired, null, 2));
  rmSync(clSettingsPath, { force: true });

  const sharedClaude3 = {
    account_id: 'acc_cl_shared_3',
    label: 'cl-invite-3',
    provider: 'claude',
    plan: 'max',
    is_owner: false,
    shared: true,
    state: 'ready',
    five_hour_used_percent: 5,
    five_hour_reset_at: '2026-11-18T02:00:00Z',
    weekly_used_percent: 10,
    weekly_reset_at: '2026-11-23T00:00:00Z',
  };
  cloud.state.pendingInvites.push({ invite_id: 'inv_ok_3', account_id: 'acc_cl_shared_3', provider: 'claude', account: sharedClaude3 });
  const acceptOkRes = await invokeCli(['accounts', 'accept', 'inv_ok_3'], sb);
  assert.equal(acceptOkRes.exit, 0, acceptOkRes.stderr);
  assert.equal(acceptOkRes.stdout.trim(), 'Accepted shared account "cl-invite-3".');
  assert.equal(existsSync(clSettingsPath), false, 'accept must never mutate ~/.claude/settings.json');
  assert.match(JSON.parse(readFileSync(managedClSettingsPath, 'utf8')).env.CLAUDE_CODE_OAUTH_TOKEN, /^pddg_cl_shared_/);
});

test('#3567 & #3539: in-place refresh preserves shares message, idempotent already_shared share, human list hides redundant pending invites, and non-TTY codex forwards stdout/stderr', async t => {
  const cloud = await createPoolGatewayServer(t, {
    accounts: [
      {
        account_id: 'acc_cx_refresh_1',
        label: 'cx-refresh',
        provider: 'codex',
        plan: 'pro',
        is_owner: true,
        shared: true,
        state: 'ready',
        five_hour_used_percent: 10,
        five_hour_reset_at: '2026-11-18T02:00:00Z',
        weekly_used_percent: 20,
        weekly_reset_at: '2026-11-23T00:00:00Z',
      },
    ],
  });
  const sb = makeSandbox(t, cloud.serverUrl);
  const origEnroll = cloud.state.accounts[0];

  // 1. In-place credential refresh clarifies that existing shares remain active.
  const cxDir = join(sb.root, 'cx-src');
  mkdirSync(cxDir, { recursive: true });
  writeFileSync(join(cxDir, 'auth.json'), JSON.stringify({
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: {
      access_token: makeJwt({ exp: Math.floor(Date.now() / 1000) + 3600 }),
      refresh_token: 'rt_refresh_01',
      id_token: makeJwt({ email: 'owner-refresh@example.com' }),
      account_id: 'acc-refresh-1',
    },
  }));
  const reCx = await invokeCli(['accounts', 'import', '--provider', 'codex', '--from', cxDir, '--label', 'cx-refresh'], sb, {
    fetch: async (url, init) => {
      if (String(url).endsWith('/v1/accounts') && (init?.method || 'GET') === 'POST') {
        return {
          ok: true,
          status: 200,
          text: async () => JSON.stringify({ account: origEnroll, already_enrolled: true }),
        };
      }
      return fetch(url, init);
    },
  });
  assert.equal(reCx.exit, 0, reCx.stderr);
  assert.match(reCx.stdout, /Already enrolled as cx-refresh — refreshed credentials\. Existing shares remain active\./);

  // 2. Idempotent server already_shared=true response on `pdd accounts share` reports clearly without expecting an invite ID.
  const shareRes = await invokeCli(['accounts', 'share', 'cx-refresh', '--with', 'teammate'], sb, {
    resolveGithubUser: async login => ({ login, id: 4242, type: 'User' }),
    fetch: async (url, init) => {
      if (String(url).includes('/share') && (init?.method || 'GET') === 'POST') {
        return {
          ok: true,
          status: 200,
          text: async () => JSON.stringify({ account: origEnroll, invite: null, invite_id: null, already_shared: true }),
        };
      }
      return fetch(url, init);
    },
  });
  assert.equal(shareRes.exit, 0, shareRes.stderr);
  assert.match(shareRes.stdout, /already shared with teammate/i);

  // 3. `pdd accounts list` human-readable output hides redundant pending invites for accounts already in `accounts`,
  //    while `--json` preserves the raw API `pending_invites` array.
  cloud.state.pendingInvites.push(
    { invite_id: 'inv_redundant_1', account_id: origEnroll.account_id, label: 'cx-refresh', provider: 'codex', owner_login: 'owner' },
    { invite_id: 'inv_fresh_2', account_id: 'acc_brand_new_99', label: 'cx-new', provider: 'codex', owner_login: 'other-owner' },
  );
  const listHuman = await invokeCli(['accounts', 'list'], sb);
  assert.equal(listHuman.exit, 0, listHuman.stderr);
  assert.doesNotMatch(listHuman.stdout, /inv_redundant_1/, 'redundant invite must be hidden in human output');
  assert.match(listHuman.stdout, /inv_fresh_2/, 'non-redundant pending invite must still be shown');
  const listJson = await invokeCli(['accounts', 'list', '--json'], sb);
  assert.equal(listJson.exit, 0, listJson.stderr);
  const parsedJson = JSON.parse(listJson.stdout);
  assert.equal(parsedJson.pending_invites.some(i => i.invite_id === 'inv_redundant_1'), true);
  assert.equal(parsedJson.pending_invites.some(i => i.invite_id === 'inv_fresh_2'), true);

  // 4. Non-TTY `pdd accounts codex` (runPlainCodexOnce) forwards Buffer stdout/stderr and maps signal exits to non-zero.
  const codexRes = await invokeCli(['accounts', 'codex', '--version'], sb, {
    run: async (_cmd, _args) => ({
      code: 0,
      stdout: Buffer.from('codex-cli 0.170.0\n'),
      stderr: Buffer.from('warn-line\n'),
    }),
  });
  assert.equal(codexRes.exit, 0, codexRes.stderr);
  assert.equal(codexRes.stdout, 'codex-cli 0.170.0\n');
  assert.equal(codexRes.stderr, 'warn-line\n');

  const sigRes = await invokeCli(['accounts', 'codex', '--version'], sb, {
    run: async () => ({ code: null, signal: 'SIGTERM', stdout: '', stderr: '' }),
  });
  assert.equal(sigRes.exit, 143, 'signal exit must never map to 0');

  // 5. Real subprocess non-TTY path (managed `exec` passthrough + unenrolled fallback) streams piped stdin, stdout, stderr, non-zero exit codes, and SIGTERM -> 143.
  const { Readable } = await import('node:stream');
  const fakeBinDir = join(sb.root, 'fake-codex-bin');
  mkdirSync(fakeBinDir, { recursive: true });
  const fakeCodexPath = join(fakeBinDir, 'codex');
  writeFileSync(fakeCodexPath, `#!/bin/sh
if [ "$1" = "exec" ]; then shift; fi
case "$1" in
  --pipe-test)
    read line || line="EOF"
    printf 'OUT:%s|%s\\n' "$line" "$CODEX_HOME"
    printf 'ERR:%s\\n' "$line" >&2
    exit 0
    ;;
  --exit-42)
    printf 'bad-out\\n'
    printf 'bad-err\\n' >&2
    exit 42
    ;;
  --sigterm)
    kill -TERM $$
    sleep 1
    ;;
esac
`);
  chmodSync(fakeCodexPath, 0o755);
  const shimSb = { ...sb, env: { ...sb.env, PATH: `${fakeBinDir}:${sb.env.PATH ?? process.env.PATH ?? ''}` } };

  const pipeRes = await invokeCli(['accounts', 'codex', 'exec', '--pipe-test'], shimSb, {
    stdin: Readable.from(['hello-from-stdin\n']),
  });
  assert.equal(pipeRes.exit, 0, pipeRes.stderr);
  assert.equal(pipeRes.stdout, `OUT:hello-from-stdin|${pddManagedCodexHome(sb.env)}\n`);
  assert.equal(pipeRes.stderr, 'ERR:hello-from-stdin\n');

  const strStdinRes = await invokeCli(['accounts', 'codex', 'exec', '--pipe-test'], shimSb, {
    stdin: 'hello-from-string\n',
  });
  assert.equal(strStdinRes.exit, 0, strStdinRes.stderr);
  assert.equal(strStdinRes.stdout, `OUT:hello-from-string|${pddManagedCodexHome(sb.env)}\n`);

  const eofStdinRes = await invokeCli(['accounts', 'codex', 'exec', '--pipe-test'], shimSb, {
    stdin: '',
  });
  assert.equal(eofStdinRes.exit, 0, eofStdinRes.stderr);
  assert.equal(eofStdinRes.stdout, `OUT:EOF|${pddManagedCodexHome(sb.env)}\n`);

  const exit42Res = await invokeCli(['accounts', 'codex', 'exec', '--exit-42'], shimSb);
  assert.equal(exit42Res.exit, 42);
  assert.equal(exit42Res.stdout, 'bad-out\n');
  assert.equal(exit42Res.stderr, 'bad-err\n');

  const realSigRes = await invokeCli(['accounts', 'codex', 'exec', '--sigterm'], shimSb);
  assert.equal(realSigRes.exit, 143);

  // Missing `codex` binary on PATH reports clear error instead of silent empty stderr.
  const emptyBinDir = join(sb.root, 'empty-bin');
  mkdirSync(emptyBinDir, { recursive: true });
  const missingBinSb = { ...sb, env: { ...sb.env, PATH: emptyBinDir } };
  const enoentRes = await invokeCli(['accounts', 'codex', 'exec', '--pipe-test'], missingBinSb);
  assert.equal(enoentRes.exit, 1);
  assert.match(enoentRes.stderr, /codex CLI not found on PATH/i);

  // Unenrolled fallback path (`!managedHome`) also uses streaming runPlainCodexOnce.
  const unenrolledSb = makeSandbox(t, cloud.serverUrl);
  const unenrolledShimSb = {
    ...unenrolledSb,
    env: { ...unenrolledSb.env, PATH: `${fakeBinDir}:${unenrolledSb.env.PATH ?? process.env.PATH ?? ''}` },
  };
  const fallbackRes = await invokeCli(['accounts', 'codex', '--exit-42'], unenrolledShimSb);
  assert.equal(fallbackRes.exit, 42);
  assert.equal(fallbackRes.stdout, 'bad-out\n');
  assert.equal(fallbackRes.stderr, 'bad-err\n');
});

test('SEC-5, SEC-6 & REL-2: atomic auto on/off preserves dotfiles symlinks & mode, detectImportProvider blocks symlinks, and add temp dir avoids /tmp', async t => {
  const cloud = await createPoolGatewayServer(t);
  const sb = makeSandbox(t, cloud.serverUrl);

  // 1. SEC-5: Stow/chezmoi symlinked ~/.zshrc with custom 0o600 permissions survives `auto on` AND `auto off` intact!
  const dotfilesDir = join(sb.root, 'dotfiles');
  mkdirSync(dotfilesDir, { recursive: true, mode: 0o700 });
  const realZshrc = join(dotfilesDir, '.zshrc');
  writeFileSync(realZshrc, '# user zshrc\nexport FOO=bar\n', { mode: 0o600 });
  chmodSync(realZshrc, 0o600);
  const homeZshrc = join(sb.home, '.zshrc');
  symlinkSync(realZshrc, homeZshrc);

  const onRes = await invokeCli(['accounts', 'auto', 'on'], sb);
  assert.equal(onRes.exit, 0, onRes.stderr);
  assert.equal(lstatSync(homeZshrc).isSymbolicLink(), true, 'auto on must preserve ~/.zshrc symlink');
  assert.equal(statSync(realZshrc).mode & 0o777, 0o600, 'auto on must preserve target file permissions');
  assert.match(readFileSync(realZshrc, 'utf8'), /# >>> pdd accounts auto >>>/);

  const offRes = await invokeCli(['accounts', 'auto', 'off'], sb);
  assert.equal(offRes.exit, 0, offRes.stderr);
  assert.equal(lstatSync(homeZshrc).isSymbolicLink(), true, 'auto off must preserve ~/.zshrc symlink');
  assert.equal(statSync(realZshrc).mode & 0o777, 0o600, 'auto off must preserve target file permissions');
  assert.doesNotMatch(readFileSync(realZshrc, 'utf8'), /# >>> pdd accounts auto >>>/);
  assert.match(readFileSync(realZshrc, 'utf8'), /export FOO=bar/);

  // 2. SEC-6: detectImportProvider refuses symlinked --from file, dir, parent dir, and child file with symlink_refused.
  const secretSource = join(sb.root, 'real-secret.json');
  writeFileSync(secretSource, JSON.stringify({ tokens: { access_token: 'a', refresh_token: 'r', id_token: 'i', account_id: 'acct' } }), { mode: 0o600 });
  const symFromFile = join(sb.root, 'sym-from.json');
  symlinkSync(secretSource, symFromFile);
  const nativeFs = await import('node:fs');
  assert.throws(
    () => detectImportProvider(nativeFs, sb.env, { fromOption: symFromFile }),
    err => err instanceof CloudAccountsError && err.code === 'symlink_refused',
  );

  const realDir = join(sb.root, 'real-import-dir');
  mkdirSync(realDir, { recursive: true, mode: 0o700 });
  writeFileSync(join(realDir, 'auth.json'), readFileSync(secretSource));
  const symFromDir = join(sb.root, 'sym-import-dir');
  symlinkSync(realDir, symFromDir);
  assert.throws(
    () => detectImportProvider(nativeFs, sb.env, { fromOption: symFromDir }),
    err => err instanceof CloudAccountsError && err.code === 'symlink_refused',
  );
  assert.throws(
    () => detectImportProvider(nativeFs, sb.env, { fromOption: join(symFromDir, 'auth.json') }),
    err => err instanceof CloudAccountsError && err.code === 'symlink_refused',
  );

  const dirWithSymChild = join(sb.root, 'dir-with-sym-child');
  mkdirSync(dirWithSymChild, { recursive: true, mode: 0o700 });
  symlinkSync(secretSource, join(dirWithSymChild, 'auth.json'));
  assert.throws(
    () => detectImportProvider(nativeFs, sb.env, { fromOption: dirWithSymChild }),
    err => err instanceof CloudAccountsError && err.code === 'symlink_refused',
  );

  // Root-owned system symlink parent (e.g. macOS /tmp -> /private/tmp) is permitted for a regular target file,
  // while a symlinked target itself inside /tmp is still refused.
  const rootParentFs = {
    ...nativeFs,
    lstatSync(p) {
      if (p === symFromDir) {
        return { isSymbolicLink: () => true, isDirectory: () => false, isFile: () => false, uid: 0 };
      }
      if (p === join(symFromDir, 'auth.json')) {
        return { isSymbolicLink: () => false, isDirectory: () => false, isFile: () => true, uid: 501 };
      }
      return nativeFs.lstatSync(p);
    },
  };
  assert.equal(detectImportProvider(rootParentFs, sb.env, { fromOption: join(symFromDir, 'auth.json') }), 'codex');

  // 3. REL-2: `pdd accounts add` allocates temporary CODEX_HOME under resolvePddStateBase(env)/codex-runtime (never /tmp).
  let capturedTmpCodexHome = null;
  const addRes = await invokeCli(['accounts', 'add', '--provider', 'codex', '--label', 'rel2-seat'], sb, {
    run: async (cmd, _args, opts) => {
      assert.equal(cmd, 'codex');
      capturedTmpCodexHome = opts.env.CODEX_HOME;
      writeFileSync(join(capturedTmpCodexHome, 'auth.json'), JSON.stringify({
        auth_mode: 'chatgpt',
        tokens: {
          access_token: 'acc_rel2',
          refresh_token: 'ref_rel2',
          id_token: makeJwt({ email: 'rel2@example.com' }),
          account_id: 'acct_rel2',
        },
      }), { mode: 0o600 });
      return { code: 0, stdout: 'Logged in\n', stderr: '' };
    },
    probeCodexUsage: async () => null,
    spawnSync: () => ({ status: 0 }),
  });
  assert.equal(addRes.exit, 0, addRes.stderr);
  const expectedRuntimeRoot = join(resolvePddStateBase(sb.env), 'codex-runtime');
  assert.ok(
    capturedTmpCodexHome && capturedTmpCodexHome.startsWith(`${expectedRuntimeRoot}/`),
    `expected add temp CODEX_HOME under ${expectedRuntimeRoot}, got ${capturedTmpCodexHome}`,
  );
  assert.equal(existsSync(capturedTmpCodexHome), false, 'temp CODEX_HOME cleaned up after add');
});
