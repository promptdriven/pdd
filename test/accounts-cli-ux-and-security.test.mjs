import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { EventEmitter } from 'node:events';
import http from 'node:http';
import { PassThrough } from 'node:stream';
import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  realpathSync,
  rmSync,
  statSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { renderAutoSwitchBlock } from '../src/accounts-cli.mjs';
import {
  managedCodexAuthPath,
  managedCodexConfigPath,
  pddManagedCodexHome,
} from '../src/login-pool.mjs';
import { parse as parseToml } from '../src/vendor/smol-toml/parse.js';

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
    failNextPostAccountsStatus: 0,
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
        five_hour_used_percent: 5,
        five_hour_reset_at: '2026-11-18T01:00:00Z',
        weekly_used_percent: 12,
        weekly_reset_at: '2026-11-22T00:00:00Z',
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
        if (body?.github_login) {
          acc.shares = acc.shares ?? [];
          acc.shares.push({ github_login: body.github_login, github_user_id: body.github_user_id ?? null, state: 'pending' });
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

    const delMatch = /^\/v1\/accounts\/([^/]+)$/.exec(url.pathname);
    if (req.method === 'DELETE' && delMatch) {
      const id = decodeURIComponent(delMatch[1]);
      const acc = state.accounts.find(a => a.account_id === id);
      if (!acc) return send(404, { detail: 'Not found' });
      acc.revoked = true;
      return send(200, { deleted: true });
    }

    return send(404, { detail: `Unhandled ${req.method} ${url.pathname}` });
  });

  await new Promise(r => server.listen(0, '127.0.0.1', r));
  t.after(() => server.close());
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
  const auth1 = JSON.parse(readFileSync(authPath, 'utf8'));
  assert.equal(auth1.auth_mode, 'apikey');
  assert.match(auth1.OPENAI_API_KEY, /^pddg_lse_[0-9a-f]+_/);
  assert.equal(auth1.tokens, undefined, 'zero raw OAuth tokens in auth.json');

  const configTextBeforeSwitch = readFileSync(configPath, 'utf8');
  const configInodeBeforeSwitch = statSync(configPath).ino;
  const parsedCfg = parseToml(configTextBeforeSwitch);
  assert.equal(parsedCfg.model_provider, 'pdd_codex_gateway');
  assert.equal(parsedCfg.model_providers.pdd_codex_gateway.base_url, `${cloud.serverUrl}/v1/codex-gateway`);
  assert.equal(parsedCfg.model_providers.pdd_codex_gateway.requires_openai_auth, true);
  assert.equal(parsedCfg.model_providers.pdd_codex_gateway.http_headers, undefined);

  const nextRes = await invokeCli(['accounts', 'next', '--provider', 'codex'], sb);
  assert.equal(nextRes.exit, 0, nextRes.stderr);
  const auth2 = JSON.parse(readFileSync(authPath, 'utf8'));
  assert.notEqual(auth2.OPENAI_API_KEY, auth1.OPENAI_API_KEY, 'auth.json rotated to new lease grant token');
  assert.match(auth2.OPENAI_API_KEY, /^pddg_lse_[0-9a-f]+_/);
  assert.equal(readFileSync(configPath, 'utf8'), configTextBeforeSwitch, 'config.toml bytes remain 100% constant across switches');
  assert.equal(statSync(configPath).ino, configInodeBeforeSwitch, 'config.toml was not rewritten when unchanged');

  // Verify zero-plaintext fallback when post-enroll `/v1/accounts/lease` returns `all_cooling` or `500`!
  const sbCooling = makeSandbox(t, cloud.serverUrl);
  cloud.state.leaseOverrideState = 'error_500';
  const coolingEnroll = await invokeCli(['accounts', 'add', '--provider', 'codex', '--label', 'glt-offline-lease'], sbCooling, {
    tmpRoot: sbCooling.root,
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
  assert.equal(coolingEnroll.exit, 0, coolingEnroll.stderr);
  assert.equal(existsSync(managedCodexAuthPath(sbCooling.env)), false, 'must never fall back to writing raw OAuth auth.json when lease fails');

  // Backward compatibility: legacy server returning non-`pddg_lse_` token keeps lease-scoped URL + `http_headers`!
  cloud.state.embeddedLeaseTokens = false;
  const legacyUse = await invokeCli(['accounts', 'use', 'glt'], sb);
  assert.equal(legacyUse.exit, 0, legacyUse.stderr);
  const legacyCfg = parseToml(readFileSync(configPath, 'utf8'));
  assert.match(legacyCfg.model_providers.pdd_codex_gateway.base_url, /\/v1\/codex-gateway\/lse_[0-9a-f]+$/);
  assert.equal(legacyCfg.model_providers.pdd_codex_gateway.requires_openai_auth, false);
  assert.match(legacyCfg.model_providers.pdd_codex_gateway.http_headers['x-pdd-gateway-grant'], /^pddg_legacy_/);
});

test('#3497 Part 2: pdd accounts codex & shell auto wrapper perform live mid-session quota rotation and resume seamlessly', async t => {
  // 1. Shell wrapper blocks (`sh` and `fish`) delegate interactive TTY codex sessions to `pdd accounts codex -- "$@"`!
  const shWrapper = renderAutoSwitchBlock('sh');
  const fishWrapper = renderAutoSwitchBlock('fish');
  assert.match(shWrapper, /pdd accounts codex -- "\$@"/);
  assert.match(fishWrapper, /pdd accounts codex -- \$argv/);

  // 2. Live mid-session quota exhaustion rotates `auth.json` to next ready account and relaunches `codex resume <session-id>`!
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
  assert.equal((await invokeCli(['accounts', 'use', 'glt'], sb)).exit, 0);

  const authPath = managedCodexAuthPath(sb.env);
  const configPath = managedCodexConfigPath(sb.env);
  const configSnapshot = readFileSync(configPath, 'utf8');
  const firstGrant = JSON.parse(readFileSync(authPath, 'utf8')).OPENAI_API_KEY;

  const capturedSessionUuid = '019a7777-8888-7000-9000-abcdef123456';
  const seenTurns = [];

  const liveRes = await invokeCli(
    ['accounts', 'codex', '--', '-m', 'gpt-5.4', 'refactor parser'],
    sb,
    {
      quotaSettleMs: 0,
      async spawnCodexPty({ args, env, turn, signal, onOutput }) {
        const activeGrantOnDisk = JSON.parse(readFileSync(join(env.CODEX_HOME, 'auth.json'), 'utf8')).OPENAI_API_KEY;
        seenTurns.push({ turn, args, codexHome: env.CODEX_HOME, grant: activeGrantOnDisk });
        if (turn === 0) {
          onOutput(`Codex session started (session id: ${capturedSessionUuid})\nWorking on refactor...\n`);
          onOutput('\x1b[31mError: You\'ve hit your usage limit (usage_limit_reached). Resets at 2026-11-18T01:30:00Z.\x1b[0m\n');
          assert.equal(signal.aborted, true, 'supervisor immediately aborts exhausted interactive turn');
          return { code: 1, signal: 'SIGTERM' };
        }
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
  assert.match(liveRes.stderr, /Quota reached on "glt"; switched active Codex account to "glt-oai2" and resuming/);

  const usageReports = cloud.state.requests.filter(r => r.method === 'POST' && r.path === '/v1/accounts/acc_live_1/usage-report');
  assert.equal(usageReports.length, 1);
  assert.equal(usageReports[0].body.limit_reached, true);
  assert.equal(usageReports[0].body.five_hour_used_percent, 100);
  assert.equal(usageReports[0].body.five_hour_reset_at, '2026-11-18T01:00:00Z');

  // 3. Disk rollout UUID discovery when TUI emits no session ID to stdout!
  cloud.state.accounts[0].state = 'ready';
  cloud.state.accounts[0].five_hour_used_percent = 5;
  assert.equal((await invokeCli(['accounts', 'use', 'glt'], sb)).exit, 0);

  const rolloutUuid = '019a9999-1111-7222-8333-fedcba654321';
  const rolloutTurns = [];
  const rolloutRes = await invokeCli(['accounts', 'codex'], sb, {
    quotaSettleMs: 0,
    async spawnCodexPty({ args, env, turn, onOutput }) {
      rolloutTurns.push({ turn, args });
      if (turn === 0) {
        const dayDir = join(env.CODEX_HOME, 'sessions', '2026', '11', '17');
        mkdirSync(dayDir, { recursive: true });
        writeFileSync(join(dayDir, `rollout-2026-11-17T20-00-00-${rolloutUuid}.jsonl`), '{"type":"session_meta"}\n');
        onOutput('Error: usage_limit_reached — quota exceeded for current window.\n');
        return { code: 1, signal: 'SIGTERM' };
      }
      return { code: 0, signal: null };
    },
  }, { isTTY: true });

  assert.equal(rolloutRes.exit, 0, rolloutRes.stderr);
  assert.equal(rolloutTurns.length, 2);
  assert.deepEqual(rolloutTurns[1].args, ['resume', rolloutUuid], 'discovered active session UUID from sessions rollout file');

  // 4. `--last` fallback when neither stdout nor disk rollout files contain a session UUID!
  rmSync(join(pddManagedCodexHome(sb.env), 'sessions'), { recursive: true, force: true });
  cloud.state.accounts[0].state = 'ready';
  cloud.state.accounts[0].five_hour_used_percent = 5;
  cloud.state.accounts[1].state = 'ready';
  cloud.state.accounts[1].five_hour_used_percent = 5;
  assert.equal((await invokeCli(['accounts', 'use', 'glt'], sb)).exit, 0);

  const fallbackTurns = [];
  const fallbackRes = await invokeCli(['accounts', 'codex', '--', '--search'], sb, {
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
  assert.deepEqual(fallbackTurns[1].args, ['resume', '--search', '--last'], 'falls back to resume --last preserving flags when no UUID was captured');
});
