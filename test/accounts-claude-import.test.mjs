import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import http from 'node:http';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runPdd } from '../src/pdd-cli.mjs';
import {
  detectImportProvider,
  readClaudeTokenFromPath,
  readLocalClaudeToken,
} from '../src/accounts-cli.mjs';
import { CloudAccountsError } from '../src/login-pool.mjs';
import { redactSecrets } from '../src/secret-redaction.mjs';

function sink() {
  return {
    text: '',
    write(chunk) {
      this.text += String(chunk);
      return true;
    },
  };
}

async function startFakeCloud(t, nowMs) {
  const requests = [];
  let seq = 1;
  const server = http.createServer((req, res) => {
    const chunks = [];
    req.on('data', c => chunks.push(c));
    req.on('end', () => {
      const raw = Buffer.concat(chunks).toString('utf8');
      const body = raw ? JSON.parse(raw) : null;
      const url = new URL(req.url, 'http://127.0.0.1');
      requests.push({ method: req.method, path: url.pathname, body });

      const send = (status, payload) => {
        res.writeHead(status, { 'content-type': 'application/json' });
        res.end(JSON.stringify(payload));
      };

      if (req.method === 'GET' && url.pathname === '/v1/accounts') {
        return send(200, { accounts: [] });
      }
      if (req.method === 'POST' && url.pathname === '/v1/accounts') {
        const id = `acc_${seq++}`;
        return send(201, {
          account: {
            account_id: id,
            label: body.label,
            provider: body.provider,
            plan: body.plan ?? 'max',
            is_owner: true,
            state: 'ready',
            five_hour_used_percent: 5,
            weekly_used_percent: 10,
          },
        });
      }
      if (req.method === 'POST' && url.pathname === '/v1/accounts/lease') {
        const label = body?.preferred_label ?? 'claude-main';
        return send(200, {
          state: 'leased',
          switched: false,
          account: {
            account_id: 'acc_leased',
            label,
            provider: 'claude',
            state: 'ready',
            five_hour_used_percent: 5,
            weekly_used_percent: 10,
          },
          lease: {
            lease_id: `lse_${seq++}`,
            expires_at: new Date(nowMs + 45 * 60_000).toISOString(),
            delivery_mode: 'direct_oauth',
            claude_oauth_token: `sk-ant-oat01-${label}-fakeLeasedToken0000`,
          },
        });
      }
      return send(404, { detail: 'not_found' });
    });
  });

  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  t.after(() => server.close());
  const addr = server.address();
  return { serverUrl: `http://127.0.0.1:${addr.port}`, requests };
}

function makeSandbox(t, serverUrl) {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-claude-creds-3483-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const home = join(root, 'home');
  const stateDir = join(root, 'state');
  const cwd = join(root, 'cwd');
  fs.mkdirSync(home, { recursive: true });
  fs.mkdirSync(stateDir, { recursive: true });
  fs.mkdirSync(cwd, { recursive: true });
  return {
    root,
    home,
    stateDir,
    cwd,
    env: {
      HOME: home,
      PDD_STATE_DIR: stateDir,
      PDD_CLOUD_URL: serverUrl,
      GH_TOKEN: 'ghu_fakeCloudAuthToken000000',
      PATH: process.env.PATH,
    },
  };
}

async function runCli(argv, sb, accountsPorts = {}) {
  const stdout = sink();
  const stderr = sink();
  const exit = await runPdd(argv, {
    cwd: sb.cwd,
    env: sb.env,
    stdout,
    stderr,
    accountsPorts,
  });
  return { exit, stdout: stdout.text, stderr: stderr.text };
}

const addArgs = ['accounts', 'add', '--provider', 'claude'];
const enrollmentScenario = JSON.parse(fs.readFileSync(new URL('./runtime/accounts-claude-add.json', import.meta.url)));
const wrappedLogin = enrollmentScenario.simulation['login.run'].result_template;
const completeToken = JSON.parse(enrollmentScenario.steps[0].checks[0].value);

test('3495: Claude add sends the whole token after a colored 80-column wrap, without joining the next status line', async t => {
  const sb = makeSandbox(t, 'https://cloud.example');
  const requests = [];
  const result = await runCli(addArgs, sb, {
    tmpRoot: sb.root,
    runLogin: async () => wrappedLogin,
    fetch: async (url, request) => {
      requests.push({ url, ...request });
      const reply = enrollmentScenario.simulation['cloud.fetch'].result_template;
      return new Response(reply.text, { status: reply.status });
    },
  });
  assert.match(result.stderr, /synthetic fixture stops after the enrollment request/);
  assert.equal(requests[0]?.method, enrollmentScenario.steps[0].checks[1].value);
  assert.equal(JSON.parse(requests[0]?.body).bundle.oauth_token, completeToken);
  assert.doesNotMatch(result.stderr, /sk-ant-oat/);
});

test('3495: Claude add refuses stale tokens from stdout alternatives and cleans the isolated config', async t => {
  const cloud = await startFakeCloud(t, Date.now());
  const sb = makeSandbox(t, cloud.serverUrl);
  const localDir = join(sb.home, '.claude');
  const settingsPath = join(localDir, 'settings.json');
  const settings = JSON.stringify({ env: { CLAUDE_CODE_OAUTH_TOKEN: 'sk-ant-oat01-synthetic-saved-settings-2222' } });
  fs.mkdirSync(localDir);
  fs.writeFileSync(settingsPath, settings);
  fs.writeFileSync(join(localDir, '.credentials.json'), JSON.stringify({ claudeAiOauth: { accessToken: 'sk-ant-oat01-synthetic-saved-credentials-3333' } }));
  const missingTokenStep = enrollmentScenario.steps[1];
  sb.env.CLAUDE_CODE_OAUTH_TOKEN = missingTokenStep.input.env.CLAUDE_CODE_OAUTH_TOKEN;
  let loginEnv;
  let loginDirMode;
  const result = await runCli(addArgs, sb, {
    tmpRoot: sb.root,
    runLogin: async (provider, { env }) => {
      assert.equal(provider, 'claude');
      loginEnv = env;
      if (env.CLAUDE_CONFIG_DIR) {
        loginDirMode = fs.statSync(env.CLAUDE_CONFIG_DIR).mode & 0o777;
        fs.writeFileSync(join(env.CLAUDE_CONFIG_DIR, 'settings.json'), settings);
      }
      return missingTokenStep.simulation_overrides[0].binding.result_template;
    },
  });
  assert.equal(result.exit, missingTokenStep.checks[0].value, 'an existing token must not make setup succeed');
  assert.match(result.stderr, /claude setup-token did not print a Claude OAuth token/);
  assert.equal(cloud.requests.length, 0);
  assert.equal(fs.readFileSync(settingsPath, 'utf8'), settings);
  assert.equal(loginEnv.CLAUDE_CODE_OAUTH_TOKEN, undefined);
  assert.equal(loginDirMode, 0o700);
  assert.equal(fs.existsSync(loginEnv.CLAUDE_CONFIG_DIR), false);
});

const hasScriptPty = process.platform === 'linux' && spawnSync('script', ['--version']).status === 0;
for (const { label, loop, cancel = false } of [
  { label: 'single shows live setup prompts and accepts pasted input', loop: false },
  { label: '--loop shows live setup prompts and accepts pasted input for each account', loop: true },
  { label: '--loop cleans up when the setup prompt is interrupted', loop: true, cancel: true },
]) {
  test(`3495: Claude add ${label} in a real TTY`, { skip: !hasScriptPty, timeout: 10_000 }, async t => {
    const cloud = await startFakeCloud(t, Date.now());
    const sb = makeSandbox(t, cloud.serverUrl);
    const fakeClaude = join(sb.root, 'claude');
    const loginDirs = join(sb.root, 'login-dirs');
    fs.writeFileSync(fakeClaude, `#!${process.execPath}
const fs = require('node:fs');
const readline = require('node:readline');
if (process.argv[2] !== 'setup-token' || !process.stdin.isTTY) process.exit(2);
const dir = process.env.CLAUDE_CONFIG_DIR;
if (!dir || process.env.COLUMNS !== '500' || (fs.statSync(dir).mode & 0o777) !== 0o700) process.exit(3);
fs.appendFileSync(process.env.LOGIN_DIRS, dir + '\\n');
process.stdout.write('Open the browser sign-in link\\n');
process.stderr.write('Paste code here if prompted > ');
const input = readline.createInterface({ input: process.stdin });
input.once('line', value => {
  input.close();
  if (value !== 'mock-authorization-code') { process.exitCode = 4; return; }
  process.stdout.write(${JSON.stringify(wrappedLogin.stdout)});
});
`, { mode: 0o700 });

    const child = spawn('script', ['-q', '-e', '-c', `exec "$TEST_NODE" "$TEST_PDD" ${addArgs.join(' ')}${loop ? ' --loop' : ''}`, '/dev/null'], {
      cwd: sb.cwd,
      env: {
        ...sb.env,
        PATH: `${sb.root}:${sb.env.PATH}`,
        TERM: 'xterm',
        TEST_NODE: process.execPath,
        TEST_PDD: fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url)),
        LOGIN_DIRS: loginDirs,
      },
    });
    t.after(() => child.kill());
    let transcript = '';
    let cursor = 0;
    const paste = ['Paste code here if prompted > ', cancel ? '\x03' : 'mock-authorization-code\n'];
    const replies = loop && !cancel ? [paste, ['Enroll another claude account? [Y/n] ', 'y\n'], paste, ['Enroll another claude account? [Y/n] ', 'n\n']] : [paste];
    child.stdout.on('data', chunk => {
      transcript += chunk;
      if (!replies.length) return;
      const [prompt, answer] = replies[0];
      const promptIndex = transcript.indexOf(prompt, cursor);
      if (promptIndex === -1) return;
      cursor = promptIndex + prompt.length;
      replies.shift();
      child.stdin.write(answer);
    });
    const exitCode = await new Promise((resolve, reject) => {
      child.once('error', reject);
      child.once('close', resolve);
    });
    assert.match(transcript, /Paste code here if prompted > /, 'the setup prompt must reach the TTY before responding');
    assert.match(transcript, /Open the browser sign-in link/);
    assert.equal(exitCode, 0, transcript);
    assert.equal(replies.length, 0);
    if (cancel) assert.match(transcript, /Loop finished with 0 claude accounts enrolled/);
    const uploads = cloud.requests.filter(({ method, path }) => method === 'POST' && path === '/v1/accounts');
    assert.deepEqual(uploads.map(({ body }) => body.bundle.oauth_token), Array(cancel ? 0 : loop ? 2 : 1).fill(completeToken));
    const usedDirs = fs.readFileSync(loginDirs, 'utf8').trim().split('\n');
    assert.equal(new Set(usedDirs).size, cancel ? 1 : uploads.length);
    assert.ok(usedDirs.every(dir => !fs.existsSync(dir)));
  });
}

test('3483: --from <dir> and default local ~/.claude fall back to .credentials.json when settings.json has no token or is absent', async t => {
  const fixedNowMs = Date.parse('2026-11-17T08:00:00Z');
  const cloud = await startFakeCloud(t, fixedNowMs);
  const sb = makeSandbox(t, cloud.serverUrl);

  // 1. --from <dir> where settings.json exists without CLAUDE_CODE_OAUTH_TOKEN and .credentials.json has valid numeric expiresAt
  const extDir = join(sb.root, 'claude-profile-1');
  fs.mkdirSync(extDir, { recursive: true });
  fs.writeFileSync(join(extDir, 'settings.json'), JSON.stringify({ theme: 'dark', env: { UNRELATED_FLAG: '1' } }));
  const fakeAccess1 = 'sk-ant-oat01-fakeValidShortLivedAccess11111';
  const fakeRefresh1 = 'sk-ant-ort01-fakeValidRefreshSecret11111';
  fs.writeFileSync(join(extDir, '.credentials.json'), JSON.stringify({
    claudeAiOauth: {
      accessToken: fakeAccess1,
      refreshToken: fakeRefresh1,
      expiresAt: fixedNowMs + 3_600_000,
    },
  }));

  const imp1 = await runCli(
    ['accounts', 'import', '--provider', 'claude', '--from', extDir, '--label', 'from-creds-dir'],
    sb,
    { now: () => fixedNowMs },
  );
  assert.equal(imp1.exit, 0, imp1.stderr);
  assert.match(imp1.stdout, /Enrolled Claude account "from-creds-dir"/);

  const upload1 = cloud.requests.find(r => r.method === 'POST' && r.path === '/v1/accounts' && r.body?.label === 'from-creds-dir');
  assert.ok(upload1, 'uploaded valid .credentials.json accessToken to Cloud');
  assert.equal(upload1.body.bundle.oauth_token, fakeAccess1);

  assert.equal(redactSecrets(`seen ${fakeAccess1} and ${fakeRefresh1}`), 'seen [redacted] and [redacted]');
  assert.ok(!imp1.stdout.includes(fakeAccess1) && !imp1.stderr.includes(fakeAccess1));
  assert.ok(!imp1.stdout.includes(fakeRefresh1) && !imp1.stderr.includes(fakeRefresh1));

  // 2. --from <dir> where settings.json does NOT exist (ENOENT) and .credentials.json has a valid token
  const noSettingsDir = join(sb.root, 'claude-no-settings-dir');
  fs.mkdirSync(noSettingsDir, { recursive: true });
  const fakeNoSettingsAccess = 'synthetic_no_settings_access_121212';
  fs.writeFileSync(join(noSettingsDir, '.credentials.json'), JSON.stringify({
    claudeAiOauth: {
      accessToken: fakeNoSettingsAccess,
      expiresAt: fixedNowMs + 3_600_000,
    },
  }));
  assert.equal(fs.existsSync(join(noSettingsDir, 'settings.json')), false);
  assert.equal(readClaudeTokenFromPath(fs, noSettingsDir, { now: () => fixedNowMs }), fakeNoSettingsAccess);

  const impNoSettings = await runCli(
    ['accounts', 'import', '--provider', 'claude', '--from', noSettingsDir, '--label', 'no-settings-dir'],
    sb,
    { now: () => fixedNowMs },
  );
  assert.equal(impNoSettings.exit, 0, impNoSettings.stderr);
  const uploadNoSettings = cloud.requests.find(r => r.method === 'POST' && r.path === '/v1/accounts' && r.body?.label === 'no-settings-dir');
  assert.equal(uploadNoSettings?.body?.bundle?.oauth_token, fakeNoSettingsAccess);

  // 3. Default local ~/.claude/.credentials.json with ISO expiresAt when ~/.claude/settings.json has no token
  const sbLocal = makeSandbox(t, cloud.serverUrl);
  const localClaudeDir = join(sbLocal.home, '.claude');
  fs.mkdirSync(localClaudeDir, { recursive: true });
  fs.writeFileSync(join(localClaudeDir, 'settings.json'), JSON.stringify({ theme: 'light' }));
  const fakeAccess2 = 'sk-ant-oat01-fakeLocalIsoAccess22222';
  fs.writeFileSync(join(localClaudeDir, '.credentials.json'), JSON.stringify({
    claudeAiOauth: {
      accessToken: fakeAccess2,
      expiresAt: new Date(fixedNowMs + 7_200_000).toISOString(),
    },
  }));

  const imp2 = await runCli(
    ['accounts', 'import', '--provider', 'claude', '--label', 'local-creds'],
    sbLocal,
    { now: () => fixedNowMs },
  );
  assert.equal(imp2.exit, 0, imp2.stderr);
  const upload2 = cloud.requests.find(r => r.method === 'POST' && r.path === '/v1/accounts' && r.body?.label === 'local-creds');
  assert.equal(upload2?.body?.bundle?.oauth_token, fakeAccess2);

  // 4. expiresAt variants: numeric epoch-ms string (valid), null, and undefined are accepted; explicit bare token file still works
  const variantsDir = join(sb.root, 'expires-variants');
  fs.mkdirSync(variantsDir, { recursive: true });
  for (const [name, oauthPayload, expectedTok] of [
    ['num-str.json', { accessToken: 'synthetic_numstr_tok_232323', expiresAt: String(fixedNowMs + 3_600_000) }, 'synthetic_numstr_tok_232323'],
    ['null-exp.json', { accessToken: 'synthetic_nullexp_tok_242424', expiresAt: null }, 'synthetic_nullexp_tok_242424'],
    ['undef-exp.json', { accessToken: 'synthetic_undefexp_tok_252525' }, 'synthetic_undefexp_tok_252525'],
  ]) {
    const filePath = join(variantsDir, name);
    fs.writeFileSync(filePath, JSON.stringify({ claudeAiOauth: oauthPayload }));
    assert.equal(readClaudeTokenFromPath(fs, filePath, { now: () => fixedNowMs }), expectedTok);
  }
  const bareFile = join(variantsDir, 'bare-token.txt');
  fs.writeFileSync(bareFile, 'synthetic_bare_file_token_262626\n');
  assert.equal(readClaudeTokenFromPath(fs, bareFile, { now: () => fixedNowMs }), 'synthetic_bare_file_token_262626');

  // 5. Long-lived settings.json env.CLAUDE_CODE_OAUTH_TOKEN still wins over stale .credentials.json
  const setupWinDir = join(sb.root, 'claude-setup-token-wins');
  fs.mkdirSync(setupWinDir, { recursive: true });
  const fakeLongLived = 'sk-ant-oat01-fakeLongLivedSetupToken33333';
  fs.writeFileSync(join(setupWinDir, 'settings.json'), JSON.stringify({
    env: { CLAUDE_CODE_OAUTH_TOKEN: fakeLongLived },
  }));
  fs.writeFileSync(join(setupWinDir, '.credentials.json'), JSON.stringify({
    claudeAiOauth: {
      accessToken: 'sk-ant-oat01-fakeStaleIgnoredToken33333',
      expiresAt: fixedNowMs - 60_000,
    },
  }));
  assert.equal(readClaudeTokenFromPath(fs, setupWinDir, { now: () => fixedNowMs }), fakeLongLived);

  // 6. Malformed `{placeholder}` terminal output in readLocalClaudeToken extraText is ignored and falls through cleanly
  const sbExtra = makeSandbox(t, cloud.serverUrl);
  const extraClaudeDir = join(sbExtra.home, '.claude');
  fs.mkdirSync(extraClaudeDir, { recursive: true });
  const envFallbackTok = 'synthetic_env_fallback_token_272727';
  assert.equal(
    readLocalClaudeToken(fs, { ...sbExtra.env, CLAUDE_CODE_OAUTH_TOKEN: envFallbackTok }, '{placeholder}', { now: () => fixedNowMs }),
    envFallbackTok,
  );
  const credsFallbackTok = 'synthetic_creds_fallback_token_282828';
  fs.writeFileSync(join(extraClaudeDir, '.credentials.json'), JSON.stringify({
    claudeAiOauth: {
      accessToken: credsFallbackTok,
      expiresAt: fixedNowMs + 3_600_000,
    },
  }));
  assert.equal(
    readLocalClaudeToken(fs, sbExtra.env, '{placeholder}', { now: () => fixedNowMs }),
    credsFallbackTok,
  );
});

test('3483: expired claudeAiOauth.expiresAt throws expired_local_login before Cloud upload or ~/.claude/settings.json mutation', async t => {
  const fixedNowMs = Date.parse('2026-11-17T08:00:00Z');
  const cloud = await startFakeCloud(t, fixedNowMs);
  const sb = makeSandbox(t, cloud.serverUrl);

  const localClaudeDir = join(sb.home, '.claude');
  fs.mkdirSync(localClaudeDir, { recursive: true });
  const localSettingsPath = join(localClaudeDir, 'settings.json');
  const initialLocalSettings = `${JSON.stringify({ theme: 'solarized', env: { KEEP_EXISTING: 'yes' } }, null, 2)}
`;
  fs.writeFileSync(localSettingsPath, initialLocalSettings, { mode: 0o600 });

  // Expired directory (.credentials.json with past numeric epoch ms and sk-ant-oat01-* token)
  const expiredDir = join(sb.root, 'expired-claude-dir');
  fs.mkdirSync(expiredDir, { recursive: true });
  const expiredCredsFile = join(expiredDir, '.credentials.json');
  const fakeExpiredTok = 'sk-ant-oat01-fakeExpiredAccessToken44444';
  const fakeExpiredRef = 'sk-ant-ort01-fakeExpiredRefreshToken44444';
  fs.writeFileSync(expiredCredsFile, JSON.stringify({
    claudeAiOauth: {
      accessToken: fakeExpiredTok,
      refreshToken: fakeExpiredRef,
      expiresAt: fixedNowMs - 5_000,
    },
  }));

  // Direct unit checks on both <dir> and <dir>/.credentials.json
  for (const target of [expiredDir, expiredCredsFile]) {
    assert.throws(
      () => readClaudeTokenFromPath(fs, target, { now: () => fixedNowMs }),
      err => {
        assert.ok(err instanceof CloudAccountsError);
        assert.equal(err.code, 'expired_local_login');
        assert.match(err.message, /expired short-lived Claude OAuth access token/);
        assert.match(err.message, /pdd accounts add --provider claude/);
        assert.match(err.message, /claude setup-token/);
        assert.ok(err.message.includes(expiredCredsFile));
        return true;
      },
    );
  }

  // Boundary & format checks: ISO at now + 60_000, numeric epoch-ms string in past, and expiresAt === 0
  const isoExpiredFile = join(sb.root, 'iso-expired.credentials.json');
  fs.writeFileSync(isoExpiredFile, JSON.stringify({
    claudeAiOauth: {
      accessToken: 'sk-ant-oat01-fakeIsoExpiredAccessToken55555',
      expiresAt: new Date(fixedNowMs + 60_000).toISOString(),
    },
  }));
  const numStrExpiredFile = join(sb.root, 'numstr-expired.credentials.json');
  fs.writeFileSync(numStrExpiredFile, JSON.stringify({
    claudeAiOauth: {
      accessToken: 'synthetic_numstr_expired_tok_565656',
      expiresAt: String(fixedNowMs - 1_000),
    },
  }));
  const zeroExpiredFile = join(sb.root, 'zero-expired.credentials.json');
  fs.writeFileSync(zeroExpiredFile, JSON.stringify({
    claudeAiOauth: {
      accessToken: 'synthetic_zero_expired_tok_575757',
      expiresAt: 0,
    },
  }));

  for (const badFile of [isoExpiredFile, numStrExpiredFile, zeroExpiredFile]) {
    assert.throws(
      () => readClaudeTokenFromPath(fs, badFile, { now: () => fixedNowMs }),
      err => err instanceof CloudAccountsError && err.code === 'expired_local_login',
    );
  }

  // CLI checks: --from <dir> and --from <file> fail with exit 1, zero Cloud requests, untouched ~/.claude/settings.json
  for (const fromArg of [expiredDir, expiredCredsFile, isoExpiredFile, numStrExpiredFile, zeroExpiredFile]) {
    const res = await runCli(
      ['accounts', 'import', '--provider', 'claude', '--from', fromArg, '--label', 'must-not-enroll'],
      sb,
      { now: () => fixedNowMs },
    );
    assert.equal(res.exit, 1);
    assert.match(res.stderr, /expired short-lived Claude OAuth access token/);
    assert.match(res.stderr, /pdd accounts add --provider claude/);
    assert.match(res.stderr, /claude setup-token/);
    assert.ok(!res.stderr.includes(fakeExpiredTok) && !res.stderr.includes(fakeExpiredRef));
  }

  // Default local ~/.claude/.credentials.json expired check
  fs.writeFileSync(join(localClaudeDir, '.credentials.json'), JSON.stringify({
    claudeAiOauth: {
      accessToken: 'sk-ant-oat01-fakeLocalExpiredToken66666',
      expiresAt: fixedNowMs - 120_000,
    },
  }));
  assert.throws(
    () => readLocalClaudeToken(fs, sb.env, '', { now: () => fixedNowMs }),
    err => err instanceof CloudAccountsError && err.code === 'expired_local_login',
  );
  const defaultRes = await runCli(['accounts', 'import', '--label', 'must-not-enroll-local'], sb, {
    now: () => fixedNowMs,
  });
  assert.equal(defaultRes.exit, 1);
  assert.match(defaultRes.stderr, /expired short-lived Claude OAuth access token/);

  assert.equal(cloud.requests.length, 0, 'zero Cloud API requests sent when local Claude token is expired');
  assert.equal(fs.readFileSync(localSettingsPath, 'utf8'), initialLocalSettings, '~/.claude/settings.json was not mutated');
});

test('3483: detectImportProvider recognizes <dir> and .credentials.json containing claudeAiOauth and registers secrets', async t => {
  const fixedNowMs = Date.parse('2026-11-17T08:00:00Z');
  const cloud = await startFakeCloud(t, fixedNowMs);
  const sb = makeSandbox(t, cloud.serverUrl);

  const claudeDir = join(sb.root, 'auto-detect-claude-dir');
  fs.mkdirSync(claudeDir, { recursive: true });
  fs.writeFileSync(join(claudeDir, 'settings.json'), JSON.stringify({ theme: 'dark' }));
  const customFormatToken = 'synthetic_claude_oauth_access_token_77777';
  const customRefreshToken = 'synthetic_claude_oauth_refresh_token_77777';
  const credsPath = join(claudeDir, '.credentials.json');
  fs.writeFileSync(credsPath, JSON.stringify({
    claudeAiOauth: {
      accessToken: customFormatToken,
      refreshToken: customRefreshToken,
      expiresAt: fixedNowMs + 3_600_000,
    },
  }));

  // Directory detection registers non-sk- accessToken and refreshToken in rememberSecrets immediately
  assert.equal(detectImportProvider(fs, sb.env, { cwd: sb.cwd, fromOption: claudeDir, now: () => fixedNowMs }), 'claude');
  assert.equal(
    redactSecrets(`dir secrets ${customFormatToken} and ${customRefreshToken}`),
    'dir secrets [redacted] and [redacted]',
  );

  // Direct file detection also registers non-sk- accessToken and refreshToken immediately
  const standaloneCredsPath = join(sb.root, 'standalone.credentials.json');
  const fileCustomAccess = 'synthetic_file_oauth_access_token_88888';
  const fileCustomRefresh = 'synthetic_file_oauth_refresh_token_88888';
  fs.writeFileSync(standaloneCredsPath, JSON.stringify({
    claudeAiOauth: {
      accessToken: fileCustomAccess,
      refreshToken: fileCustomRefresh,
      expiresAt: fixedNowMs + 3_600_000,
    },
  }));
  assert.equal(detectImportProvider(fs, sb.env, { cwd: sb.cwd, fromOption: standaloneCredsPath, now: () => fixedNowMs }), 'claude');
  assert.equal(
    redactSecrets(`file secrets ${fileCustomAccess} and ${fileCustomRefresh}`),
    'file secrets [redacted] and [redacted]',
  );

  // End-to-end CLI import without --provider auto-detects claude from <dir>/.credentials.json
  const autoImp = await runCli(['accounts', 'import', '--from', claudeDir, '--label', 'auto-detected-claude'], sb, {
    now: () => fixedNowMs,
  });
  assert.equal(autoImp.exit, 0, autoImp.stderr);
  assert.match(autoImp.stdout, /Enrolled Claude account "auto-detected-claude"/);
  const uploaded = cloud.requests.find(r => r.method === 'POST' && r.path === '/v1/accounts');
  assert.equal(uploaded?.body?.provider, 'claude');
  assert.equal(uploaded?.body?.bundle?.oauth_token, customFormatToken);
});
