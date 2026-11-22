import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { checkReleaseNotice, isNewerRelease, parseReleaseVersion, pickLatestRelease } from '../src/release-notice.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const capture = (isTTY = false) => ({ text: '', isTTY, write(s) { this.text += s; } });

test('#2710 parseReleaseVersion, isNewerRelease and pickLatestRelease handle plain, v-prefixed and prerelease-only alpha-v arrays', () => {
  assert.equal(parseReleaseVersion('0.1.32'), '0.1.32');
  assert.equal(parseReleaseVersion('v0.1.32'), '0.1.32');
  assert.equal(parseReleaseVersion('alpha-v0.1.32'), '0.1.32');
  assert.equal(parseReleaseVersion('not-a-tag'), null);
  assert.equal(isNewerRelease('alpha-v0.1.32', '0.1.31'), true);
  assert.equal(isNewerRelease('0.1.31', '0.1.31'), false);
  assert.equal(isNewerRelease('0.1.30', '0.1.31'), false);
  assert.deepEqual(
    pickLatestRelease([
      { tag_name: 'alpha-v0.1.99', draft: true, prerelease: true, published_at: '2026-11-13T12:00:00Z' },
      { tag_name: 'alpha-v0.1.31', draft: false, prerelease: true, published_at: '2026-11-12T10:00:00Z' },
      { tag_name: 'alpha-v0.1.32', draft: false, prerelease: true, published_at: '2026-11-13T10:00:00Z' },
    ]),
    { tag: 'alpha-v0.1.32', version: '0.1.32' },
  );
  assert.equal(pickLatestRelease([{ tag_name: 'alpha-v0.1.32', draft: true }]), null);
});

test('#2710 checkReleaseNotice caches for 24h, always informs --version, deduplicates interactive commands for 24h, and backs off 1h on errors', async t => {
  const stateHome = mkdtempSync(join(tmpdir(), 'pdd-release-notice-'));
  t.after(() => rmSync(stateHome, { recursive: true, force: true }));

  let now = 1_700_000_000_000;
  let fetches = 0;
  const ports = {
    stateHome,
    now: () => now,
    fetchLatestRelease: async () => {
      fetches++;
      return { tag_name: 'alpha-v0.1.99', draft: false };
    },
  };
  const cleanEnv = { HOME: stateHome };

  // 1. Suppressed in CI, agent sessions, and PDD_NO_UPDATE_CHECK=1 without network calls.
  assert.equal(await checkReleaseNotice({ currentVersion: '0.1.31', interactive: true, env: { ...cleanEnv, CI: 'true' } }, ports), null);
  assert.equal(await checkReleaseNotice({ currentVersion: '0.1.31', interactive: true, env: { ...cleanEnv, PDD_AGENT_SESSION: '1' } }, ports), null);
  assert.equal(await checkReleaseNotice({ currentVersion: '0.1.31', interactive: true, env: { ...cleanEnv, PDD_NO_UPDATE_CHECK: '1' } }, ports), null);
  assert.equal(fetches, 0);

  // 2. First interactive command fetches once, writes cache, and emits notice.
  const first = await checkReleaseNotice({ currentVersion: '0.1.31', interactive: true, env: cleanEnv }, ports);
  assert.equal(fetches, 1);
  assert.match(first, /0\.1\.31 -> 0\.1\.99/);
  assert.match(first, /To update, run: pdd upgrade/);

  // 3. Second interactive command 5 minutes later Neither fetches Nor re-notifies.
  now += 5 * 60 * 1000;
  assert.equal(await checkReleaseNotice({ currentVersion: '0.1.31', interactive: true, env: cleanEnv }, ports), null);
  assert.equal(fetches, 1);

  // 4. --version always emits the cached notice (even non-TTY) without re-fetching.
  const onVersion = await checkReleaseNotice({ currentVersion: '0.1.31', isVersionCommand: true, interactive: false, env: cleanEnv }, ports);
  assert.equal(onVersion, first);
  assert.equal(fetches, 1);

  // 5. Network failure after 24h sets a 1h backoff instead of retrying on every command.
  const errHome = mkdtempSync(join(tmpdir(), 'pdd-release-err-'));
  t.after(() => rmSync(errHome, { recursive: true, force: true }));
  let errFetches = 0;
  const errPorts = {
    stateHome: errHome,
    now: () => now,
    fetchLatestRelease: async () => { errFetches++; throw Error('offline'); },
  };
  assert.equal(await checkReleaseNotice({ currentVersion: '0.1.31', interactive: true, env: { HOME: errHome } }, errPorts), null);
  assert.equal(errFetches, 1);
  now += 30 * 60 * 1000;
  assert.equal(await checkReleaseNotice({ currentVersion: '0.1.31', interactive: true, env: { HOME: errHome } }, errPorts), null);
  assert.equal(errFetches, 1);
  now += 31 * 60 * 1000;
  assert.equal(await checkReleaseNotice({ currentVersion: '0.1.31', interactive: true, env: { HOME: errHome } }, errPorts), null);
  assert.equal(errFetches, 2);
});

test('#2710 runPdd prints cached release notice on --version stderr while keeping stdout version-only, and skips --json routes', async t => {
  const home = mkdtempSync(join(tmpdir(), 'pdd-cli-notice-'));
  t.after(() => rmSync(home, { recursive: true, force: true }));
  const stateDir = join(home, '.local/state/pdd');
  mkdirSync(stateDir, { recursive: true });
  const version = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8')).version;
  writeFileSync(join(stateDir, 'release-check.json'), JSON.stringify({
    checkedAt: Date.now(),
    latestTag: 'alpha-v99.0.0',
    latestVersion: '99.0.0',
    notifiedAt: null,
  }));

  const stdout = capture(false), stderr = capture(false);
  const code = await runPdd(['--version'], {
    cwd: home,
    packageRoot: root,
    env: { HOME: home, PATH: '' },
    stdout,
    stderr,
    pathDiagnostic: () => [],
    findSkills: () => [],
  });
  assert.equal(code, 0);
  assert.equal(stdout.text, `${version}\n`);
  assert.match(stderr.text, /99\.0\.0/);
  assert.match(stderr.text, /pdd upgrade/);

  // pdd upgrade never emits a trailing cached release notice on stderr.
  const upgOut = capture(true), upgErr = capture(true);
  const upgCode = await runPdd(['upgrade'], {
    cwd: home,
    packageRoot: root,
    env: { HOME: home, PATH: '' },
    stdout: upgOut,
    stderr: upgErr,
    cliUpgrade: { runCliUpgrade: async () => ({ exitCode: 0, message: 'Upgraded.' }) },
  });
  assert.equal(upgCode, 0);
  assert.equal(upgErr.text, '');

  // --json routes never receive a stderr notice even on a TTY.
  const jsonOut = capture(true), jsonErr = capture(true);
  const jsonCode = await runPdd(['accounts', 'status', '--json'], {
    cwd: home,
    packageRoot: root,
    env: { HOME: home, PATH: '' },
    stdout: jsonOut,
    stderr: jsonErr,
  });
  assert.equal(jsonCode, 0);
  assert.equal(jsonErr.text, '');
});

test('S1 release-notice filters prereleases when stable exists, sorts by semver, honors PDD_STATE_DIR, and excludes files/setup/init/status', async t => {
  // Stable releases take precedence over prereleases, and higher semver beats newer published_at backport.
  assert.deepEqual(
    pickLatestRelease([
      { tag_name: 'v0.1.99', draft: false, prerelease: true, published_at: '2026-11-20T12:00:00Z' },
      { tag_name: 'v0.1.40', draft: false, prerelease: false, published_at: '2026-11-21T12:00:00Z' },
      { tag_name: 'v0.2.0', draft: false, prerelease: false, published_at: '2026-11-19T12:00:00Z' },
    ]),
    { tag: 'v0.2.0', version: '0.2.0' },
  );

  // PDD_STATE_DIR overrides XDG_STATE_HOME and HOME/.local/state/pdd.
  const customState = mkdtempSync(join(tmpdir(), 'pdd-release-state-'));
  t.after(() => rmSync(customState, { recursive: true, force: true }));
  writeFileSync(join(customState, 'release-check.json'), JSON.stringify({
    checkedAt: Date.now(),
    latestTag: 'v88.0.0',
    latestVersion: '88.0.0',
    notifiedAt: null,
  }));
  const notice = await checkReleaseNotice(
    { currentVersion: '0.1.41', isVersionCommand: true, env: { HOME: '/unused', PDD_STATE_DIR: customState } },
    { fetchLatestRelease: async () => { throw Error('should read cached PDD_STATE_DIR'); } },
  );
  assert.match(notice, /88\.0\.0/);

  // files, setup, init, and status never trigger releaseNotice even on a TTY.
  let noticeCalls = 0;
  const repoDir = mkdtempSync(join(tmpdir(), 'pdd-release-excl-'));
  t.after(() => rmSync(repoDir, { recursive: true, force: true }));
  const { execFileSync } = await import('node:child_process');
  execFileSync('git', ['init', '-q'], { cwd: repoDir });
  for (const argv of [['files'], ['init'], ['status'], ['setup']]) {
    const out = capture(true), err = capture(true);
    const code = await runPdd(argv, {
      cwd: repoDir,
      packageRoot: root,
      env: { HOME: customState, PATH: '' },
      stdout: out,
      stderr: err,
      pathDiagnostic: () => [],
      releaseNotice: async () => { noticeCalls++; return 'should not run'; },
    });
    assert.equal(code, 0, `${argv.join(' ')}: ${err.text}`);
    assert.equal(noticeCalls, 0, `${argv.join(' ')} must not call releaseNotice`);
  }
});
