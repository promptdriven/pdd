import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { checkReleaseNotice, isNewerRelease, parseReleaseVersion } from '../src/release-notice.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const capture = (isTTY = false) => ({ text: '', isTTY, write(s) { this.text += s; } });

test('#2710 parseReleaseVersion and isNewerRelease handle plain, v-prefixed and alpha-v tags', () => {
  assert.equal(parseReleaseVersion('0.1.32'), '0.1.32');
  assert.equal(parseReleaseVersion('v0.1.32'), '0.1.32');
  assert.equal(parseReleaseVersion('alpha-v0.1.32'), '0.1.32');
  assert.equal(parseReleaseVersion('not-a-tag'), null);
  assert.equal(isNewerRelease('alpha-v0.1.32', '0.1.31'), true);
  assert.equal(isNewerRelease('0.1.31', '0.1.31'), false);
  assert.equal(isNewerRelease('0.1.30', '0.1.31'), false);
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
  assert.match(first, /npm install -g github:promptdriven\/pdd && pdd setup/);

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

  // workflow list --json never receives a stderr notice even on a TTY.
  const jsonOut = capture(true), jsonErr = capture(true);
  const jsonCode = await runPdd(['workflow', 'list', '--json'], {
    cwd: home,
    packageRoot: root,
    env: { HOME: home, PATH: '' },
    stdout: jsonOut,
    stderr: jsonErr,
  });
  assert.equal(jsonCode, 0);
  assert.equal(jsonErr.text, '');
});
