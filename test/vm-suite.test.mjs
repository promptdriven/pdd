import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const script = fileURLToPath(new URL('../scripts/vm-suite.sh', import.meta.url));
const sha = 'a'.repeat(40);
// Synthetic native TAP totals, chosen from the brief's count/status requirements.
const tap = (pass = 7, fail = 0, cancelled = 0, skipped = 1, todo = 0) =>
  `TAP version 13\n    # tests 99\n    # pass 99\n# tests ${pass + fail + cancelled + skipped + todo}\n# suites 0\n# pass ${pass}\n# fail ${fail}\n# cancelled ${cancelled}\n# skipped ${skipped}\n# todo ${todo}\n# duration_ms 12.5\n`;

function run(t, options = {}) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-vm-script-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const home = join(dir, 'original-home');
  const bin = join(dir, 'bin');
  const runner = join(home, 'work/2026-11-01/greg-fix');
  mkdirSync(bin, { recursive: true });
  mkdirSync(runner, { recursive: true });
  writeFileSync(join(home, 'auth-sentinel'), 'original home must survive');
  writeFileSync(join(dir, 'scenario.json'), JSON.stringify({ tap: tap(), ...options }));
  // Replace external commands through PATH. The real Node still parses the footer.
  const fake = `#!${process.execPath}
import { appendFileSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { basename, join } from 'node:path';
import { spawnSync } from 'node:child_process';
const name = basename(process.argv[1]), args = process.argv.slice(2);
const scenario = JSON.parse(readFileSync(process.env.FAKE_DIR + '/scenario.json', 'utf8'));
const event = { name, args, cwd: process.cwd(), home: process.env.HOME, state: process.env.PDD_STATE_DIR };
if (name === 'node' && args.includes('--test')) {
  event.homeFiles = readdirSync(process.env.HOME);
  event.stateFiles = readdirSync(process.env.PDD_STATE_DIR);
  event.browser = process.env.POCKET_BROWSER_BIN;
}
appendFileSync(process.env.FAKE_DIR + '/events', JSON.stringify(event) + '\\n');
if (name === 'git') {
  if (scenario.failCommand === args[0]) process.exit(9);
  if (args[0] === 'init') {
    mkdirSync(join(args.at(-1), 'test'), { recursive: true });
    writeFileSync(join(args.at(-1), 'test/example.test.mjs'), '');
  }
  if (args[0] === 'rev-parse') console.log(scenario.head || '${sha}');
  if (args[0] === 'status' && scenario.dirty) console.log(' M package.json');
} else if (name === 'npm') {
  if (scenario.failCommand === 'npm') process.exit(8);
} else if (name === 'node') {
  if (args.includes('--test')) {
    process.stdout.write(scenario.tap);
    process.exit(scenario.suiteExit || 0);
  }
  const result = spawnSync(${JSON.stringify(process.execPath)}, args, { stdio: 'inherit' });
  process.exit(result.status ?? 1);
} else if (name === 'gh') {
  if (scenario.apiFail) { console.error('status API rejected'); process.exit(7); }
  console.log('{}');
}
`;
  for (const name of ['git', 'npm', 'node', 'gh']) {
    writeFileSync(join(bin, name), fake, { mode: 0o755 });
  }
  writeFileSync(join(runner, 'fullsuite.sh'), '#!/usr/bin/env bash\nexec bash -c "$SUITE"\n', { mode: 0o755 });
  const result = spawnSync('bash', [script, options.argument ?? sha], {
    cwd: dir, encoding: 'utf8', timeout: 15000,
    env: { ...process.env, HOME: home, TMPDIR: dir, FAKE_DIR: dir, PATH: `${bin}:${process.env.PATH}` },
  });
  assert.ifError(result.error);
  let events = [];
  try { events = readFileSync(join(dir, 'events'), 'utf8').trim().split('\n').map(JSON.parse); } catch {}
  return { ...result, events, posts: events.filter(e => e.name === 'gh'), home };
}

function expectStatus(result, state, description) {
  assert.equal(result.posts.length, 1, result.stderr);
  assert.deepEqual(result.posts[0].args, [
    'api', '--method', 'POST', `repos/promptdriven/pdd/statuses/${sha}`,
    '-f', 'context=vm-suite', '-f', `state=${state}`, '-f', `description=${description}`,
  ]);
  assert.ok(description.length <= 140);
  assert.equal(result.posts[0].home, result.home);
}

test('vm-suite posts only counts on the detached tested commit, with an empty suite home/state', t => {
  const result = run(t);
  assert.equal(result.status, 0, result.stderr);
  expectStatus(result, 'success', '7/8, 0 failed');
  const git = result.events.filter(e => e.name === 'git');
  assert.deepEqual(git.find(e => e.args[0] === 'remote').args, ['remote', 'add', 'origin', 'https://github.com/promptdriven/pdd.git']);
  assert.deepEqual(git.find(e => e.args[0] === 'fetch').args, ['fetch', '--quiet', '--no-tags', '--depth=1', 'origin', sha]);
  assert.deepEqual(git.find(e => e.args[0] === 'checkout').args, ['checkout', '--quiet', '--detach', 'FETCH_HEAD']);
  assert.ok(result.events.find(e => e.name === 'npm').args.includes('--ignore-scripts'));
  const suite = result.events.find(e => e.name === 'node' && e.args.includes('--test'));
  assert.notEqual(suite.home, result.home);
  assert.deepEqual(suite.homeFiles, []);
  assert.deepEqual(suite.stateFiles, []);
  assert.equal(suite.browser, '/usr/bin/google-chrome');
  assert.ok(suite.args.includes('--test-concurrency=4'));
  assert.equal(suite.args.at(-1), 'test/example.test.mjs');
  assert.equal(suite.cwd, git.find(e => e.args[0] === 'checkout').cwd);
});

test('vm-suite posts native failure counts and returns failure', t => {
  const result = run(t, { tap: tap(5, 2), suiteExit: 1 });
  assert.notEqual(result.status, 0);
  expectStatus(result, 'failure', '5/8, 2 failed');
});

test('vm-suite cannot succeed after a nonzero suite exit, even with zero failed totals', t => {
  const result = run(t, { suiteExit: 9 });
  assert.notEqual(result.status, 0);
  expectStatus(result, 'failure', '7/8, 0 failed');
});

test('vm-suite cannot succeed when native totals contain failures or cancellations', t => {
  for (const totals of [tap(6, 1), tap(6, 0, 1)]) {
    const result = run(t, { tap: totals });
    assert.notEqual(result.status, 0);
    expectStatus(result, 'failure', totals === tap(6, 1) ? '6/8, 1 failed' : '6/8, 0 failed');
  }
});

test('vm-suite never posts missing, partial, inconsistent or empty final totals', t => {
  for (const totals of ['TAP version 13\n', tap() + '# tests 10\n# pass 10\n', tap().replace('# tests 8', '# tests 9'), tap(0, 0, 0, 0)]) {
    const result = run(t, { tap: totals });
    assert.notEqual(result.status, 0);
    assert.deepEqual(result.posts, []);
  }
});

test('vm-suite never runs tests or posts after failed setup, a different commit or a dirty checkout', t => {
  for (const options of [{ failCommand: 'fetch' }, { failCommand: 'checkout' }, { failCommand: 'npm' }, { head: 'b'.repeat(40) }, { dirty: true }]) {
    const result = run(t, options);
    assert.notEqual(result.status, 0);
    assert.deepEqual(result.posts, []);
    assert.equal(result.events.some(e => e.name === 'node' && e.args.includes('--test')), false);
  }
});

test('vm-suite surfaces a GitHub status API failure', t => {
  const result = run(t, { apiFail: true });
  assert.equal(result.status, 7);
  assert.match(result.stderr, /status API rejected/);
  expectStatus(result, 'success', '7/8, 0 failed');
});

test('vm-suite refuses a moving ref before any external action', t => {
  const result = run(t, { argument: 'alpha' });
  assert.equal(result.status, 2);
  assert.deepEqual(result.events, []);
});
