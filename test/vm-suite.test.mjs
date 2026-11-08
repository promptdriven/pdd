import { calculateCheckCapacity } from '../src/test-suite-queue.mjs';
import { checkMachine, withCheckLifetime } from './helpers/check-machine.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, copyFileSync, existsSync, mkdtempSync, mkdirSync, readFileSync, readdirSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const script = fileURLToPath(new URL('../scripts/vm-suite.sh', import.meta.url));
const lockScript = fileURLToPath(new URL('../scripts/vm-suite-lock.sh', import.meta.url));
const sha = 'a'.repeat(40);
// Synthetic native TAP totals, chosen from the brief's count/status requirements.
const tap = (pass = 7, fail = 0, cancelled = 0, skipped = 1, todo = 0) =>
  `TAP version 13\n    # tests 99\n    # pass 99\n# tests ${pass + fail + cancelled + skipped + todo}\n# suites 0\n# pass ${pass}\n# fail ${fail}\n# cancelled ${cancelled}\n# skipped ${skipped}\n# todo ${todo}\n# duration_ms 12.5\n`;
const clock = '\\d\\d:\\d\\d:\\d\\d';
const literal = text => text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

function fakes(t, options = {}) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-vm-script-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const home = join(dir, 'original-home');
  const bin = join(dir, 'bin');
  mkdirSync(bin, { recursive: true });
  mkdirSync(home, { recursive: true });
  mkdirSync(join(dir,'suite-queue'));
  writeFileSync(join(dir,'suite-queue','capacity.json'),JSON.stringify(withCheckLifetime(calculateCheckCapacity({checks:3},checkMachine({taskset:null}).ports))));
  writeFileSync(join(home, 'auth-sentinel'), 'original home must survive');
  writeFileSync(join(dir, 'scenario.json'), JSON.stringify({ tap: tap(), ...options }));
  // Replace external commands through PATH. The real Node still parses the footer.
  const fake = `#!${process.execPath}
import { appendFileSync, fstatSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { basename, join } from 'node:path';
import { spawnSync } from 'node:child_process';
const name = basename(process.argv[1]), args = process.argv.slice(2);
const scenario = JSON.parse(readFileSync(process.env.FAKE_DIR + '/scenario.json', 'utf8'));
const event = { name, args, cwd: process.cwd(), home: process.env.HOME, state: process.env.PDD_STATE_DIR, locale: process.env.LC_ALL };
if (name === 'node' && args.includes('--test')) {
  event.homeFiles = readdirSync(process.env.HOME);
  event.stateFiles = readdirSync(process.env.PDD_STATE_DIR);
}
if ((name === 'node' && args.includes('--test')) || name === 'npm') {
  event.browser = process.env.POCKET_BROWSER_BIN;
  event.stdinIsDevNull = fstatSync(0).isCharacterDevice();
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
  if (args[0] === 'test') process.exit(scenario.suiteExit || 0);
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
  const env = {
    ...process.env, SUITE: undefined, PDD_VM_SUITE_LOCK: undefined, PDD_SUITE_QUEUE: join(dir, 'suite-queue'),
    // C is available on Linux and macOS, unlike an inherited C.UTF-8 locale.
    LC_ALL: 'C',
    HOME: home, TMPDIR: dir, FAKE_DIR: dir, PATH: `${bin}:${process.env.PATH}`, ...options.env,
  };
  const events = () => {
    try { return readFileSync(join(dir, 'events'), 'utf8').trim().split('\n').map(JSON.parse); } catch { return []; }
  };
  return { dir, home, env, events };
}

function run(t, options = {}) {
  const fake = fakes(t, options);
  const result = spawnSync('bash', [options.script ?? script, options.argument ?? sha], {
    cwd: fake.dir, encoding: 'utf8', timeout: 15000, env: fake.env,
  });
  assert.ifError(result.error);
  const events = fake.events();
  return { ...result, dir: fake.dir, home: fake.home, events, posts: events.filter(e => e.name === 'gh') };
}

// The lock runner alone, run from a clone folder as other jobs on the VM run it.
function runLock(t, options = {}) {
  const fake = fakes(t, options);
  const clone = join(fake.dir, 'clone');
  mkdirSync(clone);
  const result = spawnSync('bash', [lockScript], {
    cwd: clone, encoding: 'utf8', timeout: 15000, env: { ...fake.env, PWD: clone, ...options.lockEnv?.(fake.dir) },
  });
  assert.ifError(result.error);
  return { ...result, dir: fake.dir, home: fake.home, clone, events: fake.events() };
}

const steps = events => events.map(e => (e.name === 'node' && e.args.includes('--test') ? 'suite' : `${e.name} ${e.args.join(' ')}`))
  .filter(step => /^(flock|sleep|npm (test|run)|suite)/.test(step));

function expectStatus(result, state, description) {
  assert.equal(result.posts.length, 1, result.stderr);
  assert.deepEqual(result.posts[0].args, [
    'api', '--method', 'POST', `repos/promptdriven/pdd/statuses/${sha}`,
    '-f', 'context=vm-suite', '-f', `state=${state}`, '-f', `description=${description}`,
  ]);
  assert.ok(description.length <= 140);
  assert.equal(result.posts[0].home, result.home);
}

test('vm-suite test children use a portable locale when the caller locale is unavailable', t => {
  const callerLocale = process.env.LC_ALL;
  let wrapper, runner;
  // Both helpers spawn synchronously. Restore the caller before any other test runs.
  try {
    process.env.LC_ALL = 'pdd_TEST_unavailable_locale';
    wrapper = run(t);
    runner = runLock(t, { lockEnv: () => ({ SUITE: 'npm run suite' }) });
  } finally {
    if (callerLocale === undefined) delete process.env.LC_ALL;
    else process.env.LC_ALL = callerLocale;
  }
  for (const result of [wrapper, runner]) {
    assert.equal(result.status, 0, result.stderr);
    assert.deepEqual([...new Set(result.events.map(event => event.locale))], ['C']);
    assert.equal(result.stderr, '');
  }
  expectStatus(wrapper, 'success', '7/8, 0 failed');
});

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

test('vm-suite takes a slot from the lock runner next to it, with no dated personal folder', t => {
  const result = run(t);
  assert.equal(result.status, 0, result.stderr);
  expectStatus(result, 'success', '7/8, 0 failed');
  assert.equal(existsSync(join(result.home, 'work')), false);
  assert.deepEqual(steps(result.events), ['suite']);
  assert.equal(result.events.find(e => e.name === 'node' && e.args.includes('--test')).stdinIsDevNull, true);
  const history = readFileSync(join(result.home, '.local/state/pdd/vm-suite/fullsuite.lock.history'), 'utf8');
  assert.match(history, new RegExp(`^started ${clock} in (\\S+/checkout)\\nfinished ${clock} exit 0 in \\1\\n$`));
  const log = readFileSync(join(result.dir, readdirSync(result.dir).find(name => name.startsWith('pdd-vm-suite.')), 'suite.log'), 'utf8');
  assert.match(log, new RegExp(`^queued ${clock} in (\\S+/checkout)\\nstarted ${clock} in \\1\\nTAP version 13\\n[^]*\\nfinished ${clock} exit 0 in \\1\\n$`));
});

test('vm-suite stops with one line that names the path when its lock runner is missing or not executable', t => {
  const copy = mkdtempSync(join(tmpdir(), 'pdd-vm-copy-'));
  t.after(() => rmSync(copy, { recursive: true, force: true }));
  mkdirSync(join(copy, 'scripts'));
  copyFileSync(script, join(copy, 'scripts/vm-suite.sh'));
  const runner = join(copy, 'scripts/vm-suite-lock.sh');
  for (const prepare of [() => {}, () => { copyFileSync(lockScript, runner); chmodSync(runner, 0o644); }]) {
    prepare();
    const result = run(t, { script: join(copy, 'scripts/vm-suite.sh') });
    assert.equal(result.status, 1);
    assert.match(result.stderr, /^vm-suite: [^\n]+\n$/);
    assert.ok(result.stderr.includes(runner));
    assert.deepEqual(result.events, []);
  }
});

test('vm-suite stops with one line before any external action when the configured shared lock is unusable', t => {
  const missing = join(tmpdir(), `pdd-vm-no-such-folder-${process.pid}`);
  for (const [lock, path] of [
    [join(missing, 'fullsuite.lock'), missing],
    ['fullsuite.lock', 'fullsuite.lock'],
  ]) {
    const result = run(t, { env: { PDD_VM_SUITE_LOCK: lock } });
    assert.equal(result.status, 1);
    assert.match(result.stderr, /^vm-suite-lock: [^\n]+\n$/);
    assert.ok(result.stderr.includes(path));
    assert.deepEqual(result.events, []);
  }
});

test('the compatibility runner uses the shared queue and returns the suite exit code', t => {
  const result = runLock(t, {
    lockEnv: dir => {
      mkdirSync(join(dir, 'shared'));
      return { PDD_VM_SUITE_LOCK: join(dir, 'shared/fullsuite.lock'), SUITE: 'npm run suite; exit 7' };
    },
  });
  assert.equal(result.status, 7, result.stderr);
  assert.deepEqual(steps(result.events), ['npm run suite']);
  const records = readdirSync(join(result.dir,'suite-queue')).filter(name => name.startsWith('ticket-')).map(name => JSON.parse(readFileSync(join(result.dir,'suite-queue',name),'utf8')));
  assert.equal(records.length, 1); assert.equal(records[0].state, 'finished'); assert.equal(records[0].cwd, realpathSync(result.clone));
  const suite = result.events.find(e => e.name === 'npm');
  assert.equal(suite.cwd, realpathSync(result.clone));
  assert.equal(suite.stdinIsDevNull, true);
  const clone = literal(result.clone);
  assert.match(result.stdout, new RegExp(`^queued ${clock} in ${clone}\\nstarted ${clock} in ${clone}\\nfinished ${clock} exit 7 in ${clone}\\n$`));
  const history = readFileSync(join(result.dir, 'shared/fullsuite.lock.history'), 'utf8');
  assert.match(history, new RegExp(`^started ${clock} in ${clone}\\nfinished ${clock} exit 7 in ${clone}\\n$`));
  assert.equal(existsSync(join(result.home, '.local')), false);
});

test('the lock runner runs the plain suite with Chrome when SUITE is empty', t => {
  const result = runLock(t, { suiteExit: 3 });
  assert.equal(result.status, 3, result.stderr);
  assert.deepEqual(steps(result.events), ['npm test']);
  const suite = result.events.find(e => e.name === 'npm');
  assert.equal(suite.browser, '/usr/bin/google-chrome');
  assert.equal(suite.stdinIsDevNull, true);
  const history = readFileSync(join(result.home, '.local/state/pdd/vm-suite/fullsuite.lock.history'), 'utf8');
  const clone = literal(result.clone);
  assert.match(history, new RegExp(`^started ${clock} in ${clone}\\nfinished ${clock} exit 3 in ${clone}\\n$`));
});
