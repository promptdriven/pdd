import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { createHash } from 'node:crypto';

// Native regressions for the existing Story's Safe inspection rule: observed
// regular-file changes => 5; unsafe/unreadable entries => 4. No Runtime replay.
// Scheduling hooks return genuine lstat results and mutate actual files. The
// only synthetic error is the explicitly named EACCES observation case.
const CLI = new URL('../bin/pdd.mjs', import.meta.url).pathname;
const commands = [['check'], ['check', '--files'], ['try']];
const changes = ['growth', 'same-size edit', 'regular replacement', 'removal'];
const write = (root, path, bytes) => {
  fs.mkdirSync(join(root, path, '..'), { recursive: true });
  fs.writeFileSync(join(root, path), bytes);
};
const scenario = storyPath => ({
  schema_version: 'prompt-runtime.program-scenario.v1', story_path: storyPath,
  criteria: [{ id: 'AC1', text: 'Echo text.' }], initial_world: {},
  // A separate local refusal keeps old-control metadata failures offline even
  // when the changed review is wrongly discarded as a warning.
  criteria_scope: [], steps: [],
});

const hook = String.raw`
import fs from 'node:fs';
import { spawnSync } from 'node:child_process';
import { dirname } from 'node:path';
import { syncBuiltinESMExports } from 'node:module';
const target = process.env.PDD_PREOPEN_TARGET, action = process.env.PDD_PREOPEN_ACTION;
const emit = row => fs.appendFileSync(process.env.PDD_PREOPEN_TRACE, JSON.stringify(row) + '\n');
const lstat = fs.lstatSync, open = fs.openSync, read = fs.readSync, close = fs.closeSync, full = fs.readFileSync;
const summary = stat => stat && ({ regular: stat.isFile(), symlink: stat.isSymbolicLink(),
  size: String(stat.size), ino: String(stat.ino), mtime: String(stat.mtimeNs), ctime: String(stat.ctimeNs) });
const tracked = new Set();
let observations = 0, changed = false, mutating = false;
fs.lstatSync = (path, ...args) => {
  const selected = String(path) === target;
  // Exercise an actually unreadable file from the initial observation onward.
  if (selected && observations === 0 && action === 'unreadable') fs.chmodSync(target, 0);
  if (selected && changed && action === 'synthetic EACCES') {
    emit({ op: 'denied' });
    throw Object.assign(new Error('synthetic denied observation'), { code: 'EACCES' });
  }
  const stat = lstat(path, ...args);
  if (selected) {
    emit({ op: 'stat', observation: ++observations, snapshot: summary(stat) });
    if (observations === Number(process.env.PDD_PREOPEN_OBSERVATION)) {
      changed = true;
      mutating = true;
      const bytes = ['same-size edit', 'regular replacement'].includes(action) ? full(target) : null;
      if (action === 'growth') fs.appendFileSync(target, ' ');
      if (action === 'same-size edit') {
        bytes[bytes.length - 1] = bytes.at(-1) === 32 ? 9 : 32;
        fs.writeFileSync(target, bytes);
        fs.utimesSync(target, 0, 1); // Real, deterministic mtime change as well.
      }
      if (action === 'regular replacement') {
        fs.writeFileSync(target + '-replacement', bytes);
        fs.renameSync(target + '-replacement', target);
      }
      if (action === 'removal') fs.unlinkSync(target);
      if (action === 'parent removal') fs.renameSync(dirname(target), dirname(target) + '-original');
      if (action === 'leaf symlink') {
        fs.renameSync(target, target + '-original');
        fs.symlinkSync(target + '-original', target);
      }
      if (action === 'directory' || action === 'FIFO') {
        fs.unlinkSync(target);
        if (action === 'directory') fs.mkdirSync(target);
        else {
          const child = spawnSync('mkfifo', [target]);
          if (child.status !== 0) throw new Error('mkfifo setup failed');
        }
      }
      if (action === 'ancestor symlink' || action === 'ancestor file') {
        const parent = dirname(target);
        fs.renameSync(parent, parent + '-original');
        if (action === 'ancestor symlink') fs.symlinkSync(parent + '-original', parent);
        else fs.writeFileSync(parent, 'ordinary ancestor file');
      }
      let after = null;
      try { after = summary(lstat(target, { bigint: true })); }
      catch (error) { if (!['ENOENT', 'ENOTDIR'].includes(error.code)) throw error; }
      mutating = false;
      emit({ op: 'mutation', action, observation: observations, before: summary(stat), after });
    }
  }
  return stat;
};
fs.openSync = (path, ...args) => {
  if (!mutating && String(path) === target) emit({ op: 'open', changed });
  const fd = open(path, ...args);
  if (!mutating && String(path) === target) tracked.add(fd);
  return fd;
};
fs.readSync = (fd, ...args) => {
  if (tracked.has(fd)) emit({ op: 'read', changed });
  return read(fd, ...args);
};
fs.readFileSync = (path, ...args) => {
  if (String(path) === target || tracked.has(path)) emit({ op: 'full', changed });
  return full(path, ...args);
};
fs.closeSync = fd => { tracked.delete(fd); return close(fd); };
globalThis.fetch = () => { emit({ op: 'network' }); throw new Error('offline test'); };
syncBuiltinESMExports();
`;

function fixture(t) {
  const sandbox = fs.mkdtempSync(join(tmpdir(), 'pdd-d2-preopen-')), root = join(sandbox, 'repo');
  t.after(() => fs.rmSync(sandbox, { recursive: true, force: true }));
  for (const path of [root, join(sandbox, 'home'), join(sandbox, 'bin')]) fs.mkdirSync(path);
  assert.equal(spawnSync('git', ['init', '-q'], { cwd: root }).status, 0);
  write(sandbox, 'hook.mjs', hook);
  write(sandbox, 'bin/gh', '#!/bin/sh\nprintf "auth\\n" >> "$PDD_PREOPEN_AUTH"\nexit 1\n');
  fs.chmodSync(join(sandbox, 'bin/gh'), 0o755);
  return { root, cli(args, path, action, observation = 1) {
    const trace = join(sandbox, 'trace.jsonl'), auth = join(sandbox, 'auth.log');
    fs.writeFileSync(trace, '');
    const child = spawnSync(process.execPath, ['--import', join(sandbox, 'hook.mjs'), CLI, ...args], {
      cwd: root, encoding: 'utf8', timeout: 10000,
      env: { HOME: join(sandbox, 'home'), PATH: `${join(sandbox, 'bin')}:/usr/bin:/bin`,
        PDD_RUNTIME_URL: 'http://127.0.0.1:9', PDD_PREOPEN_TARGET: join(root, path),
        PDD_PREOPEN_ACTION: action, PDD_PREOPEN_OBSERVATION: String(observation),
        PDD_PREOPEN_TRACE: trace, PDD_PREOPEN_AUTH: auth },
    });
    assert.equal(child.error, undefined, String(child.error));
    assert.equal(child.signal, null, child.stderr);
    const events = fs.readFileSync(trace, 'utf8').trim().split('\n').filter(Boolean).map(JSON.parse);
    t.diagnostic(JSON.stringify({ args, path, action, status: child.status, events, stdout: child.stdout, stderr: child.stderr }));
    assert.equal(fs.existsSync(auth), false, 'no authentication');
    assert.equal(events.filter(row => row.op === 'network').length, 0, 'no network/AI');
    const mutations = events.filter(row => row.op === 'mutation');
    assert.equal(mutations.length, 1, 'one real mutation, no discovery retry');
    assert.equal(mutations[0].before.regular, true, 'observed a genuine regular file');
    return { ...child, events, mutation: mutations[0] };
  } };
}

function changed(child, path, action) {
  // Exact contract oracle, deliberately independent of implementation output.
  assert.equal(child.status, 5, child.stdout + child.stderr);
  assert.equal(child.stderr.trim(), `${path}: files changed during discovery; stop other edits and try again.`);
  assert.doesNotMatch(child.stdout + child.stderr, /No tests found|symbolic link|numeric reviews are ignored/);
  assert.equal(child.events.filter(row => ['open', 'read', 'full'].includes(row.op) && row.changed).length, 0,
    'stop before any open/read after the observed mutation');
  assert.ok(child.events.filter(row => row.op === 'stat').length <= child.mutation.observation + 1,
    'one pre-open leaf observation, no discovery retry');
  if (action === 'removal' || action === 'parent removal') assert.equal(child.mutation.after, null);
  else {
    assert.equal(child.mutation.after.regular, true);
    assert.notDeepEqual(child.mutation.after, child.mutation.before, 'genuine metadata mismatch');
    if (action === 'growth') assert.equal(BigInt(child.mutation.after.size), BigInt(child.mutation.before.size) + 1n);
    else assert.equal(child.mutation.after.size, child.mutation.before.size);
    if (action === 'regular replacement') assert.notEqual(child.mutation.after.ino, child.mutation.before.ino);
  }
}

for (const size of [10, 1_048_577]) for (const action of changes) for (const args of commands) {
  test(`pre-open discovery: ${args.join(' ')} ${action}, ${size} actual bytes => 5`, t => {
    const { root, cli } = fixture(t), path = 'tests/ordinary.json';
    write(root, path, '{"data":1}' + ' '.repeat(size - 10));
    assert.equal(fs.statSync(join(root, path)).size, size);
    changed(cli(args, path, action), path, action);
  });
}

for (const args of commands) test(`pre-open discovery: ${args.join(' ')} missing parent after regular stat => 5`, t => {
  const { root, cli } = fixture(t), path = 'tests/ordinary.json';
  write(root, path, '{"data":1}');
  changed(cli(args, path, 'parent removal'), path, 'parent removal');
});

// Each first inspection takes three real leaf observations. Observation four is
// the initial stat of the second inspection in these public CLI paths.
for (const context of ['guidance', 'Story', 'numeric metadata', 'numeric test hash']) {
  const runs = [...changes.map(action => ({ args: ['check'], action })), { args: ['try'], action: 'growth' }];
  if (context === 'guidance') runs.push({ args: ['check', '--files'], action: 'growth' });
  for (const { args, action } of runs) test(`pre-open ${context}: ${args.join(' ')} ${action} => 5`, t => {
    const { root, cli } = fixture(t);
    let path = 'tests/ordinary.json';
    write(root, path, '{"data":1}');
    if (context === 'Story') {
      const doc = scenario(path);
      delete doc.criteria_scope; // Reach the JSON Story read during validation.
      write(root, 'tests/scenario.json', JSON.stringify(doc));
    }
    if (context.startsWith('numeric')) {
      write(root, 'user_stories/echo.md', '# Echo\n\n## Acceptance criteria\n\n1. Echo text.\n');
      write(root, 'tests/echo.json', JSON.stringify(scenario('user_stories/echo.md')));
      const reviews = context === 'numeric metadata' ? [] : [{
        test_path: 'tests/echo.json', test_sha256: createHash('sha256').update(fs.readFileSync(join(root, 'tests/echo.json'))).digest('hex'),
        step_id: 'echo', criterion_id: 'AC1', target: 'result', path: '/text', value: 1, reason: 'Unrelated numeric advice.',
      }];
      write(root, 'pdd-numeric-reviews.json', JSON.stringify({ schema_version: 'pdd.numeric-reviews.v1', reviews }));
      path = context === 'numeric metadata' ? 'pdd-numeric-reviews.json' : 'tests/echo.json';
    }
    changed(cli(args, path, action, 4), path, action);
  });
}

for (const action of ['ancestor symlink', 'ancestor file', 'leaf symlink', 'directory', 'FIFO', 'unreadable', 'synthetic EACCES']) {
  for (const args of commands) test(`pre-open safety: ${args.join(' ')} ${action} retains 4`, t => {
    const { root, cli } = fixture(t), path = 'tests/ordinary.json';
    write(root, path, '{"data":1}');
    const child = cli(args, path, action);
    assert.equal(child.status, 4, child.stdout + child.stderr);
    if (action === 'unreadable' || action === 'synthetic EACCES') assert.match(child.stderr, /unreadable.*EACCES/);
    else if (action === 'ancestor file') assert.match(child.stderr, /unsafe discovery file.*(?:symbolic link ancestor|ENOTDIR)/);
    else assert.equal(child.stderr.trim(), `${path}: unsafe discovery file (symbolic link ancestor or non-regular file).`);
    assert.doesNotMatch(child.stderr, /files changed|No tests found/);
    assert.equal(child.events.filter(row => ['read', 'full'].includes(row.op)).length, 0, 'never read unsafe targets');
    if (action !== 'unreadable') assert.equal(child.events.filter(row => row.op === 'open').length, 0);
  });
}
