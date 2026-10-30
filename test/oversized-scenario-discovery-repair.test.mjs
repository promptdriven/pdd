import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { createHash } from 'node:crypto';
import { findTests, preflight, proseSha256, selectTests } from '../src/runtime-preflight.mjs';

// Approved D2 safe-inspection rules, exercised through real CLI processes.
// Hooks delegate to real filesystem reads and mutate real files; no metadata or
// file contents are fabricated. Credentials are absent and external ports refuse.
const CLI = new URL('../bin/pdd.mjs', import.meta.url).pathname;
const CAP = 1_048_576, PREFIX = 65_536;
const story = '# Echo\n\n## Acceptance criteria\n\n1. Echo text.\n';
const schema = { type: 'object', properties: { text: { type: 'string' } }, required: ['text'], additionalProperties: false };
const noEffects = child => assert.deepEqual(child.effects, { auth: false, network: 0 });
const scenario = storyPath => ({
  schema_version: 'prompt-runtime.program-scenario.v1', story_path: storyPath,
  criteria: [{ id: 'AC1', text: 'Echo text.' }], initial_world: {},
  steps: [{ step_id: 'echo', entry_path: 'prompts/echo.prompt.md', operation: 'echo', input: { text: 'hi' },
    checks: [{ criterion_id: 'AC1', target: 'result', path: '/text', op: 'equals', value: 'hi' }] }],
});
const write = (root, path, bytes) => {
  fs.mkdirSync(join(root, path, '..'), { recursive: true });
  fs.writeFileSync(join(root, path), bytes);
};

const hook = String.raw`
import fs from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
const target = process.env.PDD_REPAIR_TARGET, action = process.env.PDD_REPAIR_ACTION;
const emit = row => fs.appendFileSync(process.env.PDD_REPAIR_TRACE, JSON.stringify(row) + '\n');
const open = fs.openSync, close = fs.closeSync, read = fs.readSync, full = fs.readFileSync;
const tracked = new Map();
let opens = 0, reads = 0, changed = false;
const afterRead = row => {
  emit(row);
  if (row.actual > 0 && ++reads === Number(process.env.PDD_REPAIR_MUTATE_READ) && !changed) {
    changed = true;
    fs.appendFileSync(target, ' ');
    emit({ op: 'growth', read: reads, size: fs.statSync(target).size });
  }
};
fs.openSync = (path, ...args) => {
  const selected = String(path) === target;
  if (selected && ++opens === 2 && action === 'deny') {
    emit({ op: 'denied', open: opens });
    throw Object.assign(new Error('denied'), { code: 'EACCES' });
  }
  const fd = open(path, ...args);
  if (selected) tracked.set(fd, opens);
  return fd;
};
fs.readSync = (fd, buffer, offset, length, position) => {
  const actual = read(fd, buffer, offset, length, position);
  if (tracked.has(fd)) afterRead({ op: 'read', open: tracked.get(fd), position, requested: length, actual });
  return actual;
};
fs.readFileSync = (path, ...args) => {
  const selected = String(path) === target || tracked.has(path);
  const bytes = full(path, ...args);
  if (selected) afterRead({ op: 'full', actual: Buffer.byteLength(bytes) });
  return bytes;
};
fs.closeSync = fd => {
  const sequence = tracked.get(fd);
  tracked.delete(fd);
  const result = close(fd);
  if (sequence === 1 && action === 'ancestor' && !changed) {
    changed = true;
    const parent = target.slice(0, target.lastIndexOf('/'));
    fs.renameSync(parent, parent + '-original');
    fs.symlinkSync(parent + '-original', parent);
    emit({ op: 'ancestor' });
  }
  return result;
};
globalThis.fetch = () => { emit({ op: 'network' }); throw new Error('offline test'); };
syncBuiltinESMExports();
`;

function fixture(t) {
  const sandbox = fs.mkdtempSync(join(tmpdir(), 'pdd-d2-repair-')), root = join(sandbox, 'repo');
  t.after(() => fs.rmSync(sandbox, { recursive: true, force: true }));
  for (const path of [root, join(sandbox, 'home'), join(sandbox, 'bin')]) fs.mkdirSync(path);
  assert.equal(spawnSync('git', ['init', '-q'], { cwd: root }).status, 0);
  write(sandbox, 'hook.mjs', hook);
  write(sandbox, 'bin/gh', '#!/bin/sh\nprintf "auth\\n" >> "$PDD_REPAIR_AUTH"\nexit 1\n');
  fs.chmodSync(join(sandbox, 'bin/gh'), 0o755);
  function cli(args, path, { mutate = 0, action = '' } = {}) {
    const trace = join(sandbox, 'trace.jsonl'), auth = join(sandbox, 'auth.log');
    fs.writeFileSync(trace, '');
    const child = spawnSync(process.execPath, ['--import', join(sandbox, 'hook.mjs'), CLI, ...args], {
      cwd: root, encoding: 'utf8', timeout: 10000,
      env: { HOME: join(sandbox, 'home'), PATH: `${join(sandbox, 'bin')}:/usr/bin:/bin`,
        PDD_RUNTIME_URL: 'http://127.0.0.1:9', PDD_REPAIR_TARGET: join(root, path),
        PDD_REPAIR_ACTION: action, PDD_REPAIR_MUTATE_READ: String(mutate), PDD_REPAIR_TRACE: trace, PDD_REPAIR_AUTH: auth },
    });
    assert.equal(child.error, undefined, String(child.error));
    assert.equal(child.signal, null, child.stderr);
    const events = fs.readFileSync(trace, 'utf8').trim().split('\n').filter(Boolean).map(line => JSON.parse(line));
    const effects = { auth: fs.existsSync(auth), network: events.filter(row => row.op === 'network').length };
    t.diagnostic(JSON.stringify({ args, path, status: child.status, events, effects }));
    return { ...child, events, effects };
  }
  function normal(storyPath = 'user_stories/echo.md') {
    write(root, storyPath, story);
    const body = { status: 'draft', prose_sha256: '', entries: [{ operation: 'echo', input_schema: schema, result_schema: schema, errors: [] }], calls: [], resources: [] };
    let text = '# Echo\nReturn the supplied text.\n\n<details><summary>Runtime interface</summary>\n\n```json\n' + JSON.stringify(body) + '\n```\n</details>\n';
    text = text.replace('"prose_sha256":""', `"prose_sha256":"${proseSha256(text)}"`);
    write(root, 'prompts/echo.prompt.md', text);
    write(root, 'tests/echo.json', JSON.stringify(scenario(storyPath)));
  }
  return { root, cli, normal };
}

for (const size of [CAP + 1, 10_485_761]) for (const command of ['check', 'try']) {
  test(`F1: real ${command} bounds all inspection of a ${size}-byte ordinary JSON Story reference`, t => {
    const { root, cli } = fixture(t), path = 'tests/ordinary.json';
    write(root, path, '{"data":"' + 'A'.repeat(size - 11) + '"}');
    assert.equal(fs.statSync(join(root, path)).size, size);
    write(root, 'tests/scenario.json', JSON.stringify(scenario(path)));
    const child = cli([command, ...(command === 'check' ? ['--json'] : [])], path);
    assert.equal(child.status, 4, child.stderr);
    noEffects(child);
    assert.match(child.stdout + child.stderr, /has no numbered.*Acceptance criteria/);
    for (const row of child.events.filter(row => row.op === 'read' || row.op === 'full')) {
      assert.ok(row.actual <= PREFIX, `oversized JSON inspection exceeds 65,536 bytes: ${JSON.stringify(row)}`);
    }
    assert.equal(child.events.filter(row => row.op === 'full').length, 0, JSON.stringify(child.events));
    const reads = child.events.filter(row => row.op === 'read');
    assert.ok(reads.length >= 1, JSON.stringify(child.events));
    const inspections = new Map();
    for (const row of reads) {
      assert.ok(row.actual > 0 && row.actual <= PREFIX, JSON.stringify(row));
      assert.ok(row.position >= 0 && row.position + row.actual <= PREFIX, JSON.stringify(row));
      inspections.set(row.open, (inspections.get(row.open) ?? 0) + row.actual);
    }
    for (const bytes of inspections.values()) assert.ok(bytes <= PREFIX, String(bytes));
  });
}

for (const args of [['check'], ['check', '--files'], ['try']]) {
  test(`F2: real ${args.join(' ')} preserves exit 5 when no-tests guidance read 2 grows the file`, t => {
    const { root, cli } = fixture(t), path = 'tests/ordinary.json', bytes = '{"data":1}';
    write(root, path, bytes);
    const child = cli(args, path, { mutate: 2 });
    assert.equal(fs.statSync(join(root, path)).size, Buffer.byteLength(bytes) + 1);
    assert.deepEqual(child.events.filter(row => row.op === 'growth'), [{ op: 'growth', read: 2, size: Buffer.byteLength(bytes) + 1 }]);
    assert.equal(child.events.filter(row => row.op === 'read').length, 2, 'no discovery retry');
    assert.equal(child.status, 5, child.stderr);
    noEffects(child);
    assert.match(child.stderr, /ordinary.json: files changed during discovery/);
    assert.doesNotMatch(child.stderr, /No tests found|not a PDD test file/);
  });
}

for (const action of ['deny', 'ancestor']) {
  test(`F2: no-tests guidance preserves ${action === 'deny' ? 'unreadable' : 'unsafe ancestor'} errors`, t => {
    const { root, cli } = fixture(t), path = 'tests/ordinary.json';
    write(root, path, '{"data":1}');
    const child = cli(['check'], path, { action });
    assert.ok(child.events.some(row => row.op === (action === 'deny' ? 'denied' : 'ancestor')));
    assert.equal(child.status, 4, child.stderr);
    noEffects(child);
    assert.match(child.stderr, action === 'deny' ? /unreadable.*EACCES/ : /symbolic link ancestor/);
    assert.doesNotMatch(child.stderr, /No tests found|not a PDD test file/);
  });
}

test('F1: auxiliary Story inspection detects growth on its second actual read', t => {
  const { root, cli } = fixture(t), path = 'tests/ordinary.json';
  write(root, path, '{"data":1}');
  write(root, 'tests/scenario.json', JSON.stringify(scenario(path)));
  const child = cli(['check'], path, { mutate: 2 });
  assert.equal(child.events.filter(row => row.op === 'growth').length, 1);
  assert.equal(child.status, 5, child.stdout + child.stderr);
  noEffects(child);
  assert.match(child.stderr, /files changed during discovery/);
});

test('preservation: small JSON-named Story text retains title fallback and normal criteria validation', t => {
  const { root, normal } = fixture(t);
  normal('tests/story.json');
  const found = findTests({ root }), selected = selectTests(found).selected;
  assert.equal(selected[0].title, 'Echo');
  assert.equal(preflight({ root, found, selected }).rows[0].refusals.length, 0);
});

test('preservation: malformed ordinary JSON and small symlinks retain real CLI no-tests guidance', t => {
  const { root, cli } = fixture(t), path = 'tests/ordinary.json';
  write(root, path, '{bad json');
  fs.symlinkSync('ordinary.json', join(root, 'tests/config.json'));
  fs.symlinkSync('missing', join(root, 'tests/dangling.json'));
  for (const args of [['check'], ['check', '--files'], ['try']]) {
    const child = cli(args, path);
    assert.equal(child.status, 2, child.stderr);
    noEffects(child);
    assert.match(child.stderr, /No tests found/);
    assert.match(child.stderr, /tests\/ordinary.json is not a PDD test file/);
    assert.doesNotMatch(child.stderr, /config.json|dangling.json/);
  }
});

test('auxiliary numeric review metadata retains snapshot errors during validation', t => {
  const { root, cli, normal } = fixture(t), path = 'pdd-numeric-reviews.json';
  normal();
  // A separate local refusal keeps even the old control away from authentication.
  write(root, 'tests/echo.json', JSON.stringify({ ...scenario('user_stories/echo.md'), criteria_scope: [] }));
  write(root, path, JSON.stringify({ schema_version: 'pdd.numeric-reviews.v1', reviews: [] }));
  const child = cli(['check'], path, { mutate: 2 });
  assert.equal(child.events.filter(row => row.op === 'growth').length, 1);
  assert.equal(child.status, 5, child.stdout + child.stderr);
  noEffects(child);
  assert.match(child.stderr, /files changed during discovery/);
});

test('auxiliary numeric-review test hash detects growth during its actual reread', t => {
  const { root, cli, normal } = fixture(t), path = 'tests/echo.json';
  normal();
  write(root, path, JSON.stringify({ ...scenario('user_stories/echo.md'), criteria_scope: [] }));
  write(root, 'pdd-numeric-reviews.json', JSON.stringify({ schema_version: 'pdd.numeric-reviews.v1', reviews: [{
    test_path: path, test_sha256: createHash('sha256').update(fs.readFileSync(join(root, path))).digest('hex'),
    step_id: 'echo', criterion_id: 'AC1', target: 'result', path: '/text', value: 1, reason: 'Unrelated numeric advice.',
  }] }));
  const child = cli(['check'], path, { mutate: 2 });
  assert.equal(child.events.filter(row => row.op === 'growth').length, 1);
  assert.equal(child.status, 5, child.stdout + child.stderr);
  noEffects(child);
  assert.match(child.stderr, /files changed during discovery/);
});
