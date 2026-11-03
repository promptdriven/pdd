import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { fillHashes } from '../src/runtime-preflight.mjs';

// Story-derived oracle: concatenate authored JSON tokens. Never scan or compact
// the source to obtain expected bytes. Deliberately retain duplicate keys,
// number spellings, literal string spaces, and odd/even backslash runs.
const whitespace = ['', ' ', '\t', '\r', '\n', ' \t\r\n'];
const strings = [
  '"keep  spaces"',
  String.raw`"quote \"  tail"`,
  String.raw`"backslash \\  tail"`,
  String.raw`"three \\\"  tail"`,
  String.raw`"escapes \n\t\r\u0041\/  tail"`,
  '"雪  café 😀"',
];
const numbers = ['-0', '1e+03', '9007199254740993', '0.1000', '-2E-02', '1e-0'];
const prefix = '# Formal compact bound\r\n\r\nKeep  prose\tbytes.\r\n\r\n';
const suffix = '\r\nOutside  bytes.\t\r\n';
const hash = createHash('sha256').update(prefix + suffix).digest('hex');
const beforeRoot = ' \t\r\n', afterRoot = '\t \r\n';
const source = body => `${prefix}<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${beforeRoot}${body}${afterRoot}\n\`\`\`\n</details>${suffix}`;
const keys = ['filled', 'current', 'refused', 'stale', 'warnings'];
const cli = fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url));

function tokens(content, current = false) {
  return ['{', '"status"', ':', '"draft"', ',', '"prose_sha256"', ':', current ? `"${hash}"` : '""',
    ',', '"payload"', ':', '{', '"text"', ':', strings[content], ',', '"values"', ':', '[',
    numbers[content], ',', 'true', ',', 'false', ',', 'null', ',', '{', '"nested"', ':', '[', ']', '}', ']',
    ',', '"dup"', ':', '1', ',', '"dup"', ':', '2', '}', '}'];
}

// Exact domain: six content pairs x (all 6^3 assignments on three adjacent
// grammar gaps, OR one nonempty member of the alphabet at any remaining gap).
// The selected gaps precede an array item, follow that number, and follow its
// comma. All other gaps are empty in the first arm. This is a finite domain,
// not an assertion about arbitrary JSON nesting or arbitrary whitespace runs.
function cases() {
  const rows = [], gapCount = tokens(0).length - 1;
  const selected = [18, 19, 20];
  const add = (content, gaps) => {
    const current = rows.length % 2 === 0;
    const original = tokens(content, current), filled = tokens(content, true);
    const render = value => value.map((token, i) => token + (gaps[i] ?? '')).join('');
    const compact = filled.join('');
    JSON.parse(compact); // Sanity-check authored grammar; not the byte oracle.
    rows.push({ path: `prompts/c${String(rows.length).padStart(4, '0')}.prompt.md`, current,
      before: source(render(original)), defaultBytes: source(render(filled)), compactBytes: source(compact),
      changed: gaps.some(Boolean) });
  };
  for (let content = 0; content < strings.length; content++) {
    for (const a of whitespace) for (const b of whitespace) for (const c of whitespace) {
      const gaps = Array(gapCount).fill('');
      [a, b, c].forEach((value, i) => { gaps[selected[i]] = value; });
      add(content, gaps);
    }
    for (let gap = 0; gap < gapCount; gap++) if (!selected.includes(gap)) {
      for (const value of whitespace.slice(1)) {
        const gaps = Array(gapCount).fill(''); gaps[gap] = value; add(content, gaps);
      }
    }
  }
  assert.equal(gapCount, 43);
  assert.equal(rows.length, 2496);
  return rows;
}

function setup(t, rows) {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-compact-formal-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  fs.mkdirSync(join(root, 'prompts'));
  assert.equal(spawnSync('git', ['init', '-q'], { cwd: root }).status, 0);
  for (const row of rows) fs.writeFileSync(join(root, row.path), row.before);
  return root;
}
function writeRows(root, rows) {
  for (const row of rows) fs.writeFileSync(join(root, row.path), row.before);
}
function assertBytes(root, rows, field) {
  for (const row of rows) assert.equal(fs.readFileSync(join(root, row.path), 'utf8'), row[field], row.path);
}
function assertResult(result, rows, { compact = false, allCurrent = false } = {}) {
  const records = selected => selected.map(({ path }) => ({ path }));
  assert.deepEqual(Object.keys(result), compact ? [...keys, 'compacted'] : keys);
  assert.deepEqual(result.filled, records(allCurrent ? [] : rows.filter(row => !row.current)));
  assert.deepEqual(result.current, records(allCurrent ? rows : rows.filter(row => row.current)));
  for (const name of ['refused', 'stale', 'warnings']) assert.deepEqual(result[name], []);
  if (compact) assert.deepEqual(result.compacted, records(allCurrent ? [] : rows.filter(row => row.changed)));
}
function noWrites(action) {
  const original = fs.writeFileSync;
  let writes = 0;
  fs.writeFileSync = (...args) => { writes++; return original(...args); };
  syncBuiltinESMExports();
  try { const result = action(); assert.equal(writes, 0, 'idempotent compaction performs zero writes'); return result; }
  finally { fs.writeFileSync = original; syncBuiltinESMExports(); }
}

test('bounded compaction: every one of 2496 token/gap cases through public fillHashes', t => {
  const rows = cases(), root = setup(t, rows), files = rows.map(row => row.path);
  assertResult(fillHashes({ root, files }), rows);
  assertBytes(root, rows, 'defaultBytes');
  assertResult(noWrites(() => fillHashes({ root, files, compact: false })), rows, { allCurrent: true });
  assertBytes(root, rows, 'defaultBytes');
  writeRows(root, rows);
  assertResult(fillHashes({ root, files, compact: true }), rows, { compact: true });
  assertBytes(root, rows, 'compactBytes');
  assertResult(noWrites(() => fillHashes({ root, files, compact: true })), rows, { compact: true, allCurrent: true });
  assertBytes(root, rows, 'compactBytes');
});

test('bounded compaction: all 2496 token/gap cases through public pdd test CLI', t => {
  const rows = cases(), root = setup(t, rows);
  const run = spawnSync(process.execPath, [cli, 'test', '--fill-hash', '--compact'], {
    cwd: root, encoding: 'utf8', maxBuffer: 4 * 1024 * 1024,
    env: { ...process.env, PDD_STATE_DIR: join(root, 'no-runtime-state') },
  });
  assert.equal(run.status, 0, run.stderr);
  assert.equal(run.stderr, '');
  assertBytes(root, rows, 'compactBytes');
  const filled = rows.filter(row => !row.current), compacted = rows.filter(row => row.changed);
  const expected = [
    ...filled.map(row => `Filled prose_sha256: ${row.path}`),
    ...compacted.map(row => `Compacted Runtime interface: ${row.path}`),
    `Interfaces: ${compacted.length} compacted.`,
    `Hashes: ${filled.length} filled, ${rows.length - filled.length} current, 0 refused, 0 stale.`,
  ].join('\n') + '\n';
  assert.equal(run.stdout, expected);
  assert.equal(fs.existsSync(join(root, 'no-runtime-state')), false);
});

test('bounded invalid token splits are refused before whitespace could salvage JSON', t => {
  // Exhaust eight selected token splits x all four JSON whitespace characters.
  const splits = [['tru', 'e'], ['fal', 'se'], ['nu', 'll'], ['1', '0'], ['-', '1'], ['1', 'e+2'], ['1.', '0'], ['1e', '+2']];
  const rows = [];
  for (const [left, right] of splits) for (const gap of whitespace.slice(1, 5)) {
    const body = `{"status":"draft","prose_sha256":"","value":${left}${gap}${right}}`;
    assert.throws(() => JSON.parse(body), SyntaxError);
    // Removing only the introduced gap would make each rejected source valid.
    JSON.parse(`{"status":"draft","prose_sha256":"","value":${left}${right}}`);
    rows.push({ path: `prompts/invalid${rows.length}.prompt.md`, before: source(body) });
  }
  assert.equal(rows.length, 32);
  const root = setup(t, rows), files = rows.map(row => row.path);
  const actual = noWrites(() => fillHashes({ root, files, compact: true }));
  for (const key of ['filled', 'current', 'stale', 'warnings', 'compacted']) assert.deepEqual(actual[key], []);
  assert.deepEqual(actual.refused.map(row => row.path), files);
  for (const row of actual.refused) assert.match(row.message, /not valid JSON/);
  assertBytes(root, rows, 'before');
});

test('bounded status x hash x directory x compact preserves classification and safe siblings: 144 cases', t => {
  const statuses = [undefined, 'draft', 'approved', null, '', 'pending'];
  const hashes = [undefined, '', hash, 'stale'];
  const directories = ['prompts', 'examples', 'test/fixtures'];
  const root = setup(t, []);
  const records = path => [{ path }];
  const body = (status, value, filled = false) => '{\n'
    + [status === undefined ? null : `"status" : ${JSON.stringify(status)}`,
      value === undefined ? null : `"prose_sha256" : ${JSON.stringify(filled ? hash : value)}`]
      .filter(part => part !== null).join(',\n') + '\n}';
  const sibling = 'prompts/safe.prompt.md';
  let checked = 0;
  for (const status of statuses) for (const value of hashes) for (const directory of directories) for (const compact of [false, true]) {
    const path = `${directory}/subject.prompt.md`, before = source(body(status, value));
    fs.mkdirSync(join(root, directory), { recursive: true });
    fs.writeFileSync(join(root, path), before);
    fs.writeFileSync(join(root, sibling), source(body('draft', '')));
    const expected = status === undefined ? (value === undefined ? 'warnings' : 'refused')
      : status === 'approved' ? (value === hash ? 'current' : 'stale')
      : status !== 'draft' || value === undefined ? 'refused'
      : value === hash ? 'current' : 'filled';
    const actual = fillHashes({ root, files: [path, sibling], compact });
    assert.deepEqual(Object.keys(actual), compact ? [...keys, 'compacted'] : keys);
    const label = JSON.stringify({ status, value, directory, compact });
    for (const key of keys) {
      const paths = [...(key === expected ? records(path) : []), ...(key === 'filled' ? records(sibling) : [])];
      assert.deepEqual(actual[key].map(({ path }) => ({ path })), paths, label);
    }
    const safe = status === 'draft' && value !== undefined;
    const expectedBody = compact && safe
      ? ['{', '"status"', ':', '"draft"', ',', '"prose_sha256"', ':', `"${hash}"`, '}'].join('')
      : body(status, value, expected === 'filled');
    assert.equal(fs.readFileSync(join(root, path), 'utf8'), safe ? source(expectedBody) : before, label);
    const siblingBody = compact ? `{"status":"draft","prose_sha256":"${hash}"}` : body('draft', '', true);
    assert.equal(fs.readFileSync(join(root, sibling), 'utf8'), source(siblingBody), label);
    if (compact) assert.deepEqual(actual.compacted, [...(safe ? records(path) : []), ...records(sibling)], label);
    checked++;
  }
  assert.equal(checked, 144);
});
