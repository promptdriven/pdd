import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { fillHashes } from '../src/runtime-preflight.mjs';
import { runCheck } from '../src/runtime-client.mjs';

// Independent native expectations were fixed in prompt space. Do not rewrite them.
const vectors = JSON.parse(fs.readFileSync(new URL('./fixtures/fill-hash/compact-cases.json', import.meta.url)));
const fixture = vectors.fixture;
const buckets = ['filled', 'current', 'refused', 'stale', 'warnings'];
const cli = fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url));
const sink = () => ({ text: '', write(value) { this.text += value; } });
const source = (row, body = row.before_body) => fixture.prefix
  + (fixture.block_prefix + body + fixture.block_suffix).repeat(row.block_count) + fixture.suffix;
function setup(t, rows) {
  const folder = fs.mkdtempSync(join(tmpdir(), 'pdd-compact-'));
  t.after(() => fs.rmSync(folder, { recursive: true, force: true }));
  const repo = join(folder, 'repo'), home = join(folder, 'home'), state = join(folder, 'state');
  fs.mkdirSync(repo); fs.mkdirSync(home);
  assert.equal(spawnSync('git', ['init', '-q'], { cwd: repo }).status, 0);
  for (const row of rows) {
    fs.mkdirSync(dirname(join(repo, row.path)), { recursive: true });
    fs.writeFileSync(join(repo, row.path), source(row));
  }
  return { folder, repo, home, state, rows };
}
function bytes(state, expected = true) {
  for (const row of state.rows) assert.deepEqual(fs.readFileSync(join(state.repo, row.path)),
    Buffer.from(source(row, expected ? row.expected_body : row.before_body)), row.id);
  assert.equal(fs.existsSync(state.state), false, 'local operation creates no runtime state');
  assert.deepEqual(fs.readdirSync(state.home), [], 'no authentication or home state');
}
function resultShape(result, row) {
  assert.deepEqual(Object.keys(result), row.compact ? [...buckets, 'compacted'] : buckets, row.id);
  if (row.expected_result) assert.deepEqual(result, row.expected_result, row.id);
  else for (const name of [...buckets, 'compacted']) {
    const expected = name === row.expected_outcome ? [{ path: row.path }] : [];
    assert.deepEqual(result[name].map(({ path }) => ({ path })), expected, `${row.id}: ${name}`);
    for (const value of result[name]) {
      assert.deepEqual(Object.keys(value), ['path', 'message']);
      for (const fragment of row.message_contains) assert.ok(value.message.includes(fragment), value.message);
    }
  }
}
function countedWrites(action) {
  const original = fs.writeFileSync;
  let count = 0;
  fs.writeFileSync = (...args) => { count++; return original(...args); };
  syncBuiltinESMExports();
  try { return { result: action(), writes: count }; }
  finally { fs.writeFileSync = original; syncBuiltinESMExports(); }
}
function checkOutput(output, rows, compact) {
  const lines = output.trimEnd().split('\n');
  const counts = Object.fromEntries(buckets.map(name => [name, rows.filter(row => row.expected_outcome === name).length]));
  const expected = [];
  for (const row of rows.filter(row => row.expected_outcome === 'warnings')) {
    const line = lines[expected.length]; assert.ok(line.startsWith('Warning: '));
    for (const part of [row.path, ...row.message_contains]) assert.ok(line.includes(part), line);
    expected.push(line);
  }
  for (const row of rows.filter(row => row.expected_outcome === 'filled')) expected.push(`Filled prose_sha256: ${row.path}`);
  if (compact) for (const row of rows.filter(row => row.expected_compacted)) expected.push(`Compacted Runtime interface: ${row.path}`);
  for (const row of rows.filter(row => row.expected_outcome === 'refused')) {
    const line = lines[expected.length]; assert.ok(line.startsWith('Refused: '));
    for (const part of [row.path, ...row.message_contains]) assert.ok(line.includes(part), line);
    expected.push(line);
  }
  for (const row of rows.filter(row => row.expected_outcome === 'stale')) expected.push(`Stale: ${row.path} is approved, but the text changed after approval: set status to draft, run pdd test --fill-hash, ask the person.`);
  if (compact) expected.push(`Interfaces: ${rows.filter(row => row.expected_compacted).length} compacted.`);
  expected.push(`Hashes: ${counts.filled} filled, ${counts.current} current, ${counts.refused} refused, ${counts.stale} stale.`);
  assert.equal(output, expected.join('\n') + '\n');
}
function noExternalPorts(state) {
  const calls = { fetch: 0, gh: 0 };
  const stdout = sink(), stderr = sink();
  return { calls, stdout, stderr, env: { HOME: state.home, PDD_INTERPRETER_QUEUE: join(state.home, 'interpreter-queue'), PDD_STATE_DIR: state.state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' },
    fetch: () => { calls.fetch++; assert.fail('unexpected network'); },
    gh: () => { calls.gh++; assert.fail('unexpected sign-in'); },
    screenBrowser: () => assert.fail('unexpected browser') };
}
function publicCli(state, name, argv) {
  // The actual executable has no gh available. A fetch tripwire catches any network attempt.
  const bin = join(state.folder, 'bin');
  if (!fs.existsSync(bin)) {
    fs.mkdirSync(bin);
    const git = spawnSync('which', ['git'], { encoding: 'utf8' }); assert.equal(git.status, 0);
    fs.symlinkSync(git.stdout.trim(), join(bin, 'git'));
    fs.writeFileSync(join(bin, 'gh'), '#!/bin/sh\nprintf "gh\\n" >> "$PDD_TEST_AUDIT"\nexit 97\n', { mode: 0o755 });
    fs.writeFileSync(join(state.folder, 'no-network.mjs'), `
import fs from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
const original = fs.writeFileSync;
const audit = fs.openSync(process.env.PDD_TEST_AUDIT, 'a');
fs.writeFileSync = (...args) => {
  fs.writeSync(audit, 'write:' + args[0] + '\\n');
  return original(...args);
};
syncBuiltinESMExports();
globalThis.fetch = () => {
  fs.writeSync(audit, 'fetch\\n');
  throw Error('UNEXPECTED NETWORK');
};
`);
  }
  const audit = join(state.folder, 'audit.txt'); fs.writeFileSync(audit, '');
  const out = spawnSync(process.execPath, ['--import', join(state.folder, 'no-network.mjs'), cli, name, ...argv], {
    cwd: state.repo, input: '', encoding: 'utf8', timeout: 30000,
    env: { HOME: state.home, PDD_INTERPRETER_QUEUE: join(state.home, 'interpreter-queue'), PATH: bin, PDD_TEST_AUDIT: audit, PDD_STATE_DIR: state.state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' },
  });
  assert.equal(out.error, undefined); assert.equal(out.signal, null);
  const effects = fs.readFileSync(audit, 'utf8').split('\n').filter(Boolean);
  assert.ok(effects.every(value => value.startsWith('write:')), effects.join('\n'));
  out.writes = effects.length;
  assert.ok(!out.stderr.includes('UNEXPECTED NETWORK'), out.stderr);
  return out;
}

test('compact Story replays all 18 literal byte/result vectors at preflight and direct handler', async t => {
  assert.equal(vectors.cases.length, 18);
  assert.equal(createHash('sha256').update(fixture.prefix + fixture.suffix).digest('hex'), fixture.expected_prose_sha256);
  for (const row of vectors.cases) {
    for (const omitted of row.compact ? [false] : [false, true]) {
      const state = setup(t, [row]);
      const { result, writes } = countedWrites(() => fillHashes({ root: state.repo, ...(omitted ? {} : { compact: row.compact }) }));
      resultShape(result, row); assert.equal(writes, row.expected_writes, row.id); bytes(state);
      if (row.exit_code === 0 && row.compact && ['filled', 'current'].includes(row.expected_outcome)) {
        const second = countedWrites(() => fillHashes({ root: state.repo, compact: true }));
        assert.deepEqual(second, { result: { filled: [], current: [{ path: row.path }], refused: [], stale: [], warnings: [], compacted: [] }, writes: 0 }, row.id);
        bytes(state);
      }
    }
    const state = setup(t, [row]), ports = noExternalPorts(state);
    assert.equal(await runCheck({ cwd: state.repo, options: { '--fill-hash': true, ...(row.compact ? { '--compact': true } : {}) } }, ports), row.exit_code, row.id);
    checkOutput(ports.stdout.text, [row], row.compact); assert.equal(ports.stderr.text, '');
    assert.deepEqual(ports.calls, { fetch: 0, gh: 0 }); bytes(state);
  }
});

test('real public test command replays all byte vectors', t => {
  for (const row of vectors.cases) {
    const name = 'test';
    const state = setup(t, [row]);
    const result = publicCli(state, name, ['--fill-hash', ...(row.compact ? ['--compact'] : [])]);
    assert.equal(result.status, row.exit_code, `${row.id}: ${result.stdout}\n${result.stderr}`);
    assert.equal(result.stderr, '');
    assert.equal(result.writes, row.expected_writes, row.id);
    checkOutput(result.stdout, [row], row.compact); bytes(state);
    if (row.id === 'pretty-draft') {
      const second = publicCli(state, name, ['--fill-hash', '--compact']);
      assert.equal(second.status, 0); assert.equal(second.writes, 0);
      assert.equal(second.stdout, 'Interfaces: 0 compacted.\nHashes: 0 filled, 1 current, 0 refused, 0 stale.\n'); bytes(state);
    }
  }
});

test('removed check name rejects compact success and refusal inputs before effects', t => {
  for (const id of ['pretty-draft', 'ambiguous-hash']) {
    const row = vectors.cases.find(row => row.id === id), state = setup(t, [row]);
    const result = publicCli(state, 'check', ['--fill-hash', '--compact']);
    assert.equal(result.status, 2);
    assert.equal(result.stdout, '');
    assert.equal(result.stderr, 'pdd check was removed. Use pdd test.\n');
    assert.equal(result.writes, 0); bytes(state, false);
  }
});

function directInput(argv) {
  const options = {}, words = [];
  const values = new Set(['--retry', '--screen', '--drawing', '--max-calls', '--timeout']);
  for (let i = 0; i < argv.length; i++) {
    if (argv[i].startsWith('--')) options[argv[i]] = values.has(argv[i]) ? argv[++i] : true;
    else words.push(argv[i]);
  }
  return { words, options };
}
test('all 12 flag conflicts reject before files, state, browser, sign-in or network', async t => {
  assert.equal(vectors.invalid_combinations.length, 12);
  const row = vectors.cases.find(row => row.id === 'pretty-draft');
  const extras = [
    ['--fill-hash', '--compact', '--lint', '--local'],
    ['--fill-hash', '--compact', '--screen', 'https://example.test', '--drawing', 'view.ui.svg'],
    ['--fill-hash', '--compact', '--details'],
    ['--fill-hash', '--compact', '--app-map', 'map.json'],
    ['--compact', '--lf'],
    ['--compact', '--cache-clear'],
    ['--fill-hash', '--compact', '--lf'],
    ['--fill-hash', '--compact', '--cache-clear'],
  ];
  for (const argv of [...vectors.invalid_combinations.map(row => row.argv), ...extras]) {
    const state = setup(t, [row]), ports = noExternalPorts(state);
    const code = await runCheck({ cwd: join(state.folder, 'does-not-exist'), ...directInput(argv) }, ports);
    assert.equal(code, 2, argv.join(' ')); assert.equal(ports.stdout.text, '');
    assert.match(ports.stderr.text, /--compact requires --fill-hash/);
    assert.deepEqual(ports.calls, { fetch: 0, gh: 0 }); bytes(state, false);
    const result = publicCli(state, 'test', argv);
    assert.equal(result.status, 2, `${argv}: ${result.stdout}\n${result.stderr}`);
    assert.equal(result.stdout, ''); assert.equal(result.writes, 0); bytes(state, false);
  }
});

test('compact help stays local and retains current-main test options', t => {
  const row = vectors.cases.find(row => row.id === 'pretty-draft');
  for (const argv of [['--fill-hash', '--compact', '--help'], ['--compact', '--lf', '--cache-clear', '--help']]) {
    const state = setup(t, [row]), result = publicCli(state, 'test', argv);
    assert.equal(result.status, 0);
    assert.equal(result.stderr, '');
    assert.ok(result.stdout.includes('pdd test --fill-hash --compact'));
    assert.ok(result.stdout.includes('[--lf] [--cache-clear]'));
    assert.equal(result.writes, 0); bytes(state, false);
  }
});

test('safe draft edits survive a refused sibling with CLI group order intact', async t => {
  const rows = ['pretty-draft', 'statusless', 'ambiguous-hash', 'approved-stale'].map((id, i) => ({
    ...vectors.cases.find(row => row.id === id), path: `prompts/${i}-${id}.prompt.md`,
  }));
  const state = setup(t, rows), ports = noExternalPorts(state);
  assert.equal(await runCheck({ cwd: state.repo, options: { '--fill-hash': true, '--compact': true } }, ports), 4);
  checkOutput(ports.stdout.text, rows, true); bytes(state);
  const cliState = setup(t, rows), result = publicCli(cliState, 'test', ['--fill-hash', '--compact']);
  assert.equal(result.status, 4); assert.equal(result.stderr, '');
  checkOutput(result.stdout, rows, true); bytes(cliState);
});
