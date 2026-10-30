import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import child from 'node:child_process';
import http from 'node:http';
import https from 'node:https';
import net from 'node:net';
import { syncBuiltinESMExports } from 'node:module';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const vectors = JSON.parse(fs.readFileSync(join(root, 'test/shared-contracts/local-contract-check.json'), 'utf8'));

// Observe native effects at their real imported boundaries. Network attempts are
// counted then refused so an accidental dispatch cannot reach a live service.
// Runtime/model zero counts below are implications of zero network dispatches;
// slot zero is an implication of zero network dispatches AND zero native writes.
// These implications cover this native command, not arbitrary external programs.
function observe({ state, symlinkTarget }) {
  const calls = { runtime: 0, model: 0, auth: 0, slots: 0, history: 0, write: 0, symlink_target_read: 0 };
  const undo = [];
  const patch = (owner, key, wrap) => {
    if (typeof owner[key] !== 'function') return;
    const old = owner[key]; owner[key] = wrap(old); undo.push(() => { owner[key] = old; });
  };
  const pathOf = value => typeof value === 'string' ? resolve(value) : value instanceof URL ? fileURLToPath(value) : '';
  for (const name of ['readFileSync', 'readdirSync', 'statSync', 'lstatSync', 'accessSync', 'realpathSync', 'openSync']) {
    patch(fs, name, old => function(path, ...args) {
      const actual = pathOf(path);
      if (actual === state || actual.startsWith(`${state}/`)) calls.history++;
      if (actual === symlinkTarget && ['readFileSync', 'openSync'].includes(name)) calls.symlink_target_read++;
      if (name === 'openSync' && (typeof args[0] === 'string' ? /[wa+]/.test(args[0]) : !!(args[0] & (fs.constants.O_WRONLY | fs.constants.O_RDWR | fs.constants.O_CREAT)))) calls.write++;
      return Reflect.apply(old, this, [path, ...args]);
    });
  }
  for (const name of ['writeFileSync', 'appendFileSync', 'writeSync', 'renameSync', 'unlinkSync', 'mkdirSync', 'rmSync', 'rmdirSync', 'truncateSync', 'ftruncateSync', 'chmodSync', 'fchmodSync', 'symlinkSync', 'linkSync', 'copyFileSync']) {
    patch(fs, name, old => function(...args) { calls.write++; return Reflect.apply(old, this, args); });
  }
  for (const name of ['spawnSync', 'spawn', 'execSync', 'exec', 'execFileSync', 'execFile', 'fork']) {
    patch(child, name, old => function(command, ...args) {
      // Git discovery is the command's permitted subprocess. Any other program
      // could authenticate or dispatch: record it and refuse that attempt.
      if (String(command) !== 'git') { calls.auth++; throw new Error('Observed unexpected external program'); }
      return Reflect.apply(old, this, [command, ...args]);
    });
  }
  const dispatch = () => { calls.runtime++; calls.model++; calls.slots++; throw new Error('Observed unexpected network dispatch'); };
  for (const owner of [http, https]) for (const key of ['request', 'get']) patch(owner, key, () => dispatch);
  for (const key of ['connect', 'createConnection']) patch(net, key, () => dispatch);
  patch(globalThis, 'fetch', () => dispatch);
  syncBuiltinESMExports();
  return { calls, restore() { for (const restore of undo.reverse()) restore(); syncBuiltinESMExports(); } };
}
function snapshot(folder) {
  const result = {};
  const walk = relative => {
    for (const name of fs.readdirSync(join(folder, relative))) {
      if (name === '.git') continue;
      const path = join(relative, name), info = fs.lstatSync(join(folder, path));
      if (info.isSymbolicLink()) result[path] = { link: fs.readlinkSync(join(folder, path)) };
      else if (info.isDirectory()) walk(path);
      else result[path] = fs.readFileSync(join(folder, path)).toString('base64');
    }
  };
  walk(''); return result;
}

test('native effect observers detect calibrated writes, history, programs and dispatch', () => {
  const folder = fs.mkdtempSync(join(tmpdir(), 'pdd-contract-observers-'));
  const state = join(folder, 'state'); fs.mkdirSync(state);
  const symlinkTarget = join(folder, 'outside'); fs.writeFileSync(symlinkTarget, 'sentinel');
  const observed = observe({state, symlinkTarget});
  try {
    fs.writeFileSync(join(folder, 'calibration'), 'x');
    fs.readdirSync(state);
    const targetFd = fs.openSync(symlinkTarget, 'r'); fs.closeSync(targetFd);
    assert.equal(observed.calls.symlink_target_read, 1);
    assert.throws(() => child.spawnSync('observer-calibration-no-program'));
    assert.throws(() => http.request('http://127.0.0.1:1'));
    assert.ok(observed.calls.write > 0); assert.ok(observed.calls.history > 0);
    assert.ok(observed.calls.auth > 0); assert.ok(observed.calls.runtime > 0);
    assert.ok(observed.calls.model > 0); assert.ok(observed.calls.slots > 0);
  } finally { observed.restore(); fs.rmSync(folder, {recursive: true, force: true}); }
});

const superseded = new Set(['writer-list','legacy-table-check','unknown-json-role','empty-container-branch','definite-problem-wins-unavailable']);
for (const vector of vectors.cases) test(`local contracts: ${vector.id}`, {skip:superseded.has(vector.id)?'Lead 13:59 superseded; frozen local-contract-layouts replacement':false}, async () => {
  const sandbox = fs.mkdtempSync(join(tmpdir(), 'pdd-local-contract-'));
  const cwd = join(sandbox, 'repo'), state = join(sandbox, 'state');
  fs.mkdirSync(cwd); fs.mkdirSync(state);
  try {
    for (const [path, text] of Object.entries({...vectors.setup.base_files, ...vector.set_files})) {
      fs.mkdirSync(dirname(join(cwd, path)), {recursive: true}); fs.writeFileSync(join(cwd, path), text);
    }
    // The fixture defines deletion before replacement, so replacement wins.
    for (const path of vector.delete_files) if (!Object.hasOwn(vector.set_files, path)) fs.rmSync(join(cwd, path), {force: true});
    // Symlink targets are external sentinels, not another Git-visible contract
    // that independent discovery could legitimately read.
    const symlinkTarget = join(sandbox, 'outside-world.md');
    for (const [path, target] of Object.entries(vector.symlinks ?? {})) {
      fs.rmSync(join(cwd, path), {force: true});
      const outside = join(sandbox, target); fs.writeFileSync(outside, 'outside sentinel');
      fs.symlinkSync(outside, join(cwd, path));
    }
    if (vector.git_repository !== false) {
      assert.equal(child.spawnSync('git', ['init', '-q'], {cwd}).status, 0);
      assert.equal(child.spawnSync('git', ['add', '.'], {cwd}).status, 0);
    }
    const before = snapshot(cwd);
    let stdout = '', stderr = '';
    const words = vector.argv.slice(1).filter(word => !word.startsWith('--'));
    const options = Object.fromEntries(vector.argv.filter(word => word.startsWith('--')).map(word => [word, true]));
    // Import before observation: module-loader reads are not command effects.
    const { runContracts } = await import('../src/contracts.mjs');
    const observed = observe({state, symlinkTarget});
    let result;
    try {
      result = await runContracts({words, options, cwd}, {env: {...process.env, PDD_STATE_DIR: state}, stdout: {write: text => { stdout += text; }}, stderr: {write: text => { stderr += text; }}});
    } finally { observed.restore(); }
    assert.equal(result, vector.expected.exit_code);
    const lines = `${stdout}\n${stderr}`.split(/\r?\n/);
    if (!vector.expected.diagnostics.length) {
      // Observe the empty expectation too. Listing/sync advisory warnings are
      // allowed; structured problem locations and unavailable verdicts are not.
      const located = lines.filter(line => !/^Warning:/.test(line) && /^[^:\r\n]+\.(?:md|json): .+: /.test(line));
      assert.deepEqual(located, [], 'unexpected located contract problem');
      if (options['--check'] && result === 0) assert.equal(lines.some(line => /validation unavailable/i.test(line)), false);
    }
    for (const diagnostic of vector.expected.diagnostics) {
      assert.ok(lines.some(line => line.length <= 8000 && line.includes(diagnostic.file) && line.includes(diagnostic.record) && line.includes(diagnostic.field) && (diagnostic.kind !== 'unavailable' || /unavailable/i.test(line))), JSON.stringify(diagnostic));
    }
    for (const [key, value] of Object.entries(vector.expected.calls)) {
      assert.ok(Object.hasOwn(observed.calls, key), `Not replayed: calls.${key}`);
      assert.equal(observed.calls[key], value, `calls.${key}`);
    }
    if (vector.expected.source_bytes_unchanged) assert.deepEqual(snapshot(cwd), before);
    for (const [key, label] of [['checked_records', 'records?'], ['checked_world_values', 'world[ -]values?']]) {
      if (Object.hasOwn(vector.expected, key)) assert.match(stdout, new RegExp(`(?:${vector.expected[key]}\\s+${label}|${label}\\s*[:=]\\s*${vector.expected[key]})`, 'i'), key);
    }
    const mapped = new Set(['exit_code', 'diagnostics', 'calls', 'source_bytes_unchanged', 'checked_records', 'checked_world_values']);
    for (const key of Object.keys(vector.expected)) assert.ok(mapped.has(key), `Not replayed: expected.${key}`);
  } finally { fs.rmSync(sandbox, {recursive: true, force: true}); }
});
