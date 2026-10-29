import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cpSync, mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';

const bin = resolve(import.meta.dirname, '../bin/pdd.mjs');
const version = JSON.parse(readFileSync(new URL('../package.json', import.meta.url))).version;
const branch = spawnSync('git', ['symbolic-ref', '--short', 'HEAD'], { encoding: 'utf8' }).stdout.trim();
const sha9 = spawnSync('git', ['rev-parse', 'HEAD'], { encoding: 'utf8' }).stdout.trim().slice(0, 9);
const checkoutVersion = `${version}-dev.${branch.replaceAll('/', '-')}.${sha9}`;
function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), "pdd-path ' proof-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const old = join(root, 'conda-bin'), alpha = join(root, 'alpha-bin'), nodeBin = join(root, 'node-bin'), home = join(root, 'home'), cwd = join(root, 'project');
  for (const path of [old, alpha, nodeBin, home, cwd]) mkdirSync(path);
  symlinkSync(process.execPath, join(nodeBin, 'node'));
  const legacy = '#!/bin/sh\nprintf "pdd, version 0.0.305.dev214\\n"\n';
  writeFileSync(join(old, 'pdd'), legacy, { mode: 0o755 });
  symlinkSync(bin, join(alpha, 'pdd'));
  const env = { ...process.env, HOME: home, CODEX_HOME: join(home, '.codex'), CLAUDE_CONFIG_DIR: '', PATH: [old, alpha, nodeBin, '/usr/bin', '/bin'].join(':') };
  delete env.PDD_PATH_PROBE;
  const run = (...args) => spawnSync(process.execPath, [bin, ...args], { cwd, env, encoding: 'utf8', timeout: 10000 });
  return { root, old, alpha, nodeBin, cwd, env, run, legacy };
}

test('PATH1: setup and version identify the running Alpha, selected legacy version, all paths and activation order', t => {
  const f = fixture(t);
  for (const args of [['setup'], ['--version']]) {
    const r = f.run(...args);
    assert.equal(r.status, 0, r.stderr);
    if (args[0] === '--version') assert.equal(r.stdout, `${checkoutVersion}\n`);
    assert.ok(r.stderr.includes(bin)); assert.ok(r.stderr.includes(`PDD Alpha ${version}`));
    assert.ok(r.stderr.includes(join(f.old, 'pdd'))); assert.ok(r.stderr.includes(join(f.alpha, 'pdd')));
    assert.match(r.stderr, /PATH selects:.*pdd, version 0\.0\.305\.dev214/);
    assert.match(r.stderr, /conda/); assert.match(r.stderr, /after.*activat/i); assert.match(r.stderr, /shadow Alpha again/);
    assert.ok(r.stderr.includes(process.execPath)); assert.match(r.stderr, /export PATH=.*hash -r/);
    assert.equal(readFileSync(join(f.old, 'pdd'), 'utf8'), f.legacy);
  }
});

test('PATH2: PATH correction selects Alpha and a second version check terminates without recursive probes', t => {
  const f = fixture(t);
  f.env.PATH = [f.alpha, f.old, f.nodeBin, '/usr/bin', '/bin'].join(':');
  const r = f.run('--version');
  assert.equal(r.status, 0, r.stderr); assert.equal(r.stdout, `${checkoutVersion}\n`);
  assert.match(r.stderr, /PATH selects:.*PDD Alpha/);
  assert.ok(r.stderr.includes(join(f.old, 'pdd')));
  rmSync(join(f.old, 'pdd'));
  const second = f.run('--version');
  assert.equal(second.status, 0, second.stderr);
  assert.equal(second.stdout, `${checkoutVersion}\n`);
  assert.match(second.stderr, /PATH selects:.*PDD Alpha/);
});

test('PATH3: an unreportable version stays visible and help makes no version probe', t => {
  const f = fixture(t), mark = join(f.root, 'probed');
  writeFileSync(join(f.old, 'pdd'), '#!/bin/sh\necho probed > "'+mark+'"\nexit 7\n', { mode: 0o755 });
  assert.equal(f.run('--help').stderr, '');
  assert.throws(() => readFileSync(mark), { code: 'ENOENT' });
  const r = f.run('--version');
  assert.equal(r.status, 0); assert.match(r.stderr, /PATH selects:.*version unavailable/);
  assert.equal(readFileSync(mark, 'utf8'), 'probed\n');
});

test('PATH4: workflow startup gives a one-line shadow warning before normal dispatch', async t => {
  const f = fixture(t), stdout = { text: '', write(s) { this.text += s; } }, stderr = { text: '', write(s) { this.text += s; } };
  let called = false;
  assert.equal(await runPdd(['workflow', 'run', 'small-change', '17'], { cwd: f.cwd, env: f.env, stdout, stderr,
    workflowRunner: { startRun: async () => { called = true; return { exitCode: 0, message: 'Local dispatch proof' }; } } }), 0);
  assert.equal(called, true); assert.equal(stdout.text, 'Local dispatch proof\n');
  assert.equal(stderr.text.trim().split('\n').length, 1);
  assert.match(stderr.text, /PATH selects:.*0\.0\.305\.dev214/); assert.ok(stderr.text.includes(bin));
});

test('PATH5: without which, relative PATH entries and symlinked Alpha still resolve correctly', t => {
  const f = fixture(t);
  f.env.PATH = '../conda-bin:../alpha-bin';
  const r = f.run('--version');
  assert.equal(r.status, 0, r.stderr); assert.equal(r.stdout, `${version}\n`);
  assert.match(r.stderr, /PATH selects:.*0\.0\.305\.dev214/);
  assert.ok(r.stderr.includes(join(f.alpha, 'pdd')));
});

test('PATH6: probing another Alpha installation terminates and keeps version-only stdout', t => {
  const f = fixture(t), other = join(f.root, 'other-alpha');
  mkdirSync(other);
  for (const name of ['src', 'bin', 'package.json']) cpSync(resolve(import.meta.dirname, '..', name), join(other, name), { recursive: true });
  rmSync(join(f.old, 'pdd')); symlinkSync(join(other, 'bin/pdd.mjs'), join(f.old, 'pdd'));
  const r = f.run('--version');
  assert.equal(r.status, 0, r.stderr); assert.equal(r.stdout, `${checkoutVersion}\n`);
  assert.match(r.stderr, new RegExp(`PATH selects:.*\\(${version.replaceAll('.', '\\.')}\\)`));
});

test('PATH7: a hanging external version probe is bounded and leaves the installation intact', t => {
  const f = fixture(t), hanging = '#!/bin/sh\nexec /bin/sleep 10\n';
  writeFileSync(join(f.old, 'pdd'), hanging, { mode: 0o755 });
  const r = f.run('--version');
  assert.equal(r.status, 0); assert.match(r.stderr, /PATH selects:.*version unavailable/);
  assert.equal(readFileSync(join(f.old, 'pdd'), 'utf8'), hanging);
});
