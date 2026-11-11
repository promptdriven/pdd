import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdirSync, mkdtempSync, readFileSync, renameSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const script = fileURLToPath(new URL('../scripts/check-generated-source.mjs', import.meta.url));
const sha = text => createHash('sha256').update(text).digest('hex');
const prompt = 'prompts/order.prompt.md', source = 'src/order.mjs';
const before = '# Order\n\nCount the orders.\n', after = '# Order\n\nCount the paid orders.\n';
const header = (path, digest) => `// Generated from ${path} (sha256: ${digest}).\nexport const count = 1;\n`;
function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-header-check-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const git = (...args) => execFileSync('git', args, { cwd: root, encoding: 'utf8' }).trim();
  git('init', '-q', '-b', 'main');
  git('config', 'user.name', 'Header test'); git('config', 'user.email', 'header@example.invalid');
  const write = (path, text) => { mkdirSync(dirname(join(root, path)), { recursive: true }); writeFileSync(join(root, path), text); };
  const commit = () => { git('add', '.'); git('commit', '-qm', 'fixture'); return git('rev-parse', 'HEAD'); };
  write(prompt, before); write(source, header(prompt, sha(before)));
  const base = commit();
  const check = (...args) => spawnSync(process.execPath, [script, ...args], { cwd: root, encoding: 'utf8' });
  return { root, git, write, commit, base, check, run: () => check('--base', base) };
}

test('changed source reports all stale headers and both digests without rewriting files', t => {
  const f = fixture(t), second = 'prompts/second.prompt.md';
  f.write(second, after);
  const bytes = header(prompt, 'a'.repeat(64)) + header(second, 'b'.repeat(64));
  f.write(source, bytes);
  const result = f.run();
  assert.equal(result.status, 1);
  assert.equal(result.stdout, '');
  assert.equal(result.stderr, `${source}: ${prompt} expected=${sha(before)} current=${'a'.repeat(64)} state=stale\n`
    + `${source}: ${second} expected=${sha(after)} current=${'b'.repeat(64)} state=stale\n`);
  assert.equal(readFileSync(join(f.root, source), 'utf8'), bytes);
  assert.equal(readFileSync(join(f.root, prompt), 'utf8'), before);
});

test('a prompt-only edit checks unchanged generated source', t => {
  const f = fixture(t); f.write(prompt, after);
  const result = f.run();
  assert.equal(result.status, 1);
  assert.equal(result.stderr, `${source}: ${prompt} expected=${sha(after)} current=${sha(before)} state=stale\n`);
});

test('integration of alpha prompts checks unchanged source against the target revision', t => {
  const f = fixture(t);
  f.git('checkout', '-qb', 'alpha'); f.write(prompt, after); f.commit();
  f.git('checkout', '-q', 'main'); f.write('topic.txt', 'topic work\n'); f.commit();
  f.git('merge', '-q', '--no-ff', '-m', 'integrate alpha', 'alpha');
  const result = f.run();
  assert.equal(result.status, 1);
  assert.match(result.stderr, new RegExp(`expected=${sha(after)} current=${sha(before)}`));
  f.write(source, header(prompt, sha(after)));
  assert.equal(f.run().status, 0);
});

test('a correct header passes while unrelated stale debt is excluded', t => {
  const f = fixture(t);
  f.write('prompts/unrelated.prompt.md', before);
  f.write('src/unrelated.mjs', header('prompts/unrelated.prompt.md', 'a'.repeat(64)));
  const base = f.commit();
  f.write(source, header(prompt, sha(before)) + '// edit\n');
  const result = f.check('--base', base);
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stdout, 'Generated-source digests: 1 checked; 0 mismatches.\n');
});

test('approval metadata leaves a behavior digest current', t => {
  const f = fixture(t);
  const prefix = '# Order\n\nCount.\n\n<details><summary>Runtime interface</summary>\n\n```json\n';
  const suffix = '\n```\n\n</details>\n';
  const declarations = { entries: [], calls: [] };
  const behavior = sha(prefix + JSON.stringify(declarations) + suffix);
  f.write(prompt, prefix + JSON.stringify({ status: 'draft', prose_sha256: '', ...declarations }) + suffix);
  f.write(source, header(prompt, behavior)); const base = f.commit();
  f.write(prompt, prefix + JSON.stringify({ status: 'approved', prose_sha256: 'a'.repeat(64), ...declarations }, null, 2) + suffix);
  const result = f.check('--base', base);
  assert.equal(result.status, 0, result.stderr);
  assert.match(result.stdout, /1 checked; 0 mismatches/);
});

test('a removed owning prompt fails with unavailable expected digest', t => {
  const f = fixture(t); rmSync(join(f.root, prompt));
  const result = f.run();
  assert.equal(result.status, 1);
  assert.equal(result.stderr, `${source}: ${prompt} expected=unavailable current=${sha(before)} state=unknown\n`);
});

test('deleted source and hashless headers need no digest check', t => {
  const f = fixture(t); rmSync(join(f.root, source));
  f.write('src/hashless.mjs', `// Generated from ${prompt}.\n`);
  f.write(prompt, after);
  const result = f.run();
  assert.equal(result.status, 0, result.stderr);
  assert.match(result.stdout, /0 checked; 0 mismatches/);
});

test('untracked sources and renamed paths with spaces and newlines are checked', t => {
  const f = fixture(t), path = 'src/renamed order\nfile.mjs';
  renameSync(join(f.root, source), join(f.root, path));
  f.write(path, header(prompt, 'a'.repeat(64)));
  const result = f.run();
  assert.equal(result.status, 1);
  assert.ok(result.stderr.includes(`${JSON.stringify(path)}: ${prompt} expected=${sha(before)} current=${'a'.repeat(64)}`));
  assert.equal(result.stderr.trimEnd().split('\n').length, 1);
});

for (const bound of [false, true]) test(`an unreadable affected source cannot pass (binding=${bound})`, t => {
  const f = fixture(t); rmSync(join(f.root, source)); mkdirSync(join(f.root, source));
  if (bound) f.write('pdd-bindings.json', JSON.stringify({ schema_version: 'pdd.bindings.v1', modules: [{ module: source, prompt }] }));
  const result = f.run();
  assert.equal(result.status, 2);
  assert.equal(result.stdout, '');
  assert.match(result.stderr, /cannot read src\/order.mjs/);
});

test('an interface declaration change stales behavior digests while the whole-file compatibility form still passes', t => {
  const f = fixture(t);
  const prefix = '# Order\n\n<details><summary>Runtime interface</summary>\n\n```json\n';
  const suffix = '\n```\n\n</details>\n';
  const declarations = { entries: [], calls: [] };
  const bytes = prefix + JSON.stringify({ status: 'draft', prose_sha256: '', ...declarations }) + suffix;
  const behavior = sha(prefix + JSON.stringify(declarations) + suffix);
  f.write(prompt, bytes);
  f.write(source, header(prompt, behavior));
  f.write('src/legacy.mjs', header(prompt, sha(bytes)));
  const base = f.commit();
  f.write(source, header(prompt, behavior) + '// edit\n');
  f.write('src/legacy.mjs', header(prompt, sha(bytes)) + '// edit\n');
  assert.equal(f.check('--base', base).status, 0);
  f.write(prompt, prefix + JSON.stringify({ status: 'draft', prose_sha256: '', entries: [], calls: [], limits: { max_steps: 2 } }) + suffix);
  const result = f.check('--base', base);
  assert.equal(result.status, 1);
  assert.equal(result.stderr.trimEnd().split('\n').length, 2);
  assert.ok(result.stderr.includes(`current=${behavior} state=stale`));
  assert.ok(result.stderr.includes(`current=${sha(bytes)} state=stale`));
});

test('missing or invalid comparisons fail closed', t => {
  const f = fixture(t);
  for (const args of [[], ['--base'], ['--base', f.base, '--extra'], ['--base', 'does-not-exist']]) {
    const result = f.check(...args);
    assert.equal(result.status, 2, JSON.stringify(args));
    assert.equal(result.stdout, '');
    assert.match(result.stderr, /generated-source check:/i);
  }
});
