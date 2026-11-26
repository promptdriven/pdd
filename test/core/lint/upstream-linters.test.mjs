import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { detectUpstreamLinters, formatUpstreamLinterReport, runUpstreamLinters } from '../../../src/core/lint/upstream-linters.mjs';
import { runLocalLint } from '../../../src/core/lint/run-local-lint.mjs';

function mkRepo(t) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-upstream-lint-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: dir });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: dir });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: dir });
  return dir;
}

function makeSink() {
  let text = '';
  return { write(s) { text += String(s); }, get text() { return text; } };
}

test('detects Cargo.toml -> cargo clippy + deslop-please and reports missing tools without auto-installing', t => {
  const dir = mkRepo(t);
  writeFileSync(join(dir, 'Cargo.toml'), '[package]\nname = "demo"\nversion = "0.1.0"\nedition = "2024"\n');
  writeFileSync(join(dir, '.deslop-please.allow'), '# empty allowlist\n');
  execFileSync('git', ['add', '.'], { cwd: dir });
  execFileSync('git', ['commit', '-q', '-m', 'init'], { cwd: dir });

  const specs = detectUpstreamLinters(dir, { env: { PATH: '' } });
  assert.deepEqual(specs.map(s => s.tool), ['cargo clippy', 'deslop-please']);
  assert.deepEqual(specs[1].args, ['--allow', '.deslop-please.allow']);

  const res = runUpstreamLinters(dir, { env: { PATH: '' } });
  assert.equal(res.ok, true, 'missing tools must report not_installed without crashing or auto-installing');
  assert.equal(res.results.length, 2);
  for (const r of res.results) {
    assert.equal(r.status, 'not_installed');
    assert.equal(r.note, 'not run: not installed');
    assert.ok(r.install_hint && r.install_hint.length > 0);
  }
  const text = formatUpstreamLinterReport(res.results);
  assert.match(text, /Upstream linter \[Cargo\.toml\]: cargo clippy — not run: not installed \(install: rustup component add clippy\)/);
  assert.match(text, /Upstream linter \[Cargo\.toml\]: deslop-please — not run: not installed \(install: cargo install deslop-please --version 0\.1\.4 --locked\)/);
});

test('detects pyproject.toml -> ruff check and preserves raw native stdout verbatim', t => {
  const dir = mkRepo(t);
  writeFileSync(join(dir, 'pyproject.toml'), '[project]\nname = "demo"\nversion = "0.1.0"\n');
  const calls = [];
  const fakeSpawn = (bin, args) => {
    calls.push([bin, args]);
    if (args[0] === '--version') return { status: 0, stdout: 'ruff 0.17.6\n', stderr: '' };
    return { status: 1, stdout: 'app.py:1:8: F401 `os` imported but unused\nFound 1 error.\n', stderr: '' };
  };
  const res = runUpstreamLinters(dir, { env: { PATH: '/fake/bin' } }, {
    locateBinary: name => ({ found: true, bin: `/fake/bin/${name}`, source: 'PATH' }),
    spawnSync: fakeSpawn,
  });
  assert.equal(res.ok, false);
  assert.equal(res.results[0].tool, 'ruff');
  assert.equal(res.results[0].version, 'ruff 0.17.6');
  assert.equal(res.results[0].exit_code, 1);
  assert.equal(res.results[0].stdout, 'app.py:1:8: F401 `os` imported but unused\nFound 1 error.\n');
  assert.equal(res.errors.length, 1);
  assert.match(res.errors[0], /\[upstream-linter-failed:ruff\]/);
  assert.deepEqual(calls[1][1], ['check', '.']);
});

test('detects package.json configured oxlint/biome/eslint or recommends oxlint when unconfigured', t => {
  const dirUnconf = mkRepo(t);
  writeFileSync(join(dirUnconf, 'package.json'), JSON.stringify({ name: 'plain', version: '1.0.0' }));
  const unconf = runUpstreamLinters(dirUnconf, { env: { PATH: '' } });
  assert.equal(unconf.ok, true);
  assert.equal(unconf.results[0].status, 'unconfigured');
  assert.equal(unconf.results[0].tool, 'oxlint');
  assert.match(formatUpstreamLinterReport(unconf.results), /recommended: oxlint/);

  const dirBiome = mkRepo(t);
  writeFileSync(join(dirBiome, 'package.json'), JSON.stringify({ name: 'b', devDependencies: { '@biomejs/biome': '1.9.4' } }));
  writeFileSync(join(dirBiome, 'biome.json'), '{}\n');
  const biomeSpecs = detectUpstreamLinters(dirBiome, { env: { PATH: '' } });
  assert.equal(biomeSpecs[0].tool, 'biome');
  assert.equal(biomeSpecs[0].pinned, '1.9.4');

  const dirEslint = mkRepo(t);
  writeFileSync(join(dirEslint, 'package.json'), JSON.stringify({ name: 'e', devDependencies: { eslint: '9.15.0' } }));
  writeFileSync(join(dirEslint, 'eslint.config.mjs'), 'export default [];\n');
  const eslintSpecs = detectUpstreamLinters(dirEslint, { env: { PATH: '' } });
  assert.equal(eslintSpecs[0].tool, 'eslint');
  assert.equal(eslintSpecs[0].pinned, '9.15.0');
});

test('detects go.mod -> golangci-lint when configured else go vet', t => {
  const dirVet = mkRepo(t);
  writeFileSync(join(dirVet, 'go.mod'), 'module example.com/demo\ngo 1.23\n');
  assert.equal(detectUpstreamLinters(dirVet, { env: { PATH: '' } })[0].tool, 'go vet');

  const dirGolangci = mkRepo(t);
  writeFileSync(join(dirGolangci, 'go.mod'), 'module example.com/demo\ngo 1.23\n');
  writeFileSync(join(dirGolangci, '.golangci.yml'), 'run:\n  timeout: 2m\n');
  assert.equal(detectUpstreamLinters(dirGolangci, { env: { PATH: '' } })[0].tool, 'golangci-lint');
});

test('runLocalLint integrates upstream linters in full-repo mode while preserving pdd.local-lint.v1 contract', t => {
  const dir = mkRepo(t);
  mkdirSync(join(dir, 'prompts'), { recursive: true });
  writeFileSync(join(dir, 'Cargo.toml'), '[package]\nname = "demo"\nversion = "0.1.0"\n');
  writeFileSync(join(dir, 'prompts', 'lib.prompt.md'), '# Demo\n\nSimple prompt.\n\n## Dependencies\nNone.\n');
  execFileSync('git', ['add', '.'], { cwd: dir });
  execFileSync('git', ['commit', '-q', '-m', 'init'], { cwd: dir });

  const out = makeSink(), err = makeSink();
  const code = runLocalLint({ cwd: dir, json: true, env: { PATH: '' } }, { stdout: out, stderr: err });
  assert.equal(code, 0);
  const parsed = JSON.parse(out.text);
  assert.equal(parsed.schema_version, 'pdd.local-lint.v1');
  assert.equal(parsed.ok, true);
  assert.equal(parsed.local_only, true);
  assert.equal(Array.isArray(parsed.upstream_linters), true);
  assert.deepEqual(parsed.upstream_linters.map(r => [r.tool, r.status]), [
    ['cargo clippy', 'not_installed'],
    ['deslop-please', 'not_installed'],
  ]);
});
