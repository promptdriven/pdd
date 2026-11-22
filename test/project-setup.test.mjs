import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { detectProjectStack, initProject, PDD_BLOCK } from '../src/project-setup.mjs';
import { classifyInstallKind, detectGlobalInstallPrefix, runCliUpgrade } from '../src/setup/cli-upgrade.mjs';
import { inspectStatus, runStatus } from '../src/core/status.mjs';

const temp = (t, prefix = 'pdd-s1c1-') => {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), prefix)));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
};

test('S1 detectProjectStack detects JavaScript, TypeScript, Python, Go, Rust, and fallback stacks', async t => {
  const jsRepo = temp(t, 'pdd-stack-js-');
  writeFileSync(join(jsRepo, 'package.json'), JSON.stringify({ name: 'x', scripts: { test: 'vitest run' } }));
  assert.deepEqual(detectProjectStack(jsRepo), { language: 'javascript', testCommand: 'npm test' });

  const tsRepo = temp(t, 'pdd-stack-ts-');
  writeFileSync(join(tsRepo, 'package.json'), JSON.stringify({ name: 'x', scripts: { test: 'vitest run' } }));
  writeFileSync(join(tsRepo, 'tsconfig.json'), '{}');
  writeFileSync(join(tsRepo, 'pnpm-lock.yaml'), 'lockfileVersion: 9\n');
  assert.deepEqual(detectProjectStack(tsRepo), { language: 'typescript', testCommand: 'pnpm test' });

  const pyRepo = temp(t, 'pdd-stack-py-');
  writeFileSync(join(pyRepo, 'pyproject.toml'), '[project]\nname = "demo"\n');
  assert.deepEqual(detectProjectStack(pyRepo), { language: 'python', testCommand: 'pytest' });

  const goRepo = temp(t, 'pdd-stack-go-');
  writeFileSync(join(goRepo, 'go.mod'), 'module example.com/demo\n');
  assert.deepEqual(detectProjectStack(goRepo), { language: 'go', testCommand: 'go test ./...' });

  const rustRepo = temp(t, 'pdd-stack-rs-');
  writeFileSync(join(rustRepo, 'Cargo.toml'), '[package]\nname = "demo"\n');
  assert.deepEqual(detectProjectStack(rustRepo), { language: 'rust', testCommand: 'cargo test' });

  const emptyRepo = temp(t, 'pdd-stack-empty-');
  assert.deepEqual(detectProjectStack(emptyRepo), { language: null, testCommand: null });

  const initRes = await initProject({ cwd: jsRepo });
  assert.equal(initRes.changed, true);
  assert.equal(initRes.language, 'javascript');
  assert.equal(initRes.testCommand, 'npm test');
  assert.ok(PDD_BLOCK.includes('<!-- pdd:start -->') && PDD_BLOCK.includes('<!-- pdd:end -->'));
});

test('S1 classifyInstallKind guards Git checkouts, PyPI pdd-cli, pnpm, npx, local node_modules, and accepts user-owned npm-global', t => {
  const sandbox = temp(t, 'pdd-upg-kind-');

  const gitCheckout = join(sandbox, 'git-repo');
  mkdirSync(join(gitCheckout, '.git'), { recursive: true });
  assert.equal(classifyInstallKind(gitCheckout).kind, 'git-checkout');
  assert.equal(detectGlobalInstallPrefix(gitCheckout), null);

  const pnpmPkg = join(sandbox, 'pnpm/global/5/.pnpm/@promptdriven+pdd@0.1.41/node_modules/@promptdriven/pdd');
  mkdirSync(pnpmPkg, { recursive: true });
  const pnpmRes = classifyInstallKind(pnpmPkg);
  assert.equal(pnpmRes.kind, 'pnpm');
  assert.match(pnpmRes.hint, /pnpm add -g @promptdriven\/pdd/);

  const npxPkg = join(sandbox, '_npx/abc123/node_modules/@promptdriven/pdd');
  mkdirSync(npxPkg, { recursive: true });
  assert.equal(classifyInstallKind(npxPkg).kind, 'npx');

  const localProject = join(sandbox, 'my-app');
  const localPkg = join(localProject, 'node_modules/@promptdriven/pdd');
  mkdirSync(localPkg, { recursive: true });
  writeFileSync(join(localProject, 'package.json'), '{"name":"my-app"}');
  assert.equal(classifyInstallKind(localPkg).kind, 'local-project');

  const pypiDir = join(sandbox, 'venv/lib/python3.12/site-packages/pdd');
  mkdirSync(pypiDir, { recursive: true });
  assert.equal(classifyInstallKind(pypiDir).kind, 'pypi');

  const globalPrefix = join(sandbox, 'npm-global');
  const globalPkg = join(globalPrefix, 'lib/node_modules/@promptdriven/pdd');
  mkdirSync(globalPkg, { recursive: true });
  const ok = classifyInstallKind(globalPkg);
  assert.equal(ok.kind, 'npm-global');
  assert.equal(ok.prefix, globalPrefix);
  assert.deepEqual(detectGlobalInstallPrefix(globalPkg), { prefix: globalPrefix, realPackageRoot: globalPkg });

  // Regression: Apple Silicon Homebrew has `/opt/homebrew/.git` while `/opt/homebrew/lib/node_modules/@promptdriven/pdd` is global npm!
  const homebrewPrefix = join(sandbox, 'opt/homebrew');
  const homebrewPkg = join(homebrewPrefix, 'lib/node_modules/@promptdriven/pdd');
  mkdirSync(join(homebrewPrefix, '.git'), { recursive: true });
  mkdirSync(homebrewPkg, { recursive: true });
  const hb = classifyInstallKind(homebrewPkg);
  assert.equal(hb.kind, 'npm-global');
  assert.equal(hb.prefix, homebrewPrefix);
  assert.deepEqual(detectGlobalInstallPrefix(homebrewPkg), { prefix: homebrewPrefix, realPackageRoot: homebrewPkg });
});

test('S1 runCliUpgrade tries npm @promptdriven/pdd@ver first, falls back to github tag, reports 4-part EEXIST hint, and clears release cache', async t => {
  const sandbox = temp(t, 'pdd-upg-run-');
  const globalPrefix = join(sandbox, 'npm-global');
  const globalPkg = join(globalPrefix, 'lib/node_modules/@promptdriven/pdd');
  const stateDir = join(sandbox, 'state');
  mkdirSync(globalPkg, { recursive: true });
  mkdirSync(stateDir, { recursive: true });
  writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.40' }));
  writeFileSync(join(stateDir, 'release-check.json'), '{}');

  const env = { HOME: sandbox, PDD_STATE_DIR: stateDir, PATH: '' };
  const releaseFetch = async () => ({
    ok: true,
    json: async () => [{ tag_name: 'v0.1.42', draft: false, prerelease: false }],
  });

  // 1. npm E404 falls back cleanly to github:promptdriven/pdd#v0.1.42, syncs skills, and clears release-check.json.
  const specs = [];
  let synced = 0;
  let out1 = '', err1 = '';
  const fallbackRes = await runCliUpgrade(
    {
      packageRoot: globalPkg,
      env,
      main: false,
      stdout: { write(s) { out1 += s; } },
      stderr: { write(s) { err1 += s; } },
      fetchImpl: releaseFetch,
      spawnSyncImpl: (cmd, args) => {
        if (cmd === 'npm') {
          specs.push(args.at(-1));
          if (args.at(-1) === '@promptdriven/pdd@0.1.42') {
            return { status: 1, stdout: '', stderr: 'npm error code E404\nNot Found' };
          }
          writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.42' }));
          return { status: 0, stdout: 'added 1 package\n', stderr: '' };
        }
        return { status: 0, stdout: '', stderr: '' };
      },
    },
    {
      skillsInstall: {
        syncOwnedUserSkills: () => { synced++; return { updated: ['/home/.agents/skills'] }; },
        findSkills: () => [],
      },
    },
  );
  assert.equal(fallbackRes.exitCode, 0, err1);
  assert.deepEqual(specs, ['@promptdriven/pdd@0.1.42', 'github:promptdriven/pdd#v0.1.42']);
  assert.equal(synced, 1);
  assert.equal(existsSync(join(stateDir, 'release-check.json')), false);
  assert.match(out1, /Upgraded pdd 0\.1\.40 -> 0\.1\.42/);

  // 2. EEXIST produces crisp 4-part agent-teaching fix hint without destructive rollback.
  writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.40' }));
  let err2 = '';
  const eexistRes = await runCliUpgrade(
    {
      packageRoot: globalPkg,
      env,
      main: false,
      stdout: { write() {} },
      stderr: { write(s) { err2 += s; } },
      fetchImpl: releaseFetch,
      spawnSyncImpl: () => ({ status: 1, stdout: '', stderr: 'npm error code EEXIST\nFile exists: /usr/local/bin/pdd' }),
    },
    { skillsInstall: { syncOwnedUserSkills: () => ({ updated: [] }), findSkills: () => [] } },
  );
  assert.equal(eexistRes.exitCode, 1);
  assert.match(err2, /Invariant:/);
  assert.match(err2, /Fix: Run `npm uninstall -g pdd`/);
  assert.match(err2, /Rerun: npm install -g/);
});

test('C1 status inspects repo offline: counts files, ownership, PDD block, Feature Map verify.paths, --changed, and EPIPE', async t => {
  const repo = temp(t, 'pdd-status-');
  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: repo });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: repo });

  mkdirSync(join(repo, 'prompts'), { recursive: true });
  mkdirSync(join(repo, 'user_stories'), { recursive: true });
  mkdirSync(join(repo, 'tests'), { recursive: true });
  mkdirSync(join(repo, 'src'), { recursive: true });

  writeFileSync(join(repo, 'prompts/app.prompt.md'), '# App\n\nOwn `src/app.mjs`.\n');
  writeFileSync(join(repo, 'user_stories/demo.md'), '# Demo\n\n## Acceptance criteria\n1. Works.\n');
  writeFileSync(join(repo, 'tests/demo.json'), JSON.stringify({ schema_version: 'prompt-runtime.program-scenario.v1', steps: [] }));
  writeFileSync(join(repo, 'src/app.mjs'), '// Prompt: prompts/app.prompt.md\nexport const ok = true;\n');
  writeFileSync(join(repo, 'src/unmapped.mjs'), 'export const x = 1;\n');
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    verify: {
      test: 'npm test',
      paths: [
        { id: 'core-app', name: 'Core app', when: ['src/app.*'], run: 'node --test test/app.test.mjs', needs: [] },
      ],
    },
  }));
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['commit', '-q', '-m', 'init'], { cwd: repo });

  // Before init: has_pdd_block is false; after init: true.
  const before = await inspectStatus({ cwd: repo, paths: ['src/app.mjs', 'src/unmapped.mjs'] });
  assert.equal(before.schema_version, 'pdd.status.v1');
  assert.equal(before.has_pdd_block, false);
  assert.equal(before.counts.prompts, 1);
  assert.equal(before.counts.stories, 1);
  assert.equal(before.counts.tests, 1);
  assert.equal(before.counts.verify_paths, 1);
  assert.equal(before.files[0].owner, 'prompts/app.prompt.md');
  assert.equal(before.files[1].owner, null);
  assert.deepEqual(before.verify.matched, ['core-app']);

  // Modify src/app.mjs so --changed detects it offline.
  await initProject({ cwd: repo });
  writeFileSync(join(repo, 'src/app.mjs'), '// Prompt: prompts/app.prompt.md\nexport const ok = 2;\n');
  let out = '', err = '';
  const code = await runStatus(
    { cwd: repo, changed: true, json: true },
    { stdout: { write(s) { out += s; } }, stderr: { write(s) { err += s; } } },
  );
  assert.equal(code, 0, err);
  const parsed = JSON.parse(out);
  assert.equal(parsed.has_pdd_block, true);
  assert.ok(parsed.changed.includes('src/app.mjs'));
  assert.deepEqual(parsed.verify.matched, ['core-app']);

  // EPIPE on stdout returns exit 0 cleanly.
  const epipeCode = await runStatus(
    { cwd: repo },
    {
      stdout: { write() { const e = new Error('EPIPE'); e.code = 'EPIPE'; throw e; } },
      stderr: { write(s) { err += s; } },
    },
  );
  assert.equal(epipeCode, 0);

  // Outside Git returns exit 2.
  const outside = temp(t, 'pdd-status-nogit-');
  let nogitErr = '';
  assert.equal(await runStatus({ cwd: outside }, { stdout: { write() {} }, stderr: { write(s) { nogitErr += s; } } }), 2);
  assert.match(nogitErr, /Git repository/);
});

test('S1/C1 in-repo symlink CLAUDE.md -> AGENTS.md updates AGENTS.md cleanly and status sees has_pdd_block: true', async t => {
  const { symlinkSync, lstatSync, readFileSync } = await import('node:fs');
  const repo = temp(t, 'pdd-inrepo-symlink-');
  execFileSync('git', ['init', '-q'], { cwd: repo });
  writeFileSync(join(repo, 'AGENTS.md'), '# Repo Rules\n');
  symlinkSync('AGENTS.md', join(repo, 'CLAUDE.md'));

  const res = await initProject({ cwd: repo });
  assert.equal(res.changed, true);
  assert.equal(lstatSync(join(repo, 'CLAUDE.md')).isSymbolicLink(), true, 'CLAUDE.md symlink stays intact');
  assert.match(readFileSync(join(repo, 'AGENTS.md'), 'utf8'), /<!-- pdd:start -->[\s\S]*<!-- pdd:end -->/);

  const status = await inspectStatus({ cwd: repo });
  assert.equal(status.instruction_file, 'CLAUDE.md');
  assert.equal(status.has_pdd_block, true);
});
