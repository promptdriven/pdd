import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import {
  chmodSync,
  cpSync,
  existsSync,
  lstatSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  realpathSync,
  rmSync,
  statSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { delimiter, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parse as parseToml } from '../src/shared/toml/parse.js';
import { bundleInstalledDependencies } from './helpers/pack-offline.mjs';

const REPO_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const CANDIDATE_VERSION = JSON.parse(readFileSync(join(REPO_ROOT, 'package.json'), 'utf8')).version;
const SPLIT_RETIRED = ['pdd-setup', 'pdd-prompting', 'pdd-small-change', 'pdd-bug', 'pdd-feature', 'pdd-product', 'pdd-graph'];
const MARKER = '.pdd-skill.json';

function makeTemp(t, prefix) {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), prefix)));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
}

function makeNodeOnlyBin(sandbox) {
  const dir = join(sandbox, 'node-only-bin');
  if (!existsSync(dir)) {
    mkdirSync(dir, { recursive: true });
    symlinkSync(process.execPath, join(dir, 'node'));
    for (const sysTool of ['/usr/bin/which', '/bin/which', '/usr/bin/git']) {
      const toolName = sysTool.split('/').at(-1);
      if (existsSync(sysTool) && !existsSync(join(dir, toolName))) {
        symlinkSync(sysTool, join(dir, toolName));
      }
    }
  }
  return dir;
}

function makeNpmEnv(sandbox, home) {
  const userCfg = join(sandbox, 'empty-user-npmrc');
  const globalCfg = join(sandbox, 'empty-global-npmrc');
  if (!existsSync(userCfg)) writeFileSync(userCfg, '');
  if (!existsSync(globalCfg)) writeFileSync(globalCfg, '');
  return {
    PATH: `${dirname(process.execPath)}:/usr/local/bin:/opt/homebrew/bin:/usr/bin:/bin:${process.env.PATH ?? ''}`,
    HOME: home,
    USERPROFILE: home,
    TMPDIR: sandbox,
    XDG_STATE_HOME: join(home, '.local/state'),
    PDD_STATE_DIR: join(home, '.local/state/pdd'),
    PDD_NO_UPDATE_CHECK: '1',
    COPYFILE_DISABLE: '1',
    npm_config_cache: join(sandbox, 'npm-cache'),
    npm_config_userconfig: userCfg,
    npm_config_globalconfig: globalCfg,
    npm_config_audit: 'false',
    npm_config_fund: 'false',
    npm_config_offline: 'true',
    npm_config_update_notifier: 'false',
  };
}

function packCandidateTarball(sandbox, npmEnv) {
  const packed = JSON.parse(
    execFileSync('npm', ['pack', '--ignore-scripts', '--json', '--pack-destination', sandbox], {
      cwd: REPO_ROOT,
      env: npmEnv,
      encoding: 'utf8',
      timeout: 30000,
    }),
  )[0];
  const archive = join(sandbox, packed.filename);
  bundleInstalledDependencies(REPO_ROOT, archive, sandbox);
  return archive;
}

function installGlobalTarball(prefix, archive, npmEnv) {
  execFileSync(
    'npm',
    ['install', '--global', '--prefix', prefix, '--offline', '--ignore-scripts', '--no-audit', '--no-fund', '--package-lock=false', archive],
    { cwd: dirname(archive), env: npmEnv, encoding: 'utf8', timeout: 60000 },
  );
  const pkgRoot = existsSync(join(prefix, 'lib/node_modules/@promptdriven/pdd/package.json'))
    ? join(prefix, 'lib/node_modules/@promptdriven/pdd')
    : join(prefix, 'node_modules/@promptdriven/pdd');
  return {
    pkgRoot,
    binEntry: join(pkgRoot, 'bin/pdd.mjs'),
    binShim: join(prefix, 'bin/pdd'),
  };
}

function makeDerivedTarball(baseArchive, sandbox, name, mutateFn) {
  const stage = join(sandbox, `stage-${name}`);
  mkdirSync(stage, { recursive: true });
  const tarEnv = { ...process.env, COPYFILE_DISABLE: '1' };
  execFileSync('tar', ['-xzf', baseArchive, '-C', stage], { env: tarEnv });
  const pkgDir = join(stage, 'package');
  mutateFn(pkgDir);
  const outArchive = join(sandbox, `${name}.tgz`);
  execFileSync('tar', ['-czf', outArchive, '-C', stage, 'package'], { env: tarEnv });
  rmSync(stage, { recursive: true, force: true });
  return outArchive;
}

function writeFakeExe(dir, name, body = '#!/bin/sh\nexit 0\n') {
  mkdirSync(dir, { recursive: true });
  const file = join(dir, name);
  writeFileSync(file, body, { mode: 0o755 });
  chmodSync(file, 0o755);
  return file;
}

function seedSplitSkill(parent, name, { version = '0.1.39', marked = false } = {}) {
  const dir = join(parent, name);
  mkdirSync(dir, { recursive: true });
  writeFileSync(
    join(dir, 'SKILL.md'),
    `---\nname: ${name}\ndescription: Legacy split skill ${name}\nmetadata:\n  pdd-skills: ${version}\n---\nLegacy instructions.\n`,
  );
  if (marked) {
    writeFileSync(join(dir, MARKER), `${JSON.stringify({ package: 'pdd', version, digest: 'old-digest' })}\n`);
  }
}

test('E2E1 (#3645): real npm-packed tarball upgrade hops (0.1.42 split -> candidate 0.1.50 -> future 9.9.9 restructured skill) succeed with zero ENOENT', t => {
  const sandbox = makeTemp(t, 'pdd-e2e-tarball-hop-');
  const home = join(sandbox, 'home');
  const prefix = join(sandbox, 'npm-prefix');
  const cwd = join(sandbox, 'work');
  mkdirSync(home, { recursive: true });
  mkdirSync(prefix, { recursive: true });
  mkdirSync(cwd, { recursive: true });

  const npmEnv = makeNpmEnv(sandbox, home);
  const candidateTgz = packCandidateTarball(sandbox, npmEnv);

  // Build realistic v0.1.42 tarball with 7 split skills (simulating pre-consolidation layout).
  const legacy42Tgz = makeDerivedTarball(candidateTgz, sandbox, 'pdd-0.1.42', pkgDir => {
    const manifest = JSON.parse(readFileSync(join(pkgDir, 'package.json'), 'utf8'));
    manifest.version = '0.1.42';
    writeFileSync(join(pkgDir, 'package.json'), `${JSON.stringify(manifest, null, 2)}\n`);
    rmSync(join(pkgDir, 'skills/pdd'), { recursive: true, force: true });
    for (const skillName of SPLIT_RETIRED) {
      seedSplitSkill(join(pkgDir, 'skills'), skillName, { version: '0.1.42', marked: false });
    }
    const skillsModPath = join(pkgDir, 'src/shared/skills-install.mjs');
    const patched = readFileSync(skillsModPath, 'utf8')
      .replace("export const PDD_SKILL_NAMES = Object.freeze(['pdd']);", `export const PDD_SKILL_NAMES = Object.freeze(${JSON.stringify(SPLIT_RETIRED)});`)
      .replace(/export const RETIRED_SKILL_NAMES = Object\.freeze\(\[[\s\S]*?\]\);/, "export const RETIRED_SKILL_NAMES = Object.freeze(['pdd-autopilot', 'pdd-check', 'pdd-merge']);");
    writeFileSync(skillsModPath, patched);
  });

  // Build realistic future v9.9.9 tarball where `skills/pdd/` is renamed to `skills/pdd-next/` (and `pdd` is retired!).
  // If pre-upgrade 0.1.50 ran its in-RAM `PDD_SKILL_NAMES=['pdd']` against the upgraded v9.9.9 root, it would crash with ENOENT.
  const future999Tgz = makeDerivedTarball(candidateTgz, sandbox, 'pdd-9.9.9', pkgDir => {
    const manifest = JSON.parse(readFileSync(join(pkgDir, 'package.json'), 'utf8'));
    manifest.version = '9.9.9';
    writeFileSync(join(pkgDir, 'package.json'), `${JSON.stringify(manifest, null, 2)}\n`);
    cpSync(join(pkgDir, 'skills/pdd'), join(pkgDir, 'skills/pdd-next'), { recursive: true });
    rmSync(join(pkgDir, 'skills/pdd'), { recursive: true, force: true });
    const nextMd = readFileSync(join(pkgDir, 'skills/pdd-next/SKILL.md'), 'utf8')
      .replace(/^name: pdd$/m, 'name: pdd-next')
      .replace(/^(  pdd-skills:).*$/m, '$1 9.9.9');
    writeFileSync(join(pkgDir, 'skills/pdd-next/SKILL.md'), nextMd);
    const skillsModPath = join(pkgDir, 'src/shared/skills-install.mjs');
    const patched = readFileSync(skillsModPath, 'utf8')
      .replace("export const PDD_SKILL_NAMES = Object.freeze(['pdd']);", "export const PDD_SKILL_NAMES = Object.freeze(['pdd-next']);")
      .replace("  'pdd-graph',\n]);", "  'pdd-graph',\n  'pdd',\n]);");
    writeFileSync(skillsModPath, patched);
  });

  // Hop 1: Install v0.1.42 into isolated prefix, run real `pdd setup --yes` -> seeds all 7 split skills + MCP entry.
  const nodeOnlyBin = makeNodeOnlyBin(sandbox);
  const installed42 = installGlobalTarball(prefix, legacy42Tgz, npmEnv);
  const bin42Env = {
    ...npmEnv,
    PATH: `${join(prefix, 'bin')}${delimiter}${nodeOnlyBin}:/usr/bin:/bin`,
  };
  mkdirSync(join(home, '.codex'), { recursive: true });
  const setup42 = spawnSync(process.execPath, [installed42.binEntry, 'setup', '--yes'], { cwd, env: bin42Env, encoding: 'utf8', timeout: 20000 });
  assert.equal(setup42.status, 0, setup42.stderr);
  for (const name of SPLIT_RETIRED) {
    assert.equal(existsSync(join(home, '.agents/skills', name, MARKER)), true, `0.1.42 installed ${name}`);
  }
  assert.equal(existsSync(join(home, '.agents/skills/pdd')), false);

  // Now upgrade prefix from v0.1.42 -> candidate 0.1.50 via real npm offline install and run real `pdd setup --upgrade`.
  const installed50 = installGlobalTarball(prefix, candidateTgz, npmEnv);
  // Before setup --upgrade, candidate `pdd --version` must warn loudly about the 7 stranded 0.1.42 retired skills!
  const verBefore50 = spawnSync(process.execPath, [installed50.binEntry, '--version'], { cwd, env: bin42Env, encoding: 'utf8', timeout: 15000 });
  assert.equal(verBefore50.status, 0);
  assert.equal(verBefore50.stdout, `${CANDIDATE_VERSION}\n`);
  assert.match(verBefore50.stderr, /Retired PDD skills remain in .*\.agents\/skills/);

  const upg50 = spawnSync(process.execPath, [installed50.binEntry, 'setup', '--upgrade'], { cwd, env: bin42Env, encoding: 'utf8', timeout: 20000 });
  assert.equal(upg50.status, 0, upg50.stderr);
  assert.match(upg50.stdout, /Removed retired PDD skills from .*\.agents\/skills/);
  assert.match(upg50.stdout, /Installed 1 PDD skill to .*\.agents\/skills: pdd/);
  for (const name of SPLIT_RETIRED) {
    assert.equal(existsSync(join(home, '.agents/skills', name)), false, `retired ${name} removed`);
  }
  assert.equal(JSON.parse(readFileSync(join(home, '.agents/skills/pdd', MARKER), 'utf8')).version, CANDIDATE_VERSION);

  const verAfter50 = spawnSync(process.execPath, [installed50.binEntry, '--version'], { cwd, env: bin42Env, encoding: 'utf8', timeout: 15000 });
  assert.equal(verAfter50.status, 0);
  assert.equal(verAfter50.stdout, `${CANDIDATE_VERSION}\n`);
  assert.equal(verAfter50.stderr, '');

  // Hop 2 (THE #3645 PROOF!): Execute REAL `node <0.1.50>/bin/pdd.mjs upgrade` targeting future `9.9.9` where `skills/pdd/` is deleted and renamed to `skills/pdd-next/`!
  // Local loopback HTTP/gh shim serves release `v9.9.9`; local npm wrapper redirects `@promptdriven/pdd@9.9.9` to REAL `npm install --global --offline <future999Tgz>`.
  const shimBin = join(sandbox, 'hop-shims');
  const realNpm = execFileSync('which', ['npm'], { env: npmEnv, encoding: 'utf8' }).trim();
  writeFakeExe(
    shimBin,
    'gh',
    `#!${process.execPath}
const args = process.argv.slice(2);
if (args[0] === 'api' && String(args[1] || '').includes('releases')) {
  process.stdout.write(JSON.stringify([{ tag_name: 'v9.9.9', draft: false, prerelease: false }]));
  process.exit(0);
}
process.exit(1);
`,
  );
  writeFakeExe(
    shimBin,
    'npm',
    `#!${process.execPath}
const { spawnSync } = require('node:child_process');
const args = process.argv.slice(2).map(a => a === '@promptdriven/pdd@9.9.9' ? ${JSON.stringify(future999Tgz)} : a);
const res = spawnSync(${JSON.stringify(realNpm)}, [...args, '--offline', '--package-lock=false'], { stdio: 'inherit', env: process.env });
process.exit(res.status ?? 1);
`,
  );

  // Use a net-guard preload that forces fetch('https://api.github.com/...') to fail cleanly so cli-upgrade falls back to our offline `gh api` shim,
  // while the real installed 0.1.50 binary runs real `npm install` of 9.9.9.tgz and spawns the real newly installed 9.9.9 `bin/pdd.mjs setup --upgrade`!
  const hopEnv = {
    ...npmEnv,
    PATH: `${shimBin}${delimiter}${join(prefix, 'bin')}${delimiter}${nodeOnlyBin}:/usr/bin:/bin`,
  };
  const hopRes = spawnSync(
    process.execPath,
    ['--import', join(REPO_ROOT, 'test/helpers/test-net-guard.mjs'), installed50.binEntry, 'upgrade'],
    { cwd, env: hopEnv, encoding: 'utf8', timeout: 60000 },
  );
  assert.equal(hopRes.status, 0, `stdout:\n${hopRes.stdout}\nstderr:\n${hopRes.stderr}`);
  assert.doesNotMatch(hopRes.stderr, /ENOENT/);
  assert.ok(
    hopRes.stdout.includes(`Upgraded pdd ${CANDIDATE_VERSION} -> 9.9.9 (v9.9.9).`),
    `unexpected upgrade stdout:\n${hopRes.stdout}`,
  );
  assert.match(hopRes.stdout, /Installed 1 PDD skill to .*\.agents\/skills: pdd-next/);
  assert.match(hopRes.stdout, /Removed retired PDD skills from .*\.agents\/skills: pdd/);
  assert.equal(existsSync(join(home, '.agents/skills/pdd-next/SKILL.md')), true, '9.9.9 pdd-next installed by newly installed binary');
  assert.equal(JSON.parse(readFileSync(join(home, '.agents/skills/pdd-next', MARKER), 'utf8')).version, '9.9.9');
  assert.equal(existsSync(join(home, '.agents/skills/pdd')), false, 'retired 0.1.50 pdd removed by newly installed 9.9.9 binary');

  // Verify the newly installed 9.9.9 binary reports clean --version with zero warnings!
  const ver999 = spawnSync(process.execPath, [installed50.binEntry, '--version'], { cwd, env: bin42Env, encoding: 'utf8', timeout: 15000 });
  assert.equal(ver999.status, 0);
  assert.equal(ver999.stdout, '9.9.9\n');
  assert.equal(ver999.stderr, '');
});

test('E2E2 (#3645 + #3646): all 5 real messy-HOME personas execute real packed binary cleanly with zero mocks', t => {
  const sandbox = makeTemp(t, 'pdd-e2e-personas-');
  const installHome = join(sandbox, 'install-home');
  const prefix = join(sandbox, 'npm-prefix');
  mkdirSync(installHome, { recursive: true });
  mkdirSync(prefix, { recursive: true });

  const baseNpmEnv = makeNpmEnv(sandbox, installHome);
  const candidateTgz = packCandidateTarball(sandbox, baseNpmEnv);
  const installed = installGlobalTarball(prefix, candidateTgz, baseNpmEnv);

  const nodeOnlyBin = makeNodeOnlyBin(sandbox);
  const runInstalled = (home, cwd, args, extraPathDirs = []) => {
    const env = {
      ...baseNpmEnv,
      HOME: home,
      USERPROFILE: home,
      XDG_STATE_HOME: join(home, '.local/state'),
      PDD_STATE_DIR: join(home, '.local/state/pdd'),
      PATH: [...extraPathDirs, join(prefix, 'bin'), nodeOnlyBin, '/usr/bin', '/bin'].join(delimiter),
    };
    return spawnSync(process.execPath, [installed.binEntry, ...args], {
      cwd,
      env,
      encoding: 'utf8',
      timeout: 20000,
    });
  };

  // --- Persona 1: Fresh laptop with codex, claude, agy on PATH ---
  {
    const home = join(sandbox, 'p1-fresh');
    const cwd = join(sandbox, 'p1-cwd');
    const fakeBin = join(sandbox, 'p1-bin');
    mkdirSync(home, { recursive: true });
    mkdirSync(cwd, { recursive: true });
    writeFakeExe(fakeBin, 'codex');
    writeFakeExe(fakeBin, 'claude');
    writeFakeExe(fakeBin, 'agy');

    const setup = runInstalled(home, cwd, ['setup', '--yes'], [fakeBin]);
    assert.equal(setup.status, 0, setup.stderr);
    assert.match(setup.stdout, /Done!/);
    assert.equal(existsSync(join(home, '.agents/skills/pdd/SKILL.md')), true);
    assert.equal(existsSync(join(home, '.claude/skills/pdd/SKILL.md')), true);
    assert.equal(existsSync(join(home, '.gemini/config/skills/pdd/SKILL.md')), true);
    assert.equal(existsSync(join(home, '.codex/config.toml')), true);
    assert.equal(existsSync(join(home, '.claude.json')), true);
    assert.equal(existsSync(join(home, '.gemini/config/mcp_config.json')), true);
    assert.equal(existsSync(join(home, '.gemini/settings.json')), false, 'Gemini CLI absent -> must not create settings.json');

    const ver = runInstalled(home, cwd, ['--version'], [fakeBin]);
    assert.equal(ver.status, 0);
    assert.equal(ver.stdout, `${CANDIDATE_VERSION}\n`);
    assert.equal(ver.stderr, '');
  }

  // --- Persona 2: Greg persona (marked 0.1.42 retired skills + 0-byte mcp_config.json + whitespace-only settings.json) ---
  {
    const home = join(sandbox, 'p2-greg');
    const cwd = join(sandbox, 'p2-cwd');
    mkdirSync(join(home, '.gemini/config'), { recursive: true });
    mkdirSync(cwd, { recursive: true });
    for (const rootRel of ['.agents/skills', '.claude/skills', '.gemini/config/skills']) {
      for (const name of SPLIT_RETIRED) seedSplitSkill(join(home, rootRel), name, { version: '0.1.42', marked: true });
    }
    const agyCfg = join(home, '.gemini/config/mcp_config.json');
    const gemCfg = join(home, '.gemini/settings.json');
    writeFileSync(agyCfg, '', { mode: 0o644 });
    writeFileSync(gemCfg, '   \n\t\n', { mode: 0o640 });
    chmodSync(agyCfg, 0o644);
    chmodSync(gemCfg, 0o640);

    const beforeVer = runInstalled(home, cwd, ['--version']);
    assert.equal(beforeVer.status, 0);
    assert.equal(beforeVer.stdout, `${CANDIDATE_VERSION}\n`);
    assert.match(beforeVer.stderr, /Retired PDD skills remain in .*\.agents\/skills/);
    assert.match(beforeVer.stderr, /Retired PDD skills remain in .*\.claude\/skills/);
    assert.match(beforeVer.stderr, /Retired PDD skills remain in .*\.gemini\/config\/skills/);

    const setup = runInstalled(home, cwd, ['setup', '--yes']);
    assert.equal(setup.status, 0, setup.stderr);
    assert.match(setup.stdout, /Done!/);
    assert.match(setup.stdout, /Removed retired PDD skills from .*\.agents\/skills:/);
    assert.match(setup.stdout, /Removed retired PDD skills from .*\.claude\/skills:/);
    assert.match(setup.stdout, /Removed retired PDD skills from .*\.gemini\/config\/skills:/);
    for (const rootRel of ['.agents/skills', '.claude/skills', '.gemini/config/skills']) {
      assert.equal(existsSync(join(home, rootRel, 'pdd/SKILL.md')), true);
      for (const name of SPLIT_RETIRED) assert.equal(existsSync(join(home, rootRel, name)), false);
    }
    assert.deepEqual(JSON.parse(readFileSync(agyCfg, 'utf8')).mcpServers.pdd.args, [installed.binEntry, 'mcp']);
    assert.deepEqual(JSON.parse(readFileSync(gemCfg, 'utf8')).mcpServers.pdd.args, [installed.binEntry, 'mcp']);
    if (process.platform !== 'win32') {
      assert.equal(statSync(agyCfg).mode & 0o777, 0o644);
      assert.equal(statSync(gemCfg).mode & 0o777, 0o640);
    }

    const afterVer = runInstalled(home, cwd, ['--version']);
    assert.equal(afterVer.status, 0);
    assert.equal(afterVer.stdout, `${CANDIDATE_VERSION}\n`);
    assert.equal(afterVer.stderr, '');
  }

  // --- Persona 3: Serhan persona (unmarked 0.1.39 pdd-skills folders + relative Claude symlinks + non-PDD skills + 0-byte mcp_config.json) ---
  for (const mode of ['--yes', '--upgrade']) {
    const home = join(sandbox, `p3-serhan-${mode.slice(2)}`);
    const cwd = join(sandbox, `p3-cwd-${mode.slice(2)}`);
    mkdirSync(join(home, '.agents/skills'), { recursive: true });
    mkdirSync(join(home, '.claude/skills'), { recursive: true });
    mkdirSync(join(home, '.gemini/config/skills'), { recursive: true });
    mkdirSync(cwd, { recursive: true });

    for (const name of SPLIT_RETIRED) {
      seedSplitSkill(join(home, '.agents/skills'), name, { version: '0.1.39', marked: false });
      seedSplitSkill(join(home, '.gemini/config/skills'), name, { version: '0.1.39', marked: false });
      symlinkSync(`../../.agents/skills/${name}`, join(home, '.claude/skills', name));
    }
    mkdirSync(join(home, '.agents/skills/finish-pr'), { recursive: true });
    writeFileSync(join(home, '.agents/skills/finish-pr/SKILL.md'), 'keep finish-pr\n');
    mkdirSync(join(home, '.gemini/config/skills/cot-review'), { recursive: true });
    writeFileSync(join(home, '.gemini/config/skills/cot-review/SKILL.md'), 'keep cot-review\n');
    writeFileSync(join(home, '.gemini/config/mcp_config.json'), '');

    const beforeVer = runInstalled(home, cwd, ['--version']);
    assert.equal(beforeVer.status, 0);
    assert.match(beforeVer.stderr, /Retired PDD skills remain in .*\.agents\/skills/);
    assert.match(beforeVer.stderr, /Retired PDD skills remain in .*\.claude\/skills/);
    assert.match(beforeVer.stderr, /Retired PDD skills remain in .*\.gemini\/config\/skills/);

    const res = runInstalled(home, cwd, ['setup', mode]);
    assert.equal(res.status, 0, res.stderr);
    for (const rootRel of ['.agents/skills', '.claude/skills', '.gemini/config/skills']) {
      assert.equal(existsSync(join(home, rootRel, 'pdd/SKILL.md')), true, `${mode}: ${rootRel}/pdd installed`);
      assert.equal(JSON.parse(readFileSync(join(home, rootRel, 'pdd', MARKER), 'utf8')).version, CANDIDATE_VERSION);
      for (const name of SPLIT_RETIRED) {
        assert.throws(() => lstatSync(join(home, rootRel, name)), { code: 'ENOENT' }, `${mode}: ${rootRel}/${name} gone`);
      }
    }
    assert.equal(readFileSync(join(home, '.agents/skills/finish-pr/SKILL.md'), 'utf8'), 'keep finish-pr\n');
    assert.equal(readFileSync(join(home, '.gemini/config/skills/cot-review/SKILL.md'), 'utf8'), 'keep cot-review\n');
    if (mode === '--yes') {
      assert.match(res.stdout, /Done!/);
      assert.deepEqual(JSON.parse(readFileSync(join(home, '.gemini/config/mcp_config.json'), 'utf8')).mcpServers.pdd.args, [installed.binEntry, 'mcp']);
    } else {
      assert.doesNotMatch(res.stdout, /Done!|GitHub CLI/);
      assert.equal(readFileSync(join(home, '.gemini/config/mcp_config.json'), 'utf8'), '', '--upgrade leaves unregistered 0-byte mcp_config.json untouched');
    }

    const afterVer = runInstalled(home, cwd, ['--version']);
    assert.equal(afterVer.status, 0);
    assert.equal(afterVer.stdout, `${CANDIDATE_VERSION}\n`);
    assert.equal(afterVer.stderr, '');
  }

  // --- Persona 4: Claude plugin persona (installed_plugins.json + leftover retired skills) ---
  {
    const home = join(sandbox, 'p4-plugin');
    const cwd = join(sandbox, 'p4-cwd');
    mkdirSync(join(home, '.claude/plugins'), { recursive: true });
    mkdirSync(join(home, '.claude/skills'), { recursive: true });
    mkdirSync(cwd, { recursive: true });
    writeFileSync(
      join(home, '.claude/plugins/installed_plugins.json'),
      JSON.stringify({ version: 2, plugins: { 'pdd@promptdriven': [{ scope: 'user', installPath: '/plugins/pdd', version: CANDIDATE_VERSION }] } }),
    );
    seedSplitSkill(join(home, '.claude/skills'), 'pdd-bug', { version: '0.1.39', marked: false });
    seedSplitSkill(join(home, '.claude/skills'), 'pdd-feature', { version: '0.1.42', marked: true });

    const beforeVer = runInstalled(home, cwd, ['--version']);
    assert.match(beforeVer.stderr, /Retired PDD skills remain in .*\.claude\/skills/);

    const setup = runInstalled(home, cwd, ['setup', '--yes']);
    assert.equal(setup.status, 0, setup.stderr);
    assert.equal(existsSync(join(home, '.claude/skills/pdd')), false, 'must not duplicate pdd/ under Claude plugin');
    assert.equal(existsSync(join(home, '.claude/skills/pdd-bug')), false);
    assert.equal(existsSync(join(home, '.claude/skills/pdd-feature')), false);
    assert.equal(existsSync(join(home, '.agents/skills/pdd/SKILL.md')), true);

    const afterVer = runInstalled(home, cwd, ['--version']);
    assert.equal(afterVer.status, 0);
    assert.equal(afterVer.stderr, '');
  }

  // --- Persona 5: Developer checkout symlink + `--upgrade` MCP refresh (and unregistered agent untouched) ---
  {
    const home = join(sandbox, 'p5-dev');
    const cwd = join(sandbox, 'p5-cwd');
    const devRepo = join(sandbox, 'p5-git-repo');
    const fakeBin = join(sandbox, 'p5-bin');
    mkdirSync(join(home, '.agents/skills'), { recursive: true });
    mkdirSync(join(home, '.codex'), { recursive: true });
    mkdirSync(join(home, '.gemini/config'), { recursive: true });
    mkdirSync(join(devRepo, '.git'), { recursive: true });
    cpSync(join(REPO_ROOT, 'skills/pdd'), join(devRepo, 'skills/pdd'), { recursive: true });
    seedSplitSkill(join(devRepo, 'skills'), 'pdd-bug', { version: '0.1.39', marked: false });
    mkdirSync(cwd, { recursive: true });
    writeFakeExe(fakeBin, 'gemini'); // Unregistered agent on PATH!

    symlinkSync(join(devRepo, 'skills/pdd'), join(home, '.agents/skills/pdd'));
    symlinkSync(join(devRepo, 'skills/pdd-bug'), join(home, '.agents/skills/pdd-bug'));

    // Stale registered Codex, Claude, Antigravity MCP entries (with custom env keys).
    writeFileSync(
      join(home, '.codex/config.toml'),
      '[mcp_servers.pdd]\ncommand = "/old/node"\nargs = ["/old/pdd/bin/pdd.mjs", "mcp"]\nenv = { DEV_KEEP = "1" }\n',
    );
    writeFileSync(
      join(home, '.claude.json'),
      JSON.stringify({ mcpServers: { pdd: { type: 'stdio', command: '/old/node', args: ['/old/pdd/bin/pdd.mjs', 'mcp'], env: { DEV_KEEP: '2' } } } }) + '\n',
    );
    writeFileSync(
      join(home, '.gemini/config/mcp_config.json'),
      JSON.stringify({ mcpServers: { pdd: { command: '/old/node', args: ['/old/pdd/bin/pdd.mjs', 'mcp'], env: { DEV_KEEP: '3' } } } }) + '\n',
    );

    const upg = runInstalled(home, cwd, ['setup', '--upgrade'], [fakeBin]);
    assert.equal(upg.status, 0, upg.stderr);
    assert.equal(lstatSync(join(home, '.agents/skills/pdd')).isSymbolicLink(), true, 'dev pdd symlink untouched');
    assert.equal(lstatSync(join(home, '.agents/skills/pdd-bug')).isSymbolicLink(), true, 'dev git-checkout pdd-bug symlink untouched');
    assert.equal(existsSync(join(devRepo, 'skills/pdd-bug/SKILL.md')), true, 'dev git-checkout target untouched');

    // Registered stale MCP entries updated cleanly preserving custom env keys.
    const codexCfg = parseToml(readFileSync(join(home, '.codex/config.toml'), 'utf8'));
    assert.equal(codexCfg.mcp_servers.pdd.command, process.execPath);
    assert.deepEqual(codexCfg.mcp_servers.pdd.args, [installed.binEntry, 'mcp']);
    assert.equal(codexCfg.mcp_servers.pdd.env?.DEV_KEEP, '1');

    const claudeCfg = JSON.parse(readFileSync(join(home, '.claude.json'), 'utf8'));
    assert.equal(claudeCfg.mcpServers.pdd.command, process.execPath);
    assert.deepEqual(claudeCfg.mcpServers.pdd.args, [installed.binEntry, 'mcp']);
    assert.deepEqual(claudeCfg.mcpServers.pdd.env, { DEV_KEEP: '2' });

    const agyCfg = JSON.parse(readFileSync(join(home, '.gemini/config/mcp_config.json'), 'utf8'));
    assert.equal(agyCfg.mcpServers.pdd.command, process.execPath);
    assert.deepEqual(agyCfg.mcpServers.pdd.args, [installed.binEntry, 'mcp']);
    assert.deepEqual(agyCfg.mcpServers.pdd.env, { DEV_KEEP: '3' });

    // Unregistered Gemini CLI must NOT be created or modified!
    assert.equal(existsSync(join(home, '.gemini/settings.json')), false, 'unregistered Gemini CLI must not be created');
    assert.doesNotMatch(upg.stdout, /Register these|GitHub CLI|Done!/);

    // Even when ~/.gemini/settings.json exists with user preferences (no `pdd` entry), `--upgrade` leaves it byte-identical.
    const gemSettingsPath = join(home, '.gemini/settings.json');
    const gemRaw = '{\n  "theme": "dark"\n}\n';
    writeFileSync(gemSettingsPath, gemRaw);
    const upg2 = runInstalled(home, cwd, ['setup', '--upgrade'], [fakeBin]);
    assert.equal(upg2.status, 0, upg2.stderr);
    assert.equal(readFileSync(gemSettingsPath, 'utf8'), gemRaw, 'unregistered existing settings.json stays byte-identical');
    assert.equal(upg2.stdout, '', 'second --upgrade run is completely quiet when already current');
  }
});
