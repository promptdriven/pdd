import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { existsSync, lstatSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, realpathSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { collectDoctorReport, formatDoctorReport, runDoctor } from '../src/setup/doctor.mjs';
import { runCliUpgrade } from '../src/setup/cli-upgrade.mjs';
import { setupSkills } from '../src/shared/skills-install.mjs';

const REPO_ROOT = resolve(import.meta.dirname, '..');
const PDD_BIN = join(REPO_ROOT, 'bin/pdd.mjs');
const PKG_VERSION = JSON.parse(readFileSync(join(REPO_ROOT, 'package.json'), 'utf8')).version;
const HOST_NODE_OK = (() => {
  const [maj, min] = process.versions.node.split('.').map(Number);
  return maj > 22 || (maj === 22 && min >= 16);
})();

function tempDir(t, prefix) {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), prefix)));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
}

function snapshotTree(dir, prefix = '') {
  const out = [];
  if (!existsSync(dir)) return out;
  for (const name of readdirSync(dir).sort()) {
    const full = join(dir, name);
    const rel = prefix ? `${prefix}/${name}` : name;
    const st = lstatSync(full, { throwIfNoEntry: false });
    if (!st) continue;
    if (st.isSymbolicLink()) {
      out.push(`${rel}:symlink`);
    } else if (st.isDirectory()) {
      out.push(`${rel}/`);
      out.push(...snapshotTree(full, rel));
    } else {
      out.push(`${rel}:${st.size}:${Math.floor(st.mtimeMs)}`);
    }
  }
  return out;
}

function makeHealthyLaptop(t) {
  const root = tempDir(t, 'pdd-doctor-healthy-');
  const home = join(root, 'home');
  const binDir = join(root, 'bin');
  const nodeBin = join(root, 'node-bin');
  const cwd = join(root, 'project');
  for (const d of [home, binDir, nodeBin, cwd, join(home, '.codex'), join(home, '.claude')]) {
    mkdirSync(d, { recursive: true });
  }
  symlinkSync(process.execPath, join(nodeBin, 'node'));
  symlinkSync(PDD_BIN, join(binDir, 'pdd'));

  // Sync bundled skills to ~/.agents/skills and ~/.claude/skills.
  setupSkills({ packageRoot: REPO_ROOT, cwd, home, env: { HOME: home, PATH: '' } });

  // Write valid Codex and Claude Code MCP configs pinned to current pdd.
  writeFileSync(
    join(home, '.codex/config.toml'),
    `[mcp_servers.pdd]\ncommand = ${JSON.stringify(process.execPath)}\nargs = ${JSON.stringify([PDD_BIN, 'mcp'])}\ndefault_tools_approval_mode = "approve"\ntool_timeout_sec = 600\n`,
  );
  writeFileSync(
    join(home, '.claude.json'),
    `${JSON.stringify({ mcpServers: { pdd: { type: 'stdio', command: process.execPath, args: [PDD_BIN, 'mcp'] } } }, null, 2)}\n`,
  );

  // Matching login shell profiles so real `zsh -lc` / `bash -lc` resolve to the exact same pdd binary.
  const profileLine = `export PATH="${binDir}:${nodeBin}:$PATH"\n`;
  writeFileSync(join(home, '.zprofile'), profileLine);
  writeFileSync(join(home, '.bash_profile'), profileLine);

  const env = {
    HOME: home,
    ZDOTDIR: home,
    USER: process.env.USER || 'tester',
    PATH: `${binDir}:${nodeBin}:/usr/bin:/bin`,
  };
  return { root, home, binDir, nodeBin, cwd, env };
}

test('Test A (Healthy laptop): single pdd install, matching login shell, synced skills, valid MCP exits 0 and writes 0 files to $HOME', t => {
  const fx = makeHealthyLaptop(t);
  const beforeHome = snapshotTree(fx.home);

  // 1. Direct runDoctor with compatible Node >= 22.16.0 and isolated systemRoots (deterministic on any host).
  let out = '';
  const res = runDoctor(
    { cwd: fx.cwd, env: fx.env, packageRoot: REPO_ROOT, home: fx.home, systemRoots: [] },
    { stdout: { write: s => { out += s; } }, nodeVersion: '22.20.0' },
  );
  assert.equal(res.exitCode, 0, out);
  assert.equal(res.report.ok, true);
  assert.equal(res.report.schema_version, 'pdd.doctor.v1');
  assert.equal(res.report.checks.runtime.status, 'ok');
  assert.equal(res.report.checks.installs.status, 'ok');
  assert.equal(res.report.checks.skills.status, 'ok');
  assert.equal(res.report.checks.mcp.status, 'ok');
  assert.match(out, /✓ CLI & Node/);
  assert.match(out, /✓ Installs & PATH/);
  assert.match(out, /✓ Agent skills/);
  assert.match(out, /✓ Agent MCP/);
  assert.match(out, /Healthy: no actionable issues found\./);
  // Shortens $HOME paths to ~/...
  assert.match(out, /~\/\.agents\/skills/);
  assert.equal(out.includes(fx.home), false, 'human output should shorten $HOME paths to ~/');

  // 2. Live bin/pdd.mjs doctor subprocess check + strict 0-file-write guarantee.
  const cliRes = spawnSync(process.execPath, [PDD_BIN, 'doctor'], {
    cwd: fx.cwd,
    env: fx.env,
    encoding: 'utf8',
    timeout: 10000,
  });
  assert.equal(cliRes.stderr, '');
  assert.match(cliRes.stdout, /pdd doctor/);
  assert.match(cliRes.stdout, /✓ Agent skills/);
  assert.match(cliRes.stdout, /✓ Agent MCP/);
  if (!existsSync('/opt/homebrew/bin/pdd') && !existsSync('/usr/local/bin/pdd') && !existsSync('/opt/homebrew/anaconda3/bin/pdd')) {
    assert.match(cliRes.stdout, /✓ Installs & PATH/);
    if (HOST_NODE_OK) {
      assert.equal(cliRes.status, 0, cliRes.stdout);
      assert.match(cliRes.stdout, /Healthy: no actionable issues found\./);
    } else {
      // Honest check when test runner itself uses Node < 22.16.0.
      assert.equal(cliRes.status, 1, cliRes.stdout);
      assert.match(cliRes.stdout, /requires >= 22\.16\.0/);
    }
  }
  assert.deepEqual(snapshotTree(fx.home), beforeHome, 'pdd doctor must write 0 files to $HOME');
});

test('Test B (Login vs interactive shell PATH split): catches older 0.1.42 in login subshell (live shell + /opt/homebrew DI), reports both paths & versions + remediation, exits 1', t => {
  // 1. Deterministic DI test for exact /opt/homebrew/bin/pdd (0.1.42) login-shell split.
  const fx = makeHealthyLaptop(t);
  let out = '';
  const diRes = runDoctor(
    {
      cwd: fx.cwd,
      env: fx.env,
      packageRoot: REPO_ROOT,
      home: fx.home,
      systemRoots: [],
      loginShells: ['/bin/zsh', '/bin/bash'],
    },
    {
      stdout: { write: s => { out += s; } },
      spawnSync: (cmd, args) => {
        if (cmd === '/bin/zsh' && args[0] === '-lc') {
          return { status: 0, stdout: '\n__PDD_WHICH__=/opt/homebrew/bin/pdd\n', stderr: '' };
        }
        if (cmd === '/bin/bash' && args[0] === '-lc') {
          return { status: 0, stdout: `\n__PDD_WHICH__=${join(fx.binDir, 'pdd')}\n`, stderr: '' };
        }
        if (cmd === '/opt/homebrew/bin/pdd' && args[0] === '--version') {
          return { status: 0, stdout: '0.1.42\n', stderr: '' };
        }
        return { status: 1, stdout: '', stderr: '' };
      },
    },
  );
  assert.equal(diRes.exitCode, 1, out);
  assert.equal(diRes.report.ok, false);
  assert.equal(diRes.report.checks.installs.shell_splits.length, 1);
  assert.equal(diRes.report.checks.installs.shell_splits[0].name, 'zsh');
  assert.equal(diRes.report.checks.installs.shell_splits[0].resolvedPath, '/opt/homebrew/bin/pdd');
  assert.equal(diRes.report.checks.installs.shell_splits[0].version, '0.1.42');
  assert.equal(diRes.report.checks.installs.shell_splits[0].kind, 'homebrew');
  assert.equal(diRes.report.checks.installs.shell_splits[0].remediation, 'brew uninstall pdd');
  assert.match(out, /\/opt\/homebrew\/bin\/pdd/);
  assert.match(out, /0\.1\.42/);
  assert.match(out, new RegExp(PKG_VERSION.replaceAll('.', '\\.')));
  assert.match(out, /brew uninstall pdd/);

  // 2. Live OS login subshell split: interactive PATH points to current pdd, ~/.zprofile + ~/.bash_profile prepend stale 0.1.42.
  const oldDir = join(fx.root, 'opt/homebrew/bin');
  mkdirSync(oldDir, { recursive: true });
  writeFileSync(join(oldDir, 'pdd'), '#!/bin/sh\necho 0.1.42\n', { mode: 0o755 });
  const splitProfile = `export PATH="${oldDir}:$PATH"\n`;
  writeFileSync(join(fx.home, '.zprofile'), splitProfile);
  writeFileSync(join(fx.home, '.bash_profile'), splitProfile);
  const beforeHome = snapshotTree(fx.home);

  const liveRes = spawnSync(process.execPath, [PDD_BIN, 'doctor', '--json'], {
    cwd: fx.cwd,
    env: fx.env,
    encoding: 'utf8',
    timeout: 10000,
  });
  assert.equal(liveRes.status, 1, liveRes.stdout);
  const parsed = JSON.parse(liveRes.stdout);
  assert.equal(parsed.ok, false);
  assert.ok(parsed.checks.installs.shell_splits.length >= 1, JSON.stringify(parsed.checks.installs.login_shells));
  assert.equal(parsed.checks.installs.shell_splits[0].resolvedPath, join(oldDir, 'pdd'));
  assert.equal(parsed.checks.installs.shell_splits[0].version, '0.1.42');
  assert.equal(parsed.checks.installs.shell_splits[0].remediation, 'brew uninstall pdd');
  assert.deepEqual(snapshotTree(fx.home), beforeHome, 'live doctor wrote 0 files to $HOME');
});

test('Test C (Dual installs across Volta + nvm + conda/Python): doctor, setup, and upgrade detect every duplicate and emit exact per-manager cleanup commands', async t => {
  const fx = makeHealthyLaptop(t);

  // Stale Volta install
  const voltaPkg = join(fx.home, '.volta/tools/image/packages/@promptdriven/pdd/lib/node_modules/@promptdriven/pdd');
  mkdirSync(join(fx.home, '.volta/bin'), { recursive: true });
  mkdirSync(join(fx.home, '.volta/tools/user/bins'), { recursive: true });
  mkdirSync(join(voltaPkg, 'bin'), { recursive: true });
  writeFileSync(join(voltaPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.41', bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(voltaPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  writeFileSync(join(fx.home, '.volta/bin/volta-shim'), '#!/bin/sh\nexit 0\n', { mode: 0o755 });
  symlinkSync('volta-shim', join(fx.home, '.volta/bin/pdd'));
  writeFileSync(join(fx.home, '.volta/tools/user/bins/pdd.json'), JSON.stringify({ name: 'pdd', package: '@promptdriven/pdd' }));

  // Stale nvm install
  const nvmPrefix = join(fx.home, '.nvm/versions/node/v20.12.0');
  const nvmPkg = join(nvmPrefix, 'lib/node_modules/@promptdriven/pdd');
  mkdirSync(join(nvmPrefix, 'bin'), { recursive: true });
  mkdirSync(join(nvmPkg, 'bin'), { recursive: true });
  writeFileSync(join(nvmPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.39', bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(nvmPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  symlinkSync('../lib/node_modules/@promptdriven/pdd/bin/pdd.mjs', join(nvmPrefix, 'bin/pdd'));

  // Stale conda/Python install
  const condaBin = join(fx.home, 'miniconda3/bin');
  mkdirSync(condaBin, { recursive: true });
  writeFileSync(join(condaBin, 'pdd'), '#!/bin/sh\n# python pdd-cli\necho "pdd, version 0.0.305"\n', { mode: 0o755 });

  // Symlink alias to the current pdd -> must NOT be counted as a duplicate!
  const dupAliasDir = join(fx.root, 'alias-current');
  mkdirSync(dupAliasDir, { recursive: true });
  symlinkSync(PDD_BIN, join(dupAliasDir, 'pdd'));
  fx.env.PATH = `${fx.binDir}:${dupAliasDir}:${fx.nodeBin}:/usr/bin:/bin`;

  // 1. Live `pdd doctor` catches all 3 duplicates with exact per-manager commands and exits 1.
  const docRes = spawnSync(process.execPath, [PDD_BIN, 'doctor'], {
    cwd: fx.cwd,
    env: fx.env,
    encoding: 'utf8',
    timeout: 10000,
  });
  assert.equal(docRes.status, 1, docRes.stdout);
  assert.match(docRes.stdout, /volta uninstall @promptdriven\/pdd/);
  assert.match(docRes.stdout, /npm uninstall -g @promptdriven\/pdd --prefix/);
  assert.match(docRes.stdout, /pip uninstall pdd-cli/);
  assert.doesNotMatch(docRes.stdout, /alias-current/);

  // 2. Live `pdd setup` proactively warns on stderr with exact per-manager cleanup commands!
  const setupRes = spawnSync(process.execPath, [PDD_BIN, 'setup'], {
    cwd: fx.cwd,
    env: fx.env,
    encoding: 'utf8',
    timeout: 10000,
  });
  assert.equal(setupRes.status, 0, setupRes.stderr);
  assert.match(setupRes.stderr, /Competing pdd installs/);
  assert.match(setupRes.stderr, /volta uninstall @promptdriven\/pdd/);
  assert.match(setupRes.stderr, /npm uninstall -g @promptdriven\/pdd --prefix/);
  assert.match(setupRes.stderr, /pip uninstall pdd-cli/);

  // 3. `pdd upgrade` (`runCliUpgrade`) proactively warns on stderr when competing installs exist!
  const fakePrefix = join(fx.root, 'npm-global');
  const fakePkgRoot = join(fakePrefix, 'lib/node_modules/@promptdriven/pdd');
  mkdirSync(join(fakePkgRoot, 'bin'), { recursive: true });
  writeFileSync(join(fakePkgRoot, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.50', bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(fakePkgRoot, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  let upOut = '';
  let upErr = '';
  const upRes = await runCliUpgrade(
    {
      packageRoot: fakePkgRoot,
      cwd: fx.cwd,
      home: fx.home,
      env: fx.env,
      stdout: { write: s => { upOut += s; } },
      stderr: { write: s => { upErr += s; } },
      fetchImpl: async () => ({ ok: true, json: async () => [{ tag_name: 'v0.1.50', draft: false, prerelease: false }] }),
      spawnSyncImpl: () => ({ status: 0, stdout: '', stderr: '' }),
    },
    {
      skillsInstall: { syncOwnedUserSkills: () => ({ updated: [] }), findSkills: () => [] },
      hostInstallPorts: { systemRoots: [], checkLoginShells: false },
    },
  );
  assert.equal(upRes.exitCode, 0, upErr);
  assert.match(upOut, /already up to date/);
  assert.match(upErr, /Competing pdd installs/);
  assert.match(upErr, /volta uninstall @promptdriven\/pdd/);
  assert.match(upErr, /pip uninstall pdd-cli/);
});

test('Test D (Stale MCP + 0-byte/malformed/symlink MCP + stale/retired skills + incompatible Node + --json): valid pdd.doctor.v1 JSON and zero file mutations', t => {
  const fx = makeHealthyLaptop(t);

  // 1. Stale skill version in ~/.agents/skills/pdd + retired skill in ~/.codex/skills/pdd-autopilot
  writeFileSync(
    join(fx.home, '.agents/skills/pdd/.pdd-skill.json'),
    `${JSON.stringify({ package: 'pdd', version: '0.1.20', digest: 'old-digest' })}\n`,
  );
  mkdirSync(join(fx.home, '.codex/skills/pdd-autopilot'), { recursive: true });
  writeFileSync(join(fx.home, '.codex/skills/pdd-autopilot/.pdd-skill.json'), '{"package":"pdd","version":"0.1.20"}\n');

  // 2. Claude Code MCP pointing to another/missing pdd binary (stale)
  writeFileSync(
    join(fx.home, '.claude.json'),
    `${JSON.stringify({ mcpServers: { pdd: { type: 'stdio', command: '/opt/old/bin/pdd', args: ['mcp'] } } }, null, 2)}\n`,
  );

  // 3. Gemini CLI 0-byte JSON config
  mkdirSync(join(fx.home, '.gemini'), { recursive: true });
  writeFileSync(join(fx.home, '.gemini/settings.json'), '');

  // 4. Antigravity malformed JSON config
  mkdirSync(join(fx.home, '.gemini/config'), { recursive: true });
  writeFileSync(join(fx.home, '.gemini/config/mcp_config.json'), '{broken json');

  // 5. Codex symlinked config.toml
  const realToml = join(fx.root, 'real-codex.toml');
  writeFileSync(realToml, 'model = "gpt-5"\n');
  rmSync(join(fx.home, '.codex/config.toml'));
  symlinkSync(realToml, join(fx.home, '.codex/config.toml'));

  const beforeHome = snapshotTree(fx.home);

  const liveJson = spawnSync(process.execPath, [PDD_BIN, 'doctor', '--json'], {
    cwd: fx.cwd,
    env: fx.env,
    encoding: 'utf8',
    timeout: 10000,
  });
  assert.equal(liveJson.status, 1, liveJson.stderr);
  assert.equal(liveJson.stderr, '');
  const report = JSON.parse(liveJson.stdout);
  assert.equal(report.schema_version, 'pdd.doctor.v1');
  assert.equal(report.ok, false);
  assert.equal(report.exit_code, 1);

  const codes = new Set(report.findings.map(f => f.code));
  assert.ok(codes.has('skills-stale'), `expected skills-stale in ${[...codes]}`);
  assert.ok(codes.has('skills-retired'), `expected skills-retired in ${[...codes]}`);
  assert.ok(codes.has('mcp-stale'), `expected mcp-stale in ${[...codes]}`);
  assert.ok(codes.has('mcp-empty'), `expected mcp-empty in ${[...codes]}`);
  assert.ok(codes.has('mcp-malformed'), `expected mcp-malformed in ${[...codes]}`);
  assert.ok(codes.has('mcp-symlink'), `expected mcp-symlink in ${[...codes]}`);

  const byAgent = new Map(report.checks.mcp.agents.map(a => [a.name, a]));
  assert.equal(byAgent.get('Claude Code')?.status, 'stale');
  assert.equal(byAgent.get('Gemini CLI')?.status, 'empty');
  assert.equal(byAgent.get('Gemini CLI')?.remediation, 'pdd setup --yes');
  const emptyFinding = report.findings.find(f => f.code === 'mcp-empty');
  assert.equal(emptyFinding?.severity, 'warn');
  assert.equal(emptyFinding?.remediation, 'pdd setup --yes');
  assert.equal(byAgent.get('Antigravity')?.status, 'malformed');
  assert.equal(byAgent.get('Codex')?.status, 'symlink');
  assert.ok(report.remediations.includes('pdd setup'));
  assert.ok(report.remediations.includes('pdd setup --yes'));
  assert.equal(report.remediations.some(r => /Fix or remove empty/i.test(r)), false);

  // Incompatible Node check via DI
  const oldNode = collectDoctorReport(
    { cwd: fx.cwd, env: fx.env, packageRoot: REPO_ROOT, home: fx.home, systemRoots: [], checkLoginShells: false },
    { nodeVersion: '20.18.0' },
  );
  assert.equal(oldNode.exit_code, 1);
  assert.equal(oldNode.checks.runtime.status, 'error');
  assert.equal(oldNode.checks.runtime.node_compatible, false);
  assert.ok(oldNode.findings.some(f => f.code === 'node-incompatible'));

  // Claude Code plugin install is respected (not flagged as missing ~/.claude/skills)
  const pluginHome = tempDir(t, 'pdd-doctor-plugin-');
  mkdirSync(join(pluginHome, '.claude/plugins'), { recursive: true });
  writeFileSync(join(pluginHome, '.claude/plugins/installed_plugins.json'), JSON.stringify({ plugins: { 'pdd@promptdriven': { installPath: '/plugins/pdd' } } }));
  const pluginReport = collectDoctorReport(
    { cwd: fx.cwd, env: { HOME: pluginHome, PATH: '' }, packageRoot: REPO_ROOT, home: pluginHome, systemRoots: [], checkLoginShells: false },
  );
  assert.equal(pluginReport.checks.skills.claude_plugin, '/plugins/pdd');
  assert.equal(pluginReport.checks.skills.status, 'ok');

  // Strict 0-file-mutation check on $HOME
  assert.deepEqual(snapshotTree(fx.home), beforeHome, 'pdd doctor --json must not mutate any file in $HOME');
});

test('Test E (Recursion & timeout safety): hanging fake pdd on PATH is bounded cleanly without hanging pdd doctor', t => {
  const fx = makeHealthyLaptop(t);
  const hangDir = join(fx.root, 'hang-bin');
  mkdirSync(hangDir, { recursive: true });
  const hangingScript = '#!/bin/sh\nexec /bin/sleep 10\n';
  writeFileSync(join(hangDir, 'pdd'), hangingScript, { mode: 0o755 });

  // Put hanging pdd ahead of current on PATH.
  fx.env.PATH = `${hangDir}:${fx.binDir}:${fx.nodeBin}:/usr/bin:/bin`;

  const start = Date.now();
  const res = runDoctor(
    {
      cwd: fx.cwd,
      env: fx.env,
      packageRoot: REPO_ROOT,
      home: fx.home,
      probeTimeoutMs: 300,
      systemRoots: [],
      checkLoginShells: false,
    },
    {},
  );
  const elapsedMs = Date.now() - start;

  assert.equal(res.exitCode, 1);
  assert.ok(elapsedMs < 3000, `expected bounded timeout < 3000ms, took ${elapsedMs}ms`);
  assert.equal(res.report.checks.installs.shadowed_on_path, true);
  assert.equal(res.report.checks.installs.duplicates[0].versionTimedOut, true);
  assert.equal(res.report.checks.installs.duplicates[0].version, null);
  assert.match(res.output, /version timed out/);
  // Hanging binary itself was never touched.
  assert.equal(readFileSync(join(hangDir, 'pdd'), 'utf8'), hangingScript);

  // gh check with GH_TOKEN succeeds without spawning gh; without hosts.yml never spawns gh.
  let ghSpawned = false;
  const envTokenReport = collectDoctorReport(
    { cwd: fx.cwd, env: { HOME: fx.home, PATH: '/usr/bin:/bin', GH_TOKEN: 'gho_test' }, packageRoot: REPO_ROOT, home: fx.home, systemRoots: [], checkLoginShells: false },
    { spawnSync: () => { ghSpawned = true; return { status: 0, stdout: 'tok' }; } },
  );
  assert.equal(envTokenReport.checks.gh.status, 'ok');
  assert.equal(envTokenReport.checks.gh.method, 'env-token');
  assert.equal(ghSpawned, false);

  const noHostsReport = collectDoctorReport(
    { cwd: fx.cwd, env: { HOME: fx.home, PATH: `${fx.nodeBin}:/usr/bin:/bin` }, packageRoot: REPO_ROOT, home: fx.home, systemRoots: [], checkLoginShells: false },
    { spawnSync: () => { ghSpawned = true; return { status: 0, stdout: 'tok' }; } },
  );
  assert.equal(noHostsReport.checks.gh.status, 'advisory');
  assert.equal(ghSpawned, false);
});

test('runPdd dispatches doctor and doctor --json cleanly and rejects invalid flags with exit 2', async t => {
  const fx = makeHealthyLaptop(t);
  let out = '';
  let err = '';
  const code = await runPdd(['doctor', '--json'], {
    cwd: fx.cwd,
    env: fx.env,
    packageRoot: REPO_ROOT,
    stdout: { write: s => { out += s; } },
    stderr: { write: s => { err += s; } },
    doctorPorts: { systemRoots: [], checkLoginShells: false, nodeVersion: '22.20.0' },
  });
  assert.equal(code, 0, `${err}\n${out}`);
  assert.equal(err, '');
  const parsed = JSON.parse(out);
  assert.equal(parsed.schema_version, 'pdd.doctor.v1');
  assert.equal(parsed.ok, true);

  // Invalid operand / flag returns exit 2
  let badErr = '';
  const badCode = await runPdd(['doctor', '--bogus'], {
    cwd: fx.cwd,
    env: fx.env,
    packageRoot: REPO_ROOT,
    stdout: { write() {} },
    stderr: { write: s => { badErr += s; } },
  });
  assert.equal(badCode, 2);
  assert.match(badErr, /Unsupported command or options/);
});

test('Adversarial hardening: ANSI/newline sanitization, broken MCP command/bare pdd, unmarked retired skills, non-regular MCP, Gemini CLI skills, gh auth token, and empty $HOME', t => {
  const fx = makeHealthyLaptop(t);
  const beforeCwd = snapshotTree(fx.cwd);

  // 1. ANSI escape & newline injection in MCP config command/args must never emit raw ESC or spoofed lines!
  writeFileSync(
    join(fx.home, '.claude.json'),
    `${JSON.stringify({ mcpServers: { pdd: { command: '/tmp/\x1b[31mFAKE\x1b[0m\n✓ Healthy\n/pdd', args: ['mcp'] } } }, null, 2)}\n`,
  );
  // 2. Codex MCP with deleted absolute command binary (even though args has real PDD_BIN) must be flagged stale!
  writeFileSync(
    join(fx.home, '.codex/config.toml'),
    `[mcp_servers.pdd]\ncommand = "/nonexistent/nvm/v18/bin/node"\nargs = ${JSON.stringify([PDD_BIN, 'mcp'])}\n`,
  );
  // 3. Gemini CLI non-regular MCP path (directory where settings.json should be) -> actionable move/remove fix (not bare pdd setup --yes).
  mkdirSync(join(fx.home, '.gemini/settings.json'), { recursive: true });
  // 4. Unmarked retired skill folder (no .pdd-skill.json) -> explicit rm -rf remediation instead of unfixable pdd setup loop.
  mkdirSync(join(fx.home, '.agents/skills/pdd-check'), { recursive: true });
  writeFileSync(join(fx.home, '.agents/skills/pdd-check/SKILL.md'), '# Retired unmarked\n');

  const res = runDoctor(
    { cwd: fx.cwd, env: fx.env, packageRoot: REPO_ROOT, home: fx.home, systemRoots: [], checkLoginShells: false },
    { nodeVersion: '22.20.0' },
  );
  assert.equal(res.exitCode, 1);
  assert.doesNotMatch(res.output, /\x1b/, 'human output must contain zero ANSI escape codes');
  assert.equal(res.output.includes('\n✓ Healthy'), false, 'newline injection must not forge output lines');

  const mcpByAgent = new Map(res.report.checks.mcp.agents.map(a => [a.name, a]));
  assert.equal(mcpByAgent.get('Codex')?.status, 'stale');
  assert.match(mcpByAgent.get('Codex')?.detail ?? '', /command binary missing/);
  assert.equal(mcpByAgent.get('Gemini CLI')?.status, 'non-regular');
  assert.match(mcpByAgent.get('Gemini CLI')?.remediation ?? '', /Move or remove non-regular/);

  const unmarkedRetired = res.report.findings.find(f => f.code === 'skills-retired' && f.message.includes('unmarked'));
  assert.ok(unmarkedRetired, JSON.stringify(res.report.findings, null, 2));
  assert.match(unmarkedRetired.remediation ?? '', /^rm -rf /);

  // 5. Bare "pdd" in MCP config when pdd is NOT on PATH must be flagged stale (not ok!).
  const offPathHome = tempDir(t, 'pdd-doctor-offpath-');
  mkdirSync(join(offPathHome, '.claude'), { recursive: true });
  writeFileSync(
    join(offPathHome, '.claude.json'),
    `${JSON.stringify({ mcpServers: { pdd: { command: 'pdd', args: ['mcp'] } } })}\n`,
  );
  const offPathRes = collectDoctorReport(
    { cwd: fx.cwd, env: { HOME: offPathHome, PATH: '/usr/bin:/bin' }, packageRoot: REPO_ROOT, home: offPathHome, systemRoots: [], checkLoginShells: false },
    { nodeVersion: '22.20.0' },
  );
  assert.equal(offPathRes.checks.mcp.agents[0]?.status, 'stale');
  assert.match(offPathRes.checks.mcp.agents[0]?.detail ?? '', /not on PATH/);

  // 6. Gemini CLI detected requires ~/.agents/skills even if Claude plugin is present.
  const gemHome = tempDir(t, 'pdd-doctor-gemini-');
  mkdirSync(join(gemHome, '.claude/plugins'), { recursive: true });
  writeFileSync(join(gemHome, '.claude/plugins/installed_plugins.json'), JSON.stringify({ plugins: { 'pdd@promptdriven': { installPath: '/p' } } }));
  mkdirSync(join(gemHome, '.gemini'), { recursive: true });
  writeFileSync(join(gemHome, '.gemini/settings.json'), JSON.stringify({ mcpServers: { pdd: { command: process.execPath, args: [PDD_BIN, 'mcp'] } } }));
  const gemRes = collectDoctorReport(
    { cwd: fx.cwd, env: { HOME: gemHome, PATH: '' }, packageRoot: REPO_ROOT, home: gemHome, systemRoots: [], checkLoginShells: false },
    { nodeVersion: '22.20.0' },
  );
  assert.equal(gemRes.checks.skills.status, 'warn');
  assert.ok(gemRes.findings.some(f => f.code === 'skills-missing' && f.path === join(gemHome, '.agents/skills')));

  // 7. gh auth token with hosts.yml passes GH_NO_UPDATE_NOTIFIER=1 and maxBuffer, and handles ok + timeout.
  const ghHome = tempDir(t, 'pdd-doctor-gh-');
  const ghBin = join(ghHome, 'bin');
  mkdirSync(ghBin, { recursive: true });
  mkdirSync(join(ghHome, '.config/gh'), { recursive: true });
  writeFileSync(join(ghBin, 'gh'), '#!/bin/sh\nexit 0\n', { mode: 0o755 });
  writeFileSync(join(ghHome, '.config/gh/hosts.yml'), 'github.com:\n  user: dev\n');
  let capturedGhOpts = null;
  const ghOk = collectDoctorReport(
    { cwd: fx.cwd, env: { HOME: ghHome, PATH: ghBin }, packageRoot: REPO_ROOT, home: ghHome, systemRoots: [], checkLoginShells: false },
    {
      nodeVersion: '22.20.0',
      spawnSync: (cmd, args, opts) => {
        if (cmd === 'gh' && args[0] === 'auth') {
          capturedGhOpts = opts;
          return { status: 0, stdout: 'gho_secret_token\n', stderr: '' };
        }
        return { status: 1, stdout: '', stderr: '' };
      },
    },
  );
  assert.equal(ghOk.checks.gh.status, 'ok');
  assert.equal(ghOk.checks.gh.method, 'gh-auth');
  assert.equal(capturedGhOpts?.env?.GH_NO_UPDATE_NOTIFIER, '1');
  assert.equal(capturedGhOpts?.maxBuffer, 65536);

  // 8. Empty/missing $HOME with throwing homedir() never crashes and never reads relative paths in cwd.
  const emptyHomeRes = collectDoctorReport(
    { cwd: fx.cwd, env: { HOME: '', PATH: '' }, packageRoot: REPO_ROOT, systemRoots: [], checkLoginShells: false },
    { nodeVersion: '22.20.0', homedir: () => { throw new Error('no home'); } },
  );
  assert.equal(emptyHomeRes.schema_version, 'pdd.doctor.v1');
  assert.deepEqual(emptyHomeRes.checks.skills.roots, []);
  assert.deepEqual(emptyHomeRes.checks.mcp.agents, []);
  assert.deepEqual(snapshotTree(fx.cwd), beforeCwd, 'doctor never writes to cwd');
});

test('#3726 Bug 1: 0-byte, whitespace-only, and UTF-8 BOM-only JSON MCP configs emit warn + deduplicated pdd setup --yes, BOM JSON parses ok, and pdd setup --yes heals them', t => {
  const fx = makeHealthyLaptop(t);

  // Antigravity: 0-byte JSON (sync skills after creating .gemini/config so only MCP issues are present)
  mkdirSync(join(fx.home, '.gemini/config'), { recursive: true });
  writeFileSync(join(fx.home, '.gemini/config/mcp_config.json'), '');
  setupSkills({ packageRoot: REPO_ROOT, cwd: fx.cwd, home: fx.home, env: { HOME: fx.home, PATH: '' } });
  // Gemini CLI: UTF-8 BOM + whitespace-only JSON
  writeFileSync(join(fx.home, '.gemini/settings.json'), '\uFEFF  \n\t ');
  // Claude Code: valid JSON missing pdd entry (mcp-missing) to verify deduplication
  writeFileSync(join(fx.home, '.claude.json'), '{}\n');

  const beforeHome = snapshotTree(fx.home);
  const res = runDoctor(
    { cwd: fx.cwd, env: fx.env, packageRoot: REPO_ROOT, home: fx.home, systemRoots: [], checkLoginShells: false },
    { nodeVersion: '22.20.0' },
  );
  assert.equal(res.exitCode, 1, res.output);
  assert.deepEqual(snapshotTree(fx.home), beforeHome, 'doctor remains strictly read-only');

  const byAgent = new Map(res.report.checks.mcp.agents.map(a => [a.name, a]));
  assert.equal(byAgent.get('Antigravity')?.status, 'empty');
  assert.equal(byAgent.get('Antigravity')?.remediation, 'pdd setup --yes');
  assert.equal(byAgent.get('Gemini CLI')?.status, 'empty');
  assert.equal(byAgent.get('Gemini CLI')?.remediation, 'pdd setup --yes');
  assert.equal(byAgent.get('Claude Code')?.status, 'missing');

  const emptyFindings = res.report.findings.filter(f => f.code === 'mcp-empty');
  assert.equal(emptyFindings.length, 2, JSON.stringify(res.report.findings, null, 2));
  for (const finding of emptyFindings) {
    assert.equal(finding.severity, 'warn');
    assert.equal(finding.remediation, 'pdd setup --yes');
  }
  assert.deepEqual(res.report.checks.mcp.remediations, ['pdd setup --yes']);
  assert.deepEqual(res.report.remediations, ['pdd setup --yes']);
  assert.doesNotMatch(res.output, /Fix or remove empty/i);
  assert.match(res.output, /fix: pdd setup --yes/);

  // Real pdd setup --yes repairs 0-byte & BOM-only JSON files directly without manual deletion.
  const setupRes = spawnSync(process.execPath, [PDD_BIN, 'setup', '--yes'], {
    cwd: fx.cwd,
    env: fx.env,
    encoding: 'utf8',
    timeout: 10000,
  });
  assert.equal(setupRes.status, 0, setupRes.stderr);

  const afterRes = runDoctor(
    { cwd: fx.cwd, env: fx.env, packageRoot: REPO_ROOT, home: fx.home, systemRoots: [], checkLoginShells: false },
    { nodeVersion: '22.20.0' },
  );
  assert.equal(afterRes.exitCode, 0, afterRes.output);
  assert.equal(afterRes.report.checks.mcp.status, 'ok');

  // UTF-8 BOM-prefixed valid JSON MCP config is parsed cleanly as ok (not malformed).
  const agyPath = join(fx.home, '.gemini/config/mcp_config.json');
  writeFileSync(agyPath, `\uFEFF${readFileSync(agyPath, 'utf8')}`);
  const bomValidRes = runDoctor(
    { cwd: fx.cwd, env: fx.env, packageRoot: REPO_ROOT, home: fx.home, systemRoots: [], checkLoginShells: false },
    { nodeVersion: '22.20.0' },
  );
  assert.equal(bomValidRes.exitCode, 0, bomValidRes.output);
  const bomAgy = bomValidRes.report.checks.mcp.agents.find(a => a.name === 'Antigravity');
  assert.equal(bomAgy?.status, 'ok');
});

test('#3726 Bugs 2 & 3 in doctor: unexposed uv/pipx tool venvs stay green, and exposed uv venv reads dist-info METADATA statically without spawning hanging python', t => {
  const fx = makeHealthyLaptop(t);

  // Create internal uv and pipx venvs plus an intentional non-colliding ~/.local/bin/pdd-v1 wrapper,
  // with NO ~/.local/bin/pdd entrypoint.
  const uvVenv = join(fx.home, '.local/share/uv/tools/pdd-cli');
  const uvBin = join(uvVenv, 'bin');
  const uvDist = join(uvVenv, 'lib/python3.12/site-packages/pdd_cli-0.0.246.dist-info');
  mkdirSync(uvBin, { recursive: true });
  mkdirSync(uvDist, { recursive: true });
  writeFileSync(join(uvBin, 'pdd'), `#!${join(uvBin, 'python3')}\nexec /bin/sleep 10\n`, { mode: 0o755 });
  writeFileSync(join(uvDist, 'METADATA'), 'Metadata-Version: 2.3\nName: pdd-cli\nVersion: 0.0.246\n\n# Body\n');

  const pipxBin = join(fx.home, '.local/pipx/venvs/pdd-cli/bin');
  mkdirSync(pipxBin, { recursive: true });
  writeFileSync(join(pipxBin, 'pdd'), '#!/usr/bin/env python3\nimport time; time.sleep(10)\n', { mode: 0o755 });

  mkdirSync(join(fx.home, '.local/bin'), { recursive: true });
  writeFileSync(join(fx.home, '.local/bin/pdd-v1'), `#!/bin/sh\nexec "${join(uvBin, 'pdd')}" "$@"\n`, { mode: 0o755 });

  const isolatedRes = runDoctor(
    { cwd: fx.cwd, env: fx.env, packageRoot: REPO_ROOT, home: fx.home, systemRoots: [], checkLoginShells: false },
    { nodeVersion: '22.20.0' },
  );
  assert.equal(isolatedRes.exitCode, 0, isolatedRes.output);
  assert.equal(isolatedRes.report.checks.installs.status, 'ok');
  assert.equal(isolatedRes.report.checks.installs.duplicates.length, 0);

  // Now expose uv tool via ~/.local/bin/pdd symlink -> doctor catches it immediately from METADATA with zero sleep!
  symlinkSync(join(uvBin, 'pdd'), join(fx.home, '.local/bin/pdd'));
  const start = Date.now();
  const exposedRes = runDoctor(
    { cwd: fx.cwd, env: fx.env, packageRoot: REPO_ROOT, home: fx.home, systemRoots: [], checkLoginShells: false, probeTimeoutMs: 400 },
    { nodeVersion: '22.20.0' },
  );
  const elapsedMs = Date.now() - start;
  assert.equal(exposedRes.exitCode, 1, exposedRes.output);
  assert.ok(elapsedMs < 1000, `expected instant static METADATA read, took ${elapsedMs}ms`);
  assert.equal(exposedRes.report.checks.installs.duplicates.length, 1);
  assert.equal(exposedRes.report.checks.installs.duplicates[0].version, '0.0.246');
  assert.equal(exposedRes.report.checks.installs.duplicates[0].versionTimedOut, false);
  assert.equal(exposedRes.report.checks.installs.duplicates[0].remediation, 'uv tool uninstall pdd-cli');
  assert.match(exposedRes.output, /0\.0\.246/);
  assert.match(exposedRes.output, /uv tool uninstall pdd-cli/);
  assert.doesNotMatch(exposedRes.output, /version timed out/);
});
