import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, realpathSync, rmSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, relative } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { setupSkills, PDD_SKILL_NAMES } from '../src/skills-install.mjs';

const root = fileURLToPath(new URL('..', import.meta.url));
const temp = t => { const p = realpathSync(mkdtempSync(join(tmpdir(), "pdd skills ' "))); t.after(() => rmSync(p, { recursive: true, force: true })); return p; };
const filesUnder = (dir, base = dir) => readdirSync(dir, { withFileTypes: true }).flatMap(entry =>
  entry.isDirectory() ? filesUnder(join(dir, entry.name), base) : [relative(base, join(dir, entry.name))]).sort();
const ROOTS = ['.agents/skills', '.claude/skills'];
const version = () => JSON.parse(readFileSync(join(root, 'package.json'), 'utf8')).version;
const MARKER = '.pdd-skill.json';
// npx skills update changes only skills that npx skills add recorded; this command replaces any copy (0.1.8 tester).
const UPDATE = 'npx skills add promptdriven/pdd#alpha -g -a codex -a claude-code -y';

// A copied package in a quoted path, so install never depends on the source checkout.
function packageCopy(t) {
  const sandbox = temp(t), pkg = join(sandbox, 'installed "pkg"');
  mkdirSync(pkg);
  for (const name of ['src', 'bin', 'package.json', 'docs', 'skills']) cpSync(join(root, name), join(pkg, name), { recursive: true });
  const home = join(sandbox, 'home'), project = join(sandbox, 'project $(x) "q"');
  for (const dir of [home, project]) mkdirSync(dir);
  const env = { ...process.env, HOME: home, CODEX_HOME: join(home, '.codex') };
  delete env.CLAUDE_CONFIG_DIR;
  const run = (args, extra = {}) => spawnSync(process.execPath, [join(pkg, 'bin/pdd.mjs'), ...args],
    { cwd: project, env: { ...env, ...extra }, encoding: 'utf8', timeout: 10000 });
  return { sandbox, pkg, home, project, env, run };
}

// Wrong: an ordinary command writes skill folders into the person's home (only pdd setup may install them).
test('INSTALL1: pdd --version, help and workflow list write nothing to HOME or CLAUDE_CONFIG_DIR', t => {
  const { sandbox, pkg, home, project, run } = packageCopy(t);
  const config = join(sandbox, 'claude config');
  const alpha = join(sandbox, 'alpha-bin'), legacy = join(sandbox, 'legacy-bin');
  mkdirSync(alpha); mkdirSync(legacy);
  symlinkSync(join(pkg, 'bin/pdd.mjs'), join(alpha, 'pdd'));
  symlinkSync(process.execPath, join(alpha, 'node'));
  writeFileSync(join(legacy, 'pdd'), '#!/bin/sh\necho "pdd, version 0.0.305"\n', { mode: 0o755 });
  const path = `${alpha}:/usr/bin:/bin`;
  for (const args of [['--version'], ['--help'], ['workflow', 'list']]) {
    const result = run(args, { CLAUDE_CONFIG_DIR: config, PATH: path });
    assert.equal(result.status, 0, result.stderr);
    if (args[0] === '--version') {
      assert.equal(result.stdout, `${version()}\n`);
      assert.equal(result.stderr, '');
    } else assert.equal(result.stderr, '');
  }
  const conflict = run(['--version'], { CLAUDE_CONFIG_DIR: config, PATH: `${legacy}:${path}` });
  assert.equal(conflict.status, 0); assert.equal(conflict.stdout, `${version()}\n`);
  assert.match(conflict.stderr, /PATH selects:.*pdd, version 0\.0\.305/);
  assert.deepEqual(readdirSync(home), []); assert.deepEqual(readdirSync(project), []); assert.equal(existsSync(config), false);
});

// Wrong: setup leaves an agent without the skills, copies them into the repo, or rewrites them on a second run.
test('INSTALL2: pdd setup installs missing skills into each agent user folder, says so, and a second run changes nothing', t => {
  const { pkg, home, project, run } = packageCopy(t);
  const first = run(['setup']);
  assert.equal(first.status, 0, first.stderr);
  for (const skillRoot of ROOTS) {
    assert.ok(first.stdout.includes(`Installed 5 PDD skills to ${join(home, skillRoot)}: ${PDD_SKILL_NAMES.join(', ')}\n`), first.stdout);
    assert.deepEqual(readdirSync(join(home, skillRoot)).sort(), [...PDD_SKILL_NAMES].sort());
    for (const name of PDD_SKILL_NAMES) {
      const installed = join(home, skillRoot, name), source = join(pkg, 'skills', name);
      assert.deepEqual(filesUnder(installed).filter(file => file !== MARKER), filesUnder(source));
      for (const file of filesUnder(source)) assert.deepEqual(readFileSync(join(installed, file)), readFileSync(join(source, file)), file);
      assert.equal(JSON.parse(readFileSync(join(installed, MARKER), 'utf8')).version, version());
    }
  }
  assert.deepEqual(readdirSync(project), ['AGENTS.md']);
  const inodes = ROOTS.map(skillRoot => statSync(join(home, skillRoot, 'pdd-bug')).ino), block = readFileSync(join(project, 'AGENTS.md'), 'utf8');
  const second = run(['setup']);
  assert.equal(second.status, 0, second.stderr);
  for (const skillRoot of ROOTS) assert.ok(second.stdout.includes(`PDD skills found in ${join(home, skillRoot)}\n`), second.stdout);
  assert.doesNotMatch(second.stdout, /Installed|Updated/);
  assert.deepEqual(ROOTS.map(skillRoot => statSync(join(home, skillRoot, 'pdd-bug')).ino), inodes);
  assert.equal(readFileSync(join(project, 'AGENTS.md'), 'utf8'), block);
});

// Wrong: setup copies over skills that npx skills add already installed (symlinked folders without the pdd marker).
test('INSTALL3: after an npx-style install in the project, pdd setup finds the skills and copies nothing', t => {
  const { pkg, home, project, run } = packageCopy(t);
  for (const name of PDD_SKILL_NAMES) {
    cpSync(join(pkg, 'skills', name), join(project, '.agents/skills', name), { recursive: true });
    mkdirSync(join(project, '.claude/skills'), { recursive: true });
    symlinkSync(join(project, '.agents/skills', name), join(project, '.claude/skills', name));
  }
  const result = run(['setup']);
  assert.equal(result.status, 0, result.stderr);
  for (const skillRoot of ROOTS) assert.ok(result.stdout.includes(`PDD skills found in ${join(project, skillRoot)}\n`), result.stdout);
  assert.doesNotMatch(result.stdout, /Installed|Updated/);
  assert.deepEqual(readdirSync(home), []);
  assert.equal(existsSync(join(project, '.agents/skills/pdd-bug', MARKER)), false);
});

// Wrong: an update keeps stale files, a newer copy is downgraded, or a person's own folder or symlink is overwritten.
test('INSTALL4: setup updates only older or changed copies that carry the pdd marker', t => {
  const { pkg, home } = packageCopy(t);
  const opts = { packageRoot: pkg, cwd: join(home, 'none'), home };
  setupSkills(opts);
  const [agents, claude] = ROOTS.map(skillRoot => join(home, skillRoot));
  const marker = dir => JSON.parse(readFileSync(join(dir, MARKER), 'utf8'));
  writeFileSync(join(agents, 'pdd-bug/steps/old.md'), 'stale\n');
  writeFileSync(join(agents, 'pdd-bug', MARKER), JSON.stringify({ ...marker(join(agents, 'pdd-bug')), version: '0.0.1' }));
  writeFileSync(join(agents, 'pdd-feature/SKILL.md'), 'edited\n');
  writeFileSync(join(agents, 'pdd-feature', MARKER), JSON.stringify({ ...marker(join(agents, 'pdd-feature')), digest: 'other' }));
  writeFileSync(join(claude, 'pdd-bug/SKILL.md'), 'newer\n');
  writeFileSync(join(claude, 'pdd-bug', MARKER), JSON.stringify({ ...marker(join(claude, 'pdd-bug')), version: '99.0.0' }));
  rmSync(join(claude, 'pdd-feature'), { recursive: true }); mkdirSync(join(claude, 'pdd-feature'));
  writeFileSync(join(claude, 'pdd-feature/SKILL.md'), 'mine\n');
  const own = join(home, 'own-skill'); mkdirSync(own); writeFileSync(join(own, 'SKILL.md'), 'linked\n');
  rmSync(join(claude, 'pdd-small-change'), { recursive: true }); symlinkSync(own, join(claude, 'pdd-small-change'));
  rmSync(join(agents, 'pdd-prompting'), { recursive: true });

  const results = setupSkills(opts);
  assert.deepEqual(results.map(result => [result.agent, result.root, result.found, result.installed.length, result.updated.length]),
    [['Codex', agents, null, 1, 2], ['Claude', claude, claude, 0, 0]]);
  assert.equal(existsSync(join(agents, 'pdd-bug/steps/old.md')), false);
  assert.equal(marker(join(agents, 'pdd-bug')).version, version());
  assert.deepEqual(readFileSync(join(agents, 'pdd-feature/SKILL.md')), readFileSync(join(pkg, 'skills/pdd-feature/SKILL.md')));
  assert.deepEqual(readFileSync(join(agents, 'pdd-prompting/guide.md')), readFileSync(join(pkg, 'docs/prompting-guide.md')));
  assert.equal(readFileSync(join(claude, 'pdd-bug/SKILL.md'), 'utf8'), 'newer\n');
  assert.equal(readFileSync(join(claude, 'pdd-feature/SKILL.md'), 'utf8'), 'mine\n');
  assert.equal(readFileSync(join(claude, 'pdd-small-change/SKILL.md'), 'utf8'), 'linked\n');
});

// Wrong: Claude started with CLAUDE_CONFIG_DIR reads <dir>/skills, so a ~/.claude copy is invisible to it.
test('INSTALL5: with CLAUDE_CONFIG_DIR set, setup installs Claude skills in <dir>/skills', t => {
  const { sandbox, home, run } = packageCopy(t);
  const config = join(sandbox, 'claude config');
  const result = run(['setup'], { CLAUDE_CONFIG_DIR: config });
  assert.equal(result.status, 0, result.stderr);
  assert.ok(result.stdout.includes(`Installed 5 PDD skills to ${join(config, 'skills')}: ${PDD_SKILL_NAMES.join(', ')}\n`), result.stdout);
  assert.deepEqual(readdirSync(join(config, 'skills')).sort(), [...PDD_SKILL_NAMES].sort());
  assert.deepEqual(readdirSync(home), ['.agents']);
});

// Wrong: one broken agent folder stops the other agent's install or the project block.
test('INSTALL6: an install failure is reported, the other agent and the block still happen, and setup exits 1', t => {
  const { home, project, run } = packageCopy(t);
  writeFileSync(join(home, '.agents'), 'not a folder\n');
  const result = run(['setup']);
  assert.equal(result.status, 1);
  assert.match(result.stderr, /pdd setup: the PDD skills could not be installed in .*\.agents\/skills/);
  assert.ok(existsSync(join(home, '.claude/skills/pdd-prompting/SKILL.md')));
  assert.ok(existsSync(join(project, 'AGENTS.md')));
});

// Wrong (0.1.4): setup says how many skills it changed but not which ones.
test('INSTALL7: pdd setup names each skill that it updated', t => {
  const { home, run } = packageCopy(t);
  assert.equal(run(['setup']).status, 0);
  const marker = join(home, '.agents/skills/pdd-bug', MARKER);
  writeFileSync(marker, JSON.stringify({ ...JSON.parse(readFileSync(marker, 'utf8')), version: '0.0.1' }));
  const result = run(['setup']);
  assert.equal(result.status, 0, result.stderr);
  assert.ok(result.stdout.includes(`Updated 1 PDD skill in ${join(home, '.agents/skills')}: pdd-bug\n`), result.stdout);
  assert.ok(result.stdout.includes(`PDD skills found in ${join(home, '.agents/skills')}\n`), result.stdout);
});

// Wrong (0.1.6 tester): setup said "PDD skills found in ~/.agents/skills" for npx skills copies that were older than this
// pdd, so a chat outside a workflow ran the old skills.
test('INSTALL8: when the skills that setup finds are older than this pdd, it says so and prints the update command; it changes nothing', t => {
  const { pkg, home, project, run } = packageCopy(t);
  // An npx skills -g copy of another pdd version (no pdd marker); the Claude folder links to it.
  mkdirSync(join(home, '.claude/skills'), { recursive: true });
  for (const name of PDD_SKILL_NAMES) {
    cpSync(join(pkg, 'skills', name), join(home, '.agents/skills', name), { recursive: true });
    symlinkSync(join(home, '.agents/skills', name), join(home, '.claude/skills', name));
  }
  // A copy from before the version line counts as older.
  writeFileSync(join(home, '.agents/skills/pdd-feature/SKILL.md'), 'an older feature skill\n');
  const result = run(['setup']);
  assert.equal(result.status, 0, result.stderr);
  for (const skillRoot of ROOTS) assert.ok(result.stdout.includes(`PDD skills in ${join(home, skillRoot)} are older than pdd ${version()}. To update them, run: ${UPDATE}\n`), result.stdout);
  assert.doesNotMatch(result.stdout, /found|Installed|Updated/);
  assert.equal(readFileSync(join(home, '.agents/skills/pdd-feature/SKILL.md'), 'utf8'), 'an older feature skill\n');
  assert.equal(existsSync(join(home, '.agents/skills/pdd-feature', MARKER)), false);
  // A project copy with a pdd marker of an older version gets the project command.
  for (const name of PDD_SKILL_NAMES) {
    cpSync(join(pkg, 'skills', name), join(project, '.agents/skills', name), { recursive: true });
    writeFileSync(join(project, '.agents/skills', name, MARKER), JSON.stringify({ package: 'pdd', version: '0.0.1', digest: 'old' }));
  }
  const local = run(['setup']);
  assert.equal(local.status, 0, local.stderr);
  assert.ok(local.stdout.includes(`PDD skills in ${join(project, '.agents/skills')} are older than pdd ${version()}. To update them, run: ${UPDATE.replace(' -g', '')}\n`), local.stdout);
});

// Wrong (0.1.8 tester): the skills had no version line, so no one could tell that the installed skills were older than pdd.
test('INSTALL9: the SKILL.md version line decides older or different, and pdd --version warns on stderr only when older', t => {
  const { pkg, home, run } = packageCopy(t);
  const feature = join(home, '.agents/skills/pdd-feature/SKILL.md');
  const withLine = (text, value) => text.replace(/^(\s*pdd-skills:).*$/m, '$1 ' + value);
  for (const name of PDD_SKILL_NAMES) {
    cpSync(join(pkg, 'skills', name), join(home, '.agents/skills', name), { recursive: true });
    assert.match(readFileSync(join(home, '.agents/skills', name, 'SKILL.md'), 'utf8').split('\n---\n')[0], /^metadata:\n  pdd-skills: \S+$/m, name);
  }
  const source = readFileSync(feature, 'utf8'), stderrOf = () => run(['--version']).stderr.split('\n').filter(text => text.startsWith('PDD skills'));
  // Same version line, other files: setup says they differ; --version stays quiet.
  writeFileSync(feature, `${withLine(source, version())}\nA local edit.\n`);
  assert.ok(run(['setup']).stdout.includes(`PDD skills in ${join(home, '.agents/skills')} differ from the skills of pdd ${version()}.`));
  assert.deepEqual(stderrOf(), []);
  // An older version line: --version prints the update line on stderr and only the version on stdout.
  writeFileSync(feature, withLine(source, '0.1.8'));
  const older = run(['--version']);
  assert.equal(older.status, 0); assert.equal(older.stdout, `${version()}\n`);
  assert.ok(older.stderr.includes(`PDD skills in ${join(home, '.agents/skills')} are older than pdd ${version()}. To update them, run: ${UPDATE}\n`), older.stderr);
  // A newer version line is not older.
  writeFileSync(feature, withLine(source, '99.0.0'));
  assert.deepEqual(stderrOf(), []);
  // The 0.1.8 case: copies that pdd setup made, with an older marker.
  rmSync(join(home, '.agents'), { recursive: true, force: true });
  assert.equal(run(['setup']).status, 0);
  for (const skillRoot of ROOTS) for (const name of PDD_SKILL_NAMES) {
    const marker = join(home, skillRoot, name, MARKER);
    writeFileSync(marker, JSON.stringify({ ...JSON.parse(readFileSync(marker, 'utf8')), version: '0.1.8' }));
  }
  assert.equal(stderrOf().length, 2);
});
