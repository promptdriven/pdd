import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, realpathSync, rmSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, relative } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { installSkills, PDD_SKILL_NAMES } from '../src/skills-install.mjs';

const root = fileURLToPath(new URL('..', import.meta.url));
const temp = t => { const p = realpathSync(mkdtempSync(join(tmpdir(), "pdd skills ' "))); t.after(() => rmSync(p, { recursive: true, force: true })); return p; };
const filesUnder = (dir, base = dir) => readdirSync(dir, { withFileTypes: true }).flatMap(entry =>
  entry.isDirectory() ? filesUnder(join(dir, entry.name), base) : [relative(base, join(dir, entry.name))]).sort();
const ROOTS = ['.agents/skills', '.claude/skills'];
const MARKER = '.pdd-skill.json';

// A copied package in a quoted path, so install never depends on the source checkout.
function packageCopy(t) {
  const sandbox = temp(t), pkg = join(sandbox, 'installed "pkg"');
  mkdirSync(pkg);
  for (const name of ['src', 'bin', 'package.json', 'docs', 'skills']) cpSync(join(root, name), join(pkg, name), { recursive: true });
  const home = join(sandbox, 'home'), project = join(sandbox, 'project $(x) "q"');
  for (const dir of [home, project]) mkdirSync(dir);
  const env = { ...process.env, HOME: home };
  delete env.CLAUDE_CONFIG_DIR;
  const run = (args, extra = {}) => spawnSync(process.execPath, [join(pkg, 'bin/pdd.mjs'), ...args],
    { cwd: project, env: { ...env, ...extra }, encoding: 'utf8', timeout: 10000 });
  return { sandbox, pkg, home, project, env, run };
}

// Wrong: skills are not installed, are copied into the person's repo, or are rewritten on every command.
test('INSTALL1: any pdd command installs the PDD skills into both home folders once, never into the repo', t => {
  const { pkg, home, project, run } = packageCopy(t);
  const first = run(['--version']);
  assert.equal(first.status, 0, first.stderr); assert.equal(first.stderr, '');
  assert.deepEqual(readdirSync(project), []);
  const version = JSON.parse(readFileSync(join(pkg, 'package.json'), 'utf8')).version;
  for (const skillRoot of ROOTS) {
    assert.deepEqual(readdirSync(join(home, skillRoot)).sort(), [...PDD_SKILL_NAMES].sort());
    for (const name of PDD_SKILL_NAMES) {
      const installed = join(home, skillRoot, name), source = join(pkg, 'skills', name);
      assert.deepEqual(filesUnder(installed).filter(file => file !== MARKER), filesUnder(source));
      for (const file of filesUnder(source)) assert.deepEqual(readFileSync(join(installed, file)), readFileSync(join(source, file)), file);
      assert.equal(JSON.parse(readFileSync(join(installed, MARKER), 'utf8')).version, version);
    }
  }
  const before = statSync(join(home, ROOTS[0], 'pdd-bug')).ino;
  const second = run(['--help']);
  assert.equal(second.status, 0, second.stderr); assert.equal(second.stderr, '');
  assert.equal(statSync(join(home, ROOTS[0], 'pdd-bug')).ino, before);
});

// Wrong: an upgrade keeps stale files, a newer install is downgraded, or a person's own folder is overwritten.
test('INSTALL2: reinstall only when missing, older or changed; keep newer copies and folders pdd does not own', t => {
  const { pkg, home } = packageCopy(t);
  const version = JSON.parse(readFileSync(join(pkg, 'package.json'), 'utf8')).version;
  installSkills({ packageRoot: pkg, home });
  const [agents, claude] = ROOTS.map(skillRoot => join(home, skillRoot));
  const marker = dir => JSON.parse(readFileSync(join(dir, MARKER), 'utf8'));
  // Older version with a stale step: replaced in full.
  writeFileSync(join(agents, 'pdd-bug/steps/old.md'), 'stale\n');
  writeFileSync(join(agents, 'pdd-bug', MARKER), JSON.stringify({ ...marker(join(agents, 'pdd-bug')), version: '0.0.1' }));
  // Same version, different content (a newer build of the same version): replaced.
  writeFileSync(join(agents, 'pdd-feature/SKILL.md'), 'edited\n');
  writeFileSync(join(agents, 'pdd-feature', MARKER), JSON.stringify({ ...marker(join(agents, 'pdd-feature')), digest: 'other' }));
  // Newer version: kept.
  writeFileSync(join(claude, 'pdd-bug/SKILL.md'), 'newer\n');
  writeFileSync(join(claude, 'pdd-bug', MARKER), JSON.stringify({ ...marker(join(claude, 'pdd-bug')), version: '99.0.0' }));
  // A folder without the pdd marker and a symlink belong to the person: kept.
  rmSync(join(claude, 'pdd-feature'), { recursive: true }); mkdirSync(join(claude, 'pdd-feature'));
  writeFileSync(join(claude, 'pdd-feature/SKILL.md'), 'mine\n');
  const own = join(home, 'own-skill'); mkdirSync(own); writeFileSync(join(own, 'SKILL.md'), 'linked\n');
  rmSync(join(claude, 'pdd-small-change'), { recursive: true }); symlinkSync(own, join(claude, 'pdd-small-change'));
  // Missing: installed.
  rmSync(join(agents, 'pdd-prompting'), { recursive: true });

  installSkills({ packageRoot: pkg, home });
  assert.equal(existsSync(join(agents, 'pdd-bug/steps/old.md')), false);
  assert.equal(marker(join(agents, 'pdd-bug')).version, version);
  assert.deepEqual(readFileSync(join(agents, 'pdd-feature/SKILL.md')), readFileSync(join(pkg, 'skills/pdd-feature/SKILL.md')));
  assert.deepEqual(readFileSync(join(agents, 'pdd-prompting/guide.md')), readFileSync(join(pkg, 'docs/prompting-guide.md')));
  assert.equal(readFileSync(join(claude, 'pdd-bug/SKILL.md'), 'utf8'), 'newer\n');
  assert.equal(readFileSync(join(claude, 'pdd-feature/SKILL.md'), 'utf8'), 'mine\n');
  assert.equal(readFileSync(join(claude, 'pdd-small-change/SKILL.md'), 'utf8'), 'linked\n');
  assert.deepEqual(readdirSync(agents).sort(), [...PDD_SKILL_NAMES].sort());
});

// Wrong: Claude started with CLAUDE_CONFIG_DIR reads <dir>/skills, so it never sees the ~/.claude copy.
test('INSTALL4: CLAUDE_CONFIG_DIR gets its own copy next to ~/.claude/skills and ~/.agents/skills', t => {
  const { sandbox, home, run } = packageCopy(t);
  const config = join(sandbox, 'claude config');
  const result = run(['--version'], { CLAUDE_CONFIG_DIR: config });
  assert.equal(result.status, 0, result.stderr); assert.equal(result.stderr, '');
  for (const skillRoot of [join(config, 'skills'), join(home, '.claude/skills'), join(home, '.agents/skills')])
    assert.deepEqual(readdirSync(skillRoot).sort(), [...PDD_SKILL_NAMES].sort(), skillRoot);
  assert.deepEqual(readdirSync(config), ['skills']);
});

// Wrong: a home folder that cannot take the skills breaks every pdd command.
test('INSTALL3: install failure warns once on stderr and the command still runs', t => {
  const { pkg, home, run } = packageCopy(t);
  writeFileSync(join(home, '.agents'), 'not a folder\n');
  const result = run(['--version']);
  assert.equal(result.status, 0);
  assert.equal(result.stdout, JSON.parse(readFileSync(join(pkg, 'package.json'), 'utf8')).version + '\n');
  assert.equal(result.stderr.trim().split('\n').length, 1);
  assert.match(result.stderr, /skills/);
  assert.ok(existsSync(join(home, '.claude/skills/pdd-prompting/SKILL.md')));
});
