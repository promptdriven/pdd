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

// A copied package with a quoted path, so the absolute pdd command must be shell-safe.
function packageCopy(t) {
  const sandbox = temp(t), pkg = join(sandbox, 'installed "pkg"');
  mkdirSync(pkg);
  for (const name of ['src', 'bin', 'package.json', 'docs', 'skills']) cpSync(join(root, name), join(pkg, name), { recursive: true });
  const home = join(sandbox, 'home'), project = join(sandbox, 'project $(x) "q"'), native = join(sandbox, 'native');
  for (const dir of [home, project, native]) mkdirSync(dir);
  writeFileSync(join(native, 'agent.mjs'), `import fs from 'node:fs';
const home=process.env.HOME;
console.log(JSON.stringify({agent:process.argv[1],argv:process.argv.slice(2),cwd:process.cwd(),agentSession:process.env.PDD_AGENT_SESSION,
  installed:['.agents/skills','.claude/skills'].every(r=>fs.existsSync(home+'/'+r+'/pdd-prompting/SKILL.md'))}));
process.exit(Number(process.env.FIXTURE_EXIT||0));
`);
  for (const agent of ['codex', 'claude']) writeFileSync(join(native, agent), `#!${process.execPath}\nimport(${JSON.stringify(join(native, 'agent.mjs'))});\n`, { mode: 0o755 });
  const env = { ...process.env, HOME: home, PATH: `${native}:${process.env.PATH}` };
  delete env.CLAUDE_CONFIG_DIR;
  const run = (args, extra = {}) => spawnSync(process.execPath, [join(pkg, 'bin/pdd.mjs'), ...args],
    { cwd: project, env: { ...env, ...extra }, encoding: 'utf8', timeout: 10000 });
  return { sandbox, pkg, home, project, env, run };
}

// Wrong: skills are not installed, are copied into the person's repo, or are rewritten on every command.
test('INSTALL1: any pdd command installs the four skills into both home folders once, never into the repo', t => {
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

// Wrong: session pastes the guide or workflows, loses the core rules, or points the agent at a bare pdd.
test('SESSION1: pdd session starts the agent with the short intro after the skills are installed', t => {
  const { pkg, project, env, run } = packageCopy(t);
  const skillText = readFileSync(join(pkg, 'skills/pdd-prompting/SKILL.md'), 'utf8');
  const rules = skillText.split(/^## /m).find(part => part.startsWith('Core rules\n')).split('\n').filter(line => line.startsWith('- '));
  const guide = readFileSync(join(pkg, 'docs/prompting-guide.md'), 'utf8');
  for (const agent of ['codex', 'claude']) {
    for (const request of [[], ['Fix the CSV export; $(touch x) "quoted"']]) {
      const result = run(['session', '--agent', agent, ...request]);
      assert.equal(result.status, 0, result.stderr); assert.equal(result.stderr, '');
      const seen = JSON.parse(result.stdout), message = seen.argv.at(-1), lines = message.split('\n');
      assert.equal(seen.cwd, project); assert.equal(seen.installed, true); assert.equal(seen.agentSession, '1');
      assert.equal(seen.argv.length, agent === 'codex' ? 5 : 2);
      assert.equal(lines[0], `This is a PDD session in ${project}.`);
      assert.equal(lines[1], 'In PDD, prompts are the source. Write the prompt, Story and test cases first, then the code.');
      const start = lines.indexOf('Core rules:');
      assert.deepEqual(lines.slice(start + 1, start + 1 + rules.length), rules);
      assert.ok(lines.includes('Workflows = the skills pdd-small-change, pdd-bug and pdd-feature.'));
      const command = lines.find(line => line.startsWith('Use this pdd: ')).slice('Use this pdd: '.length);
      assert.ok(lines.some(line => line.includes(`${command} workflow run <name> <issue>`)));
      const check = spawnSync('/bin/sh', ['-c', `${command} --version`], { cwd: project, env: { ...env, PATH: '/nonexistent' }, encoding: 'utf8' });
      assert.equal(check.status, 0, check.stderr);
      assert.equal(check.stdout, JSON.parse(readFileSync(join(pkg, 'package.json'), 'utf8')).version + '\n');
      assert.equal(lines.at(-1), request.length ? request[0] : 'Ask what the person wants to work on.');
      assert.ok(Buffer.byteLength(message) <= 2600, `${Buffer.byteLength(message)} bytes`);
      assert.equal(message.includes(guide.slice(0, 200)), false);
      assert.equal(message.includes('Use the pdd-'), false);
    }
  }
  assert.deepEqual(readdirSync(project), []);
});

// Wrong: the intro hides a package runbook, or names a runbook that does not exist.
test('SESSION4: the intro names RUNBOOK.md only when the package has one', t => {
  const { pkg, run } = packageCopy(t);
  const line = `Runtime: read ${join(pkg, 'RUNBOOK.md')} before you run a check.`;
  const without = JSON.parse(run(['session']).stdout).argv.at(-1);
  assert.equal(without.includes('Runtime:'), false);
  writeFileSync(join(pkg, 'RUNBOOK.md'), '# Runbook\n');
  const lines = JSON.parse(run(['session']).stdout).argv.at(-1).split('\n');
  assert.equal(lines.filter(text => text.startsWith('Runtime:')).length, 1);
  assert.equal(lines.at(-2), line);
  assert.deepEqual(lines.filter(text => text !== line), without.split('\n'));
});

// Wrong: the manual workflow shortcut still pastes recipe files instead of naming the skill.
test('SESSION2: pdd workflow NAME uses the same intro and names the pdd-NAME skill', t => {
  const { run } = packageCopy(t);
  const plain = JSON.parse(run(['session', '--', 'Rename the button']).stdout).argv.at(-1);
  for (const name of ['small-change', 'bug', 'feature']) {
    for (const agent of [null, 'claude']) {
      const result = run(['workflow', name, ...(agent ? ['--agent', agent] : []), '--', 'Rename the button']);
      assert.equal(result.status, 0, result.stderr);
      const seen = JSON.parse(result.stdout);
      assert.match(seen.agent, new RegExp(`/${agent ?? 'codex'}$`));
      assert.equal(seen.argv.at(-1), `${plain}\nUse the pdd-${name} skill for this request.`);
    }
  }
});

// Wrong: a broken package starts the agent without the skills it promises.
test('SESSION3: a missing pdd-prompting or selected workflow skill refuses before the agent starts', t => {
  const { pkg, run } = packageCopy(t);
  rmSync(join(pkg, 'skills/pdd-bug/SKILL.md'));
  const bug = run(['workflow', 'bug']);
  assert.equal(bug.status, 1); assert.equal(bug.stdout, ''); assert.ok(bug.stderr.trim());
  const feature = run(['workflow', 'feature']);
  assert.equal(feature.status, 0, feature.stderr);
  rmSync(join(pkg, 'skills/pdd-prompting/SKILL.md'));
  const session = run(['session']);
  assert.equal(session.status, 1); assert.equal(session.stdout, ''); assert.ok(session.stderr.trim());
});
