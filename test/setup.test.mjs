import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, realpathSync, rmSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { PDD_BLOCK } from '../src/project-setup.mjs';

const root = fileURLToPath(new URL('..', import.meta.url));
const START = '<!-- pdd:start -->', END = '<!-- pdd:end -->';

function fixture(t) {
  const sandbox = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-setup-')));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));
  const pkg = join(sandbox, 'pkg'), home = join(sandbox, 'home'), project = join(sandbox, 'project');
  for (const dir of [pkg, home, project]) mkdirSync(dir);
  for (const name of ['src', 'bin', 'package.json', 'skills']) cpSync(join(root, name), join(pkg, name), { recursive: true });
  symlinkSync(join(root, 'node_modules'), join(pkg, 'node_modules'), 'dir');
  const env = { ...process.env, HOME: home, CODEX_HOME: join(home, '.codex'), PATH: '/usr/bin:/bin' };
  delete env.CLAUDE_CONFIG_DIR;
  const run = (...args) => spawnSync(process.execPath, [join(pkg, 'bin/pdd.mjs'), ...args], { cwd: project, env, encoding: 'utf8', timeout: 10000 });
  return { sandbox, pkg, home, project, run };
}

test('SETUP1: pdd init creates AGENTS.md with the 4-line PDD block, detects stack/test command, and a second run changes nothing', t => {
  const { project, run } = fixture(t);
  writeFileSync(join(project, 'package.json'), JSON.stringify({ name: 'demo', scripts: { test: 'node --test' } }));
  const first = run('init');
  assert.equal(first.status, 0, first.stderr);
  assert.match(first.stdout, /AGENTS\.md/);
  assert.match(first.stdout, /javascript .*npm test/);
  const text = readFileSync(join(project, 'AGENTS.md'), 'utf8');
  assert.equal(text, `${PDD_BLOCK}\n`);
  const lines = text.trimEnd().split('\n');
  assert.ok(lines.length <= 6, `${lines.length} lines`);
  assert.equal(text.includes('pdd workflow run'), false);
  assert.equal(text.includes('RUNBOOK.md'), false);
  assert.equal(existsSync(join(project, '.gitignore')), false, 'pdd init never edits root .gitignore');

  const before = statSync(join(project, 'AGENTS.md')).mtimeMs;
  const second = run('init');
  assert.equal(second.status, 0, second.stderr);
  assert.match(second.stdout, /no change/i);
  assert.equal(readFileSync(join(project, 'AGENTS.md'), 'utf8'), text);
  assert.equal(statSync(join(project, 'AGENTS.md')).mtimeMs, before);
});

test('SETUP2: pdd init prefers CLAUDE.md over AGENTS.md, replaces an old block in place, preserves CRLF, and keeps user text', t => {
  const { project, run } = fixture(t);
  writeFileSync(join(project, 'AGENTS.md'), '# Agents\n');
  writeFileSync(join(project, 'CLAUDE.md'), `# Team rules\r\n\r\nUse tabs.\r\n\r\n${START}\r\nold PDD text\r\n${END}\r\n\r\n## More\r\nKeep me.\r\n`);
  const result = run('init');
  assert.equal(result.status, 0, result.stderr);
  assert.match(result.stdout, /CLAUDE\.md/);
  assert.equal(readFileSync(join(project, 'AGENTS.md'), 'utf8'), '# Agents\n');
  const crlfBlock = PDD_BLOCK.replaceAll('\n', '\r\n');
  assert.equal(readFileSync(join(project, 'CLAUDE.md'), 'utf8'), `# Team rules\r\n\r\nUse tabs.\r\n\r\n${crlfBlock}\r\n\r\n## More\r\nKeep me.\r\n`);
  // Second CRLF run must be a no-op (never duplicate block).
  const again = run('init');
  assert.equal(again.status, 0, again.stderr);
  assert.match(again.stdout, /no change/i);

  // Appending to a file with no trailing newline preserves content cleanly.
  writeFileSync(join(project, 'AGENTS.md'), '# Agents\nNo trailing newline');
  rmSync(join(project, 'CLAUDE.md'));
  assert.equal(run('init').status, 0);
  assert.equal(readFileSync(join(project, 'AGENTS.md'), 'utf8'), `# Agents\nNo trailing newline\n\n${PDD_BLOCK}\n`);
});

test('SETUP3: pdd init refuses unmatched markers, symlinks, and extra arguments without writing', t => {
  const { sandbox, project, run } = fixture(t);
  const broken = `# Rules\n${START}\nno end marker\n`;
  writeFileSync(join(project, 'AGENTS.md'), broken);
  const refused = run('init');
  assert.equal(refused.status, 1);
  assert.doesNotMatch(refused.stdout, /PDD block/);
  assert.match(refused.stderr, /pdd:start|pdd:end/);
  assert.equal(readFileSync(join(project, 'AGENTS.md'), 'utf8'), broken);

  // Symlinked CLAUDE.md is refused without touching target.
  const target = join(sandbox, 'real-claude.md');
  writeFileSync(target, '# Original\n');
  symlinkSync(target, join(project, 'CLAUDE.md'));
  const sym = run('init');
  assert.equal(sym.status, 1);
  assert.match(sym.stderr, /symbolic link/i);
  assert.equal(readFileSync(target, 'utf8'), '# Original\n');

  // Extra args rejected by parser with exit 2.
  assert.equal(run('init', 'extra').status, 2);
  assert.equal(run('setup', 'now').status, 2);
});

test('SETUP4: pdd help says how to call the single /pdd skill in Codex and in Claude Code', () => {
  const help = spawnSync(process.execPath, [join(root, 'bin/pdd.mjs'), '--help'], { encoding: 'utf8' });
  assert.equal(help.status, 0, help.stderr);
  assert.ok(
    help.stdout.includes('Open Codex or Claude as usual and invoke the PDD skill: $pdd in Codex,\n/pdd in Claude Code (covers product, bug, feature, and small-change).'),
    help.stdout,
  );
});

test('SETUP5: pdd setup --yes is laptop-only, never false-detects Antigravity on a clean machine, and installs Antigravity when present', t => {
  const { sandbox, home, project, run } = fixture(t);
  spawnSync('git', ['init', '-q', project]);
  const res = run('setup', '--yes');
  assert.equal(res.status, 0, res.stderr);
  assert.ok(existsSync(join(home, '.agents/skills/pdd/SKILL.md')));
  assert.ok(existsSync(join(home, '.claude/skills/pdd/SKILL.md')));
  assert.equal(existsSync(join(home, '.gemini/config/skills')), false, 'clean laptop without Antigravity must not create ~/.gemini/config/skills');
  assert.equal(existsSync(join(home, '.gemini/config/mcp_config.json')), false, 'clean laptop without Antigravity must not create ~/.gemini/config/mcp_config.json');
  assert.deepEqual(readdirSync(project).filter(f => f !== '.git'), [], 'pdd setup never edits repository files');
  assert.equal(existsSync(join(project, 'AGENTS.md')), false);
  assert.equal(existsSync(join(project, '.gitignore')), false);
  assert.equal(existsSync(join(project, 'pdd.json')), false);

  // When Antigravity is present (~/.gemini/antigravity-cli), pdd setup --yes installs both skills and MCP config.
  mkdirSync(join(home, '.gemini/antigravity-cli'), { recursive: true });
  const agyRes = run('setup', '--yes');
  assert.equal(agyRes.status, 0, agyRes.stderr);
  assert.ok(existsSync(join(home, '.gemini/config/skills/pdd/SKILL.md')));
  assert.ok(existsSync(join(home, '.gemini/config/mcp_config.json')));

  // --skills-dir targets an explicit folder cleanly.
  const customDir = join(sandbox, 'my-skills');
  const custom = run('setup', '--skills-dir', customDir);
  assert.equal(custom.status, 0, custom.stderr);
  assert.ok(existsSync(join(customDir, 'pdd/SKILL.md')));
});
