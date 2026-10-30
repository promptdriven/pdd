import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, realpathSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const root = fileURLToPath(new URL('..', import.meta.url));
const START = '<!-- pdd:start -->', END = '<!-- pdd:end -->';

function fixture(t) {
  const sandbox = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-setup-')));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));
  const pkg = join(sandbox, 'pkg'), home = join(sandbox, 'home'), project = join(sandbox, 'project');
  for (const dir of [pkg, home, project]) mkdirSync(dir);
  for (const name of ['src', 'bin', 'package.json', 'skills', 'RUNBOOK.md']) cpSync(join(root, name), join(pkg, name), { recursive: true });
  const env = { ...process.env, HOME: home, CODEX_HOME: join(home, '.codex') };
  delete env.CLAUDE_CONFIG_DIR;
  const run = (...args) => spawnSync(process.execPath, [join(pkg, 'bin/pdd.mjs'), 'setup', ...args], { cwd: project, env, encoding: 'utf8', timeout: 10000 });
  return { pkg, project, run };
}
// The block as the pdd-setup skill states it, so the skill and the command cannot drift apart.
function skillBlock(pkg, runbook) {
  const lines = readFileSync(join(pkg, 'skills/pdd-setup/SKILL.md'), 'utf8').split('\n');
  const block = lines.slice(lines.indexOf(START), lines.indexOf(END) + 1);
  return block.filter(line => runbook || !line.includes('RUNBOOK.md')).join('\n');
}

// Wrong: setup pastes the guide, writes a long section, or edits a file the agent does not read first.
test('SETUP1: pdd setup creates AGENTS.md with the one short block when no agent file exists, and a second run changes nothing', t => {
  const { pkg, project, run } = fixture(t);
  const first = run();
  assert.equal(first.status, 0, first.stderr);
  assert.match(first.stdout, /AGENTS\.md/);
  const text = readFileSync(join(project, 'AGENTS.md'), 'utf8');
  assert.equal(text, `${skillBlock(pkg, true)}\n`);
  const lines = text.trimEnd().split('\n');
  assert.ok(lines.length <= 10, `${lines.length} lines`);
  for (const word of ['pdd-prompting (the Prompting guide)', '`$pdd-feature` in Codex', '`/pdd-feature` in Claude Code', 'pdd workflow start NAME ISSUE', 'RUNBOOK.md']) assert.ok(text.includes(word), word);
  assert.equal(text.includes('Give the reader a useful first path'), false);
  const before = statSync(join(project, 'AGENTS.md')).mtimeMs;
  const second = run();
  assert.equal(second.status, 0, second.stderr);
  assert.match(second.stdout, /no change/i);
  assert.equal(readFileSync(join(project, 'AGENTS.md'), 'utf8'), text);
  assert.equal(statSync(join(project, 'AGENTS.md')).mtimeMs, before);
  assert.deepEqual(readdirSync(project), ['AGENTS.md']);
});

// Wrong: setup writes AGENTS.md although the project uses CLAUDE.md, or loses the person's own text.
test('SETUP2: CLAUDE.md wins over AGENTS.md; an old block is replaced in place and other text stays', t => {
  const { pkg, project, run } = fixture(t);
  writeFileSync(join(project, 'AGENTS.md'), '# Agents\n');
  writeFileSync(join(project, 'CLAUDE.md'), `# Team rules\n\nUse tabs.\n\n${START}\nold PDD text\n${END}\n\n## More\nKeep me.\n`);
  const result = run();
  assert.equal(result.status, 0, result.stderr);
  assert.match(result.stdout, /CLAUDE\.md/);
  assert.equal(readFileSync(join(project, 'AGENTS.md'), 'utf8'), '# Agents\n');
  assert.equal(readFileSync(join(project, 'CLAUDE.md'), 'utf8'), `# Team rules\n\nUse tabs.\n\n${skillBlock(pkg, true)}\n\n## More\nKeep me.\n`);
  writeFileSync(join(project, 'AGENTS.md'), '# Agents\nNo trailing newline');
  rmSync(join(project, 'CLAUDE.md'));
  assert.equal(run().status, 0);
  assert.equal(readFileSync(join(project, 'AGENTS.md'), 'utf8'), `# Agents\nNo trailing newline\n\n${skillBlock(pkg, true)}\n`);
});

// Wrong: the block points at a runbook that pdd does not ship.
test('SETUP3: the RUNBOOK.md line appears only when pdd ships a runbook', t => {
  const { pkg, project, run } = fixture(t);
  rmSync(join(pkg, 'RUNBOOK.md')); rmSync(join(pkg, 'skills/pdd-prompting/RUNBOOK.md'), { force: true });
  assert.equal(run().status, 0);
  const text = readFileSync(join(project, 'AGENTS.md'), 'utf8');
  assert.equal(text, `${skillBlock(pkg, false)}\n`);
  assert.equal(text.includes('RUNBOOK'), false);
});

// Wrong: a broken marker pair makes setup append a second block or cut the person's text.
test('SETUP4: an unmatched marker or extra words refuse without writing', t => {
  const { project, run } = fixture(t);
  const broken = `# Rules\n${START}\nno end marker\n`;
  writeFileSync(join(project, 'AGENTS.md'), broken);
  const refused = run();
  assert.equal(refused.status, 1); assert.doesNotMatch(refused.stdout, /PDD block/); assert.match(refused.stderr, /pdd:start|pdd:end/);
  assert.equal(readFileSync(join(project, 'AGENTS.md'), 'utf8'), broken);
  const extra = run('now');
  assert.equal(extra.status, 2);
  assert.equal(existsSync(join(project, 'CLAUDE.md')), false);
});

// Wrong (0.1.4): help says /pdd-… only; Codex calls a skill with $pdd-….
test('SETUP5: pdd help says how to call a PDD skill in Codex and in Claude Code', () => {
  // --help writes nothing to HOME, so the real environment is safe here.
  const help = spawnSync(process.execPath, [join(root, 'bin/pdd.mjs'), '--help'], { encoding: 'utf8' });
  assert.equal(help.status, 0, help.stderr);
  assert.ok(help.stdout.includes('Open Codex or Claude as usual and call a PDD skill: $pdd-feature in Codex, /pdd-feature in Claude Code (also pdd-bug, pdd-small-change, pdd-prompting).'), help.stdout);
});
