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
  const agentBin = join(sandbox, 'agent-bin');
  mkdirSync(agentBin);
  writeFileSync(join(agentBin, 'codex'), '#!/bin/sh\necho Logged in\n', { mode: 0o755 });
  const env = { ...process.env, HOME: home, CODEX_HOME: join(home, '.codex'), PATH: `${agentBin}:/usr/bin:/bin` };
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
  for (const word of ['pdd-prompting (the Prompting guide)', '`$pdd-feature` in Codex', '`/pdd-feature` in Claude Code', 'pdd workflow run NAME ISSUE', 'RUNBOOK.md']) assert.ok(text.includes(word), word);
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

// Wrong: setup leaves .pdd/ (the pdd test cache) open to a commit, adds the line twice, or loses the person's ignore rules.
test('SETUP6: in a Git repo, pdd setup adds .pdd/ to the root .gitignore once and keeps other lines', t => {
  const { project, run } = fixture(t);
  spawnSync('git', ['init', '-q', project]);
  const ignore = join(project, '.gitignore');
  const first = run();
  assert.equal(first.status, 0, first.stderr);
  assert.equal(readFileSync(ignore, 'utf8'), '.pdd/\n');
  assert.ok(first.stdout.includes(ignore), first.stdout);
  const second = run();
  assert.equal(second.status, 0, second.stderr);
  assert.equal(readFileSync(ignore, 'utf8'), '.pdd/\n');
  assert.equal(second.stdout.includes(ignore), false, second.stdout);
  writeFileSync(ignore, 'node_modules/\n# keep');
  assert.equal(run().status, 0);
  assert.equal(readFileSync(ignore, 'utf8'), 'node_modules/\n# keep\n.pdd/\n');
  // Git drops trailing spaces and a CR, so these lines already ignore .pdd/.
  for (const line of ['/.pdd/', '.pdd', '.pdd/  ', '/.pdd\r']) {
    writeFileSync(ignore, `dist/\n${line}\n`);
    assert.equal(run().status, 0);
    assert.equal(readFileSync(ignore, 'utf8'), `dist/\n${line}\n`, line);
  }
  // Git keeps leading spaces, so this line does not ignore .pdd/.
  writeFileSync(ignore, '  .pdd/\n');
  assert.equal(run().status, 0);
  assert.equal(readFileSync(ignore, 'utf8'), '  .pdd/\n.pdd/\n');
  // Git itself now ignores the cache folder.
  mkdirSync(join(project, '.pdd/cache/test'), { recursive: true });
  writeFileSync(join(project, '.pdd/cache/test/stories.json'), '{}');
  writeFileSync(ignore, '');
  assert.equal(run().status, 0);
  const status = spawnSync('git', ['status', '--porcelain', '--untracked-files=all'], { cwd: project, encoding: 'utf8' });
  assert.equal(status.stdout.includes('.pdd/'), false, status.stdout);
});

// Wrong (M2): setup rewrites the whole .gitignore, so a byte that is not UTF-8 becomes U+FFFD, or it overrides a "!.pdd/" line.
test('SETUP7: pdd setup only appends to .gitignore, keeps every old byte and line end, and respects a !.pdd/ line', t => {
  const { project, run } = fixture(t);
  spawnSync('git', ['init', '-q', project]);
  const ignore = join(project, '.gitignore');
  const cases = [
    ['# caf\xe9 files\nbuild/\n', '.pdd/\n'],
    ['node_modules/\r\ndist/\r\n', '.pdd/\r\n'],
    ['a\r\n\xff\xfe', '\r\n.pdd/\r\n'],
  ];
  for (const [old, added] of cases) {
    const before = Buffer.from(old, 'latin1');
    writeFileSync(ignore, before);
    const result = run();
    assert.equal(result.status, 0, result.stderr);
    assert.deepEqual(readFileSync(ignore), Buffer.concat([before, Buffer.from(added)]), JSON.stringify(old));
    const check = spawnSync('git', ['check-ignore', '-q', '.pdd/cache/test/stories.json'], { cwd: project });
    assert.equal(check.status, 0, `Git must ignore .pdd/ after ${JSON.stringify(old)}`);
  }
  // A "!" line keeps .pdd/ in Git; the last matching line counts, as in Git.
  for (const [text, negated] of [['.pdd*\n!.pdd/\n', true], ['.pdd/\n!/.pdd\r\n', true], ['!.pdd/\n.pdd/\n', false]]) {
    writeFileSync(ignore, text);
    const result = run();
    assert.equal(result.status, 0, result.stderr);
    assert.equal(readFileSync(ignore, 'utf8'), text);
    const lines = result.stdout.split('\n').filter(line => line.includes(ignore));
    assert.equal(lines.length, negated ? 1 : 0, result.stdout);
    if (negated) assert.equal(lines[0], `${ignore} has a "!" line for .pdd/, so pdd setup did not change the file.`);
  }
});

// Wrong (F6): setup appends .pdd/ after "!.pdd/config.json", so Git now ignores the file that the person keeps in Git.
test('SETUP8: pdd setup keeps a more specific "!" line for a path in .pdd/ and does not append', t => {
  const { project, run } = fixture(t);
  spawnSync('git', ['init', '-q', project]);
  const ignore = join(project, '.gitignore');
  mkdirSync(join(project, '.pdd'), { recursive: true });
  writeFileSync(join(project, '.pdd/config.json'), '{}');
  for (const text of ['.pdd/*\n!.pdd/config.json\n', 'dist/\n!/.pdd/config.json\n', '!**/.pdd/config.json\n']) {
    writeFileSync(ignore, text);
    const result = run();
    assert.equal(result.status, 0, result.stderr);
    assert.equal(readFileSync(ignore, 'utf8'), text, JSON.stringify(text));
    assert.deepEqual(result.stdout.split('\n').filter(line => line.includes(ignore)), [`${ignore} has a "!" line for .pdd/, so pdd setup did not change the file.`]);
    const check = spawnSync('git', ['check-ignore', '-q', '.pdd/config.json'], { cwd: project });
    assert.equal(check.status, 1, `Git must still keep .pdd/config.json after ${JSON.stringify(text)}`);
  }
  // A "!" line for another name that starts with .pdd is not about this folder.
  writeFileSync(ignore, '!.pddrc\n');
  assert.equal(run().status, 0);
  assert.equal(readFileSync(ignore, 'utf8'), '!.pddrc\n.pdd/\n');
});
