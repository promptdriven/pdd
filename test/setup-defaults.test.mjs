import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, existsSync, symlinkSync, rmSync, realpathSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { parseArgv } from '../src/argument-parser.mjs';

function fixture(t, { stdinTTY = false, stdoutTTY = false } = {}) {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-setup-defaults-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const home = join(root, 'home'), cwd = join(root, 'repo');
  mkdirSync(home); mkdirSync(cwd); mkdirSync(join(home, '.codex'));
  execFileSync('git', ['init', '-q', cwd]);
  let out = '', err = '';
  const options = {
    cwd,
    env: { HOME: home, PATH: '' },
    stdin: { isTTY: stdinTTY },
    stdout: { isTTY: stdoutTTY, write: s => { out += s; } },
    stderr: { write: s => { err += s; } },
    pathDiagnostic: () => [],
    workflowAgents: { checkWorkflowAgents: async () => assert.fail('laptop setup must not probe coding-agent logins') },
    setupSkills: () => [],
    autopilot: { runAutopilot: async () => assert.fail('laptop setup must not invoke Autopilot') },
  };
  return { home, cwd, options, output: () => out, errors: () => err };
}

test('3207/S1: setup --yes and --skills-dir parse cleanly and reject invalid options or extra operands', () => {
  assert.deepEqual(parseArgv(['setup', '--yes']).options, { '--yes': true });
  assert.deepEqual(parseArgv(['setup', '--skills-dir', '/tmp/s']).options, { '--skills-dir': '/tmp/s' });
  for (const args of [['setup', '--yes', '--yes'], ['setup', '--yes=true'], ['setup', '--skills-dir'], ['setup', 'extra']]) {
    assert.throws(() => parseArgv(args));
  }
});

for (const [name, stdinTTY, stdoutTTY] of [
  ['pipes', false, false],
  ['stdin pipe', false, true],
  ['stdout pipe', true, false],
]) test(`S1: non-interactive ${name} without --yes skips MCP registration and never touches repo files`, async t => {
  const f = fixture(t, { stdinTTY, stdoutTTY });
  const settings = '{"other":{"keep":true}}\n';
  writeFileSync(join(f.cwd, 'pdd.json'), settings);
  const code = await runPdd(['setup'], f.options);
  assert.equal(code, 0, f.errors());
  assert.equal(existsSync(join(f.cwd, 'AGENTS.md')), false, 'setup never writes AGENTS.md');
  assert.equal(existsSync(join(f.cwd, '.gitignore')), false, 'setup never writes .gitignore');
  assert.equal(readFileSync(join(f.cwd, 'pdd.json'), 'utf8'), settings);
  assert.equal(existsSync(join(f.home, '.codex/config.toml')), false);
  assert.doesNotMatch(f.output(), /\[y\/N\]|Add anyone else|Autopilot for this repo/);
});

test('S1: setup --yes applies previewed PDD Simulator MCP registration without prompting or touching repo files', async t => {
  const f = fixture(t, { stdinTTY: false, stdoutTTY: false });
  const code = await runPdd(['setup', '--yes'], f.options);
  assert.equal(code, 0, f.errors());
  assert.equal(existsSync(join(f.home, '.codex/config.toml')), true);
  assert.match(readFileSync(join(f.home, '.codex/config.toml'), 'utf8'), /\[mcp_servers\.pdd\]/);
  assert.equal(existsSync(join(f.cwd, 'AGENTS.md')), false);
  assert.equal(existsSync(join(f.cwd, '.gitignore')), false);
  assert.doesNotMatch(f.output(), /\[y\/N\]|Autopilot/);
});

test('3207/S1: symlinked MCP config warns with exit 0 and preserves target', async t => {
  const f = fixture(t), target = join(f.home, 'target.toml'), bytes = 'model = "keep"\n';
  writeFileSync(target, bytes);
  symlinkSync(target, join(f.home, '.codex/config.toml'));
  assert.equal(await runPdd(['setup', '--yes'], f.options), 0, f.errors());
  assert.match(f.errors(), /warning:.*symlink.*register PDD manually/);
  assert.equal(readFileSync(target, 'utf8'), bytes);
});

test('3207/S1: malformed MCP config fails setup with exit 1 while keeping error clear', async t => {
  const f = fixture(t);
  writeFileSync(join(f.home, '.codex/config.toml'), '[broken');
  assert.equal(await runPdd(['setup', '--yes'], f.options), 1);
  assert.match(f.errors(), /malformed TOML/);
});
