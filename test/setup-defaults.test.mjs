import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, existsSync, symlinkSync, rmSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { runAutopilot } from '../src/autopilot.mjs';

function fixture(t, { stdinTTY = false, stdoutTTY = false } = {}) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-setup-defaults-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const home = join(root, 'home'), cwd = join(root, 'repo');
  mkdirSync(home); mkdirSync(cwd); mkdirSync(join(home, '.codex'));
  execFileSync('git', ['init', '-q', cwd]);
  let out = '', err = '', lookup = 0;
  const options = {
    cwd, env: { HOME: home, PATH: '' }, stdin: { isTTY: stdinTTY },
    stdout: { isTTY: stdoutTTY, write: s => { out += s; } }, stderr: { write: s => { err += s; } },
    pathDiagnostic: () => [], workflowAgents: { checkWorkflowAgents: async () => ({ ok: true, agent: 'codex' }) },
    setupSkills: () => [], gitContext: async () => ({ toplevel: cwd }),
    autopilot: { runAutopilot }, autopilotPorts: {
      config: { read: async () => ({ raw: null }), save: async () => assert.fail('safe defaults must not save Autopilot') },
      github: { lookup: async () => { lookup++; return { owner: '', writers: [], complete: false }; } },
      terminal: { mode: async () => assert.fail('mode question'), names: async () => assert.fail('trust question') },
    },
    confirm: async () => assert.fail('safe defaults must not confirm optional writes'),
  };
  return { home, cwd, options, output: () => out, errors: () => err, lookups: () => lookup };
}

test('3207: setup --yes parses as a flag and rejects operands, values and duplicates', () => {
  assert.deepEqual(parseArgv(['setup', '--yes']).options, { '--yes': true });
  for (const args of [['setup', '--yes', '--yes'], ['setup', '--yes=true'], ['setup', 'extra']])
    assert.throws(() => parseArgv(args));
});

for (const [name, stdinTTY, stdoutTTY, yes] of [
  ['pipes', false, false, false], ['stdin pipe', false, true, false],
  ['stdout pipe', true, false, false], ['--yes in terminal', true, true, true],
]) test(`3207: ${name} takes defaults without questions or optional writes`, async t => {
  const f = fixture(t, { stdinTTY, stdoutTTY });
  const prompt = '# A module without a Runtime interface\n';
  mkdirSync(join(f.cwd, 'prompts')); writeFileSync(join(f.cwd, 'prompts/example.prompt.md'), prompt);
  execFileSync('git', ['add', 'prompts'], { cwd: f.cwd });
  const settings = '{"other":{"keep":true}}\n'; writeFileSync(join(f.cwd, 'pdd.json'), settings);
  const code = await runPdd(['setup', ...(yes ? ['--yes'] : [])], f.options);
  assert.equal(code, 0, f.errors());
  assert.equal(f.lookups(), 0);
  assert.ok(existsSync(join(f.cwd, 'AGENTS.md')));
  assert.equal(readFileSync(join(f.cwd, '.gitignore'), 'utf8'), '.pdd/\n');
  assert.equal(readFileSync(join(f.cwd, 'pdd.json'), 'utf8'), settings);
  assert.equal(readFileSync(join(f.cwd, 'prompts/example.prompt.md'), 'utf8'), prompt);
  assert.equal(existsSync(join(f.home, '.codex/config.toml')), false);
  assert.doesNotMatch(f.output(), /\[y\/N\]|Add anyone else|Autopilot for this repo/);
});

test('3207: symlinked optional MCP config warns with exit 0 and preserves target', async t => {
  const f = fixture(t), target = join(f.home, 'target.toml'), bytes = 'model = "keep"\n';
  writeFileSync(target, bytes); symlinkSync(target, join(f.home, '.codex/config.toml'));
  assert.equal(await runPdd(['setup'], f.options), 0, f.errors());
  assert.match(f.errors(), /warning:.*symlink.*register PDD manually/);
  assert.equal(readFileSync(target, 'utf8'), bytes);
  assert.ok(existsSync(join(f.cwd, 'AGENTS.md')));
});

test('3207: terminal setup still asks and incomplete owner lookup is a warning, exit 0', async t => {
  const f = fixture(t, { stdinTTY: true, stdoutTTY: true }); let mode = 0, names = 0, saves = 0;
  f.options.confirm = async () => 'n';
  f.options.autopilotPorts.terminal = {
    mode: async () => { mode++; return { answer: '' }; },
    names: async info => { names++; assert.equal(info.complete, false); return { names: [] }; },
  };
  f.options.autopilotPorts.config.save = async args => { saves++; assert.deepEqual(JSON.parse(args.raw), { mode: 'off', trust: [] }); return args; };
  assert.equal(await runPdd(['setup'], f.options), 0, f.errors());
  assert.deepEqual([mode, names, saves, f.lookups()], [1, 1, 1, 1]);
  assert.match(f.output(), /trusted list may be incomplete/i);
});

test('3207: safe defaults do not hide required project write failures or malformed configs', async t => {
  const f = fixture(t);
  f.options.setupProject = () => { throw Error('cannot write project block'); };
  assert.equal(await runPdd(['setup'], f.options), 1);
  assert.match(f.errors(), /cannot write project block/);
  delete f.options.setupProject;
  writeFileSync(join(f.home, '.codex/config.toml'), '[broken');
  assert.equal(await runPdd(['setup'], f.options), 1);
  assert.match(f.errors(), /malformed TOML/);
});
