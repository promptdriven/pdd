import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, relative, resolve } from 'node:path';
import { runAutopilotLauncher } from '../src/autopilot-launcher.mjs';
import { codexConfigs } from './helpers/codex-config-args.mjs';

// Replay the draft autopilot-codex-command-context Story vectors on the real launcher (RUNBOOK §17).
// The launcher prompt has no Runtime interface yet, so these are native results only.
// Bindings (fake programs only: no live agent, Herdr session, GitHub call or model call):
// - World paths such as /repo and /home/sam live under a temporary root. Herdr pane values stay literal.
// - saved_state seeds the coordinator identity. Its agent and environment reach the launcher as the
//   selected agent and the start environment, because the launcher refuses a saved agent that has no
//   owner launch binding. The step then checks that the saved state holds the same agent and environment.
// - herdr.pane_run runs the launch text in /bin/sh with the herdr_pane env, as a Herdr pane shell does.
//   Each /launches entry is what the started Codex program reads from its arguments: codex_config holds
//   its -c keys, and command_environment_set its shell_environment_policy.set entries.
// - codex.config_write: each file added, changed or removed under a codex_profile folder.
const scenario = JSON.parse(readFileSync(new URL('./runtime/autopilot-codex-command-context.json', import.meta.url), 'utf8'));
const pointer = (value, path) => path === '' ? value : path.slice(1).split('/').reduce(
  (current, key) => current?.[key.replace(/~1/g, '/').replace(/~0/g, '~')], value);
const compare = { equals: (actual, value) => assert.deepEqual(actual, value) };
// Open decision, not a pass: the launcher does not know the pane shell's Herdr socket path, so it sets
// no Herdr values (prompts/cli/autopilot-launcher.prompt.md, Native Codex startup). Issue 3031.
const open = { AC2: 'AC2 needs Herdr pane and socket values that the launcher does not know; open decision for issue 3031' };

function files(folder) {
  if (!existsSync(folder)) return {};
  return Object.fromEntries(readdirSync(folder, { recursive: true, withFileTypes: true }).filter(entry => entry.isFile())
    .map(entry => { const path = join(entry.parentPath ?? entry.path, entry.name); return [path, readFileSync(path, 'utf8')]; }));
}

async function replayStep(t, step, world, root) {
  assert.equal(step.operation, 'runAutopilotLauncher', `Not replayed: unmapped operation ${step.operation}`);
  const host = path => join(root, path);
  const saved = world.saved_state, bin = join(root, 'fake-bin'), record = join(root, 'codex-calls.jsonl'), stateRoot = join(root, 'state');
  const cwd = host(step.input.cwd);
  for (const folder of [cwd, bin, stateRoot]) mkdirSync(folder, { recursive: true });
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  for (const [path, text] of Object.entries(world.codex_profile)) { mkdirSync(dirname(host(path)), { recursive: true }); writeFileSync(host(path), text); }
  writeFileSync(join(bin, 'codex'), `#!${process.execPath}\nrequire('node:fs').appendFileSync(${JSON.stringify(record)}, JSON.stringify({argv:process.argv.slice(2),env:{PDD_AUTOPILOT_CONTEXT:process.env.PDD_AUTOPILOT_CONTEXT}})+'\\n');\n`, { mode: 0o755 });
  const { coordinatorId, machine, activatedAt, enabled, repo } = saved;
  writeFileSync(join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`), JSON.stringify({ enabled, repo, cwd, coordinatorId, machine, activatedAt }));
  const env = { ...step.input.env, HOME: host(step.input.env.HOME), CODEX_HOME: host(step.input.env.CODEX_HOME), PATH: `${bin}:${step.input.env.PATH}` };
  const profiles = [...new Set(Object.keys(world.codex_profile).map(path => dirname(host(path))))];
  const before = Object.assign({}, ...profiles.map(files));
  const pane = world.herdr_pane;
  let started = false;
  const live = () => ({ pane_id: pane.pane_id, workspace_id: 'w1', cwd, foreground_cwd: cwd, tab_id: 't1', terminal_id: 'term1', agent: 'codex', agent_status: 'idle', agent_session: 'session' });
  const ports = {
    stateRoot, now: () => Date.parse('2026-11-06T00:00:00Z'), readRunProgress: async () => [], warn: () => {},
    selectAgent: async () => ({ ...saved.agent, env: {} }), pathDiagnostic: () => [], timer: async () => true,
    run: async (command, args) => {
      if (command === 'git') return { code: 0, stdout: `${cwd}\n`, stderr: '' };
      if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: JSON.stringify({ nameWithOwner: saved.repo, url: `https://github.com/${saved.repo}` }), stderr: '' };
      if (command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
      if (command === 'gh' && args[0] === 'api') return { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n[]', stderr: '' };
      if (command === 'herdr') return { code: 0, stdout: '1.0', stderr: '' };
      if (command === 'loginctl') return { code: 0, stdout: 'yes\n', stderr: '' };
      throw Error(`unexpected process ${command} ${args}`);
    },
    queryIssues: async () => ({ status: 200, etag: '"one"', issues: [] }),
    comments: async () => [],
    reconcileDependencyIntake: async () => ({ eligible: [], queued: [], skipped: [] }),
    herdr: async args => {
      if (args[0] === 'status') return { running: true };
      if (args[0] === 'workspace') return { result: { type: 'workspace_info', workspace: { workspace_id: 'w1' }, root_pane: { pane_id: pane.pane_id } } };
      if (args[0] === 'pane' && args[1] === 'get') return { result: { type: 'pane_info', pane: live() } };
      if (args[0] === 'agent' && args[1] === 'get') { if (!started) throw Object.assign(Error('agent_not_found'), { code: 'agent_not_found' }); return { result: { type: 'agent_info', agent: live() } }; }
      if (args[0] === 'pane' && args[1] === 'run') {
        started = true;
        const calls = existsSync(record) ? readFileSync(record, 'utf8').trim().split('\n').length : 0;
        execFileSync('/bin/sh', ['-c', args[3]], { cwd, env: { PATH: '/usr/bin:/bin', HOME: env.HOME, ...pane.env }, timeout: 10000 });
        const call = JSON.parse(readFileSync(record, 'utf8').trim().split('\n')[calls]);
        const { set, config } = codexConfigs(call.argv);
        world.launches.push({ pane_id: args[2], argv: call.argv, process_environment: call.env, codex_config: config, command_environment_set: set });
        return {};
      }
      if (args[0] === 'pane' && args[1] === 'read') return '';
      return {};
    },
  };
  const result = await runAutopilotLauncher({ ...structuredClone(step.input), cwd, env, packageRoot: resolve('.') }, ports);
  assert.equal(result.exitCode, 0, result.message);
  const after = Object.assign({}, ...profiles.map(files));
  for (const path of new Set([...Object.keys(before), ...Object.keys(after)])) {
    if (before[path] !== after[path]) world.config_writes.push({ path: `/${relative(root, path)}`, before: before[path] ?? null, after: after[path] ?? null });
  }
  const state = JSON.parse(readFileSync(join(stateRoot, readdirSync(stateRoot).find(name => name.endsWith('.json'))), 'utf8'));
  assert.deepEqual(state.agent, saved.agent, 'binding: the saved agent matches the world');
  for (const [key, value] of Object.entries(saved.environment)) assert.equal(state.environment[key], host(value), `binding: saved ${key} matches the world`);
}

test('replay draft autopilot-codex-command-context Story vectors through runAutopilotLauncher', async t => {
  assert.ok(scenario.steps.length > 0);
  const root = mkdtempSync(join(tmpdir(), 'pdd-3031-vectors-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const world = structuredClone(scenario.initial_world), seen = new Set();
  for (const step of scenario.steps) {
    await t.test(step.step_id, async st => {
      await replayStep(st, step, world, root);
      for (const check of step.checks) {
        assert.equal(check.target, 'world', `Not replayed: unmapped target ${check.target}`);
        assert.ok(compare[check.op], `Not replayed: unmapped comparison ${check.op}`);
        seen.add(check.criterion_id);
        await st.test(`${check.criterion_id} ${check.path} ${check.op} ${JSON.stringify(check.value)}`, { todo: open[check.criterion_id] },
          () => compare[check.op](pointer(world, check.path), check.value));
      }
    });
  }
  assert.deepEqual([...seen].sort(), scenario.criteria.map(criterion => criterion.id).sort());
});
