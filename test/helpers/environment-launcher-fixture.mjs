// Same fake Herdr, GitHub, clock and real alert custody as the runtime-outage tests.
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, readdirSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
export async function launcher(t) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-runtime-outage-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const cwd = join(dir, 'repo'), home = join(dir, 'home');
  mkdirSync(cwd); mkdirSync(home);
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  const f = { dir, cwd, home, time: Date.parse('2026-11-06T12:00:00Z'), prompts: [], issues: [], waits: [], health: { state: 'healthy', detail: 'HTTP 200' }, healthCalls: 0, probe: 'pending', alerts: [], sent: [] };
  f.ports = {
    allocationCheck: async () => ({ state: 'ready', message: '' }),
    stateRoot: join(home, 'state'), now: () => f.time, readRunProgress: async () => [], warn: () => {},
    readRuntimeWaits: async () => structuredClone(f.waits),
    readEnvironmentWaits: async () => structuredClone(f.environmentWaits ?? []),
    environmentHealthy: async input => { (f.healthInputs ??= []).push(input); return f.machineHealthy !== false; },
    runtimeHealth: async () => { f.healthCalls++; return f.health; },
    readRuntimeProbe: async () => f.probe,
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }), pathDiagnostic: () => [],
    run: async (command, args) => {
      if (command === 'git') return { code: 0, stdout: cwd + '\n', stderr: '' };
      if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: '{"nameWithOwner":"owner/repo","url":"https://github.com/owner/repo"}', stderr: '' };
      if (command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
      if (command === 'gh' && args[0] === 'api') return { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n[]', stderr: '' };
      if (command === 'herdr') return { code: 0, stdout: '1.0', stderr: '' };
      throw Error(`unexpected process ${command} ${args}`);
    },
    timer: async () => true,
    queryIssues: async () => ({ status: 200, etag: '"one"', issues: structuredClone(f.issues) }),
    comments: async () => [],
    reconcileDependencyIntake: async () => ({ eligible: f.issues.map(issue => issue.html_url), queued: [], skipped: [] }),
    herdr: async args => {
      if (args[0] === 'status') return { running: true };
      const live = { pane_id: 'p1', workspace_id: 'w1', cwd, foreground_cwd: cwd, tab_id: 't1', terminal_id: 'term1', agent: 'codex', agent_status: 'idle', agent_session: 'session' };
      if (args[0] === 'workspace') return { result: { type: 'workspace_info', workspace: { workspace_id: 'w1' }, root_pane: { pane_id: 'p1' } } };
      if (args[0] === 'pane' && args[1] === 'get') return { result: { type: 'pane_info', pane: live } };
      if (args[0] === 'agent' && args[1] === 'get') { if (!f.agentStarted) throw Object.assign(Error('agent_not_found'), { code: 'agent_not_found' }); return { result: { type: 'agent_info', agent: live } }; }
      if (args[0] === 'pane' && args[1] === 'run') { f.agentStarted = true; return {}; }
      if (args[0] === 'pane' && args[1] === 'read') return '';
      if (args[0] === 'agent' && args[1] === 'prompt') { const match = /Artifact path: (.+)/.exec(args.at(-1)); f.prompts.push(match ? readFileSync(JSON.parse(match[1]), 'utf8') : args.at(-1)); }
      return {};
    },
    // The real alerts module with a saved Discord webhook and a fake HTTP port.
    alertPorts: { http: async ({ body }) => { f.sent.push(body.content); return { status: 200, text: JSON.stringify({ id: String(f.sent.length), content: body.content }) }; } },
  };
  const env = { HOME: home, PATH: process.env.PATH, XDG_CONFIG_HOME: join(home, '.config') };
  f.env = env;
  mkdirSync(join(home, '.config', 'pdd'), { recursive: true });
  writeFileSync(join(home, '.config', 'pdd', 'autopilot-alerts.json'), JSON.stringify({ v: 1, service: 'discord', url: 'https://discord.com/api/webhooks/1/abc' }));
  const module = await import('../../src/autopilot-launcher.mjs');
  f.start = () => module.runAutopilotLauncher({ command: 'start', cwd, env, packageRoot: resolve('.'), issues: [] }, f.ports);
  f.stateFile = () => join(f.ports.stateRoot, readdirSync(f.ports.stateRoot).find(x => x.endsWith('.json')));
  f.tick = () => module.tickAutopilot(f.stateFile(), f.ports);
  f.packet = () => JSON.parse(f.prompts.at(-1).trim().split('\n').at(-1));
  f.rules = () => f.prompts.length ? f.packet().timeRules ?? [] : [];
  return f;
}
