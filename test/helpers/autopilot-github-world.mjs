// An Autopilot world for GitHub call counts: a real Git checkout, the real launcher tick, the real dependency intake
// and `pdd dependencies complete`, a fake Herdr coordinator and the counting fake GitHub of github-repo-fake.mjs.
// `src` selects the source tree, so the same world measures another version of the code.
import { execFileSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, readdirSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { createGithubRepoFake } from './github-repo-fake.mjs';

export async function autopilotGithubWorld({ src = fileURLToPath(new URL('../../src', import.meta.url)), issues = 200, repository = 'acme/widgets', github, sharedGithub, machine, start = Date.parse('2026-11-07T12:00:00Z') } = {}) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-github-world-'));
  const home = join(dir, 'home'), stateRoot = join(home, 'state'), checkout = join(dir, 'repo');
  mkdirSync(checkout); mkdirSync(home);
  const git = (...args) => execFileSync('git', args, { cwd: checkout, encoding: 'utf8' });
  git('init', '-q'); git('remote', 'add', 'origin', `https://github.com/${repository}.git`);
  writeFileSync(join(checkout, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], ...(github ? { github } : {}) } }));
  mkdirSync(join(checkout, 'src')); writeFileSync(join(checkout, 'src', 'widget.mjs'), 'export const widget = 1;\n');
  git('add', '.'); git('-c', 'user.email=test@example.com', '-c', 'user.name=test', 'commit', '-qm', 'init');
  const cwd = realpathSync(checkout), env = { HOME: home, PATH: process.env.PATH };
  const w = { dir, cwd, home, stateRoot, repository, time: start, agent: 'idle', agentStarted: false, prompts: [], requests: [], resume: null, warnings: [] };
  w.github = sharedGithub ?? createGithubRepoFake({ repository, owner: repository.split('/')[0], issues, now: () => w.time });
  const runGit = (args, at) => { try { return { code: 0, stdout: execFileSync('git', args, { cwd: at ?? cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }), stderr: '' }; } catch (error) { return { code: error.status ?? 1, stdout: String(error.stdout ?? ''), stderr: String(error.stderr ?? '') }; } };
  const run = async (command, args, options = {}) => {
    if (command === 'git') return runGit(args, options.cwd);
    if (command === 'gh') return w.github.gh(args, options);
    if (command === 'herdr') return { code: 0, stdout: '1.0', stderr: '' };
    return { code: 1, stdout: '', stderr: `no ${command} in this world` };
  };
  const live = () => ({ pane_id: 'p1', workspace_id: 'w1', cwd, foreground_cwd: cwd, tab_id: 't1', terminal_id: 'term1', agent: 'codex', agent_status: w.agent, agent_session: 'session' });
  const herdr = async args => {
    if (args[0] === 'status') return { running: true };
    if (args[0] === 'workspace') return { result: { type: 'workspace_info', workspace: { workspace_id: 'w1' }, root_pane: { pane_id: 'p1' } } };
    if (args[0] === 'pane' && args[1] === 'get') return { result: { type: 'pane_info', pane: live() } };
    if (args[0] === 'agent' && args[1] === 'get') { if (!w.agentStarted) throw Object.assign(Error('agent_not_found'), { code: 'agent_not_found' }); return { result: { type: 'agent_info', agent: live() } }; }
    if (args[0] === 'pane' && args[1] === 'run') { w.agentStarted = true; return {}; }
    if (args[0] === 'pane' && args[1] === 'read') return '';
    if (args[0] === 'agent' && args[1] === 'prompt') {
      const text = args.at(-1), path = /Artifact path: (.+)/.exec(text)?.[1];
      w.prompts.push(text);
      if (path && text.includes('Dependency analysis request artifact')) w.requests.push(JSON.parse(readFileSync(JSON.parse(path), 'utf8')));
      return {};
    }
    return {};
  };
  w.ports = { stateRoot, machine, now: () => w.time, sleep: async () => {}, readRunProgress: async () => [], warn: text => w.warnings.push(text),
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }), pathDiagnostic: () => [], timer: async () => true,
    run, herdr, wait: async () => {}, armCoordinatorIdle: (_identity, options) => { w.resume = options.resume; } };
  const launcher = await import(pathToFileURL(join(src, 'autopilot-launcher.mjs')).href);
  const intake = await import(pathToFileURL(join(src, 'issue-dependencies-intake.mjs')).href);
  const calls = await import(pathToFileURL(join(src, 'github-calls.mjs')).href);
  // A pdd command's runner, as the CLI has it: gh calls count into the Autopilot ledger of the repository.
  const commandExec = async (file, args, options = {}) => {
    if (file === 'git') { const r = runGit(args, options.cwd); if (r.code !== 0) throw Object.assign(Error('git failed'), r); return r; }
    if (file === 'gh') return w.github.gh(args, options);
    throw Error(`no ${file} in this world`);
  };
  w.commandPorts = (extra = {}) => ({ execFile: calls.nativeGithubCounter(commandExec, { stateRoot, now: () => w.time }), autopilotStateRoot: stateRoot, now: () => w.time, env, ...extra });
  w.invoke = command => launcher.runAutopilotLauncher({ command, cwd, env, packageRoot: resolve(src, '..'), issues: [] }, w.ports);
  w.stateFile = () => join(stateRoot, readdirSync(stateRoot).find(name => /^[0-9a-f]{20}\.json$/.test(name)));
  w.state = () => JSON.parse(readFileSync(w.stateFile(), 'utf8'));
  w.tick = () => launcher.tickAutopilot(w.stateFile(), w.ports);
  // The coordinator runs `pdd dependencies complete`; the CLI then asks the launcher for its completion tick.
  w.complete = async (request, analysis = analysisFor(request), ports = w.commandPorts()) => {
    w.agent = 'working';
    const reply = await intake.runDependencyIntake({ command: 'complete', cwd, stdin: JSON.stringify({ request, analysis }) }, ports);
    const wake = await launcher.requestAutopilotCompletion({ cwd, env }, w.ports);
    return { exitCode: reply.exitCode, result: reply.exitCode === 0 ? JSON.parse(reply.message) : reply.message.trim(), wake };
  };
  // The coordinator's turn ends: the armed idle wait runs its tick.
  w.idle = async () => { w.agent = 'idle'; const resume = w.resume; w.resume = null; if (resume) await resume(); };
  w.cleanup = () => rmSync(dir, { recursive: true, force: true });
  return w;
}

// The coordinator's answer: each subject needs no other issue first. It copies the base heads, candidates and
// required rows of the request exactly, as the dependency step says.
export function analysisFor(request) {
  const snapshot = JSON.parse(request.snapshotJson), context = JSON.parse(request.contextJson), repo = request.repository.toLowerCase();
  const rows = new Map([...snapshot.issues.map(x => [x.key, x.revision]), ...snapshot.inputs.map(x => [x.key, x.revision])]);
  const candidates = snapshot.issues.filter(x => x.key.startsWith(`https://github.com/${repo}/issues/`)).map(x => ({ key: x.key, revision: x.revision }));
  const reviews = request.issues.map(issue => {
    const inputs = new Map([[issue, rows.get(issue)]]);
    for (const x of context.source) if (x.issues.includes(issue)) inputs.set(x.key, x.revision);
    for (const x of context.requirements) if (x.issue === issue && x.authority === 'trusted') inputs.set(x.key, x.revision);
    const base = snapshot.reviews.filter(r => r.issue === issue && r.authority === 'trusted' && r.intact && !snapshot.reviews.some(o => o.base.includes(r.id))).map(r => r.id);
    return { analysis: `Checked ${issue}: it needs no other open issue first.`, base, continuation: '', issue, inputs: [...inputs].map(([key, revision]) => ({ key, revision })),
      candidates, outcome: 'complete', dependencies: [], questions: [], effects: 'none' };
  });
  return { reviews, impactJson: '' };
}
