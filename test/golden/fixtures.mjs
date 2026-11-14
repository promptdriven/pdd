import { cpSync, mkdirSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { join } from 'node:path';

export const repository = 'acme/widgets';
const issueUrl = number => `https://github.com/${repository}/issues/${number}`;

function writeTree(base, files) {
  for (const [path, text] of Object.entries(files)) {
    mkdirSync(join(base, path, '..'), { recursive: true });
    writeFileSync(join(base, path), text);
  }
}

export function project(context, { files = { 'value.mjs': 'export const value = 1;\n' }, publish = true } = {}) {
  const { repo, root, git } = context;
  git(repo, 'init', '-q', '-b', 'main');
  git(repo, 'remote', 'add', 'origin', `https://github.com/${repository}.git`);
  writeTree(repo, files);
  git(repo, 'add', '-A');
  git(repo, 'commit', '-qm', 'Base');
  if (!publish) return;
  const remote = join(root, 'remotes', `${repository}.git`);
  mkdirSync(remote, { recursive: true });
  git(remote, 'init', '--bare', '-q', '-b', 'main');
  git(repo, 'push', '-q', remote, 'main');
  git(repo, 'update-ref', 'refs/remotes/origin/main', 'HEAD');
}

export function harborProject(context, edit) {
  cpSync(join(context.harnessRoot, 'test/fixtures/harbor'), context.repo, { recursive: true });
  edit?.(context.repo);
  project(context, { files: {}, publish: false });
}

export const draftPrompt = text => text.replace('"status": "approved"', '"status": "draft"').replace(/("prose_sha256": )"[a-f0-9]{64}"/, '$1""');

export function ownerProject(context) {
  project(context, { publish: false, files: {
    'prompts/widget.prompt.md': '# Widget\n\nOwn `src/claimed.mjs` and build the widget.\n',
    'pdd-bindings.json': JSON.stringify({ schema_version: 'pdd.bindings.v1', modules: [{ module: 'src/bound.mjs', stories: ['user_stories/widget.md'], prompt: 'prompts/widget.prompt.md' }] }, null, 2) + '\n',
    'user_stories/widget.md': '# Widget\n\nI can use the widget.\n',
    'src/bound.mjs': 'export const bound = true;\n',
    'src/headed.mjs': `// Generated from prompts/widget.prompt.md (sha256: ${'a'.repeat(64)}).\nexport const headed = true;\n`,
    'src/claimed.mjs': 'export const claimed = true;\n',
    'src/loose.mjs': 'export const loose = true;\n',
  } });
}

const smallChangeAreas = [
  { name: 'plan', steps: ['scope'], optional: [], gate: 'approve' },
  { name: 'build', steps: ['change', 'verify', 'formal'], optional: [], gate: 'pr' },
];
const sessionId = '00000000-0000-4000-8000-000000000017';

const phases = {
  working: () => ({ state: 'running', chatState: 'running', agentStatus: 'working' }),
  gate: at => ({ state: 'waiting', chatState: 'running', agentStatus: 'idle', done: { scope: { at, summary: 'Scoped the change.' } }, gate: { area: 'plan', kind: 'approve', at } }),
  completed: at => ({ state: 'completed', chatState: 'ended', agentStatus: 'idle', extra: { doneAt: at } }),
};

export function startedRun(context, { number = 17, phase = 'working' } = {}) {
  const at = context.now - 3 * 3600 * 1000;
  const { state, chatState, agentStatus, done = {}, gate = null, extra = {} } = phases[phase](at + 3600 * 1000);
  project(context);
  const { repo, root, git } = context;
  const worktree = join(root, 'project.pdd-worktrees', `run-${number}`), branch = `pdd/small-change-${number}-golden`;
  git(repo, 'worktree', 'add', '-q', '-b', branch, worktree, 'HEAD');
  const commonDir = join(repo, '.git'), runDir = join(commonDir, 'pdd', 'runs', String(number));
  const areaName = smallChangeAreas[0].name, label = `widgets#${number} small-change › ${areaName}`;
  const launchProfile = { agent: 'codex', configDir: null, model: null, herdrAgentName: 'pdd-golden', codexThreads: 5 };
  const run = {
    v: 1, runId: `00000000-0000-4000-8000-${String(number).padStart(12, '0')}`, workflow: 'small-change', skill: 'pdd-small-change',
    skillDir: join(context.checkout, 'skills/pdd-small-change'), repo: repository,
    issue: { number, title: `Issue ${number}`, url: issueUrl(number), asked: `Make part ${number} work.` }, number,
    root: worktree, branch, baseBranch: 'main', baseSha: git(repo, 'rev-parse', 'HEAD'), sourceRoot: repo, commonDir, runDir,
    agent: 'codex', configDir: null, draft: false, startedAt: at, state, areas: smallChangeAreas, area: 0, done, gate,
    chats: [{ area: areaName, agent: 'codex', launchProfile, herdrAgentName: 'pdd-golden-17', tabId: 't9', paneId: 'p10', terminalId: 'term11',
      workspaceId: 'w5', repoWorkspaceId: 'w1', label, startedAt: at, session: { agent: 'codex', id: sessionId }, configDir: null,
      messageFile: join(runDir, `${areaName}-start.md`), state: chatState }],
    decisions: [], changes: [], approvalRecord: null, pr: [], prState: null, cancelled: null, warnings: [], journalSeq: 1, previous: [],
    launchProfile, updatedAt: at, ...extra,
  };
  mkdirSync(runDir, { recursive: true });
  writeFileSync(join(runDir, `${areaName}-start.md`), `Start the ${areaName} area for issue ${number}.\n`);
  writeFileSync(join(runDir, 'status.json'), JSON.stringify(run), { mode: 0o600 });
  const agent = { agent: 'codex', agent_status: agentStatus, agent_session: { agent: 'codex', kind: 'id', value: sessionId }, prompts: [], name: 'pdd-golden-17' };
  context.world.herdr = {
    workspaces: [
      { workspace_id: 'w1', label: 'widgets', worktree: { checkout_path: repo, repo_key: commonDir, is_linked_worktree: false } },
      { workspace_id: 'w5', label: `widgets#${number} small-change`, worktree: { checkout_path: worktree, repo_key: commonDir, is_linked_worktree: true } }],
    tabs: [{ tab_id: 't2', workspace_id: 'w1', label: '1' }, { tab_id: 't6', workspace_id: 'w5', label: '1' }, { tab_id: 't9', workspace_id: 'w5', label: areaName }],
    panes: [
      { workspace_id: 'w1', tab_id: 't2', pane_id: 'p3', terminal_id: 'term4', cwd: repo, agent: null },
      { workspace_id: 'w5', tab_id: 't6', pane_id: 'p7', terminal_id: 'term8', cwd: worktree, agent: null },
      { workspace_id: 'w5', tab_id: 't9', pane_id: 'p10', terminal_id: 'term11', cwd: worktree, agent }],
    next: 12, calls: [], sessions: [{ agent: 'codex', id: sessionId, root: worktree, at }],
  };
  const index = join(context.home, '.local/state/pdd');
  mkdirSync(index, { recursive: true, mode: 0o700 });
  writeFileSync(join(index, 'runs.json'), JSON.stringify({ version: 1, runs: [{ repo: repository, number, workflow: 'small-change', state, runDir, root: worktree, updatedAt: at }] }, null, 2) + '\n', { mode: 0o600 });
  context.worktree = worktree;
  return run;
}

export function autopilotStateFile(context, state) {
  const id = createHash('sha256').update(context.repo).digest('hex').slice(0, 20);
  const folder = join(context.home, '.local/state/pdd/autopilot');
  mkdirSync(folder, { recursive: true, mode: 0o700 });
  writeFileSync(join(folder, `${id}.json`), JSON.stringify({ cwd: context.repo, id, repo: repository, defaultBranch: 'main', engine: 'core', ...state }));
  return join(folder, `${id}.json`);
}

export function holdLock(context, path) {
  const file = join(context.root, path);
  mkdirSync(join(file, '..'), { recursive: true });
  writeFileSync(file, JSON.stringify({ pid: process.pid, token: '00000000-0000-4000-8000-00000000beef' }), { mode: 0o600 });
}
