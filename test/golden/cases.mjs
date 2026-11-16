import { createHash } from 'node:crypto';
import { mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { autopilotStateFile, draftPrompt, harborProject, holdLock, ownerProject, project, repository, startedRun } from './fixtures.mjs';

const place = 'prompts/place_order.prompt.md';
const worktree = 'project.pdd-worktrees/run-17';
const personWords = 'Yes, go ahead with the build.\n';
const coordinator = { version: 'pdd.autopilot-coordinator.v1', repository, coordinatorId: 'golden-coordinator', machine: 'golden-machine', activation: '2026-11-13T12:00:00.000Z' };

const draftHarbor = context => harborProject(context, repo => writeFileSync(join(repo, place), draftPrompt(readFileSync(join(repo, place), 'utf8'))));
const withSettings = autopilot => context => project(context, { files: { 'value.mjs': 'export const value = 1;\n', 'pdd.json': JSON.stringify({ autopilot }, null, 2) + '\n' } });
const autopilotRepo = context => {
  withSettings({ mode: 'observe', label: 'pdd:autopilot', trust: [] })(context);
  autopilotStateFile(context, { enabled: true, timerInstalled: true, label: 'pdd:autopilot', coordinatorId: 'golden-coordinator', machine: 'golden-machine',
    nextTick: context.now + 600000, controlRevision: '00000000-0000-4000-8000-00000000c0de', agent: { id: 'codex', kind: 'codex', command: 'codex' } });
};
const githubLedger = context => {
  const folder = join(context.home, '.local/state/pdd/autopilot/github');
  mkdirSync(folder, { recursive: true, mode: 0o700 });
  writeFileSync(join(folder, `${createHash('sha256').update(repository).digest('hex').slice(0, 20)}.jsonl`), '', { mode: 0o600 });
};
const scopeDone = context => context.pdd(['workflow', 'done', 'scope', '--summary', 'Scoped the change to value.mjs.'], { cwd: context.worktree });
const firstGraph = context => context.pdd(['graph']);
const dropGraphCache = context => rmSync(join(context.home, '.cache/pdd/graph'), { recursive: true, force: true });

export const cases = [
  { id: 'cli-version', argv: ['--version'], build: project },
  { id: 'cli-help', argv: ['--help'], build: project },
  { id: 'cli-workflow-help', argv: ['workflow', '--help'], build: project },
  { id: 'cli-unknown-command', argv: ['frobnicate'], build: project },

  { id: 'workflow-run-missing-issue', argv: ['workflow', 'run', 'small-change'], build: project },
  { id: 'workflow-run-unknown-agent', argv: ['workflow', 'run', 'small-change', '17', '--agent', 'nobody'], build: project },
  { id: 'workflow-run-start', argv: ['workflow', 'run', 'small-change', '17', '--agent', 'codex'], build: project },
  { id: 'workflow-run-admission-busy', argv: ['workflow', 'run', 'small-change', '17', '--agent', 'codex'], env: { PDD_AUTOPILOT_CONTEXT: JSON.stringify(coordinator) },
    build: context => { project(context); holdLock(context, 'project/.git/pdd/autopilot-admission.lock'); } },
  { id: 'workflow-status-text', argv: ['workflow', 'status'], build: startedRun },
  { id: 'workflow-status-json', argv: ['workflow', 'status', '17', '--json'], build: startedRun },
  { id: 'workflow-status-all', argv: ['workflow', 'status', '--all'], cwd: 'home', build: startedRun },
  { id: 'workflow-view', argv: ['workflow', 'view', '17'], build: context => startedRun(context, { phase: 'gate' }) },
  { id: 'workflow-done', argv: ['workflow', 'done', 'scope', '--summary', 'Scoped the change to value.mjs.'], cwd: worktree, build: startedRun },
  { id: 'workflow-ask', argv: ['workflow', 'ask', 'Should', 'the', 'value', 'be', 'two?'], cwd: worktree, build: startedRun },
  { id: 'workflow-approve-said', argv: ['workflow', 'approve', '17', '--said', '-'], stdin: personWords, build: startedRun, setup: [scopeDone] },
  { id: 'workflow-approve-no-review', argv: ['workflow', 'approve', '17', '--said', '-'], stdin: personWords, build: context => startedRun(context, { phase: 'gate' }) },
  { id: 'workflow-tidy-dry-run', argv: ['workflow', 'tidy', '--dry-run'], build: context => startedRun(context, { phase: 'completed' }) },
  { id: 'workflow-tidy', argv: ['workflow', 'tidy'], build: context => startedRun(context, { phase: 'completed' }) },

  { id: 'autopilot-status-text', argv: ['autopilot', 'status'], build: autopilotRepo },
  { id: 'autopilot-status-json', argv: ['autopilot', 'status', '--json'], build: autopilotRepo },
  { id: 'autopilot-start-bad-mode', argv: ['autopilot', 'start', '--mode', 'sometimes'], build: autopilotRepo },
  { id: 'autopilot-start-full-engine', argv: ['autopilot', 'start', '--engine', 'full'], build: autopilotRepo },
  { id: 'autopilot-start-no-label', argv: ['autopilot', 'start'], build: withSettings({ mode: 'observe', trust: [] }) },
  { id: 'autopilot-stop', argv: ['autopilot', 'stop'], build: autopilotRepo },
  { id: 'autopilot-add', argv: ['autopilot', 'add', '17', `${repository}#18`], build: autopilotRepo },
  { id: 'autopilot-add-other-repo', argv: ['autopilot', 'add', 'other/repo#3'], build: autopilotRepo },
  { id: 'autopilot-release', argv: ['autopilot', 'release', '17'], build: autopilotRepo,
    world: { github: { changes: [['claim', 17, { coordinatorId: 'golden-coordinator', machine: 'golden-machine' }], ['label', 17, 'pdd:stuck']] } } },

  { id: 'owner-binding', argv: ['owner', 'src/bound.mjs', '--json'], build: ownerProject },
  { id: 'owner-header', argv: ['owner', 'src/headed.mjs'], build: ownerProject },
  { id: 'owner-unowned', argv: ['owner', 'src/loose.mjs', 'src/claimed.mjs'], build: ownerProject },
  { id: 'approve-said-stdin', argv: ['approve', place, '--said', '-'], stdin: 'Yes, approve the place order prompt.\n', build: draftHarbor },
  { id: 'approve-refused-pipe', argv: ['approve', place], stdin: 'y\n', build: draftHarbor },
  { id: 'graph-cached', argv: ['graph'], build: project, setup: [firstGraph], world: { github: { issues: 6, changes: [['link', 3, 2]] } } },
  { id: 'graph-refresh-paged-304', argv: ['graph', '--issue', '3'], build: context => { project(context); githubLedger(context); }, setup: [firstGraph, dropGraphCache],
    world: { github: { issues: 105, changes: [['link', 3, 2], ['link', 104, 3]] } } },
];
