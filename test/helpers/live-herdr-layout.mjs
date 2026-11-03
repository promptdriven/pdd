import {join} from 'node:path';
import {fixture} from './workflow-runner-fixture.mjs';
import * as layout from '../../src/workflow-herdr-layout.mjs';

export async function liveLayout(t) {
  const f = await fixture(t), cwd = join(f.base, 'assigned');
  f.git(f.source, 'worktree', 'add', '-qb', 'assigned', cwd);
  const input = {runId: 'run', repository: 'example/project', sourceRoot: f.source,
    commonDir: f.git(f.source, 'rev-parse', '--path-format=absolute', '--git-common-dir'), cwd,
    issueNumber: 17, workflowName: 'bug', stageId: 'story'};
  const ports = {command: f.herdr.herdr, execFile: f.ports.execFile, directory: f.ports.layoutDirectory, checkpoint: async () => {}};
  return {...f, input, ports, layout, open: extra => layout.withHerdrLayoutLock(() => layout.openHerdrRunLayout({...input, ...extra}, ports), ports)};
}
export const mutations = f => f.herdr.calls.filter(a => ['create', 'open', 'rename', 'close', 'remove', 'run'].includes(a[1]));
export const ownerFor = (f, opened) => ({runId: f.input.runId, layout: {workspaceId: opened.workspaceId, repoWorkspaceId: opened.repoWorkspaceId, ...opened.root}, chats: [{area: 'story', ...opened}]});
export async function closeRun(f, opened) {
  await f.herdr.herdr(['tab', 'close', opened.tabId]);
  return f.layout.withHerdrLayoutLock(() => f.layout.closeHerdrRunLayout({...f.input, layout: opened}, f.ports), f.ports);
}
