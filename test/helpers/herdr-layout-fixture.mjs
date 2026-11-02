import {join} from 'node:path';
import {randomUUID} from 'node:crypto';
import {liveLayout, ownerFor} from './live-herdr-layout.mjs';

// Full live Herdr inventory with real disposable Git checkouts. The caller retains
// actual root custody just as the production runner does, without a layout registry.
export async function fixture(t) {
  const live = await liveLayout(t), {herdr, git} = live;
  git(live.source, 'remote', 'set-url', 'origin', 'https://github.com/alice/coffee.git');
  const input = {...live.input, repository: 'alice/coffee', issueNumber: 2, workflowName: 'small-change', stageId: 'scope', runId: randomUUID()};
  const owners = new Map(), layouts = new Map();
  live.ports.command = async args => structuredClone(await herdr.herdr(args));
  const f = {root: live.base, input, ports: live.ports, module: live.layout, calls: herdr.calls, herdr,
    git: async (cwd, ...args) => git(cwd, ...args),
    init: async (cwd, repository) => {git(cwd, 'init', '-q', '-b', 'main'); git(cwd, '-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', 'commit', '--allow-empty', '-qm', 'Base'); git(cwd, 'remote', 'add', 'origin', `https://github.com/${repository}.git`);}};
  Object.defineProperty(f, 'workspaces', {get: () => herdr.workspaces});
  f.open = async (extra = {}) => {
    const request = {...input, ...extra}, owner = owners.get(request.runId);
    try {git(request.cwd, 'rev-parse', '--git-dir');} catch {git(request.sourceRoot, 'worktree', 'add', '--detach', request.cwd);}
    const result = await live.layout.withHerdrLayoutLock(() => live.layout.openHerdrRunLayout({...request, ...(owner ? {run: owner} : {})}, f.ports), f.ports);
    owners.set(request.runId, ownerFor({input: request}, result));
    layouts.set(result.tabId, result);
    return result;
  };
  f.close = async request => {
    // Caller closes only area tabs it allocated; person-created tabs remain.
    for (const tab of layouts.values()) if (tab.workspaceId === request.layout.workspaceId && herdr.tabs.some(t => t.tab_id === tab.tabId)) await f.ports.command(['tab', 'close', tab.tabId]);
    return live.layout.closeHerdrRunLayout(request, f.ports);
  };
  return f;
}
