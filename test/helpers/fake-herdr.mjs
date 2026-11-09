import {realpathSync, statSync} from 'node:fs';
import {execFileSync} from 'node:child_process';
// A fake Herdr server for session pdd: workspaces, tabs, panes and the agents that pane commands start.
export function fakeHerdr() {
  // sessions: the native session files that agents started by pane commands wrote ({agent, id, root, at}).
  // realIdentity: true follows the identity rules of real Herdr 0.9.1: a new workspace has no Git identity, and opening
  // the workspace's own non-linked checkout gives it that identity (already_open) instead of opening another workspace.
  const h = { workspaces: [], tabs: [], panes: [], calls: [], next: 1, focus: null, sessions: [], nextSession: 17, now: () => Date.now(), realIdentity: false, shellStartFolder: null };
  const id = prefix => `${prefix}${h.next++}`;
  const commonDir = cwd => realpathSync(execFileSync('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'], { cwd, encoding: 'utf8' }).trim());
  const gitOut = (cwd, ...args) => { try { return execFileSync('git', args, { cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }).trim(); } catch { return null; } };
  const workTree = path => { const top = gitOut(path, 'rev-parse', '--show-toplevel'); return top !== null && realpathSync(top) === realpathSync(path); };
  const linked = path => gitOut(path, 'rev-parse', '--absolute-git-dir') !== gitOut(path, 'rev-parse', '--path-format=absolute', '--git-common-dir');
  const pane = (workspace, tab, cwd) => {
    const p = { workspace_id: workspace, tab_id: tab, pane_id: id('p'), terminal_id: id('term'), cwd, agent: null }; h.panes.push(p);
    if (!h.shellStartFolder) return p;
    const reply = { ...p }; p.cwd = h.shellStartFolder; return reply;
  };
  const folder = path => { try { return statSync(path).isDirectory(); } catch { return false; } };
  const fail = code => { throw Object.assign(Error(code), { code }); };
  h.herdr = async args => {
    h.calls.push(args);
    const [group, verb, ...rest] = args;
    const flag = name => rest[rest.indexOf(name) + 1];
    if (group === 'status') return { running: true, session: 'pdd', compatible: true };
    if (group === 'workspace' && verb === 'list') return { id: 'cli:workspace:list', result: { type: 'workspace_list', workspaces: h.workspaces } };
    if (h.paneLimit !== undefined && h.panes.length >= h.paneLimit && ((group === 'workspace' || group === 'tab') && verb === 'create' || group === 'worktree' && verb === 'open')) fail('test_pane_limit');
    if (group === 'workspace' && verb === 'create') {
      const cwd = flag('--cwd'), w = { workspace_id: id('w'), label: flag('--label'), ...(!h.realIdentity ? { worktree: { checkout_path: cwd, repo_key: commonDir(cwd), is_linked_worktree: false } } : {}) };
      h.workspaces.push(w); const t = { tab_id: id('t'), workspace_id: w.workspace_id, label: '1' }; h.tabs.push(t); const p = pane(w.workspace_id, t.tab_id, cwd);
      return { id: 'cli:workspace:create', result: { workspace: w, tab:t, root_pane:p } };
    }
    if (group === 'worktree' && verb === 'open') {
      // Real Herdr 0.9.1: the source must be a repository parent workspace inside Git, and the path a Git work tree.
      const source = h.workspaces.find(w => w.workspace_id === flag('--workspace')), sourceCwd = source?.worktree?.checkout_path ?? h.panes.find(p => p.workspace_id === source?.workspace_id)?.cwd;
      if (!source) fail('workspace_not_found');
      // A linked source refuses, also a new workspace at a linked checkout that has no Git identity yet.
      if (source.worktree ? source.worktree.is_linked_worktree : sourceCwd && linked(sourceCwd)) throw Object.assign(Error('New and open worktree actions start from the repo parent workspace.'), { code: 'linked_worktree_source' });
      if (!sourceCwd || gitOut(sourceCwd, 'rev-parse', '--git-dir') === null) throw Object.assign(Error('Herdr worktree actions require a workspace inside a Git work tree'), { code: 'not_git_worktree' });
      if (!workTree(flag('--path'))) throw Object.assign(Error('worktree cannot be opened'), { code: 'worktree_not_found' });
      // A work tree of another repository (another common Git directory) refuses, and the source gets no identity.
      if (commonDir(flag('--path')) !== commonDir(sourceCwd)) throw Object.assign(Error('worktree path not found'), { code: 'worktree_not_found' });
      // The source gets its repository identity on its first worktree action; a bare source keeps its own folder.
      source.worktree ??= { checkout_path: sourceCwd, repo_key: commonDir(sourceCwd), is_linked_worktree: false };
      if (h.realIdentity && realpathSync(flag('--path')) === realpathSync(sourceCwd) && !linked(sourceCwd))
        return { id: 'cli:worktree:open', result: { workspace: source, already_open: true } };
      const cwd = flag('--path'), w = { workspace_id: id('w'), label: flag('--label'), worktree: { checkout_path: cwd, repo_key: commonDir(cwd), is_linked_worktree: true } };
      h.workspaces.push(w); const t = { tab_id: id('t'), workspace_id: w.workspace_id, label: '1' }; h.tabs.push(t); const p = pane(w.workspace_id, t.tab_id, cwd);
      return { id: 'cli:worktree:open', result: { workspace: w, tab: t, root_pane: p, already_open: false } };
    }
    if (group === 'workspace' && verb === 'close') {
      h.workspaces = h.workspaces.filter(w => w.workspace_id !== rest[0]); h.tabs = h.tabs.filter(t => t.workspace_id !== rest[0]); h.panes = h.panes.filter(p => p.workspace_id !== rest[0]);
      return { id: 'cli:workspace:close', result: { type: 'ok' } };
    }
    if (group === 'pane' && verb === 'list') return { id: 'cli:pane:list', result: { type: 'pane_list', panes: h.panes.filter(p => (!rest.includes('--workspace') || p.workspace_id === flag('--workspace')) && h.tabs.some(t => t.tab_id === p.tab_id)) } };
    if (group === 'tab' && verb === 'create') {
      if (!h.workspaces.some(w => w.workspace_id === flag('--workspace'))) fail('workspace_not_found');
      const t = { tab_id: id('t'), workspace_id: flag('--workspace'), label: flag('--label') }; h.tabs.push(t);
      return { id: 'cli:tab:create', result: { tab: t, root_pane: pane(t.workspace_id, t.tab_id, flag('--cwd')) } };
    }
    if (group === 'tab' && verb === 'list') return { id: 'cli:tab:list', result: { type: 'tab_list', tabs: h.tabs.filter(t => t.workspace_id === flag('--workspace')) } };
    if (group === 'tab' && verb === 'get') { const t = h.tabs.find(t => t.tab_id === rest[0]) ?? fail('tab_not_found'); return { result: { tab: t } }; }
    if (group === 'tab' && verb === 'focus') { h.tabs.find(t => t.tab_id === rest[0]) ?? fail('tab_not_found'); h.focus = rest[0]; return { result: { type: 'ok' } }; }
    if (group === 'tab' && verb === 'close') { h.panes = h.panes.filter(p => p.tab_id !== rest[0]); h.tabs = h.tabs.filter(t => t.tab_id !== rest[0]); return { id: 'cli:tab:close', result: { type: 'ok' } }; }
    if (group === 'pane' && verb === 'run') {
      const p = h.panes.find(p => p.pane_id === rest[0]) ?? fail('pane_not_found');
      const command = rest[1];
      // The shell runs a leading `cd '<folder>' && …` first; when that cd fails, nothing after it runs.
      const cd = /^cd ('(?:[^']|'\\'')*') && /.exec(command), target = cd?.[1].slice(1, -1).replace(/'\\''/g, "'");
      if (cd && !folder(target)) { p.commands = [...(p.commands ?? []), command]; return {}; }
      if (cd) p.cwd = target;
      const kind = / claude /.test(command) ? 'claude' : / codex /.test(command) ? 'codex' : / gemini /.test(command) ? 'gemini' : / agy /.test(command) ? 'agy' : null;
      const session = command.match(/--(?:session-id|resume) '?([0-9a-f-]{36})/)?.[1] ?? command.match(/ resume '?([0-9a-f-]{36})/)?.[1] ?? `00000000-0000-4000-8000-${String(h.nextSession++).padStart(12, '0')}`;
      p.commands = [...(p.commands ?? []), command];
      if (kind) {
        p.agent = { agent: kind, agent_status: 'working', agent_session: { agent: kind, kind: 'id', value: session }, prompts: [] };
        if (!h.sessions.some(item => item.id === session && item.agent === kind)) h.sessions.push({ agent: kind, id: session, root: p.cwd, at: h.now() });
      }
      return {};
    }
    // The plain-text screen of a pane (empty unless a test draws one, for example an agent dialog).
    if (group === 'pane' && verb === 'read') return (h.panes.find(p => p.pane_id === rest[0]) ?? fail('pane_not_found')).screen ?? '';
    if (group === 'pane' && verb === 'process-info') {
      const p = h.panes.find(p => p.pane_id === flag('--pane')) ?? fail('pane_not_found');
      const shellPid = 100;
      return {result:{type:'pane_process_info', process_info: p.processInfo ?? {
        pane_id:p.pane_id, shell_pid:shellPid, foreground_process_group_id:p.agent ? 101 : shellPid,
        foreground_processes:[{pid:p.agent ? 101 : shellPid, name:p.agent?.agent ?? 'bash'}]
      }}};
    }
    if (group === 'agent' && verb === 'rename') {
      const p = h.panes.find(p => p.pane_id === rest[0]); if (!p?.agent) fail('agent_not_found');
      if (!/^[a-z][a-z0-9_-]{0,31}$/.test(rest[1])) fail('invalid_agent_name');
      if (h.panes.some(other => other !== p && other.agent?.name === rest[1])) fail('agent_name_conflict');
      p.agent.name = rest[1]; return {result: {type: 'ok'}};
    }
    if (group === 'agent' && verb === 'get') { const p = h.panes.find(p => p.pane_id === rest[0] || p.agent?.name === rest[0]); if (!p?.agent) fail('agent_not_found'); return { result: { agent: { ...p.agent, pane_id: p.pane_id } } }; }
    if (group === 'agent' && verb === 'prompt') { const p = h.panes.find(p => p.pane_id === rest[0]); if (!p?.agent) fail('agent_not_found'); if (p.agent.agent_status === 'blocked') fail('agent_blocked'); p.agent.prompts.push(rest[1]); return { result: { type: 'agent_prompted' } }; }
    fail(`unexpected herdr ${args.join(' ')}`);
  };
  h.paneOf = chat => h.panes.find(p => p.pane_id === chat.paneId);
  // The native session lookup over the files above: same agent and worktree, started inside the window, saved id if given.
  h.findNativeSessions = async stage => h.sessions.filter(item => item.agent === stage.agent && realpathSync(item.root) === realpathSync(stage.root)
    && item.at >= stage.startedAt && item.at <= stage.endedAt && (!stage.sessionId || item.id === stage.sessionId)).map(item => ({ id: item.id, startedAt: item.at }));
  // Every chat finished its turn (after done, the chat writes its gate message and then waits).
  h.idle = () => { for (const p of h.panes) if (p.agent) p.agent.agent_status = 'idle'; };
  return h;
}
