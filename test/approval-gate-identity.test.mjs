import test from 'node:test';

import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, mkdtempSync, mkdirSync, rmSync, existsSync, realpathSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { execFile as callbackExec, execFileSync } from 'node:child_process';
import { promisify } from 'node:util';
import { fileURLToPath } from 'node:url';
const repositoryRoot = fileURLToPath(new URL('../', import.meta.url));
const {startRun,stepDone,approveRun,changeRun,runStatus}=await import(`${process.env.PDD_TEST_ROOT ?? repositoryRoot}/src/workflow-runner.mjs`);
const {preparePrEvidence}=await import(`${process.env.PDD_TEST_ROOT ?? repositoryRoot}/src/workflow-pr-evidence.mjs`);
// Reuse the established scratch Git and injected gh/Herdr fixture pattern. No live processes.
const exec = promisify(callbackExec);
const packageRoot = process.env.PDD_TEST_ROOT ?? repositoryRoot;
const issueUrl = "https://github.com/example/project/issues/17";
// A fake Herdr server for session pdd: workspaces, tabs, panes and the agents that pane commands start.
function fakeHerdr() {
  const h = { workspaces: [], tabs: [], panes: [], calls: [], next: 1, focus: null };
  const id = prefix => `${prefix}${h.next++}`;
  const commonDir = cwd => realpathSync(execFileSync('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'], { cwd, encoding: 'utf8' }).trim());
  const pane = (workspace, tab, cwd) => { const p = { workspace_id: workspace, tab_id: tab, pane_id: id('p'), terminal_id: id('term'), cwd, agent: null }; h.panes.push(p); return p; };
  const fail = code => { throw Object.assign(Error(code), { code }); };
  h.herdr = async args => {
    h.calls.push(args);
    const [group, verb, ...rest] = args;
    const flag = name => rest[rest.indexOf(name) + 1];
    if (group === 'status') return { running: true, session: 'pdd', compatible: true };
    if (group === 'workspace' && verb === 'list') return { id: 'cli:workspace:list', result: { type: 'workspace_list', workspaces: h.workspaces } };
    if (group === 'workspace' && verb === 'create') {
      const cwd = flag('--cwd'), w = { workspace_id: id('w'), label: flag('--label'), worktree: { checkout_path: cwd, repo_key: commonDir(cwd), is_linked_worktree: false } };
      h.workspaces.push(w); const t = { tab_id: id('t'), workspace_id: w.workspace_id, label: '1' }; h.tabs.push(t); pane(w.workspace_id, t.tab_id, cwd);
      return { id: 'cli:workspace:create', result: { workspace: w, tab:t, root_pane:h.panes.at(-1) } };
    }
    if (group === 'worktree' && verb === 'open') {
      const cwd = flag('--path'), w = { workspace_id: id('w'), label: flag('--label'), worktree: { checkout_path: cwd, repo_key: commonDir(cwd), is_linked_worktree: true } };
      h.workspaces.push(w); const t = { tab_id: id('t'), workspace_id: w.workspace_id, label: '1' }; h.tabs.push(t); const p = pane(w.workspace_id, t.tab_id, cwd);
      return { id: 'cli:worktree:open', result: { workspace: w, tab: t, root_pane: p } };
    }
    if (group === 'workspace' && verb === 'close') {
      h.workspaces = h.workspaces.filter(w => w.workspace_id !== rest[0]); h.tabs = h.tabs.filter(t => t.workspace_id !== rest[0]);
      return { id: 'cli:workspace:close', result: { type: 'ok' } };
    }
    if (group === 'pane' && verb === 'list') return { id: 'cli:pane:list', result: { type: 'pane_list', panes: h.panes.filter(p => p.workspace_id === flag('--workspace') && h.tabs.some(t => t.tab_id === p.tab_id)) } };
    if (group === 'tab' && verb === 'create') {
      const t = { tab_id: id('t'), workspace_id: flag('--workspace'), label: flag('--label') }; h.tabs.push(t);
      return { id: 'cli:tab:create', result: { tab: t, root_pane: pane(t.workspace_id, t.tab_id, flag('--cwd')) } };
    }
    if (group === 'tab' && verb === 'list') return { id: 'cli:tab:list', result: { type: 'tab_list', tabs: h.tabs.filter(t => t.workspace_id === flag('--workspace')) } };
    if (group === 'tab' && verb === 'get') { const t = h.tabs.find(t => t.tab_id === rest[0]) ?? fail('tab_not_found'); return { result: { tab: t } }; }
    if (group === 'tab' && verb === 'focus') { h.tabs.find(t => t.tab_id === rest[0]) ?? fail('tab_not_found'); h.focus = rest[0]; return { result: { type: 'ok' } }; }
    if (group === 'tab' && verb === 'close') { h.tabs = h.tabs.filter(t => t.tab_id !== rest[0]); return { id: 'cli:tab:close', result: { type: 'ok' } }; }
    if (group === 'pane' && verb === 'run') {
      const p = h.panes.find(p => p.pane_id === rest[0]) ?? fail('pane_not_found');
      const command = rest[1], kind = / claude /.test(command) ? 'claude' : / codex /.test(command) ? 'codex' : null;
      const session = command.match(/--(?:session-id|resume) ([0-9a-f-]{36})/)?.[1] ?? command.match(/ resume ([0-9a-f-]{36})/)?.[1] ?? '00000000-0000-4000-8000-000000000017';
      p.commands = [...(p.commands ?? []), command];
      if (kind) p.agent = { agent: kind, agent_status: 'working', agent_session: { agent: kind, kind: 'id', value: session }, prompts: [] };
      return {};
    }
    if (group === 'agent' && verb === 'get') { const p = h.panes.find(p => p.pane_id === rest[0]); if (!p?.agent) fail('agent_not_found'); return { result: { agent: { ...p.agent, pane_id: p.pane_id } } }; }
    if (group === 'agent' && verb === 'prompt') { const p = h.panes.find(p => p.pane_id === rest[0]); if (!p?.agent) fail('agent_not_found'); if (p.agent.agent_status === 'blocked') fail('agent_blocked'); p.agent.prompts.push(rest[1]); return { result: { type: 'agent_prompted' } }; }
    fail(`unexpected herdr ${args.join(' ')}`);
  };
  h.paneOf = chat => h.panes.find(p => p.pane_id === chat.paneId);
  // Every chat finished its turn (after done, the chat writes its gate message and then waits).
  h.idle = () => { for (const p of h.panes) if (p.agent) p.agent.agent_status = 'idle'; };
  return h;
}

async function fixture(t, { agent = 'claude', name = 'small-change' } = {}) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-runner-')));
  t.after(() => rmSync(base, { recursive: true, force: true }));
  const source = join(base, 'project'), state = join(base, 'state'), home = join(base, 'home');
  for (const dir of [source, state, home, join(home, '.claude')]) mkdirSync(dir);
  const git = (cwd, ...args) => execFileSync('git', args, { cwd, encoding: 'utf8' }).trim();
  git(source, 'init', '-q', '-b', 'main'); git(source, 'config', 'user.email', 'test@example.invalid'); git(source, 'config', 'user.name', 'Runner Test');
  git(source, 'remote', 'add', 'origin', 'https://github.com/example/project.git');
  writeFileSync(join(source, 'value.mjs'), 'export const value = 1;\n'); git(source, 'add', '.'); git(source, 'commit', '-qm', 'initial');
  git(source, 'update-ref', 'refs/remotes/origin/main', git(source, 'rev-parse', 'HEAD'));
  const f = { base, source, state, git, herdr: fakeHerdr(), prs: [], pushes: [], edits: [], fetches: 0, clock: Date.parse('2026-10-27T17:00:00Z'), ci: [], merged: false, mergedNumbers: [] };
  async function execFile(file, args, opts) {
    if (file === 'git' && args[0] === 'push') {
      f.pushes.push(args);
      // Like a real push, keep the remote-tracking branch current.
      const [from, to] = args[2].split(':'), sha = (await exec('git', ['rev-parse', from], { cwd: opts.cwd })).stdout.trim();
      await exec('git', ['update-ref', to.replace('refs/heads/', 'refs/remotes/origin/'), sha], { cwd: opts.cwd });
      return { stdout: '' };
    }
    if (file === 'git' && args[0] === 'ls-remote') {
      // The remote branch as the last push left it (pushes keep the remote-tracking branch current).
      const ref = args.at(-1), local = await exec('git', ['rev-parse', '--verify', '--quiet', ref.replace('refs/heads/', 'refs/remotes/origin/')], { cwd: opts.cwd }).catch(() => ({ stdout: '' }));
      return local.stdout.trim() ? { stdout: `${local.stdout.trim()}\t${ref}\n` } : { stdout: '', code: 2 };
    }
    if (file === 'git' && args[0] === 'fetch') {
      f.fetches++;
      const branch = args[2].replace(/^refs\/heads\//, '').split(':')[0];
      const merged = f.prs.find(pr => f.mergedNumbers.includes(pr.number) && pr.baseRefName === branch);
      if (merged) await exec('git', ['update-ref', `refs/remotes/origin/${branch}`, merged.headRefOid], { cwd: opts.cwd });
      return { stdout: '' };
    }
    if (file !== 'gh') return exec(file, args, { ...opts, encoding: 'utf8' });
    if (args[0] === 'repo' && args[1] === 'view') return { stdout: JSON.stringify({ nameWithOwner: 'example/project', defaultBranchRef: { name: 'main' }, url: 'https://github.com/example/project' }) };
    if (args[0] === 'api' && args[1] === 'repos/example/project/issues/17') return { stdout: JSON.stringify({ number: 17, html_url: issueUrl, title: 'Use value two', body: f.issueBody ?? 'Value must be two.' }) };
    if (args[0] === 'pr' && args[1] === 'create' && f.createError) { const stderr = f.createError; f.createError = null; return { stdout: '', stderr, code: 1 }; }
    if (args[0] === 'pr' && args[1] === 'create') {
      const value = flag => args[args.indexOf(flag) + 1];
      const number = 23 + f.prs.length;
      const pr = { number, url: `https://github.com/example/project/pull/${number}`, state: 'OPEN', headRefName: value('--head'), baseRefName: value('--base'),
        headRefOid: (await exec('git', ['rev-parse', 'HEAD'], { cwd: opts.cwd })).stdout.trim(), body: String(opts.input ?? ''), title: value('--title'),
        headRepository: { name: 'project' }, headRepositoryOwner: { login: 'example' }, isCrossRepository: false, mergeCommit: null };
      f.prs.push(pr); return { stdout: pr.url + '\n' };
    }
    if (args[0] === 'pr' && args[1] === 'list') {
      const head = args.includes('--head') ? args[args.indexOf('--head') + 1] : null, search = args.includes('--search') ? args[args.indexOf('--search') + 1].split('"')[1] : null;
      return { stdout: JSON.stringify(f.prs.filter(pr => (!head || pr.headRefName === head) && (!search || pr.body.includes(search)))) };
    }
    if (args[0] === 'pr' && args[1] === 'view') {
      const pr = f.prs.find(item => item.url === args[2]);
      return { stdout: JSON.stringify({ state: f.merged || f.mergedNumbers.includes(pr?.number) ? 'MERGED' : 'OPEN', mergedAt: null, statusCheckRollup: f.ci, body: pr?.body }) };
    }
    if (args[0] === 'pr' && args[1] === 'edit') {
      const pr = f.prs.find(item => item.url === args[2]) ?? assert.fail(`no PR ${args[2]}`);
      pr.body = String(opts.input ?? ''); f.edits.push(pr.number); return { stdout: '' };
    }
    throw Error(`unexpected gh ${args.join(' ')}`);
  }
  f.prompts = [];
  f.ports = { execFile, herdr: f.herdr.herdr, stateDir: state, layoutDirectory: join(state, 'herdr-layout'), now: () => f.clock,
    env: { HOME: home, CLAUDE_CONFIG_DIR: join(home, '.claude') }, isTTY: true, pdd: '/abs/node /abs/pdd.mjs',
    confirm: async question => { f.prompts.push(question); return f.answer ?? true; },
    attach: async () => 0, readApprovalEvidence: async () => ({ok:false,reason:'no native approval supplied'}) };
  f.run = () => startRun({ name, issue: '17', agent, cwd: source, packageRoot }, f.ports);
  f.record = () => JSON.parse(readFileSync(join(f.git(source, 'rev-parse', '--path-format=absolute', '--git-common-dir'), 'pdd', 'runs', '17', 'status.json'), 'utf8'));
  f.tick = (ms = 1000) => { f.clock += ms; };
  f.agentPorts = extra => ({ ...f.ports, isTTY: false, env: { ...f.ports.env, PDD_AGENT_SESSION: '1' }, ...extra });
  return f;
}



async function ready(t, kind = 'approve') {
 const f = await fixture(t, {name:'feature'});
 assert.equal((await f.run()).exitCode, 0);
 f.finish = async () => {
  const current=f.record(), areas=current.areas ?? current.workflow?.areas;
  if(current.area===1) { writeFileSync(join(current.root,"value.mjs"),"export const value = 2;\n"); f.git(current.root,"add","value.mjs"); f.git(current.root,"commit","-qm","Synthetic prompt-space change"); }
  const steps=areas?.[current.area]?.steps ?? (current.area===0 ? ['understand','visual','prompt-story'] : ['check','try']);
  for (const step of steps) { f.tick(); const out=await stepDone({step,summary:'Synthetic gate work ready',cwd:current.root},f.agentPorts()); assert.equal(out.exitCode,0,out.message); }
  f.herdr.idle();
 };
 await f.finish();
 if(kind!=='approve') {
  let out=await approveRun({ref:'17',cwd:f.source},f.ports); assert.equal(out.exitCode,0,out.message);
  await f.finish();
 }
 if(kind==='ask-code') {
  let questions=0;
  const out=await approveRun({ref:'17',cwd:f.source},{...f.ports,confirm:async()=>++questions===1}); assert.equal(out.exitCode,0,out.message);
  f.herdr.idle();
 }
 assert.equal(f.record().gate.kind,kind);
 return f;
}



const approvals = f => JSON.parse(readFileSync(join(f.record().commonDir,'pdd','approvals.json'),'utf8')).approvals;
for (const commandAdvance of [0,1000]) test(`R1 distinct same-time gates preserve terminal and said evidence, command offset ${commandAdvance}`,async t=>{
 const f=await ready(t,'ask-code'),before=f.record(),terminal=before.decisions.at(-1);
 assert.equal(before.gate.at,terminal.gateAt ?? terminal.at,'fixture must expose same-time gate collision');
 f.clock+=commandAdvance;
 const out=await approveRun({ref:'17',cwd:f.source,said:'ship it'},f.agentPorts());assert.equal(out.exitCode,0,out.message);
 const after=f.record();assert.equal(after.decisions.at(-1).text,'ship it','later code decision retains exact words');
 assert.deepEqual(after.decisions.at(-2),terminal,'terminal event survives unchanged');
 assert.ok(before.gate.id);assert.notEqual(before.gate.id,terminal.gateId);
 assert.equal(after.decisions.at(-1).gateId,before.gate.id);
 assert.notEqual(after.decisions.at(-1).evidence.id,terminal.evidence.id);
 assert.equal(after.approvalRecord.evidence.words,'ship it');
 assert.equal(approvals(f).length,after.decisions.length,'one journal event per gate decision');
 assert.match(f.prs[0].body,/ship it/);
});
test('R1 same-gate publication retry keeps original evidence exactly once',async t=>{
 const f=await ready(t,'approve-pr');f.createError='synthetic publication refusal';
 let out=await approveRun({ref:'17',cwd:f.source,said:'first approval'},f.agentPorts());assert.notEqual(out.exitCode,0);assert.match(out.message,/synthetic publication refusal/);
 const before=f.record(),journal=approvals(f);assert.equal(before.gate.kind,'approve-pr');
 out=await approveRun({ref:'17',cwd:f.source,said:'retry words'},f.agentPorts());assert.equal(out.exitCode,0,out.message);
 assert.deepEqual(f.record().decisions,before.decisions);assert.deepEqual(approvals(f),journal);
 assert.equal(f.prs[0].body.split('Approved in chat:').length-1,1);
 assert.match(f.prs[0].body,/first approval/);assert.doesNotMatch(f.prs[0].body,/retry words/);
});
test('R1 fixed-clock changed same-kind gate records fresh words and identity',async t=>{
 const f=await ready(t,'approve-pr');f.createError='synthetic publication refusal';
 let out=await approveRun({ref:'17',cwd:f.source,said:'old approval'},f.agentPorts());assert.notEqual(out.exitCode,0);assert.match(out.message,/synthetic publication refusal/);
 const before=f.record();
 out=await changeRun({ref:'17',cwd:f.source,text:'Revise the explanation.'},f.ports);assert.equal(out.exitCode,0,out.message);f.herdr.idle();
 const fixedClock=f.clock;
 out=await stepDone({step:'try',summary:'Show the revised gate again',cwd:before.root},f.agentPorts());assert.equal(out.exitCode,0,out.message);f.herdr.idle();
 assert.equal(f.clock,fixedClock,'re-show keeps the fixed approval clock');
 out=await approveRun({ref:'17',cwd:f.source,said:'fresh approval'},f.agentPorts());assert.equal(out.exitCode,0,out.message);
 const after=f.record();assert.equal(after.decisions.at(-1).text,'fresh approval');
 assert.notEqual(after.decisions.at(-1).gateId,before.decisions.at(-1).gateId);
 assert.notEqual(after.decisions.at(-1).evidence.id,before.decisions.at(-1).evidence.id);
 assert.equal(after.decisions.length,before.decisions.length+1);
});
test('R1 publisher preserves separate identical-content events and deduplicates journal copy',async()=>{
 const event={id:'event-a',route:'said',actor:{kind:'agent',id:'session'},at:100,words:'ship it',prompts:[]};
 const run={runId:'synthetic',runDir:'/unused',root:'/unused',baseSha:'a'.repeat(40),number:17,workflow:'feature',baseBranch:'main',steps:[],decisions:[{stage:'prompt-pr',decision:'approve',gateId:'gate-a',evidence:event},{stage:'prompt-pr',decision:'approve',gateId:'gate-b',evidence:{...event,id:'event-b'}}],promptApprovals:[structuredClone(event)]};
 const result=await preparePrEvidence({run,isCode:false},{readStepNotes:async()=>({notes:[]})});
 assert.ok(Array.isArray(result.approvalLines), 'preparePrEvidence requires approvalLines array for identified and legacy approval evidence');
 assert.equal(result.approvalLines.filter(line=>line.startsWith('Approved in chat:')).length,2,'two decisions survive; same event journal copy appears once');
});
test('R1 legacy evidence remains readable without invented actor or words',async()=>{
 const run={runId:'legacy',runDir:'/unused',root:'/unused',baseSha:'a'.repeat(40),number:17,workflow:'feature',baseBranch:'main',steps:[],decisions:[{stage:'story',decision:'approve',via:'terminal',at:100}]};
 const result=await preparePrEvidence({run,isCode:false},{readStepNotes:async()=>({notes:[]})});
 assert.ok(Array.isArray(result.approvalLines), 'preparePrEvidence requires approvalLines array for identified and legacy approval evidence');
 assert.equal(result.approvalLines.filter(line=>line.startsWith('Approved in terminal:')).length,1);assert.doesNotMatch(result.approvalLines.join('\n'),/actor|ship it/);
});
