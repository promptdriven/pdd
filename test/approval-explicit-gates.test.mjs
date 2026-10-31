import test from 'node:test';
import { readWorkflowAreas, formatWorkflowList } from '../src/workflow-areas.mjs';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, mkdtempSync, mkdirSync, rmSync, existsSync, realpathSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { execFile as callbackExec, execFileSync } from 'node:child_process';
import { promisify } from 'node:util';
import { startRun, stepDone, approveRun, runStatus } from '../src/workflow-runner.mjs';
// Reuse the established scratch Git and injected gh/Herdr fixture pattern. No live processes.
const exec = promisify(callbackExec);
const packageRoot = resolve(import.meta.dirname, "..");
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
    attach: async () => 0, readApprovalEvidence: async () => assert.fail('A terminal person needs no chat evidence') };
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

for(const kind of ['approve','approve-pr','ask-code']) {
 for(const words of ['What about the empty list?','ok, one more thing','I approve','queued before prompt']) {
  test(`2762 ${kind}: no said refuses latest ${words}`,async t=>{
   const f=await ready(t,kind); let reads=0;
   const before=f.record(), state=readFileSync(join(before.runDir,'status.json'),'utf8');
   if(words==='queued before prompt') for(const p of f.herdr.panes) if(p.agent) p.agent.agent_status='working';
   const out=await approveRun({ref:'17',cwd:f.source},f.agentPorts({readApprovalEvidence:async()=>{reads++; return {ok:true,decision:'approve',agent:'claude',sessionId:before.chats[0].session.id,userMessage:words,userMessageAt:f.clock+1};}}));
   assert.equal(out.exitCode,1,'no-said agent must refuse');
   assert.match(out.message,/ask|person/i); assert.match(out.message,/--said/);
   assert.equal(reads,0,'native evidence must not be read for approval');
   assert.equal(readFileSync(join(before.runDir,'status.json'),'utf8'),state);
  });
 }
 for(const words of ['looks good','ship it','what about X?']) {
  test(`2762 ${kind}: nonblank said ${words}`,async t=>{
   const f=await ready(t,kind); let reads=0;
   const out=await approveRun({ref:'17',cwd:f.source,said:words},f.agentPorts({readApprovalEvidence:async()=>{reads++;return {ok:false,code:'user_message_missing',message:'No recorded turn'};}}));
   assert.equal(out.exitCode,0,out.message); assert.equal(reads,0);
   assert.notEqual(f.record().gate?.kind,kind);
  });
 }
}

test('2762 preservation: chat, status and repeated done cannot approve a waiting gate',async t=>{
 const f=await ready(t), before=f.record();
 const chat=before.chats.at(-1), dir=join(f.base,'home','.claude','projects','synthetic'); mkdirSync(dir,{recursive:true});
 const message={type:'user',sessionId:chat.session.id,cwd:before.root,timestamp:new Date(f.clock+1).toISOString(),message:{role:'user',content:[{type:'text',text:'I approve'}]}};
 writeFileSync(join(dir,chat.session.id+'.jsonl'),JSON.stringify(message)+'\n');
 const ports=f.agentPorts();
 await runStatus({ref:'17',cwd:f.source},ports);
 await stepDone({step:'prompt-story',summary:'Still ready',cwd:before.root},ports);
 const after=f.record(); assert.equal(after.area,before.area); assert.equal(after.gate.kind,'approve'); assert.deepEqual(after.decisions,before.decisions);
});

test('2762 missing approve boundary: valid custom single-area workflow warns without blocking',async t=>{
 const f=await fixture(t); const dir=join(f.source,'.agents','skills','pdd-custom'); mkdirSync(dir,{recursive:true});
 writeFileSync(join(dir,'workflow.json'),JSON.stringify({version:2,areas:[{name:'build',steps:['build'],optional:[],gate:'pr'}]}));
 const workflow=readWorkflowAreas({packageRoot,name:'custom',cwd:f.source,home:join(f.base,'home')});
 assert.equal(workflow.areas.length,1);
 assert.match((workflow.warnings??[]).join(' '),/no approve gate before code/i);
 assert.match(formatWorkflowList([workflow],{}),/no approve gate before code/i);
 const out=await startRun({name:'custom',issue:'17',agent:'claude',cwd:f.source,packageRoot},f.ports);
 assert.equal(out.exitCode,0,out.message); assert.match(out.message,/no approve gate before code/i);
});

for(const strict of [false,true]) test(`2762 refuse ${strict?'strict said':'blank said'}`,async t=>{
 const f=await ready(t), r=f.record();
 if(strict) writeFileSync(join(r.root,'pdd.json'),JSON.stringify({strict_approvals:true}));
 const before=readFileSync(join(r.runDir,'status.json'),'utf8');
 const out=await approveRun({ref:'17',cwd:f.source,said:strict?'looks good':'  '},f.agentPorts({readApprovalEvidence:async()=>({ok:false,code:'user_message_missing',message:'No turn'})}));
 assert.equal(out.exitCode,1); assert.equal(readFileSync(join(r.runDir,'status.json'),'utf8'),before);
});
for(const answer of [true,false]) test(`2762 preservation terminal ${answer?'y':'N'}`,async t=>{
 const f=await ready(t);f.answer=answer;const before=f.record();
 const out=await approveRun({ref:'17',cwd:f.source},f.ports);
 assert.equal(out.exitCode,answer?0:1,out.message);
 assert.equal(f.record().area,answer?before.area+1:before.area);
 if(!answer) assert.deepEqual(f.record().decisions,before.decisions);
});
