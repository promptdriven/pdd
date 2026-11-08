import { readAutopilotState } from '../src/autopilot-store.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {mkdirSync, writeFileSync, rmSync, realpathSync} from 'node:fs';
import {join} from 'node:path';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {readDependencySnapshot} from '../src/issue-dependencies-github.mjs';
import {reconcileDependencyIntake, checkDependencyStart} from '../src/issue-dependencies-intake.mjs';
import {runAutopilotLauncher} from '../src/autopilot-launcher.mjs';
import {startRun, stepDone, yieldAutomaticCapacity} from '../src/workflow-runner.mjs';
import {armWorkerCompletion, waitForWorkerCompletion} from '../src/workflow-worker-completion.mjs';
const repository = 'example/project';
const baseTime = Date.parse('2026-11-05T18:00:00.000Z');
const candidate = packageRoot;
const reply = value => ({json: JSON.stringify(value)});
const sha = value => createHash('sha256').update(value).digest('hex');
const issueKey = number => `https://github.com/${repository}/issues/${number}`;
const revisionFor = issue => sha(JSON.stringify({title: issue.title, body: issue.body}));
const rowFor = issue => ({key: issue.html_url, revision: revisionFor(issue)});
const makeIssue = (number, overrides = {}) => ({
  id: number,
  number,
  html_url: issueKey(number),
  title: `Synthetic issue ${number}`,
  body: `Please resolve synthetic case ${number}.`,
  state: 'open',
  user: {login: 'owner'},
  labels: [],
  assignees: [],
  created_at: '2026-11-05T19:00:00.000Z',
  updated_at: '2026-11-05T19:00:00.000Z',
  comments: 0,
  ...overrides,
});

function reviewComment(issue, allIssues, id, dependencies = []) {
  const key = issue.html_url;
  const value = {
    analysis: 'Requirements reviewed for this offline acceptance fixture.',
    base: [],
    continuation: '',
    issue: key,
    inputs: [rowFor(issue)],
    candidates: allIssues.map(rowFor),
    outcome: 'complete',
    dependencies,
    questions: [],
    effects: dependencies.length ? 'confirmed' : 'none',
  };
  return {
    id,
    body: `Dependencies checked: ${dependencies.length ? 'recorded.' : 'none.'}\n\n<!-- pdd-dependency-review:v1 -->\n\`\`\`json\n${JSON.stringify({schema_version: 'pdd.dependency-review.v1', review: value})}\n\`\`\``,
    created_at: '2026-11-05T19:30:00.000Z',
    updated_at: '2026-11-05T19:30:00.000Z',
    user: {login: 'owner'},
  };
}

function graphPorts({issues, labels = {}, assignees = {}, timelines = {}, blockers = {}, comments = {}, owners = {}, brokenPages = []}) {
  const byNumber = new Map(issues.map(issue => [issue.number, issue]));
  const broken = new Set(brokenPages.map(row => `${row.kind}:${row.issue}`));
  const ownerData = {
    localOwner: 'coordinator-a',
    claims: [],
    runs: [],
    runsKnown: true,
    ...owners,
  };
  return {
    github: {
      issue: async ({issue}) => reply(byNumber.get(issue) ?? {error: 'not_found'}),
      page: async ({kind, issue}) => {
        if (kind === 'issues') return reply({items: issues, next: ''});
        if (broken.has(`${kind}:${issue}`)) throw Error(`fixture cannot read ${kind}`);
        const value = kind === 'comments' ? (comments[issue] ?? [])
          : kind === 'timeline' ? (timelines[issue] ?? [])
          : kind === 'blockedBy' ? (blockers[issue] ?? [])
          : kind === 'blocking' ? [] : [];
        return reply({items: value, next: ''});
      },
    },
    authority: {read: async () => ({authority: 'trusted'})},
    context: {read: async () => reply({inputs: [], conditions: [], execution: [], nativeExecution: true})},
    owners: {read: async () => reply(ownerData)},
    clock: {now: async () => ({iso: '2026-11-05T20:00:00.000Z'})},
  };
}

function launcherIssue(number, createdAt, body = `Please resolve synthetic case ${number}.`) {
  return makeIssue(number, {title: `Backlog issue ${number}`, body, created_at: createdAt, updated_at: '2026-11-05T19:00:00.000Z'});
}

async function launcherHarness(f) {
  const dir = f.base, cwd = f.source, home = f.ports.env.HOME, stateRoot = join(home, '.local/state/pdd/autopilot');
  mkdirSync(stateRoot, {recursive: true});
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', trust: []}}));
  const oldIssue = launcherIssue(17, '2026-11-05T19:00:00.000Z');
  const newIssue = launcherIssue(102, '2026-11-05T19:00:00.000Z');
  const all = [oldIssue];
  const comments = Object.fromEntries(all.map((issue, index) => [issue.number, [reviewComment(issue, all, String(501 + index))]]));
  const graph = await readDependencySnapshot({cwd, repository}, graphPorts({issues: all, comments}));
  let now = baseTime;
  let issueRows = all.map(issue => ({...issue, labels: [], assignees: [], author_association: 'OWNER'}));
  const timerCalls = [], commandCalls = [], herdrCalls = [], prompts = [], packets = [], queryCalls = [];
  let agentStarted = false, workspaceCount = 0, coordinatorStatus = 'idle';
  let coordinatorSnapshot = graph.snapshot;
  const ownerPorts = {read: async () => reply({localOwner: 'launcher-coordinator', claims: [], runs: [], runsKnown: true})};
  const ports = {
    env: {HOME: home, PATH: process.env.PATH},
    stateRoot,
    now: () => now,
    elapsedNow: () => 10,
    sleep: async () => {},
    timer: async (action, state) => { timerCalls.push({action, nextTick: state.nextTick, enabled: state.enabled}); return action === 'start'; },
    selectAgent: async () => ({id: 'offline-fixture', kind: 'codex', command: 'offline-fixture', env: {}}),
    pathDiagnostic: () => [],
    readRunProgress: async () => [],
    allocationCheck: async () => ({ state: 'ready', message: '' }),
    reconcileDependencyIntake: (args, intakePorts) => reconcileDependencyIntake(args, {
      ...intakePorts,
      snapshots: {read: async () => ({snapshot: coordinatorSnapshot})},
      owners: ownerPorts,
    }),
    queryIssues: async () => { queryCalls.push(now); return {status: 200, etag: `"${queryCalls.length}"`, issues: structuredClone(issueRows)}; },
    comments: async () => [],
    pullRequest: async () => ({state: 'closed'}),
    requestArtifact: {
      create: async ({bytes}) => { packets.push(bytes.toString('utf8')); },
      verify: async ({bytes}) => { if (!packets.some(value => Buffer.from(value).equals(bytes))) throw Error('artifact bytes mismatch'); },
    },
    warn: (...args) => console.log("launcher warning", ...args),
    run: async (command, args) => {
      commandCalls.push([command, args]);
      if (command === 'git') {
        if (args[0] === 'rev-parse' && args[1] === '--show-toplevel') return {code: 0, stdout: cwd + '\n', stderr: ''};
        if (args[0] === 'rev-parse' && args.includes('--git-common-dir')) return {code: 0, stdout: cwd + '/.git\n', stderr: ''};
        return {code: 0, stdout: cwd + '\n', stderr: ''};
      }
      if (command === 'gh' && args[0] === 'repo') return {code: 0, stdout: JSON.stringify({nameWithOwner: repository}), stderr: ''};
      if (command === 'gh' && args[0] === 'api' && args.at(-1).endsWith('/permission')) return {code:0, stdout:'HTTP/1.1 200 OK\r\n\r\n{\"permission\":\"admin\"}', stderr:''};
      if (command === 'gh' && args[0] === 'auth') return {code: 0, stdout: '', stderr: ''};
      if (command === 'herdr' && args[0] === '--version') return {code: 0, stdout: 'fixture', stderr: ''};
      throw Error(`Unexpected command in offline launcher fixture: ${command} ${args.join(' ')}`);
    },
    herdr: async args => {
      herdrCalls.push(args);
      if (args[0] === 'workspace' && args[1] === 'create') {
        workspaceCount++;
        return {result: {workspace: {workspace_id: `workspace-${workspaceCount}`}, root_pane: {pane_id: `pane-${workspaceCount}`}}};
      }
      if (args[0] === 'agent' && args[1] === 'get') {
        if (!agentStarted) throw Object.assign(Error('agent not found'), {code: 'agent_not_found'});
        return {result: {agent: {agent_status: coordinatorStatus, agent_session: {kind: 'id', value: 'offline-session-1'}}}};
      }
      if (args[0] === 'pane' && args[1] === 'run') { agentStarted = true; return {}; }
      if (args[0] === 'pane' && args[1] === 'read') return 'Ready\n› ';
      if (args[0] === 'agent' && args[1] === 'prompt') { prompts.push(args[3]); return {}; }
      return {};
    },
  };
  const input = {command: 'start', cwd, env: ports.env, packageRoot: candidate, issues: []};
  const stateId = sha(cwd).slice(0, 20);
  const stateFile = join(stateRoot, `${stateId}.json`);
  return {dir, cwd, home, stateRoot, stateFile, input, ports, oldIssue, newIssue, all,
    get coordinatorStatus() { return coordinatorStatus; }, set coordinatorStatus(value) { coordinatorStatus = value; },
    get graph() { return coordinatorSnapshot; }, set graph(value) { coordinatorSnapshot = value; },
    get issueRows() { return issueRows; }, set issueRows(value) { issueRows = value; },
    get now() { return now; }, set now(value) { now = value; },
    timerCalls, commandCalls, herdrCalls, prompts, packets, queryCalls,
    cleanup() { rmSync(dir, {recursive: true, force: true}); }};
}

function packetNumbers(text) {
  const row = text.split(/\r?\n/).findLast(line => line.startsWith('{') && line.includes('"issues"'));
  if (!row) return [];
  return JSON.parse(row).issues.map(issue => issue.number);
}


test('worker completion waits for coordinator then delivers ready work once', async t => {
  const f = await fixture(t, {name:'bug', agent:'codex'});
  const h = await launcherHarness(f);
  const started = await runAutopilotLauncher(h.input, h.ports);
  assert.equal(started.exitCode, 0, started.message);
  assert.ok(h.packets.some(packet => packetNumbers(packet).includes(17)), 'initial coordinator packet includes issue 17');
  console.log('Initial actual packet issue numbers:', h.packets.map(packetNumbers));
  const state = readAutopilotState(h.stateFile);
  const origin = {repository, coordinatorId:state.coordinatorId, machine:state.machine, claim:{commentId:'11',labelEventId:'12'}};
  const fixturePath=join(f.base,'reader.json'), logPath=join(f.base,'gh.log');
  writeFileSync(fixturePath,JSON.stringify({labels:['pdd:working'],events:[{id:12,event:'labeled',label:{name:'pdd:working'},actor:{login:'example'}}],comments:[{id:11,user:{login:'example'},body:JSON.stringify({...origin, labelEventId:'12'})}]}));
  const {execFile: callback}=await import('node:child_process'); const {promisify}=await import('node:util'); const exec=promisify(callback);
  const original=f.ports.execFile;
  const execFile=(file,args,opts)=>file==='gh' && args[0]==='api' && args[1]==='--include' ? exec(process.execPath,[join(packageRoot,'test/helpers/continuation-fake-gh.mjs'),...args],{...opts,env:{...process.env,READER_FIXTURE_FILE:fixturePath,READER_GH_LOG:logPath}}) : original(file,args,opts);
  let workerDone, coordinatorIdle, observation;
  const workerWait=new Promise(resolve=>workerDone=resolve), coordinatorWait=new Promise(resolve=>coordinatorIdle=resolve);
  const wait=(_session,_pane,until)=>until.includes('done') && !until.includes('idle') ? workerWait : coordinatorWait;
  const ports={...f.ports,execFile,autopilotStateRoot:h.stateRoot,
    checkDependencyStart:(args, readPorts)=>{ const snapshot=structuredClone(h.graph); const subject=snapshot.issues.find(row=>row.key===issueKey(17)); subject.execution='running'; subject.holds=['Claimed']; subject.executionClaim={coordinatorId:origin.coordinatorId,...origin.claim}; const claim={issue:issueKey(17),active:true,owner:origin.coordinatorId,...origin,...origin.claim}; return checkDependencyStart(args,{...readPorts,reviewQueue:{read:async()=>reply({})},settings:{read:async()=>({mode:'auto',activation:state.activatedAt})},snapshots:{read:async()=>({snapshot})},owners:{read:async()=>reply({localOwner:origin.coordinatorId,claims:[claim],runs:[],runsKnown:true})}}); },
    armWorkerCompletion:(identity, options)=>armWorkerCompletion(identity,{...options,spawn:(_cmd,args)=>{observation=waitForWorkerCompletion(JSON.parse(args[1]),{env:options.env,wait,yieldCapacity:(args,observerPorts)=>yieldAutomaticCapacity(args,{...ports,...h.ports,...observerPorts,execFile,herdr:args=>args[2]===state.paneId ? h.ports.herdr(args) : f.herdr.herdr(args)})}); return {on(){},unref(){}};}})};
  const result=await startRun({name:'bug',issue:'17',agent:'codex',cwd:f.source,packageRoot,coordinator:{...origin,activation:state.activatedAt}},ports);
  assert.equal(result.exitCode,0,result.message);
  assert.ok(observation, 'automatic start armed the completion observer');
  const run=f.record(), chat=run.chats.find(c=>c.area===run.areas[run.area].name);
  for (const step of ['reproduce','prompt-story']) {f.tick(); const done=await stepDone({step,summary:step,cwd:run.root},{...ports,isTTY:false,env:{...ports.env,PDD_AGENT_SESSION:'1'}}); assert.equal(done.exitCode,0,done.message);}
  const all=[{...h.oldIssue,labels:[{name:'pdd:working'}]},h.newIssue];
  const comments=Object.fromEntries(all.map((issue,index)=>[issue.number,[reviewComment(issue,all,String(601+index))]]));
  h.graph=(await readDependencySnapshot({cwd:f.source,repository},graphPorts({issues:all,comments}))).snapshot;
  h.issueRows=all.map(issue=>({...issue,assignees:[],author_association:'OWNER'}));
  f.herdr.paneOf(chat).agent.agent_status='done';
  h.coordinatorStatus='working';
  const prior=h.prompts.length; workerDone(); await new Promise(resolve=>setImmediate(resolve));
  assert.equal(h.prompts.length,prior);
  h.coordinatorStatus='idle'; coordinatorIdle(); const delivered=await observation;
  assert.equal(delivered?.exitCode,0,delivered?.message);
  console.log("completion", delivered, "packet numbers", h.packets.map(packetNumbers));
  assert.equal(h.prompts.length,prior+1);
  assert.ok(packetNumbers(h.packets.at(-1)).includes(102));
});

test('automatic open resume and replacement arm their captured attempts', async t => {
  const {openRun} = await import('../src/workflow-runner.mjs');
  const {updateRun} = await import('../src/workflow-runs.mjs');
  const f = await fixture(t, {name:'bug', agent:'codex'});
  assert.equal((await f.run()).exitCode, 0);
  const before = f.record();
  updateRun(before.runDir, run => { run.automaticOrigin = {repository, coordinatorId:'coordinator', machine:'machine', claim:{commentId:'11',labelEventId:'12'}}; return run; }, f.ports);
  const armed = [], ports = {...f.ports, isTTY:false, env:{...f.ports.env, HERDR_SOCKET_PATH:'/sessions/pdd-autopilot/socket', HERDR_PANE_ID:'coordinator'}, armWorkerCompletion: identity => armed.push(identity)};
  const old = f.record().chats.at(-1); f.herdr.paneOf(old).agent = null; f.tick(31000);
  const resumed = await openRun({ref:'17',cwd:f.source,packageRoot}, ports);
  assert.equal(resumed.exitCode, 0, resumed.message);
  assert.equal(armed.length, 1); assert.equal(armed[0].paneId, old.paneId); assert.equal(armed[0].requireActivity, true);
  assert.equal(armed[0].startAnchor, f.record().chats.at(-1).resumedAt);
  const replaced = await openRun({ref:'17',cwd:f.source,packageRoot,newSession:true}, ports);
  assert.equal(replaced.exitCode, 0, replaced.message);
  assert.equal(armed.length, 2); assert.notEqual(armed[1].paneId, old.paneId); assert.notEqual(armed[1].requireActivity, true);
});
