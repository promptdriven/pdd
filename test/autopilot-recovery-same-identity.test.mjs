import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {mkdirSync, writeFileSync, readFileSync, rmSync, realpathSync} from 'node:fs';
import {join} from 'node:path';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {readDependencySnapshot} from '../src/issue-dependencies-github.mjs';
import {reconcileDependencyIntake, checkDependencyStart, prepareDependencyIntake} from '../src/issue-dependencies-intake.mjs';
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
    ...healthyMachine, checkCapacityPorts: isolatedCheckCapacity(dir),
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
      owners: ownerPorts, evidence: {read: async () => reply({source:[],requirements:[]})},
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
      if (command === 'gh' && args[0] === 'repo') return {code: 0, stdout: JSON.stringify({nameWithOwner: repository, defaultBranchRef: { name: 'main' }}), stderr: ''};
      if (command === 'gh' && args[0] === 'api' && args.at(-1).endsWith('/permission')) return {code:0, stdout:'HTTP/1.1 200 OK\r\n\r\n{\"permission\":\"admin\"}', stderr:''};
      if (command === 'gh' && args[0] === 'auth') return {code: 0, stdout: '', stderr: ''};
      if (command === 'herdr' && args[0] === '--version') return {code: 0, stdout: 'fixture', stderr: ''};
      throw Error(`Unexpected command in offline launcher fixture: ${command} ${args.join(' ')}`);
    },
    herdr: async args => {
      herdrCalls.push(args);
      if (args[0] === 'pane' && args[1] === 'list') return {result: {type: 'pane_list', panes: Array.from({length: workspaceCount}, (_, i) => ({pane_id: `pane-${i + 1}`, workspace_id: `workspace-${i + 1}`, tab_id: `tab-${i + 1}`, terminal_id: `terminal-${i + 1}`}))}};
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


test('public start recovers v2 with real intake', async t => {
 const f=await fixture(t,{name:'bug',agent:'codex'}); const h=await launcherHarness(f);
 // A newly observed issue that is claimed elsewhere does not stale the
 // unchanged review of issue 17: 17 stays current and eligible, and the new
 // issue is skipped instead of queued.
 const candidateIssue=makeIssue(103), inputIssues=[h.oldIssue,candidateIssue];
 const input=await readDependencySnapshot({cwd:f.source,repository},graphPorts({issues:inputIssues,comments:{17:[reviewComment(h.oldIssue,[h.oldIssue],'501')]}}));
 const owners={localOwner:'coordinator-a',claims:[{issue:candidateIssue.html_url,active:true,owner:null}],runs:[],runsKnown:true};
 const intakePorts={snapshots:{read:async()=>({snapshot:structuredClone(input.snapshot)})},owners:{read:async()=>reply(owners)},evidence:{read:async()=>reply({source:[],requirements:[]})}};
 const prepared=await prepareDependencyIntake({cwd:f.source,repository},intakePorts);
 assert.deepEqual(prepared.queued,[]); assert.deepEqual(prepared.skipped,[candidateIssue.html_url]);
 const projected=(await import('../src/issue-dependencies.mjs')).projectIssueGraph({snapshot:input.snapshot});
 const oldNode=projected.nodes.find(node=>node.key===h.oldIssue.html_url); assert.equal(oldNode.reviewState,'current'); assert.equal(oldNode.eligible,true);
 const reconciled=await reconcileDependencyIntake({cwd:f.source,repository,trigger:'tick',mode:'auto'},intakePorts);
 assert.deepEqual(reconciled.queued,[]); assert.equal(reconciled.eligible.includes(h.oldIssue.html_url),true);
 const initial=await runAutopilotLauncher(h.input,h.ports); assert.equal(initial.exitCode,0,initial.message);
 const state=JSON.parse(readFileSync(h.stateFile));
 const old={version:2,paneId:state.paneId,workspaceId:state.workspaceId,at:1,fingerprint:'older-distinct-semantic-identity',payloadDigest:'old-payload'};
 const history={kind:'legacy-uncertain',paneId:state.paneId,workspaceId:state.workspaceId,at:0,payloadDigest:'historical-payload'};
 state.reconciliationIntent=old;state.uncertainDeliveryHistory=[history];writeFileSync(h.stateFile,JSON.stringify(state));
 const external=makeIssue(900,{html_url:'https://github.com/example/other/issues/900'});
 const built=await readDependencySnapshot({cwd:f.source,repository},graphPorts({issues:[h.oldIssue,external],brokenPages:[{kind:'comments',issue:900}]}));
 h.graph=built.snapshot; h.graph.coverage.scope=true; const local=h.graph.issues[0]; h.graph.issues.push({...local,key:external.html_url,nodeId:'900',title:'Unrelated external'}); h.graph.coverage.issues.push({...h.graph.coverage.issues[0],key:external.html_url,comments:false,missing:['comments']}); h.graph.warnings=['Unrelated external comments unavailable'];h.issueRows=[{...h.oldIssue,assignees:[],author_association:'OWNER'}];
 console.log('snapshot',JSON.stringify(h.graph));
 let atSend; const originalRun=h.ports.run,originalHerdr=h.ports.herdr;
 h.ports.run=async (cmd,args)=>cmd==='gh'&&args[0]==='repo'?{code:0,stdout:JSON.stringify({nameWithOwner:repository, defaultBranchRef: { name: 'main' },url:`https://github.com/${repository}`}),stderr:''}:originalRun(cmd,args);
 const live={pane_id:state.paneId,workspace_id:state.workspaceId,cwd:h.cwd,foreground_cwd:h.cwd,tab_id:'tab',terminal_id:'terminal',agent:state.agent.kind,agent_status:'idle',agent_session:{kind:'id',value:'offline-session-1'}};
 h.ports.herdr=async args=>{if(args[0]==='agent'&&args[1]==='prompt') atSend=JSON.parse(readFileSync(h.stateFile)); return args[0]==='agent'&&args[1]==='get'?{result:{type:'agent_info',agent:live}}:args[0]==='pane'&&args[1]==='get'?{result:{type:'pane_info',pane:live}}:args[0]==='workspace'&&args[1]==='get'?{result:{type:'workspace_info',workspace:{workspace_id:state.workspaceId}}}:originalHerdr(args)};
 const origIntake=h.ports.reconcileDependencyIntake; h.ports.reconcileDependencyIntake=async (...args)=>{const result=await origIntake(...args);console.log('REAL INTAKE RESULT',JSON.stringify(result));return result};
 const before=h.packets.length;const result=await runAutopilotLauncher(h.input,h.ports); const after=JSON.parse(readFileSync(h.stateFile));
 console.log('RESULT',JSON.stringify({result,packetsBefore:before,packetsAfter:h.packets.length,prompts:h.prompts.length,old,history,afterIntent:after.reconciliationIntent,afterHistory:after.uncertainDeliveryHistory}));
 assert.ok(h.packets.length>before,'fresh coordinator artifact delivered by public start');
 // Simulate an uncertain recovery of the same current semantic request.
 const pending=JSON.parse(readFileSync(h.stateFile)); pending.reconciliationIntent={...atSend.reconciliationIntent,payloadDigest:'unknown-earlier-payload'}; pending.dependencyPending.delivered=null; writeFileSync(h.stateFile,JSON.stringify(pending));
 const priorPrompts=h.prompts.length, priorQueries=h.queryCalls.length; atSend=undefined;
 await runAutopilotLauncher(h.input,h.ports);
 assert.ok(h.queryCalls.length>priorQueries,'fresh scan rereads current issues');
 assert.equal(h.prompts.length,priorPrompts+1,'same semantic identity receives a freshly built packet');
 assert.equal(atSend.reconciliationIntent.fingerprint,pending.reconciliationIntent.fingerprint); assert.notEqual(atSend.reconciliationIntent.payloadDigest,old.payloadDigest); assert.match(h.prompts.at(-1),/fresh current-state reconciliation/);
 assert.ok(atSend.uncertainDeliveryHistory.some(x=>x.payloadDigest==='unknown-earlier-payload' && x.kind==='fresh-reconciliation'));
 const ordinary=JSON.parse(readFileSync(h.stateFile)); ordinary.deliveryIntent={...atSend.reconciliationIntent,payloadDigest:'ordinary-unknown'}; delete ordinary.reconciliationIntent; ordinary.dependencyPending.delivered=null; writeFileSync(h.stateFile,JSON.stringify(ordinary));
 let reject=true; const priorHerdr=h.ports.herdr; h.ports.herdr=async args=>{if(reject && args[0]==='agent' && args[1]==='prompt') {reject=false; throw Object.assign(Error('confirmed rejection'),{code:'agent_blocked'});} return priorHerdr(args);};
 await runAutopilotLauncher(h.input,h.ports);
 const rejected=JSON.parse(readFileSync(h.stateFile));
 assert.ok(rejected.uncertainDeliveryHistory.some(x=>x.payloadDigest==='ordinary-unknown' && x.kind==='ordinary-delivery'));
 assert.equal(rejected.reconciliationIntent,undefined,'confirmed rejection clears the new intent');
 const beforeRetry=h.prompts.length; await runAutopilotLauncher(h.input,h.ports);
 assert.equal(h.prompts.length,beforeRetry+1,'confirmed rejection can retry the same current request');


 assert.deepEqual(after.uncertainDeliveryHistory[0],history); assert.equal(after.uncertainDeliveryHistory[1].payloadDigest,'old-payload'); assert.equal(after.reconciliationIntent,undefined); assert.doesNotMatch(h.prompts.at(-1),/old-payload/); assert.match(h.packets.at(-1),/example\/project\/issues\/17/); console.log('SEND RECEIPT',JSON.stringify({atSendIntent:atSend.reconciliationIntent,finalPending:after.dependencyPending,packetExcerpt:h.packets.at(-1).slice(0,500)}));
});

test('explicit start rearms a current resumed automatic worker from saved activity', async t => {
 const f=await fixture(t,{name:'bug',agent:'codex'}), h=await launcherHarness(f);
 assert.equal((await runAutopilotLauncher(h.input,h.ports)).exitCode,0);
 const state=JSON.parse(readFileSync(h.stateFile,'utf8'));
 assert.equal((await f.run()).exitCode,0);
 const run=f.record(), chat=run.chats.at(-1), anchor=chat.startedAt+100;
 run.automaticOrigin={repository,coordinatorId:state.coordinatorId,machine:state.machine,claim:{commentId:'11',labelEventId:'12'}};
 chat.resumedAt=anchor; chat.completionActivityAnchor=anchor;
 const armed=[];
 const result=await runAutopilotLauncher(h.input,{...h.ports,allRuns:()=>[run],armWorkerCompletion:id=>armed.push(id)});
 assert.equal(result.exitCode,0,result.message);
 assert.equal(armed.length,1); assert.equal(armed[0].paneId,chat.paneId); assert.equal(armed[0].startAnchor,anchor); assert.notEqual(armed[0].requireActivity,true);
});
