import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync} from 'node:fs';
import {join} from 'node:path';
import {prepareWorkflowPr, publishWorkflowPr, reconcileWorkflowPr} from '../src/workflow-github.mjs';
import {startRun, stepDone, approveRun} from '../src/workflow-runner.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

// Independent bounded oracle: accepted workflow-draft-publication Story, AC3/4
// and Rules to check. Column order is the complete observation domain below.
// Default readback is preserved; only the literal true observation qualifies a
// requested draft. These expected rows are requirements, not code observations.
const observations = [
  {name:'absent', fields:{}}, {name:'false', fields:{isDraft:false}},
  {name:'true', fields:{isDraft:true}}, {name:'null', fields:{isDraft:null}},
  {name:'string-true', fields:{isDraft:'true'}}, {name:'one', fields:{isDraft:1}},
];
const requests = [
  {name:'absent', fields:{}, createDraftCount:0, expected:['open','open','open','open','open','open']},
  {name:'false', fields:{draft:false}, createDraftCount:0, expected:['open','open','open','open','open','open']},
  {name:'true', fields:{draft:true}, createDraftCount:1, expected:['recovery_required','recovery_required','open','recovery_required','recovery_required','recovery_required']},
];
const stages = ['prompt-pr','code'];
const routes = [
  {name:'existing', existing:true, code:0},
  {name:'create-zero', existing:false, code:0},
  {name:'create-nonzero', existing:false, code:1},
];
const intentKeys = ['baseBranch','headBranch','headSha','marker','repository','runId','stageId','title'];
const cwd = '/synthetic/formal-project', headSha = 'a'.repeat(40);

// All program/GitHub ports are fake here. The production public functions do
// their real preparation, validation, publication and reconciliation work.
function publicationWorld(stage, observation, route) {
  const f = {calls:[], rows:[], remote:null};
  const body = `Synthetic formal proof\n<!-- pdd-workflow:formal-run:${stage} -->\n`;
  const row = () => ({number:42,url:'https://github.com/example/project/pull/42',state:'OPEN',
    headRefName:'topic/formal',baseRefName:'main',headRefOid:headSha,mergeCommit:null,body,
    isCrossRepository:false,headRepository:{name:'project'},headRepositoryOwner:{login:'example'},...observation.fields});
  if (route.existing) f.rows = [row()];
  f.ports = {async execFile(file,args,options) {
    f.calls.push({file,args:[...args],input:options.input});
    const key = [file,...args].join(' ');
    if (key === 'git remote get-url origin' || key === 'git remote get-url --push --all origin')
      return {stdout:'https://github.com/example/project.git'};
    if (file === 'gh' && args[0] === 'repo') return {stdout:JSON.stringify({
      nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'})};
    if (file === 'git' && ['check-ref-format','status'].includes(args[0])) return {stdout:''};
    if (key === 'git rev-parse --show-toplevel') return {stdout:cwd};
    if (file === 'git' && args[0] === 'symbolic-ref') return {stdout:'topic/formal'};
    if (file === 'git' && args[0] === 'rev-parse') return {stdout:headSha};
    if (file === 'git' && args[0] === 'rev-list') return {stdout:'1'};
    if (file === 'git' && args[0] === 'log') return {stdout:'Synthetic formal proof'};
    if (file === 'gh' && args[1] === 'list') return {stdout:JSON.stringify(f.rows)};
    if (file === 'git' && args[0] === 'ls-remote') return f.remote === null
      ? {stdout:'',code:2} : {stdout:`${f.remote}\trefs/heads/topic/formal\n`};
    if (file === 'git' && args[0] === 'push') { f.remote = headSha; return {stdout:''}; }
    if (file === 'gh' && args[1] === 'create') {
      // The observation is independent of argv and create exit status. A create
      // URL claims success in every case, even when readback cannot qualify it.
      assert.equal(options.input,body);
      f.rows = observation.noPr ? [] : [row()];
      return {stdout:'https://github.com/example/project/pull/42\n',code:route.code};
    }
    assert.fail(`Unexpected synthetic port: ${key}`);
  }};
  f.prepare = () => prepareWorkflowPr({cwd,runId:'formal-run',stageId:stage,repository:'example/project',baseBranch:'main'},f.ports);
  f.input = intent => ({cwd,intent,body});
  f.effects = () => f.calls.filter(c => c.file === 'git' && c.args[0] === 'push'
    || c.file === 'gh' && ['create','edit','ready','merge','close'].includes(c.args[1]));
  return f;
}

for (const stage of stages) for (const request of requests) for (const [index,observation] of observations.entries())
  for (const route of routes) test(`formal publication matrix: ${stage}/${request.name}/${observation.name}/${route.name}`,async () => {
    const f = publicationWorld(stage,observation,route), intent = await f.prepare();
    assert.deepEqual(Object.keys(intent).sort(),intentKeys,'prepared intent keeps exactly eight keys');
    const original = structuredClone(intent); f.calls = [];
    const input = {...f.input(intent),...request.fields};
    const out = await publishWorkflowPr(input,f.ports), expected = request.expected[index];
    assert.equal(out.state,expected,'Story AC4: actual readback, never create status/URL, qualifies draft');
    assert.equal(out.pr?.number ?? null,expected === 'open' ? 42 : null);
    assert.equal(out.pr?.url ?? null,expected === 'open' ? 'https://github.com/example/project/pull/42' : null);
    assert.deepEqual(intent,original,'draft cannot alter prepared intent');
    const creates = f.calls.filter(c => c.file === 'gh' && c.args[1] === 'create');
    assert.equal(creates.length,route.existing ? 0 : 1,'no duplicate creation');
    assert.equal(f.calls.filter(c => c.file === 'git' && c.args[0] === 'push').length,route.existing ? 0 : 1);
    for (const create of creates) assert.equal(create.args.filter(a => a === '--draft').length,request.createDraftCount,
      'Story AC1/3: --draft is supplied separately only for a true request');
    assert.equal(f.effects().length,route.existing ? 0 : 2,'no conversion or other PR write');
    const before = structuredClone(f.effects()), rows = structuredClone(f.rows);
    const recovered = await reconcileWorkflowPr({cwd,intent,...request.fields},f.ports);
    assert.equal(recovered.state,expected,'read-only reconciliation obeys the same Story qualification');
    assert.equal(recovered.pr?.number ?? null,expected === 'open' ? 42 : null);
    assert.deepEqual(f.effects(),before,'reconciliation cannot create, push or convert');
    assert.deepEqual(f.rows,rows,'existing ready PR remains unchanged');
  });

for (const stage of stages) for (const request of requests) for (const route of routes.filter(r => !r.existing))
  test(`formal unobserved create: ${stage}/${request.name}/${route.name}`,async () => {
    const f = publicationWorld(stage,{fields:{},noPr:true},route), intent = await f.prepare(); f.calls = [];
    const input = {...f.input(intent),...request.fields};
    assert.equal((await publishWorkflowPr(input,f.ports)).state,'recovery_required',
      'Story: printed create URL alone never proves a successful PR');
    const before = structuredClone(f.effects());
    assert.equal((await reconcileWorkflowPr({cwd,intent,...request.fields},f.ports)).state,'recovery_required');
    assert.deepEqual(f.effects(),before);
    assert.equal(before.filter(c => c.file === 'gh' && c.args[1] === 'create').length,1);
  });

const invalidRequests = [null,0,1,'','true',{},[]];
for (const stage of stages) for (const [index,draft] of invalidRequests.entries())
  test(`formal invalid request: ${stage}/${index}`,async () => {
    const f = publicationWorld(stage,observations[2],routes[0]), intent = await f.prepare(); f.calls = [];
    assert.equal((await publishWorkflowPr({...f.input(intent),draft},f.ports)).state,'failed');
    assert.deepEqual(f.calls,[],'nonboolean publication request refuses before commands');
    assert.equal((await reconcileWorkflowPr({cwd,intent,draft},f.ports)).state,'recovery_required');
    assert.deepEqual(f.calls,[],'nonboolean reconciliation request refuses before commands');
  });

for (const stage of stages) for (const request of requests)
  test(`formal intent separation: ${stage}/${request.name}`,async () => {
    const f = publicationWorld(stage,observations[2],routes[0]), intent = await f.prepare(); f.calls = [];
    assert.equal((await publishWorkflowPr({...f.input({...intent,draft:true}),...request.fields},f.ports)).state,'failed');
    assert.deepEqual(f.calls,[],'draft extra key is not accepted as prepared intent');
  });

// Separate Story-derived truth table for a legitimate, reviewed, unpublished
// story gate. Rows: saved absent/false/true; columns: request absent/false/true.
const savedPolicies = [
  {name:'legacy-absent', fields:{}, approved:[false,false,true], restart:[0,0,1]},
  {name:'false', fields:{draft:false}, approved:[false,false,true], restart:[0,0,1]},
  {name:'true', fields:{draft:true}, approved:[true,true,true], restart:[0,0,0]},
];
const words = 'Synthetic approval words for the reviewed current gate.';
const ok = out => assert.equal(out.exitCode,0,out.message);
async function policyWorld(t) {
  const f = await fixture(t,{name:'bug',agent:'codex'}), config = join(f.base,'formal-dummy-codex');
  mkdirSync(config);
  // No host credentials/profile, native agent, global env change or live port.
  f.ports.env = {HOME:f.ports.env.HOME,CODEX_HOME:config};
  f.start = fields => startRun({name:'bug',issue:'17',agent:'codex',cwd:f.source,packageRoot,...fields},f.ports);
  f.gate = async saved => {
    ok(await f.start({}));
    for (const step of ['reproduce','prompt-story']) {
      f.tick(); ok(await stepDone({step,summary:`Synthetic ${step}`,cwd:f.record().root},f.agentPorts()));
    }
    const r = f.record(); delete r.draft; Object.assign(r,saved.fields); writeRun(r,f.ports);
    assert.deepEqual(f.record().gate.promptSnapshot,[],'real step boundary saved the complete empty review');
  };
  f.snapshot = () => ({record:f.record(),chats:structuredClone(f.herdr.calls),prs:structuredClone(f.prs),pushes:structuredClone(f.pushes)});
  return f;
}

for (const [index,request] of requests.entries()) test(`formal fresh start policy: ${request.name}`,async t => {
  const f = await policyWorld(t), seen = [], herdr = f.ports.herdr;
  f.ports.herdr = async args => { seen.push(f.record().draft); return herdr(args); };
  ok(await f.start(request.fields));
  assert.equal(f.record().draft,[false,false,true][index]);
  assert.ok(seen.length > 0); assert.ok(seen.every(value => value === [false,false,true][index]),'policy durable before fake chat startup');
});

for (const saved of savedPolicies) for (const [index,request] of requests.entries()) {
  test(`formal legitimate approval policy: ${saved.name}/${request.name}`,async t => {
    const f = await policyWorld(t); await f.gate(saved);
    const before = f.record(), gateId = before.gate.id;
    ok(await approveRun({ref:'17',cwd:f.source,said:words,...request.fields},f.agentPorts()));
    const after = f.record();
    // Legacy missing may remain absent for a default request; its policy is false.
    assert.equal(after.draft ?? false,saved.approved[index],'Story: false/omission cannot downgrade true');
    assert.equal(after.decisions.length,before.decisions.length+1);
    assert.equal(after.decisions.at(-1).gateId,gateId,'only current gate consent is used');
    assert.equal(after.decisions.at(-1).evidence.words,words);
    assert.equal(after.areas[after.area].name,'prompt-pr','story approval cannot start code');
    assert.deepEqual(f.prs,[]); assert.deepEqual(f.pushes,[]);
  });
  test(`formal active start policy: ${saved.name}/${request.name}`,async t => {
    const f = await policyWorld(t); await f.gate(saved); const before = f.snapshot();
    const out = await f.start(request.fields);
    assert.equal(out.exitCode,saved.restart[index],'Story: start cannot replace active nondraft policy');
    if (saved.restart[index] === 1) {
      assert.deepEqual(f.snapshot(),before,'requested strengthening cannot replace an active nondraft run');
    } else {
      // Ordinary explicit restart retains the preexisting replacement contract.
      // Same-run monotonicity is checked above; this is a distinct fresh run.
      assert.notEqual(f.record().runId,before.record.runId);
      assert.equal(f.record().draft,[false,false,true][index],'fresh replacement uses the requested new-run policy');
      assert.deepEqual(f.prs,[]); assert.deepEqual(f.pushes,[]);
    }
  });
  test(`formal refused approval policy: ${saved.name}/${request.name}`,async t => {
    const f = await policyWorld(t); await f.gate(saved);
    const r = f.record(); delete r.gate.promptSnapshot; writeRun(r,f.ports);
    const before = f.snapshot();
    assert.equal((await approveRun({ref:'17',cwd:f.source,said:words,...request.fields},f.agentPorts())).exitCode,1);
    assert.deepEqual(f.snapshot(),before,'Story: absent current review permits no policy adoption, consent, chat or publication');
  });
}
