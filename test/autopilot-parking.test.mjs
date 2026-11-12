import './helpers/test-home.mjs';
import test from 'node:test';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
import {existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {readRunResults} from '../src/workflow-results.mjs';
import {tickAutopilot, runAutopilotLauncher} from '../src/autopilot-launcher.mjs';
import {runStatus, parkAutomaticRun, changeRun, startRun, openRun} from '../src/workflow-runner.mjs';
import {createDependencyReadPorts} from '../src/issue-dependencies-github.mjs';
import {checkDependencyStart} from '../src/issue-dependencies-intake.mjs';

const save = (f, run) => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
const launches = f => f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run');
const deliveries = f => f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'prompt');
const fixtureClaimRows = f => {
  const folder = join(f.record().commonDir, 'pdd', 'runs');
  try { return readdirSync(folder).filter(name => /^[1-9][0-9]*(?:-cancelled-[0-9a-f]+)?$/.test(name))
    .map(name => JSON.parse(readFileSync(join(folder, name, 'status.json'), 'utf8')))
    .filter(run => run.automaticOrigin && !['completed', 'cancelled'].includes(run.state))
    .map(run => ({issue:run.issue.url, active:true, owner:run.automaticOrigin.coordinatorId,
      coordinatorId:run.automaticOrigin.coordinatorId, machine:run.automaticOrigin.machine,
      ...run.automaticOrigin.claim})); }
  catch { return []; }
};

// #3091 final review: exercise saved-batch inference through the production reader.
// #3091: saved-check identity must be current even when only one input changes.
async function setup(t, agent = 'claude', name = 'small-change') {
  const f = await fixture(t, {agent, name});
  assert.equal((await f.run()).exitCode, 0);
  assert.equal((await runStatus({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  f.herdr.idle(); // This fixture represents a stopped worker, not a busy turn.
  const run = f.record();
  run.automaticOrigin = {repository: run.repo, coordinatorId: 'park-owner', machine: 'park-machine', claim: {commentId: '11', labelEventId: '12'}};
  save(f, run);
  f.ports.owners = {read: async input => ({json: JSON.stringify({localOwner: 'park-owner',
    claims: input.issues.map(issue => ({issue, active: true, owner: 'park-owner', coordinatorId: 'park-owner',
      machine: 'park-machine', commentId: '11', labelEventId: '12'}))})})};
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', trust: []}}));
  const stateFile = join(f.state, 'launcher.json');
  writeFileSync(stateFile, JSON.stringify({enabled: true, defaultBranch: 'main', baseBranch: 'main', stateFile,
    cwd: f.source, repo: run.repo, packageRoot, runs: 1, coordinatorId: 'park-owner', machine: 'park-machine', activatedAt: 1,
    agent: {id: agent, kind: agent, command: agent}, environment: f.ports.env, retryAt: f.clock + 86400000}));
  const warnings = [];
  const ports = {...healthyMachine, ...f.ports, sendDigest: async () => ({exitCode: 0}),
    checkCapacityPorts: isolatedCheckCapacity(f.base), run: async (file, args, options) => ({code: 0, ...await f.ports.execFile(file, args, options)}),
    reconcileDependencyIntake: async () => ({eligible:[], claims:fixtureClaimRows(f), groups:[], queued:[], skipped:[]}),
    refreshClaimHeartbeat: async ({at}) => ({state:'refreshed',lastSeen:at}),
    warn: message => warnings.push(message)};
  f.herdr.calls.length = 0;
  return {f, run, stateFile, ports, warnings, tick: () => tickAutopilot(stateFile, ports)};
}
test('3091 explicit installed-release and reset blockers are stored with clearing evidence', async t => {
  const {f} = await setup(t);
  for (const [blocker, until] of [['pdd', 'capability:fixture-fix'], ['dependency', '2897'], ['account', '2026-11-10T12:00:00Z']]) {
    const result = await parkAutomaticRun({cwd: f.record().root, reason: 'Controlled external wait', blocker, until}, {...f.ports, owners: {read: async () => ({json: JSON.stringify({localOwner: 'park-owner', runsKnown: true, runs: [], claims: [{issue: f.record().issue.url, active: true, owner: 'park-owner', coordinatorId: 'park-owner', machine: 'park-machine', commentId: '11', labelEventId: '12'}]})})}});
    assert.equal(result.exitCode, 0, result.message);
    assert.deepEqual(f.record().blockedOn, {kind: blocker, until}, '3091: preserve the explicit clearing condition');
  }
});

async function anotherRun(f, number) {
  const execute = f.ports.execFile;
  f.ports.execFile = async (file, args, options) => {
    if (file === 'gh' && args[0] === 'api' && args[1] === `repos/example/project/issues/${number}`)
      return {stdout: JSON.stringify({number, html_url: `https://github.com/example/project/issues/${number}`, title: 'Independent work', body: 'Use another value.'})};
    return execute(file, args, options);
  };
  assert.equal((await startRun({name: 'small-change', issue: String(number), agent: 'claude', cwd: f.source, packageRoot}, f.ports)).exitCode, 0);
  assert.equal((await runStatus({ref: String(number), cwd: f.source}, f.ports)).exitCode, 0);
  const path = join(f.record().commonDir, 'pdd', 'runs', String(number), 'status.json');
  f.herdr.idle(); // The additional run is also stopped before parking.
  const run = JSON.parse(readFileSync(path)); run.automaticOrigin = f.record().automaticOrigin;
  run.state = 'paused'; run.blockedOn = {kind: 'pdd', until: 'capability:fixture-fix'};
  save(f, run);
  return () => JSON.parse(readFileSync(path));
}

function fullTicks(f, stateFile, ports) {
  const state = JSON.parse(readFileSync(stateFile)); delete state.retryAt; state.recipeDelivered = true;
  writeFileSync(stateFile, JSON.stringify(state));
  ports.reconcileDependencyIntake = async () => ({eligible: [], claims: fixtureClaimRows(f), groups: [], queued: [], skipped: []});
  ports.queryIssues = async () => ({status: 200, issues: []});
  ports.comments = async () => [];
  const herdr = ports.herdr;
  ports.herdr = async args => {
    if (args[0] === 'pane' && args[1] === 'get') {
      const pane = f.herdr.panes.find(pane => pane.pane_id === args[2]);
      if (!pane) throw Object.assign(Error('pane_not_found'), {code: 'pane_not_found'});
      return {result: {type: 'pane_info', pane: {...pane, foreground_cwd: pane.cwd, ...pane.agent}}};
    }
    return herdr(args);
  };
  ports.runtimeHealth = async () => ({state: 'healthy', detail: 'controlled health'});
  ports.sendAlert = async () => ({exitCode: 0});
}

// Repair 1: AC3/AC6. A release and a reply must not both acquire the run.
// AC3: both clear in the same tick, with only one working slot.
// AC1/AC3: the park command cannot invent a completed person wait.
// AC4: use the native wait reader and real saved check batches in the fixture home.
// Repair 2: AC2/AC6. Check admission can occur after chat shutdown.
// The release boundary must protect itself even without a prior reconciliation.
const parkCommandPorts = f => ({...f.ports, owners: {read: async () => ({json: JSON.stringify({
  localOwner: 'park-owner', runsKnown: true, runs: [], claims: [{issue: f.record().issue.url, active: true,
    owner: 'park-owner', coordinatorId: 'park-owner', machine: 'park-machine', commentId: '11', labelEventId: '12'}],
})})}});

// AC1/AC3. Replacing the wait must replace its clearing condition.
// AC4. Late saved verdicts reorder events already observed on a previous tick.
// AC4. A scan without a result must not exclude the first late completion.
// AC2/AC3. A reply after backfill must join admission, not launch over capacity.
// #3091 gap: these records were stopped before the installed coordinator knew parking.
test('3157: release holds the run lock and refuses check or worker custody without changing the run or labels', async t => {
  const {runAutopilotLauncher} = await import('../src/autopilot-launcher.mjs');
  const {acquireRunLock} = await import('../src/workflow-runner.mjs');
  const {createGithubRepoFake} = await import('./helpers/github-repo-fake.mjs');
  const {f,ports}=await setup(t);
  const run=f.record();run.state='paused';run.blockedOn={kind:'pdd',until:'capability:fixture-fix'};save(f,run);
  const workerPane=f.herdr.paneOf(run.chats.at(-1));
  const github=createGithubRepoFake({repository:run.repo,owner:'example',issues:18,now:()=>f.clock});
  const comment=github.claim(17,{coordinatorId:run.automaticOrigin.coordinatorId,machine:run.automaticOrigin.machine});
  github.label(17,'pdd:stuck');
  const parked=f.record();parked.automaticOrigin.claim={commentId:comment.id,labelEventId:github.issues.get(17).timeline.find(e=>e.label==='pdd:working').id};save(f,parked);
  const launcherPorts={...ports,authority:{read:async()=>({authority:'trusted'})},run:async(file,args,options)=>{
    if(file==='gh'&&args[0]==='api')return github.gh(args,options);
    if(file==='gh'&&args[0]==='repo')return{code:0,stdout:JSON.stringify({nameWithOwner:run.repo,url:`https://github.com/${run.repo}`,defaultBranchRef:{name:'main'}}),stderr:''};
    return ports.run(file,args,options);
  }};
  const release=()=>runAutopilotLauncher({command:'release',cwd:f.source,env:f.ports.env,issues:['17']},launcherPorts);
  const unlock=acquireRunLock(run.runDir);
  let locked;try{locked=await release();}finally{unlock();}
  assert.equal(locked.exitCode,1);assert.equal(f.record().state,'paused');
  assert.deepEqual(github.issues.get(17).labels.sort(),['pdd:stuck','pdd:working']);
  launcherPorts.readSuiteProgress=()=>({state:'running'});
  const heldCheck=await release();assert.equal(heldCheck.exitCode,1);assert.equal(f.record().state,'paused');
  assert.deepEqual(github.issues.get(17).labels.sort(),['pdd:stuck','pdd:working']);
  launcherPorts.readSuiteProgress=()=>({state:'idle'});
  workerPane.agent.agent_status='working';
  const heldWorker=await release();assert.equal(heldWorker.exitCode,1);assert.equal(f.record().state,'paused');
  assert.deepEqual(github.issues.get(17).labels.sort(),['pdd:stuck','pdd:working']);
});

test('3157: release refuses an unattributed working label',async t=>{
  const {releaseParkedClaim}=await import('../src/issue-dependencies-github.mjs');
  const {createGithubRepoFake}=await import('./helpers/github-repo-fake.mjs');
  const {f,run,ports}=await setup(t);
  const github=createGithubRepoFake({repository:run.repo,owner:'example',issues:18,now:()=>f.clock});
  github.label(17,'pdd:working');github.label(17,'pdd:stuck');
  const releasePorts={...ports,authority:{read:async()=>({authority:'trusted'})},execFile:async(file,args,options)=>
    file==='gh'&&args[0]==='api'?github.gh(args,options):f.ports.execFile(file,args,options)};
  const result=await releaseParkedClaim({cwd:f.source,repository:run.repo,claim:{issue:run.issue.url},machine:'park-machine',reason:'release'},releasePorts);
  assert.deepEqual(result,{state:'refused',machine:'unknown'});
  assert.deepEqual(github.issues.get(17).labels.sort(),['pdd:stuck','pdd:working']);
});

function wireClaimGithub(f, ports, github) {
  const originalRun = ports.run, originalExec = f.ports.execFile;
  ports.authority = {read: async () => ({authority: 'trusted'})};
  ports.run = async (file, args, options) => file === 'gh' && args[0] === 'api' ? github.gh(args, options) : originalRun(file, args, options);
  ports.execFile = f.ports.execFile = async (file, args, options) => file === 'gh' && args[0] === 'api' ? github.gh(args, options) : originalExec(file, args, options);
}

function installClaimEra(github, run, {coordinatorId = run.automaticOrigin.coordinatorId,
  machine = run.automaticOrigin.machine, lastSeen = new Date(github.now()).toISOString()} = {}) {
  const comment = github.claim(17, {coordinatorId, machine});
  const eventId = github.issues.get(17).timeline.filter(event => event.label === 'pdd:working').at(-1).id;
  github.editComment(17, comment.id, `Autopilot claim.\n\n\`\`\`json\n${JSON.stringify({
    repository: run.repo, coordinatorId, machine, labelEventId: eventId, lastSeen,
  })}\n\`\`\``);
  run.automaticOrigin.claim = {commentId: comment.id, labelEventId: eventId};
  return {comment, eventId, coordinatorId, machine};
}

test('3157: legacy parked release finishes old working-first cleanup and preserves a replacement claim', async t => {
  const {releaseParkedClaim} = await import('../src/issue-dependencies-github.mjs');
  const {createGithubRepoFake} = await import('./helpers/github-repo-fake.mjs');
  const {f, ports} = await setup(t), run = f.record();
  const github = createGithubRepoFake({repository: run.repo, owner: 'example', issues: 18, now: () => f.clock});
  const old = installClaimEra(github, run);
  const oldRecord = JSON.parse(/```json\n([\s\S]*?)\n```/.exec(old.comment.body)[1]);
  oldRecord.parkRelease = {runId: run.runId, branch: run.branch};
  github.editComment(17, old.comment.id, `Autopilot claim.\n\n\`\`\`json\n${JSON.stringify(oldRecord)}\n\`\`\``);
  github.label(17, 'pdd:stuck');
  github.unlabel(17, 'pdd:working');
  assert.deepEqual(github.issues.get(17).labels, ['pdd:stuck'], 'legacy partial cleanup has no working label but retains its old stuck label');
  wireClaimGithub(f, ports, github);
  const input = {cwd: f.source, repository: run.repo,
    claim: {issue: run.issue.url, coordinatorId: old.coordinatorId, machine: old.machine,
      commentId: old.comment.id, labelEventId: old.eventId},
    coordinatorId: old.coordinatorId, machine: old.machine, runId: run.runId, branch: run.branch};
  const deleted = [], execute = ports.execFile;
  ports.execFile = f.ports.execFile = async (file, args, options) => {
    const path = args.find(arg => arg.includes('/labels/'));
    if (file === 'gh' && args[0] === 'api' && args.includes('--method')
      && args[args.indexOf('--method') + 1] === 'DELETE' && path) deleted.push(path.split('/labels/').at(-1));
    return execute(file, args, options);
  };
  const resumed = await releaseParkedClaim(input, ports);
  assert.equal(resumed.state, 'released');
  assert.deepEqual(github.issues.get(17).labels, []);
  assert.deepEqual(deleted, ['pdd%3Astuck'], 'retry completes the saved old state without another working-label delete');
  assert.match(github.issues.get(17).comments.find(comment => comment.id === old.comment.id).body,
    new RegExp(`parkRelease.*${run.runId}`));

  const replacement = installClaimEra(github, run, {coordinatorId: 'replacement-coordinator', machine: old.machine});
  github.label(17, 'pdd:stuck');
  const replaced = await releaseParkedClaim(input, ports);
  assert.equal(replaced.state, 'skipped');
  assert.notEqual(replacement.comment.id, old.comment.id);
  assert.deepEqual(deleted, ['pdd%3Astuck'], 'the old saved marker cannot delete labels from the replacement era');
  assert.deepEqual([...github.issues.get(17).labels].sort(), ['pdd:stuck', 'pdd:working']);
});

for (const checkState of ['running', 'unavailable'])
  test(`3157: manual cancel retains local and remote ownership when a check is ${checkState}`, async t => {
    const {cancelRun} = await import('../src/workflow-runner.mjs');
    const {createGithubRepoFake} = await import('./helpers/github-repo-fake.mjs');
    const {f, ports} = await setup(t);
    const run = f.record(), github = createGithubRepoFake({repository: run.repo, owner: 'example', issues: 18, now: () => f.clock});
    installClaimEra(github, run); save(f, run); github.label(17, 'pdd:stuck');
    ports.readSuiteProgress = () => ({state: checkState});
    wireClaimGithub(f, ports, github);
    await cancelRun({ref: '17', cwd: f.source}, ports);
    const allocation = join(run.commonDir, 'pdd/worktree-assignments/issues/17.json');
    assert.ok(existsSync(allocation), 'local issue ownership stays allocated');
    assert.equal(JSON.parse(readFileSync(allocation, 'utf8')).runId, run.runId);
    assert.deepEqual(github.issues.get(17).labels.sort(), ['pdd:stuck', 'pdd:working']);
    assert.equal(f.record().claimRelease?.state, 'pending');
  });

test('3157: manual cancel retains ownership when Herdr keeps a chat', async t => {
  const {cancelRun} = await import('../src/workflow-runner.mjs');
  const {createGithubRepoFake} = await import('./helpers/github-repo-fake.mjs');
  const {f, ports} = await setup(t), run = f.record();
  const github = createGithubRepoFake({repository: run.repo, owner: 'example', issues: 18, now: () => f.clock});
  installClaimEra(github, run); save(f, run); github.label(17, 'pdd:stuck');
  const herdr = ports.herdr;
  ports.herdr = async args => {
    if (args[0] === 'workspace' && args[1] === 'list') throw Object.assign(Error('controlled inventory outage'), {code: 'inventory_unavailable'});
    return herdr(args);
  };
  wireClaimGithub(f, ports, github);
  await cancelRun({ref: '17', cwd: f.source}, ports);
  const allocation = join(run.commonDir, 'pdd/worktree-assignments/issues/17.json');
  assert.ok(existsSync(allocation), 'local issue ownership stays allocated');
  assert.equal(JSON.parse(readFileSync(allocation, 'utf8')).runId, run.runId);
  assert.deepEqual(github.issues.get(17).labels.sort(), ['pdd:stuck', 'pdd:working']);
  assert.equal(f.record().claimRelease?.state, 'pending');
  assert.ok(f.herdr.paneOf(run.chats.at(-1)), 'the retained chat remains in Herdr');
});

test('3157: explicit release retains ownership after idle preflight when Herdr inventory fails', async t => {
  const {releaseRunClaim} = await import('../src/workflow-runner.mjs');
  const {createGithubRepoFake} = await import('./helpers/github-repo-fake.mjs');
  const {f, ports} = await setup(t), run = f.record();
  const github = createGithubRepoFake({repository: run.repo, owner: 'example', issues: 18, now: () => f.clock});
  installClaimEra(github, run); save(f, run); github.label(17, 'pdd:stuck');
  ports.readSuiteProgress = () => ({state: 'idle'});
  let inventoryAttempts = 0;
  const herdr = ports.herdr;
  ports.herdr = async args => {
    if (args[0] === 'workspace' && args[1] === 'list') {inventoryAttempts++; throw Object.assign(Error('controlled inventory outage'), {code: 'inventory_unavailable'});}
    return herdr(args);
  };
  wireClaimGithub(f, ports, github);
  await releaseRunClaim({ref: '17', cwd: f.source}, ports);
  assert.equal(inventoryAttempts, 1, 'the idle preflight passes before the cleanup inventory failure');
  const allocation = join(run.commonDir, 'pdd/worktree-assignments/issues/17.json');
  assert.ok(existsSync(allocation), 'local issue ownership stays allocated');
  assert.equal(JSON.parse(readFileSync(allocation, 'utf8')).runId, run.runId);
  assert.deepEqual(github.issues.get(17).labels.sort(), ['pdd:stuck', 'pdd:working']);
  assert.equal(f.record().claimRelease?.state, 'pending');
  assert.ok(f.herdr.paneOf(run.chats.at(-1)), 'idle preflight does not erase Herdr custody after inventory fails');
});

test('3157: explicit release of saved claim era A preserves same-machine replacement era B', async t => {
  const {releaseRunClaim} = await import('../src/workflow-runner.mjs');
  const {createGithubRepoFake} = await import('./helpers/github-repo-fake.mjs');
  const {f, ports} = await setup(t), run = f.record();
  const github = createGithubRepoFake({repository: run.repo, owner: 'example', issues: 18, now: () => f.clock});
  const eraA = installClaimEra(github, run);
  github.unlabel(17, 'pdd:working');
  const savedEraA = {commentId: eraA.comment.id, labelEventId: eraA.eventId};
  installClaimEra(github, run, {coordinatorId: 'replacement-coordinator', machine: 'park-machine'});
  github.label(17, 'pdd:stuck');
  run.automaticOrigin.claim = savedEraA;
  save(f, run);
  wireClaimGithub(f, ports, github);
  await releaseRunClaim({ref: '17', cwd: f.source}, ports);
  assert.deepEqual(github.issues.get(17).labels.sort(), ['pdd:stuck', 'pdd:working']);
});

test('3157: release rechecks claim identity after stuck removal before working removal', async t => {
  const {releaseParkedClaim} = await import('../src/issue-dependencies-github.mjs');
  const {createGithubRepoFake} = await import('./helpers/github-repo-fake.mjs');
  const {f, ports} = await setup(t), run = f.record();
  const github = createGithubRepoFake({repository: run.repo, owner: 'example', issues: 18, now: () => f.clock});
  const old = installClaimEra(github, run);
  save(f, run); github.label(17, 'pdd:stuck');
  wireClaimGithub(f, ports, github);
  const deleted = [], execute = ports.execFile;
  let replaced = false;
  ports.execFile = f.ports.execFile = async (file, args, options) => {
    const path = args.find(arg => arg.includes('/labels/'));
    const deleting = file === 'gh' && args[0] === 'api' && args.includes('--method')
      && args[args.indexOf('--method') + 1] === 'DELETE' && path;
    if (deleting) deleted.push(path.split('/labels/').at(-1));
    const result = await execute(file, args, options);
    if (deleting && !replaced) {
      replaced = true;
      if (github.issues.get(17).labels.includes('pdd:working')) github.unlabel(17, 'pdd:working');
      installClaimEra(github, run, {coordinatorId: 'replacement-coordinator', machine: old.machine});
      if (!github.issues.get(17).labels.includes('pdd:stuck')) github.label(17, 'pdd:stuck');
    }
    return result;
  };
  const result = await releaseParkedClaim({
    cwd: f.source, repository: run.repo,
    claim: {issue: run.issue.url, coordinatorId: old.coordinatorId, machine: old.machine,
      commentId: old.comment.id, labelEventId: old.eventId},
    coordinatorId: old.coordinatorId, machine: old.machine, reason: 'release',
  }, ports);
  assert.equal(replaced, true);
  assert.deepEqual(deleted, ['pdd%3Astuck']);
  assert.equal(result.state, 'skipped');
  assert.deepEqual([...github.issues.get(17).labels].sort(), ['pdd:stuck', 'pdd:working']);
});

test('3157: manual cancel contends on the existing run lock used by coordinator recovery', async t => {
  const {cancelRun, acquireRunLock, recoverAutomaticRunOwner} = await import('../src/workflow-runner.mjs');
  const {createGithubRepoFake} = await import('./helpers/github-repo-fake.mjs');
  const {f, ports} = await setup(t), run = f.record();
  const github = createGithubRepoFake({repository: run.repo, owner: 'example', issues: 18, now: () => f.clock});
  installClaimEra(github, run); save(f, run); github.label(17, 'pdd:stuck');
  wireClaimGithub(f, ports, github);
  let recoveryCalls = 0;
  ports.recoverCoordinatorClaim = async () => { recoveryCalls++; return {state: 'recovered'}; };
  const herdrCalls = f.herdr.calls.length, unlock = acquireRunLock(run.runDir);
  let recovery, cancelled;
  try {
    recovery = await recoverAutomaticRunOwner({ref: '17', cwd: f.source,
      coordinatorId: run.automaticOrigin.coordinatorId, machine: run.automaticOrigin.machine}, ports);
    cancelled = await cancelRun({ref: '17', cwd: f.source}, ports);
  } finally { unlock(); }
  assert.notEqual(recovery.exitCode, 0);
  assert.notEqual(cancelled.exitCode, 0);
  assert.equal(recoveryCalls, 0);
  assert.equal(f.herdr.calls.length, herdrCalls);
  assert.equal(f.record().state, run.state);
  assert.equal(f.record().claimRelease, undefined);
  assert.deepEqual([...github.issues.get(17).labels].sort(), ['pdd:stuck', 'pdd:working']);
  const retry = await cancelRun({ref: '17', cwd: f.source}, ports);
  assert.equal(retry.exitCode, 0, retry.message);
  assert.equal(f.record().state, 'cancelled');
  assert.deepEqual(github.issues.get(17).labels, []);
});

test('3157: repeated cancel recovers both lost label acknowledgements', async t => {
  const {cancelRun} = await import('../src/workflow-runner.mjs');
  const {createGithubRepoFake} = await import('./helpers/github-repo-fake.mjs');
  const {f, ports} = await setup(t), run = f.record();
  const github = createGithubRepoFake({repository: run.repo, owner: 'example', issues: 18, now: () => f.clock});
  installClaimEra(github, run); save(f, run); github.label(17, 'pdd:stuck');
  wireClaimGithub(f, ports, github);
  const lostAck = new Set(['pdd%3Astuck', 'pdd%3Aworking']), deleted = [];
  const execute = ports.execFile;
  ports.execFile = f.ports.execFile = async (file, args, options) => {
    const path = args.find(arg => arg.includes('/labels/'));
    const deleting = file === 'gh' && args[0] === 'api' && args.includes('--method')
      && args[args.indexOf('--method') + 1] === 'DELETE' && path;
    const label = deleting ? path.split('/labels/').at(-1) : null;
    if (label) deleted.push(label);
    const result = await execute(file, args, options);
    if (label && lostAck.delete(label)) throw Error('controlled lost label-delete acknowledgement');
    return result;
  };
  const cancel = () => cancelRun({ref: '17', cwd: f.source}, ports);
  const first = await cancel();
  assert.equal(first.exitCode, 0);
  assert.deepEqual([...github.issues.get(17).labels], ['pdd:working']);
  assert.equal(f.record().claimRelease?.state, 'pending');
  const second = await cancel();
  assert.equal(second.exitCode, 0);
  assert.deepEqual(github.issues.get(17).labels, []);
  assert.equal(f.record().claimRelease?.state, 'pending');
  const third = await cancel();
  assert.equal(third.exitCode, 0);
  assert.deepEqual(github.issues.get(17).labels, []);
  assert.equal(f.record().claimRelease, undefined);
  assert.deepEqual(deleted, ['pdd%3Astuck', 'pdd%3Aworking']);
});

test('3157: cancel keeps retry state when local allocation is unreadable and remote labels are already clear', async t => {
  const {cancelRun} = await import('../src/workflow-runner.mjs');
  const {createGithubRepoFake} = await import('./helpers/github-repo-fake.mjs');
  const {renameSync, rmSync, mkdirSync} = await import('node:fs');
  const {f, ports} = await setup(t), run = f.record();
  const github = createGithubRepoFake({repository: run.repo, owner: 'example', issues: 18, now: () => f.clock});
  installClaimEra(github, run); save(f, run); github.label(17, 'pdd:stuck');
  wireClaimGithub(f, ports, github);
  github.unlabel(17, 'pdd:working');
  github.unlabel(17, 'pdd:stuck');
  assert.deepEqual(github.issues.get(17).labels, [], 'remote labels are already clear before cancellation');
  const allocation = join(run.commonDir, 'pdd/worktree-assignments/issues/17.json'), unreadable = `${allocation}.unreadable`;
  renameSync(allocation, unreadable);
  mkdirSync(allocation);
  try {
    await cancelRun({ref: '17', cwd: f.source}, ports);
    assert.equal(JSON.parse(readFileSync(unreadable, 'utf8')).runId, run.runId, 'the saved local allocation remains available for recovery');
    assert.deepEqual(github.issues.get(17).labels, []);
    assert.equal(f.record().claimRelease?.state, 'pending');
  } finally {
    rmSync(allocation, {recursive: true, force: true});
    renameSync(unreadable, allocation);
  }
});

