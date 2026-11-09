import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, readFileSync, writeFileSync, statSync, readdirSync} from 'node:fs';
import {join} from 'node:path';
import * as runner from '../src/workflow-runner.mjs';
import {runPdd} from '../src/pdd-cli.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const save = (f, run) => writeFileSync(join(run.runDir,'status.json'), JSON.stringify(run));
const effects = f => f.herdr.calls.filter(a => ['create','open','close','run'].includes(a[1]));
async function tidy(f, dryRun = false) {
  let message = '';
  const output = {write: text => {message += text;}};
  const exitCode = await runPdd(['workflow','tidy',...(dryRun ? ['--dry-run'] : [])], {
    cwd:f.source,env:f.ports.env,stdout:output,stderr:output,packageRoot,
    workflowRunner:{tidyRuns: input => runner.tidyRuns(input,f.ports)}
  });
  return {exitCode,message};
}
async function ended(t, agent = 'claude') {
  const f = await fixture(t,{agent}); assert.equal((await f.run()).exitCode,0);
  const run = f.record(); run.state = 'completed'; run.chats[0].endedAt = f.clock;
  save(f,run); f.tick(16*60_000); f.herdr.idle(); f.herdr.paneOf(run.chats[0]).screen = 'saved screen';
  f.herdr.calls.length = 0;
  return {f,run,chat:run.chats[0]};
}

test('2709: tidy closes finished chats, checkpoints durable intent before close and preserves native history', async t => {
  const {f,run,chat} = await ended(t);
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => {
    if (args[0] === 'tab' && args[1] === 'close') {
      const marked = f.record().chats[0];
      assert.equal(marked.closed.reason,'run-end');
      assert.equal(marked.session.id,chat.session.id);
      assert.equal(readFileSync(marked.closed.screen,'utf8'),'saved screen');
      assert.equal(statSync(marked.closed.screen).mode & 0o777,0o600);
    }
    return herdr(args);
  };
  assert.equal((await tidy(f)).exitCode,0);
  assert.equal(f.herdr.paneOf(chat),undefined,'finished pane must be released');
  assert.equal(f.herdr.workspaces.some(w => w.workspace_id === chat.workspaceId),false);
  assert.equal(f.herdr.panes.length,1,'only the repository shell remains');
  assert.ok(existsSync(run.root)); assert.ok(existsSync(chat.messageFile));
  assert.equal(f.record().chats[0].closed.reason,'run-end');
});

for (const condition of ['busy','blocked','own-pane','foreign-terminal','foreign-workspace','split','no-session-no-screen','grace','opened-recently','current-gate']) {
  test(`2709: tidy protects ${condition}`, async t => {
    const {f,run,chat} = await ended(t,condition === 'no-session-no-screen' ? 'gemini' : 'claude');
    const pane = f.herdr.paneOf(chat);
    if (condition === 'busy') pane.agent.agent_status = 'working';
    if (condition === 'blocked') pane.agent.agent_status = 'blocked';
    if (condition === 'own-pane') f.ports.env.HERDR_PANE_ID = chat.paneId;
    if (condition === 'foreign-terminal') pane.terminal_id = 'foreign-terminal';
    if (condition === 'foreign-workspace') f.herdr.workspaces.find(w => w.workspace_id === chat.workspaceId).worktree.checkout_path = f.source;
    if (condition === 'split') f.herdr.panes.push({...pane,pane_id:'split',terminal_id:'split-terminal'});
    if (condition === 'grace') { run.chats[0].endedAt = f.clock; save(f,run); }
    if (condition === 'opened-recently') { run.chats[0].openedAt = f.clock-5*60_000; save(f,run); }
    if (condition === 'current-gate') { run.state = 'waiting'; run.gate = {area:'story',kind:'approve',at:f.clock}; save(f,run); }
    if (condition === 'no-session-no-screen') {
      pane.agent=null;run.chats[0].session=null;save(f,run);
      const h=f.ports.herdr; f.ports.herdr=async args=>{
      if (args[0]==='pane' && args[1]==='read') throw Object.assign(Error('capture unavailable'),{code:'screen_unavailable'});
      return h(args);
    }; }
    const before = f.herdr.panes.length;
    assert.equal((await tidy(f)).exitCode,0);
    assert.equal(f.herdr.panes.length,before);
    assert.equal(f.record().chats[0].closed,undefined);
    assert.equal(effects(f).length,0);
  });
}

test('2709: busy finished agent closes on a later sweep; dry-run has no changes', async t => {
  const {f,chat} = await ended(t);
  const before = readFileSync(join(f.record().runDir,'status.json'));
  assert.equal((await tidy(f,true)).exitCode,0);
  assert.deepEqual(readFileSync(join(f.record().runDir,'status.json')),before);
  assert.equal(effects(f).length,0);
  assert.equal(existsSync(join(f.record().runDir,'chats')),false);
  f.herdr.paneOf(chat).agent.agent_status = 'working';
  assert.equal((await tidy(f)).exitCode,0); assert.ok(f.herdr.paneOf(chat));
  f.herdr.idle(); assert.equal((await tidy(f)).exitCode,0); assert.equal(f.herdr.paneOf(chat),undefined);
});

test('2709: status refresh records completion but does not close Herdr objects', async t => {
  const {f,chat} = await ended(t);
  assert.equal((await runner.runStatus({ref:'17',cwd:f.source},f.ports)).exitCode,0);
  assert.ok(f.herdr.paneOf(chat)); assert.equal(effects(f).length,0);
  assert.equal((await tidy(f)).exitCode,0); assert.equal(f.herdr.paneOf(chat),undefined);
  const shown = await runner.runStatus({ref:'17',cwd:f.source,json:true},f.ports);
  assert.ok(JSON.parse(shown.message).runs[0].chats[0].closed);
});

for (const agent of ['claude','codex']) test(`2709: explicit live open resumes intentionally closed ${agent} immediately`, async t => {
  const {f,run,chat} = await ended(t,agent);
  // Advance to a new area with no recorded chat. The old area remains historical.
  run.state = 'running'; run.areas.push({...run.areas[0],name:'next'}); run.area = run.areas.length-1; save(f,run);
  assert.equal((await tidy(f)).exitCode,0); assert.equal(f.herdr.paneOf(chat),undefined);
  const result = await runner.openRun({ref:'17',area:chat.area,cwd:f.source,packageRoot},f.ports);
  assert.equal(result.exitCode,0,result.message);
  const after = f.record().chats[0];
  assert.notEqual(after.paneId,chat.paneId); assert.equal(after.closed,undefined);
  assert.equal(after.openedAt,f.clock);
  assert.ok(f.herdr.calls.some(a => a[0] === 'pane' && a[1] === 'run' && a[3].includes('resume') && a[3].includes(after.session.id)));
});

test('2709: ended-run open is read-only and gives screen and native resume details', async t => {
  const {f,chat} = await ended(t);
  assert.equal((await tidy(f)).exitCode,0); f.herdr.calls.length = 0;
  const result = await runner.openRun({ref:'17',cwd:f.source,packageRoot},f.ports);
  assert.equal(result.exitCode,0,result.message);
  assert.ok(result.message.includes(f.record().chats[0].closed.screen));
  assert.ok(result.message.includes(chat.session.id)); assert.ok(result.message.includes('CLAUDE_CONFIG_DIR'));
  assert.equal(f.herdr.calls.length,0);
});

test('2709: budget refusal precedes Git allocation and leaves the existing run unchanged', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run = f.record(), bytes = readFileSync(join(run.runDir,'status.json')), branches = f.git(f.source,'branch','--format=%(refname)');
  f.ports.env.PDD_HERDR_PANE_BUDGET = '3'; f.herdr.calls.length = 0;
  const result = await f.run();
  assert.notEqual(result.exitCode,0); assert.match(result.message,/herdr_pane_budget/);
  assert.deepEqual(readFileSync(join(run.runDir,'status.json')),bytes);
  assert.equal(f.git(f.source,'branch','--format=%(refname)'),branches);
  assert.equal(effects(f).length,0);
});

test('2709: budget pressure bypasses grace for safe finished chats', async t => {
  const {f,run,chat} = await ended(t);
  run.chats[0].endedAt = f.clock; save(f,run);
  f.ports.env.PDD_HERDR_PANE_BUDGET = '4';
  const result = await f.run(); assert.equal(result.exitCode,0,result.message);
  assert.equal(f.herdr.paneOf(chat),undefined);
  assert.ok(f.herdr.panes.length <= 4);
  const old = f.record().previous.at(-1);
  assert.equal(JSON.parse(readFileSync(join(old.runDir,'status.json'))).chats[0].closed.reason,'budget');
});

test('2930 and 2929: replacement closes safe chats and explains the stop in the old worktree', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0); f.herdr.idle();
  const old = f.record();
  assert.equal((await f.run()).exitCode,0);
  const replacement = f.record(); assert.notEqual(replacement.runId,old.runId);
  assert.equal(f.herdr.paneOf(old.chats[0]),undefined);
  const retained = JSON.parse(readFileSync(join(replacement.previous.at(-1).runDir,'status.json')));
  assert.equal(retained.runDir,replacement.previous.at(-1).runDir);
  assert.equal(retained.replacedBy,replacement.runId);
  assert.ok(existsSync(retained.chats[0].messageFile));
  const response = await runner.stepDone({step:'reproduce',summary:'late',cwd:old.root},f.ports);
  assert.notEqual(response.exitCode,0); assert.ok(response.message.includes(old.runId)); assert.ok(response.message.includes(replacement.runId));
  assert.equal(f.record().done.reproduce,undefined);
});

test('2930: cancel from replaced worktree retries busy old chats without closing replacement', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const old = f.record(); assert.equal((await f.run()).exitCode,0);
  const replacement = f.record(); assert.ok(f.herdr.paneOf(old.chats[0]));
  const result = await runner.cancelRun({cwd:old.root},f.ports);
  assert.equal(result.exitCode,0,result.message);
  assert.equal(f.herdr.paneOf(old.chats[0]),undefined);
  assert.ok(f.herdr.paneOf(replacement.chats[0])); assert.equal(f.record().state,'running');
});

test('2931: a merged run permits a fresh manual run and retains completed custody', async t => {
  const {f,run} = await ended(t);
  const result = await f.run(); assert.equal(result.exitCode,0,result.message);
  const next = f.record(); assert.notEqual(next.runId,run.runId);
  assert.notEqual(next.root,run.root); assert.ok(existsSync(run.root));
  const old = JSON.parse(readFileSync(join(next.previous.at(-1).runDir,'status.json')));
  assert.equal(old.state,'completed'); assert.equal(old.runId,run.runId);
});

test('2709: capture failure does not prevent a safe close; close failure retains the durable mark and retries', async t => {
  const {f,chat} = await ended(t); const herdr = f.ports.herdr; let refuse = true;
  f.ports.herdr = async args => {
    if (args[0] === 'pane' && args[1] === 'read') throw Object.assign(Error('read'),{code:'read_failed'});
    if (args[0] === 'tab' && args[1] === 'close' && refuse) throw Object.assign(Error('close'),{code:'close_failed'});
    return herdr(args);
  };
  assert.equal((await tidy(f)).exitCode,0); assert.ok(f.herdr.paneOf(chat));
  assert.equal(f.record().chats[0].closed.screen,null);
  refuse = false; assert.equal((await tidy(f)).exitCode,0); assert.equal(f.herdr.paneOf(chat),undefined);
});

test('2930: first explicit cancellation closes the run shell and marks each intentional close', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run = f.record();
  const result = await runner.cancelRun({ref:'17',cwd:f.source},f.ports);
  assert.equal(result.exitCode,0,result.message);
  assert.equal(f.record().layout.phase,'closed');
  assert.equal(f.herdr.panes.length,1);
  assert.equal(f.record().chats[0].closed?.reason,'cancel');
  assert.ok(existsSync(run.root));
});

test('2929: an agent in the archived worktree gets both run identities and cannot change the new run', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const old = f.record(); assert.equal((await f.run()).exitCode,0);
  const replacement = f.record(), bytes = readFileSync(join(replacement.runDir,'status.json'));
  const response = await runner.stepDone({step:'scope',summary:'late',cwd:old.root},f.ports);
  assert.notEqual(response.exitCode,0);
  assert.ok(response.message.includes(old.runId)); assert.ok(response.message.includes(replacement.runId));
  assert.deepEqual(readFileSync(join(replacement.runDir,'status.json')),bytes);
});

test('2709: cleanup rechecks terminal identity after the close checkpoint', async t => {
  const {f,chat} = await ended(t); const herdr = f.ports.herdr; let changed = false;
  f.ports.herdr = async args => {
    if (!changed && args[0] === 'workspace' && args[1] === 'list' && f.record().chats[0].closed) {
      changed = true; f.herdr.paneOf(chat).terminal_id = 'replacement-terminal';
    }
    return herdr(args);
  };
  assert.equal((await tidy(f)).exitCode,0);
  assert.ok(changed); assert.ok(f.herdr.paneOf(chat));
  assert.equal(f.herdr.calls.some(a => a[0] === 'tab' && a[1] === 'close'),false);
});

test('2709: budget cleanup uses global chat age and stops once the next step fits', async t => {
  const a = await fixture(t), b = await fixture(t);
  b.ports.stateDir = a.state; b.ports.herdr = a.ports.herdr; b.herdr = a.herdr;
  assert.equal((await a.run()).exitCode,0); assert.equal((await b.run()).exitCode,0);
  const {startChat} = await import('../src/workflow-chat.mjs');
  const ar = a.record(), br = b.record();
  a.tick(1000);
  const later = await startChat({run:ar,area:'later',message:'finished'}, {...a.ports,checkpoint:async()=>{}});
  ar.chats.push(later); ar.state = br.state = 'completed';
  ar.chats[0].endedAt = a.clock-3000; br.chats[0].endedAt = a.clock-2000; later.endedAt = a.clock-1000;
  save(a,ar); save(b,br); a.herdr.idle();
  a.ports.env.PDD_HERDR_PANE_BUDGET = String(a.herdr.panes.length-1);
  a.herdr.calls.length = 0;
  const sink = {write(){}};
  const exitCode = await runPdd(['workflow','tidy'],{cwd:a.source,env:a.ports.env,stdout:sink,stderr:sink,packageRoot,
    workflowRunner:{tidyRuns: () => runner.tidyRuns({graceMs:0,need:1},a.ports)}});
  assert.equal(exitCode,0);
  assert.deepEqual(a.herdr.calls.filter(x => x[0] === 'tab' && x[1] === 'close').map(x => x[2]),[ar.chats[0].tabId,br.chats[0].tabId]);
  assert.ok(a.herdr.paneOf(later));
});

for (const condition of ['caller-pane','foreign-terminal']) test(`2930: cancel retains ${condition} and reports the reason`, async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const chat = f.record().chats[0];
  if (condition === 'caller-pane') f.ports.env.HERDR_PANE_ID = chat.paneId;
  else f.herdr.paneOf(chat).terminal_id = 'foreign';
  const result = await runner.cancelRun({ref:'17',cwd:f.source},f.ports);
  assert.equal(result.exitCode,0,result.message);
  assert.ok(f.herdr.paneOf(chat));
  const reason = condition === 'caller-pane' ? condition : 'chat-identity';
  assert.ok(result.message.includes(reason));
  assert.deepEqual(f.record().cleanupKept,[{area:chat.area,reason}]);
  assert.equal(f.record().chats[0].closed,undefined);
});

test('2709: unknown Herdr allocation refusal includes the observed pane count', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  assert.equal((await runner.stepDone({step:'scope',summary:'contained change',cwd:f.record().root},f.ports)).exitCode,0);
  f.herdr.paneLimit = f.herdr.panes.length;
  const result = await runner.approveRun({ref:'17',cwd:f.source,packageRoot},f.ports);
  assert.notEqual(result.exitCode,0);
  assert.match(result.message,/test_pane_limit/);
  assert.ok(result.message.includes(String(f.herdr.panes.length)));
  assert.ok(result.message.includes('panes'));
});

test('2709: automatic capacity handoff accepts a deliberately closed pane', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run = f.record(), chat = run.chats[0];
  run.state = 'completed';
  run.automaticOrigin = {repository:run.repo,coordinatorId:'coordinator',machine:'machine',claim:{commentId:'claim',labelEventId:'label'}};
  chat.state = 'ended'; chat.closed = {at:f.clock,reason:'run-end',screen:null,confirmedAt:f.clock}; save(f,run);
  await f.herdr.herdr(['tab','close',chat.tabId]);
  const herdr = f.ports.herdr;
  let handoffs = 0;
  const result = await runner.yieldAutomaticCapacity({ref:'17',cwd:f.source},{...f.ports,
    herdr:async args => {
      if (args[0] === 'agent' && args[1] === 'get') throw Object.assign(Error('missing'),{code:'pane_not_found'});
      return herdr(args);
    }, requestAutopilotCompletion:async()=>{handoffs++;return {state:'inactive'};}
  });
  assert.equal(result.exitCode,0,result.message); assert.equal(handoffs,1);
});

test('3068 coordination: automatic open cannot clear an intentional-close mark', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run = f.record(), chat = run.chats[0];
  chat.closed = {at:f.clock,reason:'run-end',screen:null}; chat.state = 'ended'; save(f,run);
  await f.herdr.herdr(['tab','close',chat.tabId]); f.herdr.calls.length = 0;
  const bytes = readFileSync(join(run.runDir,'status.json'));
  const result = await runner.openRun({ref:'17',cwd:f.source,packageRoot,automaticResume:{coordinatorId:'coordinator',machine:'machine'}},f.ports);
  assert.equal(result.exitCode,0); assert.equal(result.recovery,'skipped');
  assert.equal(f.herdr.calls.length,0); assert.deepEqual(readFileSync(join(run.runDir,'status.json')),bytes);
});
