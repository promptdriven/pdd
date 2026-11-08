import test from 'node:test';
import assert from 'node:assert/strict';
import {pathToFileURL} from 'node:url';
import {resolve} from 'node:path';
import {mergeWorld} from './helpers/autopilot-merge-world.mjs';

// This selector replays the same public CLI expectations on an archived base.
const source = process.env.PDD_MERGE_TEST_SOURCE;
const {runPdd} = await import(source ? pathToFileURL(resolve(source,'src/pdd-cli.mjs')).href : '../src/pdd-cli.mjs');
async function invoke(w,{observe=false} = {}) {
  let stdout='',stderr='';
  const exitCode = await runPdd(['autopilot','merge','17','--input','-',...(observe ? ['--observe'] : [])],{
    cwd:'/synthetic/repo',stdin:JSON.stringify(w.evidence),autopilotMergePorts:w.ports,
    stdout:{write:s=>{stdout+=s;}},stderr:{write:s=>{stderr+=s;}},
  });
  // Unsupported public behavior on the base is an assertion failure, not an import crash.
  assert.ok(stdout.trim().startsWith('{'),`merge-result JSON missing: exit=${exitCode}; stderr=${stderr}`);
  const result=JSON.parse(stdout); assert.equal(result.exitCode,exitCode); return result;
}
const cases = [
  ['fresh_review',w=>{w.evidence.reviews[0].mustFix=1;}],
  ['fresh_review',w=>{w.evidence.reviews[0].fresh=false;}],
  ['fresh_review',w=>{w.evidence.reviews[0].verdict='NOT SURE';}],
  ['fresh_review',w=>{w.evidence.reviews[0].head='old';}],
  ['fresh_review',w=>{w.evidence.reviews=[];}],
  ['full_suite',w=>{w.evidence.fullSuite.head='old';}],
  ['full_suite',w=>{w.evidence.fullSuite.passed=false;}],
  ['full_suite',w=>{w.evidence.fullSuite.noNewSkips=false;}],
  ['required_ci',w=>{w.ci.head='old';}],
  ['required_ci',w=>{w.ci.checks=[];}],
  ['required_ci',w=>{w.ci.required.push('missing');}],
  ['required_ci',w=>{w.ci.checks[0].passed=false;}],
  ['required_ci',w=>{w.ci.complete=false;}],
  ['human_review',w=>{w.pull.reviewDecision='REVIEW_REQUIRED';}],
  ['human_review',w=>{w.pull.reviewDecision='CHANGES_REQUESTED';}],
  ['repairs',w=>{w.evidence.repairs=3;}],
  ['repairs',w=>{delete w.evidence.repairs;}],
  ['autonomy',w=>{w.config.autopilot.merge={areas:{cli:'manual'}};}],
  ['autonomy',w=>{w.config.autopilot.mode='off';}],
  ['autonomy',w=>{w.trusted=false;}],
  ['post_merge_audit',w=>{w.evidence.audit.planned=false;}],
  ['post_merge_audit',w=>{delete w.evidence.audit;}],
  ['authorization',w=>{w.evidence.authorization='';}],
  ['authorization',w=>{w.evidence.gatesSatisfied=false;}],
  ['question',w=>{w.evidence.questionOpen=true;}],
  ['exact_head',w=>{w.evidence.head='old';}],
  ['exact_head',w=>{w.evidence.base='main';}],
  ['policy',w=>{w.config.autopilot.merge={max_repairs:3};}],
  ['policy',w=>{w.config.autopilot.merge={full_suite:false};}],
  ['policy',w=>{w.config.autopilot.merge={unknown:true};}],
];
for (const [index,[rule,change]] of cases.entries()) test(`merge rule ${rule} rejects failing proof ${index}`,async()=>{
  const w=mergeWorld();change(w);const result=await invoke(w);
  assert.equal(result.outcome,'refused');assert.equal(result.rule,rule);assert.match(result.message,new RegExp(rule));
  assert.equal(w.writes.length,0);assert.equal(w.comments.length,0);
});
for (const queue of [false,true]) test(`eligible exact head uses ${queue?'queue':'direct'} path`,async()=>{
  const w=mergeWorld({queue}),result=await invoke(w);
  assert.equal(result.outcome,queue?'queued':'merged_pending_audit');assert.equal(result.exitCode,3);
  assert.deepEqual(w.writes,[queue?{kind:'queue',id:w.pull.id,head:w.evidence.head}:{kind:'direct',pr:17,head:w.evidence.head}]);
  assert.equal(w.comments.length,1);assert.equal(w.repo.issues.get(1).comments.length,1);
});
for (const repairs of [0,1,2]) test(`repair boundary ${repairs} permits submission`,async()=>{
  const w=mergeWorld();w.evidence.repairs=repairs;assert.equal((await invoke(w)).outcome,'merged_pending_audit');assert.equal(w.writes.length,1);
});
test('tighter base repair policy is enforced',async()=>{
  const w=mergeWorld();w.config.autopilot.merge={max_repairs:1};w.evidence.repairs=2;
  assert.equal((await invoke(w)).rule,'repairs');assert.equal(w.writes.length,0);
});
for (const area of [false,true]) test(`observe ${area?'area':'repository'} reports without merge write`,async()=>{
  const w=mergeWorld({queue:true});if(area)w.config.autopilot.merge={areas:{cli:'observe'}};else w.config.autopilot.mode='observe';
  assert.equal((await invoke(w)).outcome,'would_merge');assert.equal(w.writes.length,0);assert.equal(w.comments.length,1);
});
for (const guard of ['risk','sensitive','splitVerdict']) test(`second review required by ${guard}`,async()=>{
  const w=mergeWorld();if(guard==='risk')w.evidence.reviews[0].risk=4;else w.evidence[guard]=true;
  assert.equal((await invoke(w)).rule,'fresh_review');
  w.evidence.reviews.push({...w.evidence.reviews[0],session:'second-fresh-session'});
  assert.equal((await invoke(w)).outcome,'merged_pending_audit');
});
test('duplicate review sessions do not satisfy two reviews',async()=>{
  const w=mergeWorld();w.evidence.sensitive=true;w.evidence.reviews.push({...w.evidence.reviews[0]});
  assert.equal((await invoke(w)).rule,'fresh_review');assert.equal(w.writes.length,0);
});
test('equal patch ID permits old review but never old full-suite proof',async()=>{
  const w=mergeWorld();w.evidence.reviews[0].head='old';w.ports.patchEquivalent=async(old,head)=>{assert.equal(old,'old');assert.equal(head,w.pull.head);return true;};
  w.evidence.fullSuite.head='old';assert.equal((await invoke(w)).rule,'full_suite');
  w.evidence.fullSuite.head=w.pull.head;assert.equal((await invoke(w)).outcome,'merged_pending_audit');
});
for (const field of ['head','base','baseOid']) test(`changed ${field} after comment prevents submission`,async()=>{
  const w=mergeWorld();w.afterComment=()=>{w.pull[field]='changed';};assert.equal((await invoke(w)).rule,'exact_head');assert.equal(w.writes.length,0);
});
test('failed comment prevents merge',async()=>{
  const w=mergeWorld();w.ports.github.comment=async()=>{throw Error('comment failed');};assert.equal((await invoke(w)).rule,'comment');assert.equal(w.writes.length,0);
});
test('CI failure after comment prevents merge',async()=>{
  const w=mergeWorld();w.afterComment=()=>{w.ci.checks[0].passed=false;};assert.equal((await invoke(w)).rule,'required_ci');assert.equal(w.writes.length,0);
});
test('unknown queue never falls back to direct merge',async()=>{
  const w=mergeWorld();w.pull.queue=null;assert.equal((await invoke(w)).rule,'merge_queue');assert.equal(w.writes.length,0);
});
for (const state of ['QUEUED','AWAITING_CHECKS','LOCKED','MERGEABLE','UNMERGEABLE']) test(`queue ${state} is reconciled without another write`,async()=>{
  const w=mergeWorld({queue:true});w.pull.entry={id:'existing',state};
  assert.equal((await invoke(w,{observe:true})).outcome,state==='UNMERGEABLE'?'queue_failed':'queued');assert.equal(w.writes.length,0);assert.equal(w.comments.length,0);
});
test('queue removal is a failure and never a direct merge',async()=>{
  const w=mergeWorld({queue:true});await invoke(w);w.pull.entry=null;
  assert.equal((await invoke(w,{observe:true})).outcome,'queue_failed');assert.equal(w.writes.length,1);assert.equal(w.writes[0].kind,'queue');
});
test('queue success requires merged state then independent audit on merged commit',async()=>{
  const w=mergeWorld({queue:true});await invoke(w);w.pull.state='MERGED';w.pull.entry=null;w.pull.mergeCommit='merged-combination';
  assert.equal((await invoke(w,{observe:true})).outcome,'merged_pending_audit');
  w.evidence.audit={planned:true,head:w.pull.head,passed:true,independent:true,evidence:'audit report'};
  assert.equal((await invoke(w,{observe:true})).outcome,'merged_pending_audit');
  w.evidence.audit.head=w.pull.mergeCommit;w.evidence.audit.passed=false;
  assert.equal((await invoke(w,{observe:true})).outcome,'merged_pending_audit');
  w.evidence.audit.passed=true;w.evidence.audit.independent=false;
  assert.equal((await invoke(w,{observe:true})).outcome,'merged_pending_audit');
  w.evidence.audit.independent=true;const result=await invoke(w,{observe:true});
  assert.equal(result.outcome,'audited');assert.equal(result.exitCode,0);assert.equal(result.mergeCommit,w.pull.mergeCommit);assert.equal(w.writes.length,1);
});
test('lost enqueue reply reads the accepted entry without retry',async()=>{
  const w=mergeWorld({queue:true});w.afterWrite=()=>{throw Error('lost reply');};
  assert.equal((await invoke(w)).outcome,'queued');assert.equal(w.writes.length,1);
});
test('lost write and unreadable result remains unknown',async()=>{
  const w=mergeWorld({queue:true});w.afterWrite=()=>{w.ports.github.pull=async()=>{throw Error('offline');};throw Error('lost reply');};
  assert.equal((await invoke(w)).outcome,'unknown');assert.equal(w.writes.length,1);
});
test('queue rejection never causes direct merge',async()=>{
  const w=mergeWorld({queue:true});w.ports.github.enqueue=async(id,head)=>{w.writes.push({kind:'queue',id,head});throw Error('rejected');};
  assert.equal((await invoke(w)).outcome,'unknown');assert.equal(w.writes.length,1);
});

const {nativeMergeWorld}=await import('./helpers/autopilot-merge-world.mjs');
for(const queue of [false,true])test(`native gh adapter ${queue?'queue':'direct'} uses actual base and checked head`,async()=>{
  const w=nativeMergeWorld({queue});const result=await invoke(w);
  assert.equal(result.outcome,queue?'queued':'merged_pending_audit');assert.equal(w.writes.length,1);
  assert.equal(w.writes[0].head,w.evidence.head);assert.equal(w.writes[0].kind,queue?'queue':'direct');
  assert.deepEqual(w.configRefs,[w.pull.baseOid]);assert.ok(w.queueBranches.every(b=>b==='autopilot-next'));
  assert.equal(w.comments.length,1);
  const mergeCommands=w.commands.filter(c=>c.file==='gh'&&c.args[0]==='pr'&&c.args[1]==='merge');
  assert.equal(mergeCommands.length,queue?0:1);
  if(!queue){assert.ok(mergeCommands[0].args.includes('--merge'));assert.ok(mergeCommands[0].args.includes('--match-head-commit'));}
  assert.ok(w.commands.every(c=>!c.args.includes('--auto')&&!c.args.includes('--admin')));
});
test('native queue discovery error refuses without write or fallback',async()=>{
  const w=nativeMergeWorld({queue:true});w.queueError=true;
  assert.equal((await invoke(w)).rule,'merge_queue');assert.equal(w.writes.length,0);assert.equal(w.comments.length,0);
});
test('native check pending exit retains failed evidence and blocks merge',async()=>{
  const w=nativeMergeWorld();w.ci.checks[0].passed=false;w.checkError=true;
  assert.equal((await invoke(w)).rule,'required_ci');assert.equal(w.writes.length,0);
});
test('native required human review and unknown mergeability block writes',async()=>{
  for(const state of ['BLOCKED','UNKNOWN']){const w=nativeMergeWorld();w.pull.mergeStateStatus=state;
    assert.equal((await invoke(w)).rule,'required_ci');assert.equal(w.writes.length,0);}
});
test('native untrusted issue author cannot merge',async()=>{
  const w=nativeMergeWorld();w.repo.issues.get(1).user='outsider';
  assert.equal((await invoke(w)).rule,'autonomy');assert.equal(w.writes.length,0);
});
test('native base explicit trust permits issue author with no write permission',async()=>{
  const w=nativeMergeWorld();w.repo.issues.get(1).user='helper';w.config.autopilot.trust=['Helper'];
  assert.equal((await invoke(w)).outcome,'merged_pending_audit');assert.equal(w.writes.length,1);
});

for(const field of ['splitVerdict','sensitive'])for(const value of [undefined,null,'false'])test(`unknown ${field} ${String(value)} blocks one-review merge`,async()=>{
  const w=mergeWorld();w.evidence[field]=value;
  assert.equal((await invoke(w)).rule,'fresh_review');assert.equal(w.writes.length,0);
});
for(const native of [false,true])test(`pending requested human review blocks ${native?'native':'port'} merge`,async()=>{
  const w=native?nativeMergeWorld():mergeWorld();w.pull.pendingReviews=1;
  assert.equal((await invoke(w)).rule,'human_review');assert.equal(w.writes.length,0);
});
for(const check of [null,{}, {name:'tests',passed:null}])test(`malformed CI ${JSON.stringify(check)} returns named refusal`,async()=>{
  const w=mergeWorld();w.ci.checks=[check];
  assert.equal((await invoke(w)).rule,'required_ci');assert.equal(w.writes.length,0);
});

test('a passing check with a duplicate name cannot hide a required failure',async()=>{
  const w=mergeWorld();w.ci.checks.push({name:'tests',passed:false});
  assert.equal((await invoke(w)).rule,'required_ci');assert.equal(w.writes.length,0);
});
