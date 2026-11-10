import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync, statSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import * as alerts from '../src/autopilot-alerts.mjs';

const MINUTE = 60000, HOUR = 60 * MINUTE, DAY = 24 * HOUR;
const ask = {code:'policy-choice', cause:'Two policies conflict', tried:'Read both policies.', need:'Choose the safer policy?', ifNoAnswer:'This run waits; other work continues.'};
function setup(t) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-real-asks-'));
  t.after(() => rmSync(dir, {recursive:true, force:true}));
  const f = {dir, time:Date.parse('2026-11-10T10:00:00Z'), repo:'example/project', host:'machine-a', requests:[], reply:null};
  f.env = {HOME:dir, XDG_CONFIG_HOME:join(dir,'config')};
  f.ports = {stateRoot:join(dir,'state'), repository:async()=>({nameWithOwner:f.repo}), now:()=>f.time, hostname:()=>f.host,
    http:async r => { f.requests.push(r); if(f.reply instanceof Error)throw f.reply; return f.reply ?? {status:200,text:'ok'}; }};
  f.run = input => alerts.runAutopilotAlerts({cwd:join(dir,'checkout'),env:f.env,...input},f.ports);
  f.alert = (issue=1, kind='decision', fields=ask, extra={}) => f.run({action:'alert',issue:String(issue),kind,text:JSON.stringify(fields),...extra});
  f.digest = (attention=[]) => f.run({action:'digest',attention});
  f.config = async destination => assert.equal((await f.run({action:'set',destination,text:'https://hooks.slack.com/services/synthetic/test/fixture'})).exitCode,0);
  f.records = () => readdirSync(join(f.ports.stateRoot,'alerts')).filter(n=>/^[a-f0-9]{20}\.json$/.test(n)).map(n=>JSON.parse(readFileSync(join(f.ports.stateRoot,'alerts',n),'utf8')));
  f.incidents = () => f.records().flatMap(r=>Object.values(r.incidents));
  f.recover = (issue=1, fields={cause:'Service restored.'}) => f.alert(issue,'recovered',fields);
  return f;
}

for(const kind of ['decision','access'])test(`${kind}: a concrete ask includes link, attempt, consequence and fits about 400 chars`,async t=>{
  const f=setup(t);await f.config();const r=await f.alert(1,kind);
  assert.equal(r.exitCode,0);assert.equal(f.requests.length,1);
  const text=f.requests[0].body.text;assert.match(text,/https:\/\/github.com\/example\/project\/issues\/1/);
  assert.match(text,/Ask: Choose the safer policy\?/);assert.match(text,/Tried: Read both policies\./);
  assert.match(text,/If no answer: This run waits; other work continues\./);assert.ok(text.length<=480);
  assert.doesNotMatch(text,/Two policies conflict/);
});

for(const kind of ['test-suite','long-running','stuck'])test(`${kind}: return record-only outcome for issue/report, never chat`,async t=>{
  const f=setup(t);await f.config();const r=await f.alert(1,kind);
  assert.equal(r.exitCode,0);assert.match(r.message,/record/i);assert.equal(f.requests.length,0);
  assert.equal(f.incidents()[0].kind,kind);assert.equal(alerts.alertStatusLine({repo:f.repo,env:f.env},f.ports),'');
});

for(const need of ['', 'No action needed.', 'Informational only.', 'No operator action required.', 'No action now.', 'Identify the blocker', 'No named blocker is saved', 'Choose A? Also choose B?', 'Choose A. Then approve B.', 'Choose A?\nGrant access?', 'Approve the change and grant access', 'Can you approve this and grant access?', 'No further action required.', 'No human intervention needed.', 'Nothing to do.', 'FYI: Choose policy A?'])test(`refuse empty, generic, no-action or multiple asks: ${JSON.stringify(need)}`,async t=>{
  const f=setup(t);await f.config();const r=await f.alert(1,'decision',{...ask,need});
  assert.equal(f.requests.length,0);assert.equal(r.exitCode,need?0:2);
});

for(const missing of ['code','ifNoAnswer'])test(`legacy ask missing ${missing} stays recorded`,async t=>{
  const f=setup(t);await f.config();const fields={...ask};delete fields[missing];
  assert.equal((await f.alert(1,'decision',fields)).exitCode,0);assert.equal(f.requests.length,0);assert.equal(f.incidents().length,1);
});

test('machine incidents require paused work, two distinct ticks and at least 15 minutes',async t=>{
  const f=setup(t);await f.config();const fields={...ask,code:'io-stall',paused:true,tick:'a'};
  await f.alert(1,'resource',fields);assert.equal(f.requests.length,0);
  f.time+=15*MINUTE;await f.alert(1,'resource',fields);assert.equal(f.requests.length,0,'one tick repeated');
  await f.alert(1,'resource',{...fields,tick:'b'});assert.equal(f.requests.length,1);
});

test('two machine ticks before 15 minutes stay quiet; unpaused observation resets the window',async t=>{
  const f=setup(t);await f.config();const fields={...ask,code:'io-stall',paused:true};
  await f.alert(1,'resource',fields);f.time+=14*MINUTE;await f.alert(1,'resource',fields);assert.equal(f.requests.length,0);
  await f.alert(1,'resource',{...fields,paused:false});f.time+=MINUTE;await f.alert(1,'resource',fields);
  f.time+=15*MINUTE-1;await f.alert(1,'resource',fields);assert.equal(f.requests.length,0);
  f.time++;await f.alert(1,'resource',fields);assert.equal(f.requests.length,1);
});

for(const kind of ['usage-limit','interpreter','interpreter-access'])test(`${kind} uses the machine debounce and infrastructure destination`,async t=>{
  const f=setup(t);await f.config();await f.run({action:'set',destination:'infrastructure',text:'https://hooks.slack.com/services/synthetic/infrastructure/fixture'});
  await f.alert(1,kind,{...ask,paused:true});assert.equal(f.requests.length,0);
  f.time+=15*MINUTE;await f.alert(1,kind,{...ask,paused:true});assert.equal(f.requests.length,1);assert.match(f.requests[0].url,/infrastructure/);
});

test('stable code joins many issues without resending changed cause prose or update flags',async t=>{
  const f=setup(t);await f.config();await f.alert();
  for(let n=2;n<=5;n++)await f.alert(n,'decision',{...ask,cause:`Observation ${n}`},{update:true});
  assert.equal(f.requests.length,1);assert.deepEqual(f.incidents()[0].issues,[1,2,3,4,5]);
  f.time+=DAY;await f.alert(2,'decision',{...ask,cause:'Different prose'},{update:true});assert.equal(f.requests.length,1);
});

test('known issues are listed together in the first message',async t=>{
  const f=setup(t);await f.config();await f.alert(1,'decision',{...ask,issues:[5,3,2,4,1]});assert.equal(f.requests.length,1);
  for(let n=1;n<=5;n++)assert.ok(f.requests[0].body.text.includes(`https://github.com/example/project/issues/${n}`));
});

test('ask/owner changes alone can update, still bounded to one message per issue per 24 hours',async t=>{
  const f=setup(t);await f.config();await f.alert();const changed={...ask,need:'Approve the alternative policy?',owner:'Maintainers'};
  f.time+=DAY-1;await f.alert(1,'decision',changed,{update:true});assert.equal(f.requests.length,1);
  f.time++;await f.alert(1,'decision',changed,{update:true});assert.equal(f.requests.length,2);
});

test('different codes and kinds on one issue cannot bypass 24-hour limit',async t=>{
  const f=setup(t);await f.config();await f.alert();
  await f.alert(1,'access',{...ask,code:'sign-in'});assert.equal(f.requests.length,1);
  f.time+=DAY;await f.alert(1,'access',{...ask,code:'sign-in'});assert.equal(f.requests.length,2);
});

test('recovery only notifies for a sent alert, open 15 minutes, within all message budgets',async t=>{
  const f=setup(t);await f.config();await f.alert();f.time+=DAY;await f.recover();
  assert.equal(f.requests.length,2);assert.match(f.requests[1].body.text,/recovered/);assert.equal(f.incidents().length,0);
});

for(const mode of ['short','unsent','failed','unconfirmed','issue-budget'])test(`quiet recovery: ${mode}`,async t=>{
  const f=setup(t);if(mode!=='unsent')await f.config();
  if(mode==='failed')f.reply={status:500,text:'error'};
  if(mode==='unconfirmed')f.reply={status:200,text:''};
  await f.alert();const before=f.requests.length;f.reply=null;
  f.time+=mode==='short'?14*MINUTE:mode==='issue-budget'?15*MINUTE:DAY;await f.recover();
  assert.equal(f.requests.length,before);assert.equal(f.incidents().length,0);
});

test('reopen after recovery waits two hours even for a different code and a quiet recovery',async t=>{
  const f=setup(t);await f.config();await f.alert();f.time+=DAY;await f.recover();
  f.time+=DAY; // clear the recovery message issue budget before another quiet incident
  await f.alert(4);await f.alert(2);await f.recover(2); // shared cause, quiet close; issue 3 had no send
  const before=f.requests.length;
  await f.alert(3,'decision',{...ask,code:'other-policy'}); // unrelated issue remains eligible
  assert.equal(f.requests.length,before+1);
  await f.alert(2,'decision',{...ask,code:'reopened'});assert.equal(f.requests.length,before+1);
  f.time+=2*HOUR-1;await f.alert(2,'decision',{...ask,code:'reopened'});assert.equal(f.requests.length,before+1);
  f.time++;await f.alert(2,'decision',{...ask,code:'reopened'});assert.equal(f.requests.length,before+2);
});

test('at most six messages per rolling hour per machine across repos; exactly an hour releases capacity',async t=>{
  const f=setup(t);await f.config();
  for(let n=1;n<=7;n++){f.repo=`example/project${n}`;await f.alert(n,'decision',{...ask,code:`choice-${n}`});}
  assert.equal(f.requests.length,6);f.time+=HOUR-1;await f.alert(7,'decision',{...ask,code:'choice-7'});assert.equal(f.requests.length,6);
  f.time++;await f.alert(7,'decision',{...ask,code:'choice-7'});assert.equal(f.requests.length,7);
});

test('digest sends at most daily per channel across hosts/repos, and only when open list changes',async t=>{
  const f=setup(t);await f.config();await f.alert(1,'decision',ask);f.time+=DAY;
  await f.digest();assert.equal(f.requests.length,2);assert.match(f.requests.at(-1).body.text,/digest/);
  f.host='machine-b';f.repo='example/other';await f.digest([{number:2,category:'access',need:'Grant repository access?'}]);assert.equal(f.requests.length,2);
  f.time+=DAY-1;await f.digest([{number:2,category:'access',need:'Grant repository access?'}]);assert.equal(f.requests.length,2);
  f.time++;await f.digest([{number:2,category:'access',need:'Grant repository access?'}]);assert.equal(f.requests.length,3);
  const digest=f.requests.at(-1).body.text;assert.match(digest,/example\/project\/issues\/1/);assert.match(digest,/example\/other\/issues\/2/);
  assert.doesNotMatch(digest,/Two policies conflict|more open items/);
  f.time+=DAY;await f.digest([{number:2,category:'access',need:'Grant repository access?'}]);assert.equal(f.requests.length,3,'unchanged open list');
});

test('digest omits test suites, long running, machine incidents and cause-only parked rows',async t=>{
  const f=setup(t);await f.config();
  for(const kind of ['test-suite','long-running','resource'])await f.alert(1,kind,{...ask,code:kind});
  await f.digest([{number:2,category:'parked',cause:'Tooling gap'},{number:3,category:'decision',cause:'No question'}]);assert.equal(f.requests.length,0);
});

test('digest shares per-issue cooldown and hourly budget with alert messages',async t=>{
  const f=setup(t);await f.config();await f.alert();await f.digest();assert.equal(f.requests.length,1);
  f.time+=DAY;await f.digest();assert.equal(f.requests.length,2);await f.alert(1,'access',{...ask,code:'permission'});assert.equal(f.requests.length,2);
});

test('failed digest consumes daily attempt; no destination consumes none',async t=>{
  const f=setup(t);const rows=[{number:1,category:'access',need:'Grant repository access?'}];
  await f.digest(rows);await f.config();f.reply={status:503,text:'error'};await f.digest(rows);assert.equal(f.requests.length,1);
  f.reply=null;f.time+=DAY-1;await f.digest([...rows,{number:2,category:'decision',need:'Choose policy A?'}]);assert.equal(f.requests.length,1);
});

test('parallel calls across checkouts serialize stable cause and preserve issue membership',async t=>{
  const f=setup(t);await f.config();await Promise.all(Array.from({length:5},(_,i)=>f.alert(i+1)));
  assert.equal(f.requests.length,1);assert.deepEqual(f.incidents()[0].issues,[1,2,3,4,5]);
});

test('private shared history holds no destination secret; corrupt existing history fails closed',async t=>{
  const f=setup(t);await f.config();await f.alert();const path=join(f.ports.stateRoot,'alerts','delivery.json');
  assert.equal(statSync(path).mode&0o777,0o600);assert.doesNotMatch(readFileSync(path,'utf8'),/hooks\.slack|fixture/);
  writeFileSync(path,'broken');const r=await f.alert(2,'access',{...ask,code:'access'});assert.equal(r.exitCode,1);assert.equal(f.requests.length,1);
});

test('oversize asks and secret text are never sent as truncated questions or exposed credentials',async t=>{
  const f=setup(t);await f.config();await f.alert(1,'decision',{...ask,need:`Choose ${'a'.repeat(600)}?`});assert.equal(f.requests.length,0);
  await f.alert(2,'decision',{...ask,code:'safe',tried:'Read https://hooks.slack.com/services/sensitive/value.'});
  assert.equal(f.requests.length,1);assert.doesNotMatch(f.requests[0].body.text,/sensitive|hooks\.slack/);
  assert.doesNotMatch(JSON.stringify(f.records()),/sensitive|hooks\.slack/);
});

test('native hook accepts fields without a text envelope and preserves no approvals or core coupling',async t=>{
  const f=setup(t);await f.config();assert.equal(typeof alerts.notifyAutopilotAsk,'function');
  const r=await alerts.notifyAutopilotAsk({env:f.env,issue:'1',kind:'decision',fields:ask},f.ports);
  assert.equal(r.exitCode,0);assert.equal(f.requests.length,1);
});


test('failed alert retries only after 24 hours; a destination test does not erase open failures',async t=>{
  const f=setup(t);await f.config();f.reply={status:500,text:'error'};await f.alert();
  assert.match(alerts.alertStatusLine({repo:f.repo,env:f.env},f.ports),/1 open alert not delivered/);
  f.reply=null;await f.alert();assert.equal(f.requests.length,1);
  await f.run({action:'test'});assert.match(alerts.alertStatusLine({repo:f.repo,env:f.env},f.ports),/1 open alert not delivered/);
  f.time+=DAY;await f.alert();assert.equal(f.requests.length,3);assert.equal(alerts.alertStatusLine({repo:f.repo,env:f.env},f.ports),'');
});

test('a missing destination consumes no issue budget and setup allows the recorded ask to send',async t=>{
  const f=setup(t);await f.alert();assert.equal(f.requests.length,0);
  assert.match(alerts.alertStatusLine({repo:f.repo,env:f.env},f.ports),/set one/);
  await f.config();await f.alert();assert.equal(f.requests.length,1);
});

test('only changing the owner can update an ask after the issue cooldown',async t=>{
  const f=setup(t);await f.config();await f.alert();f.time+=DAY;
  await f.alert(1,'decision',{...ask,owner:'Maintainers'},{update:true});assert.equal(f.requests.length,2);
  assert.match(f.requests.at(-1).body.text,/Owner: Maintainers/);
});

test('digest observes the recovery quiet period even when the prior recovery did not send',async t=>{
  const f=setup(t);await f.config();await f.alert(1);await f.alert(2);await f.recover(2);
  const rows=[{number:2,category:'decision',need:'Choose another policy?'}];
  await f.digest(rows);assert.equal(f.requests.length,1);
  f.time+=2*HOUR-1;await f.digest(rows);assert.equal(f.requests.length,1);
  f.time++;await f.digest(rows);assert.equal(f.requests.length,2);
});

test('destination changes do not leak the previous channel open list into a new channel digest',async t=>{
  const f=setup(t);await f.config();await f.alert(1);f.time+=DAY;
  await f.run({action:'set',text:'https://hooks.slack.com/services/synthetic/other/channel'});
  await f.digest([{number:2,category:'access',need:'Grant access?'}]);assert.equal(f.requests.length,2);
  assert.doesNotMatch(f.requests.at(-1).body.text,/issues\/1/);
});

test('oversize digest remains local without truncating links or hiding open asks',async t=>{
  const f=setup(t);await f.config();const rows=Array.from({length:40},(_,i)=>({number:i+1,category:'decision',need:'Choose policy A?'}));
  await f.digest(rows);assert.equal(f.requests.length,0);
});


for(const action of ['alert','recovered','digest'])test(`legacy ${action} log seeds quiet budgets when shared history is absent`,async t=>{
  const f=setup(t);await f.config();const root=join(f.ports.stateRoot,'alerts');mkdirSync(root,{recursive:true});
  const id=createHash('sha256').update(f.repo).digest('hex').slice(0,20);
  writeFileSync(join(root,`${id}.json`),JSON.stringify({v:1,repo:f.repo,incidents:{},log:[{
    at:new Date(f.time-HOUR).toISOString(),host:f.host,issue:action==='digest'?undefined:1,kind:action==='digest'?'digest':'decision',action,result:action==='recovered'?'not-sent':'delivered'
  }]}));
  if(action==='digest')await f.digest([{number:1,category:'decision',need:'Choose policy A?'}]);else await f.alert();
  assert.equal(f.requests.length,0);
  f.time+=action==='recovered'?HOUR:23*HOUR;
  if(action==='digest')await f.digest([{number:1,category:'decision',need:'Choose policy A?'}]);else await f.alert();
  assert.equal(f.requests.length,1);
});

for (const order of [['resource','access'],['access','resource']]) test(`repair: mixed cause ${order.join(' to ')} joins one incident and separates machine hosts`, async t => {
  const f=setup(t); await f.config();
  await f.alert(1,order[0],{...ask,paused:true}); f.time+=15*MINUTE;
  await f.alert(1,order[0],{...ask,paused:true});
  await f.alert(2,order[1],{...ask,paused:true});
  assert.equal(f.requests.length,1); assert.equal(f.incidents().length,1);
  assert.deepEqual(f.incidents()[0].issues,[1,2]);
  f.host='machine-b'; await f.alert(3,'resource',{...ask,paused:true});f.time+=15*MINUTE;
  await f.alert(3,'resource',{...ask,paused:true});assert.equal(f.requests.length,2);
});

test('repair: complete compact message accepts an ask longer than 160 characters',async t=>{
  const f=setup(t);await f.config();
  const need='Choose whether the release should preserve the existing retention period for archived records or apply the shorter period only to records created after the next scheduled deployment?';
  await f.alert(1,'decision',{...ask,need,tried:'Read policy.',ifNoAnswer:'Release waits.'});
  assert.equal(f.requests.length,1);assert.ok(f.requests[0].body.text.includes(need));assert.ok(f.requests[0].body.text.length<=480);
});
for(const need of ['?','!!!?','Approve the deployment; grant write access.','Approve the deployment, grant write access.','Approve the deployment — grant write access.']) test(`repair: refuse insubstantial or multiple action clauses ${need}`,async t=>{
  const f=setup(t);await f.config();await f.alert(1,'decision',{...ask,need});assert.equal(f.requests.length,0);
});

test('repair: actual automaticAttention questions reach digest while parked and gate descriptions stay quiet', async t=>{
  const {automaticAttention}=await import('../src/workflow-runner.mjs');
  const f=setup(t);await f.config();
  const base={repo:f.repo,automaticOrigin:{machine:f.host},state:'waiting'};
  const attention=automaticAttention({repo:f.repo,machine:f.host},{readRuns:()=>[
    {...base,number:1,question:{text:'Choose policy A?',at:2}},
    {...base,number:2,gate:{kind:'approve-pr',at:1}},
    {...base,number:3,state:'paused',parkReason:'No supported route'},
    {...base,number:4,state:'paused',question:{text:'Grant repository access?',at:2}},
  ]});
  await f.digest(attention);assert.equal(f.requests.length,1);
  const text=f.requests[0].body.text;assert.match(text,/issues\/1 — Choose policy A\?/);assert.match(text,/issues\/4 — Grant repository access\?/);
  assert.doesNotMatch(text,/issues\/[23]|approve-pr|No supported route/);
});

test('repair: person classification joins its own machine cause before a different host person cause', async t=>{
  const f=setup(t);await f.config();await f.alert(1,'access');
  f.host='machine-b';await f.alert(2,'resource',{...ask,paused:true});f.time+=15*MINUTE;await f.alert(2,'resource',{...ask,paused:true});
  await f.alert(3,'access');
  const own=f.incidents().find(item=>item.host==='machine-b');
  assert.deepEqual(own.issues,[2,3]);assert.equal(f.requests.length,2);
});

for(const kind of ['test-suite','long-running','stuck'])test(`repair: ${kind} stays quiet when it shares an existing person cause`,async t=>{
  const f=setup(t);await f.config();await f.alert();f.time+=DAY;
  await f.alert(1,kind,{...ask,need:'Choose a different policy?'},{update:true});assert.equal(f.requests.length,1);
  assert.equal(f.incidents()[0].fields.need,ask.need);
});
test('repair: a recorded suite cause can acquire its first real person ask',async t=>{
  const f=setup(t);await f.config();await f.alert(1,'test-suite');
  await f.alert(2,'decision');assert.equal(f.requests.length,1);
});
