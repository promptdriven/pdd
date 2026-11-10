import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync, statSync} from 'node:fs';
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

for(const need of ['', 'No action needed.', 'Informational only.', 'No operator action required.', 'No action now.', 'Identify the blocker', 'No named blocker is saved', 'Choose A? Also choose B?', 'Choose A. Then approve B.', 'Choose A?\nGrant access?'])test(`refuse empty, generic, no-action or multiple asks: ${JSON.stringify(need)}`,async t=>{
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
  await f.alert(2);await f.recover(2); // shared cause, quiet close; issue 3 had no send
  const before=f.requests.length;
  await f.alert(3,'decision',{...ask,code:'other-policy'}); // unrelated issue remains eligible
  assert.equal(f.requests.length,before+1);
  await f.alert(2,'decision',{...ask,code:'reopened'});assert.equal(f.requests.length,before+1);
  f.time+=2*HOUR;await f.alert(2,'decision',{...ask,code:'reopened'});assert.equal(f.requests.length,before+2);
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
});

test('native hook accepts fields without a text envelope and preserves no approvals or core coupling',async t=>{
  const f=setup(t);await f.config();assert.equal(typeof alerts.notifyAutopilotAsk,'function');
  const r=await alerts.notifyAutopilotAsk({env:f.env,issue:'1',kind:'decision',fields:ask},f.ports);
  assert.equal(r.exitCode,0);assert.equal(f.requests.length,1);
});
