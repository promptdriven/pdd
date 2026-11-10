import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, readdirSync, rmSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {launcher} from './helpers/environment-launcher-fixture.mjs';
import {runAutopilotAlerts} from '../src/autopilot-alerts.mjs';
const MIN = 60_000, DAY = 24 * 60 * MIN;
const state = f => JSON.parse(readFileSync(f.stateFile(), 'utf8'));
const lost = (number, at) => ({number, at, batch:`synthetic-batch-${number}`, cause:'unknown', mark:'1:2'});
const issue = number => ({number, state:'open', title:'Synthetic work', body:'Local test', user:{login:'owner'}, author_association:'OWNER', labels:[], comments:0, html_url:`https://github.com/owner/repo/issues/${number}`});
const records = f => readdirSync(join(f.ports.stateRoot,'alerts')).filter(n=>/^[a-f0-9]{20}\.json$/.test(n)).map(n=>JSON.parse(readFileSync(join(f.ports.stateRoot,'alerts',n),'utf8')));

test('native lost-verdict group reaches real HTTP once with one resend ask and all issue links', async t=>{
  const f=await launcher(t);await f.start();f.waits=[lost(12,f.time),lost(15,f.time+1)];
  await f.tick();assert.equal(f.sent.length,1);
  assert.match(f.sent[0],/Ask: Run pdd workflow resend 12 15 --said -\?/);
  for(const n of [12,15])assert.ok(f.sent[0].includes(`/issues/${n}`));
  assert.match(f.sent[0],/Tried:/);assert.match(f.sent[0],/If no answer:/);assert.ok(f.sent[0].length<=480);
  assert.ok(state(f).runtime.lostDecision);
  f.time+=MIN;await f.tick();assert.equal(f.sent.length,1);
});

for(const suppression of ['unconfigured','issue-budget','failed','unconfirmed'])test(`native lost-verdict ${suppression} is not marked delivered and remains owned on later ticks`,async t=>{
  const f=await launcher(t);await f.start();f.waits=[lost(12,f.time)];
  if(suppression==='unconfigured')rmSync(join(f.home,'.config','pdd','autopilot-alerts.json'));
  if(suppression==='issue-budget')await runAutopilotAlerts({action:'alert',cwd:f.cwd,env:f.env,issue:'12',kind:'access',text:JSON.stringify({code:'other-ask',cause:'Permission missing',tried:'Read permission',need:'Grant write access?',ifNoAnswer:'This run waits.'})},{...f.ports.alertPorts,stateRoot:f.ports.stateRoot,repository:async()=>({nameWithOwner:'owner/repo'}),now:()=>f.time});
  const http=f.ports.alertPorts.http;
  if(['failed','unconfirmed'].includes(suppression))f.ports.alertPorts.http=async()=>({status:suppression==='failed'?503:200,text:''});
  await f.tick();assert.equal(state(f).runtime?.lostDecision,undefined,'recording does not confirm delivery');
  assert.ok(records(f).some(r=>Object.values(r.incidents).some(i=>i.code==='lost-verdict')),'deferred ask is available for digest');
  if(suppression==='unconfigured')writeFileSync(join(f.home,'.config','pdd','autopilot-alerts.json'),JSON.stringify({v:1,service:'discord',url:'https://discord.com/api/webhooks/1/abc'}));
  f.ports.alertPorts.http=http;f.time+=DAY;const before=f.sent.length;await f.tick();
  if(suppression==='unconfirmed') {assert.equal(f.sent.length,before,'uncertain delivery is never repeated');assert.equal(state(f).runtime?.lostDecision,undefined);}
  else {assert.equal(f.sent.length,before+1);assert.ok(state(f).runtime.lostDecision);}
});

for(const kind of ['resource','usage-limit','interpreter-access','interpreter'])test(`native ${kind} persists through real owner debounce across ticks`,async t=>{
  const f=await launcher(t);await f.start();f.issues=[issue(12),issue(15)];
  if(kind==='resource')f.ports.machineHealth=async()=>({healthy:false,causes:['disk available 3%'],resources:null});
  if(kind==='usage-limit')f.ports.codexLimits=async()=>({state:'limited',usedPercent:100,resetAt:null});
  if(kind.startsWith('interpreter')){f.waits=[lost(12,f.time),lost(15,f.time+1)];f.health={state:kind==='interpreter'?'unavailable':'access',detail:kind==='interpreter'?'HTTP 503':'HTTP 401',fix:'gh auth status'};}
  await f.tick();assert.equal(f.sent.length,0,'first tick stays quiet');
  await f.tick();assert.equal(f.sent.length,0,'same observation time is not another tick');
  f.time+=15*MIN;await f.tick();assert.equal(f.sent.length,1,'persistent paused work reaches chat');
  assert.match(f.sent[0],new RegExp(`needs you: ${kind}`));assert.match(f.sent[0],/Ask: Run pdd autopilot doctor\?/);
  for(const n of [12,15])assert.ok(f.sent[0].includes(`/issues/${n}`));
  assert.match(f.sent[0],/If no answer:/);assert.ok(f.sent[0].length<=480);
  f.time+=15*MIN;await f.tick();assert.equal(f.sent.length,1,'later tick does not repost');
});
