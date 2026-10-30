import test from 'node:test';
import assert from 'node:assert/strict';
import { uptakeFixture,fs,facts,viewOptions,hostname } from './helpers/workflow-uptake-fixture.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
const vectors=JSON.parse(fs.readFileSync(new URL('./workflow-request-uptake/cases.json',import.meta.url),'utf8'));
const vector=vectors.cases.find(v=>v.id==='probe-I-protected-in-flight-manual-recovery');
test(`2722 vector: ${vector.id}`,{timeout:30000},async t=>{
 for(const ownerKind of vector.given.ownerVariants){
  const f=await uptakeFixture(t),run=f.record();run.areas[0].name='plan';run.chats[0].area='plan';run.chats[0].paneId='p10';writeRun(run,f.ports);
  const owner=ownerKind==='unverifiable-owner'?{pid:'unknown',hostname:hostname(),token:'unknown'}:{pid:654321,hostname:ownerKind==='foreign-host-after-hostname-change'?'original-host':hostname(),token:'original-sender'};
  f.ports.processIdentity=()=>({alive:true});
  const intent=f.entry('stuck-x',{text:'Old request',area:'plan',paneId:'p10',state:'pending',inFlight:true,owner});
  f.save([intent]);const bytes=f.bytes();
  for(const opts of viewOptions){const status=await f.status(opts);assert.equal(status.exitCode,0);if(opts.json){const row=JSON.parse(status.message).runs[0];assert.deepEqual(row.inFlightRequests,vector.expect.statusInFlightRequests);assert.deepEqual(row.requests,vector.expect.jsonDeliveredRequests);}else facts(status.message,['stuck-x','Old request','plan','p10','original chat','wait','typing','clear or resend']);assert.equal(f.bytes(),bytes);}
  const cancelled=f.record();cancelled.state='cancelled';writeRun(cancelled,f.ports);facts((await f.status({ref:undefined,cancelled:true})).message,['stuck-x','Old request','plan','p10','original chat','wait','typing','clear or resend']);cancelled.state='running';writeRun(cancelled,f.ports);
  for(const elapsed of [0,3600000])for(const text of ['Old request','New request']){
   f.save([intent]);f.tick(elapsed);const sends=f.sent().length,launches=f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run').length;
   const refused=await f.change(text);assert.notEqual(refused.exitCode,0);facts(refused.message,['stuck-x','Old request','plan','p10','original chat','wait','typing','clear or resend']);assert.ok(!/Retry:|target changed|type.*if absent/i.test(refused.message));if(text==='New request')facts(refused.message,['Your request is saved pending']);assert.equal(f.sent().length,sends);assert.equal(f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run').length,launches);assert.deepEqual(f.read()[0],intent);if(text==='Old request')assert.equal(f.bytes(),bytes);
  }
 }
});
