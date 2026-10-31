import test from 'node:test';
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {uptakeFixture,fs} from './helpers/workflow-uptake-fixture.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
import {PUBLIC_COMMAND_ROUTES} from '../src/command-catalog.mjs';

const invalid=[['large',1e20],['numeric-string','1000'],['string','invalid'],['positive-overflow',Infinity],['negative-overflow',-Infinity],['below',-8640000000000001],['above',8640000000000001]];
const controls=[0,-8640000000000000,8640000000000000];
const local=value=>new Intl.DateTimeFormat('en-US',{month:'short',day:'numeric',hour:'2-digit',minute:'2-digit',hourCycle:'h23',timeZone:'America/Los_Angeles'}).format(new Date(value));
async function capture(action){try{return {value:await action()};}catch(error){return {error};}}
for(const field of ['deliveredAt','ackedAt'])for(const [label,value] of invalid)test(`round2 status and done preserve ${field} ${label}`,async t=>{
 // Run the valid controls first, so old-code failure cannot hide preservation evidence.
 for(const time of (label==='large'?[...controls,value]:[value]))for(const operation of ['done','status']){
  const f=await uptakeFixture(t);f.ports.timeZone='America/Los_Angeles';
  const entry=f.entry('round2-time',{[field]:time,...(field==='ackedAt'?{ackSummary:'Addressed'}:{})});
  f.save([entry]);
  if(!Number.isFinite(time)&&typeof time==='number')fs.writeFileSync(f.path,f.bytes().replace(`"${field}": null`,`"${field}": ${time>0?'1e309':'-1e309'}`));
  const bytes=f.bytes();
  const result=await capture(()=>operation==='status'?f.status():f.done('reproduce'));
  assert.equal(result.error,undefined,`${operation} must not throw for saved ${field} ${String(time)}: ${result.error?.stack}`);
  assert.equal(result.value.exitCode,0,result.value.message);
  const known=controls.includes(time);
  if(operation==='status'){
   assert.ok(result.value.message.includes(`${field==='ackedAt'?'acknowledged':'delivered'} at ${known?local(time):'unknown'}`),result.value.message);
   for(const options of [{ref:undefined},{ref:undefined,all:true}]){
    const listed=await capture(()=>f.status(options));assert.equal(listed.error,undefined);assert.equal(listed.value.exitCode,0);
    if(field==='deliveredAt')assert.ok(listed.value.message.includes(known?local(time):'unknown'));
    else assert.doesNotMatch(listed.value.message,/round2-time/);
   }
  }else{
   assert.ok(f.record().done.reproduce,'successful done saved its step');
   if(field==='ackedAt')assert.doesNotMatch(result.value.message,/round2-time/);
   else assert.ok(result.value.message.includes(`delivered at ${known?local(time):'unknown'}`),result.value.message);
  }
  const row=await f.row();assert.ok(Array.isArray(row.requests));assert.equal(row.requests[0][field],typeof time==='number'&&!Number.isFinite(time)?null:time);
  assert.equal(f.bytes(),bytes,'visibility and done never rewrite saved journal bytes');
 }
});
for(const state of ['completed','cancelled'])test(`round2 ${state} pending custody is historical`,async t=>{
 const f=await uptakeFixture(t);f.save([f.entry('pending-ended',{state:'pending'})]);const bytes=f.bytes();const run=f.record();run.state=state;writeRun(run,f.ports);
 for(const options of [{},{ref:undefined,cancelled:true},{ref:undefined,all:true,cancelled:true}]){const result=await f.status(options);assert.equal(result.exitCode,0);const line=result.message.split('\n').find(line=>line.includes('pending-ended'));assert.ok(line);assert.match(line,/not sent/i);assert.match(line,/run ended/i);assert.doesNotMatch(result.message,/not yet acknowledged/);}
 assert.equal(f.bytes(),bytes);
});
for(const mode of ['read','malformed'])test(`round2 ${mode} journal keeps every visibility collection null`,async t=>{
 const f=await uptakeFixture(t);f.save([f.entry()]);if(mode==='malformed')fs.writeFileSync(f.path,'{broken');const bytes=f.bytes();
 const ports=mode==='read'?{...f.ports,deliveryFiles:{...fs,readFileSync:(path,...args)=>{if(path===f.path)throw Error('read denied');return fs.readFileSync(path,...args);}}}:f.ports;
 for(const options of [{},{ref:undefined},{ref:undefined,all:true}]){const result=await f.status({...options,json:true},ports);assert.equal(result.exitCode,0);const row=JSON.parse(result.message).runs[0];for(const key of ['requests','inFlightRequests','pendingRequests','uncertainRequests'])assert.equal(row[key],null,key);assert.match(row.requestWarning,/unavailable/i);}
 const result=await f.done('reproduce',ports);assert.equal(result.exitCode,0);assert.ok(f.record().done.reproduce);assert.match(result.message,/warning:.*unavailable/i);assert.equal(f.bytes(),bytes);
});
test('round2 done derives a shell safe conditional ACK hint without automatic uptake',async t=>{
 const f=await uptakeFixture(t);const id="id with quote' $(touch injected)";f.ports.pdd="'/private/current node' '/private/current package/bin/pdd.mjs'";f.save([f.entry(id),f.entry('already-addressed',{ackedAt:0,ackSummary:'Done'})]);const bytes=f.bytes();
 const result=await f.done('reproduce');assert.equal(result.exitCode,0);assert.ok(f.record().done.reproduce);const warnings=result.message.split('\n').filter(line=>line.startsWith('warning:'));assert.ok(warnings.length>=2,result.message);assert.ok(result.message.slice(result.message.indexOf('warning:')).split('\n').every(line=>line.startsWith('warning:')));
 const hint=warnings.find(line=>line.includes(f.ports.pdd));assert.ok(hint,'done supplies the running package hint');assert.match(hint,/after.*address/i);assert.doesNotMatch(result.message,/type.*(?:your|own).*chat/i);assert.doesNotMatch(result.message,/already-addressed/);
 const command=hint.slice(hint.indexOf(f.ports.pdd));const argv=JSON.parse(execFileSync('bash',['-c',`set -- ${command}; node -e 'console.log(JSON.stringify(process.argv.slice(1)))' "$@"`],{cwd:f.base,env:{PATH:process.env.PATH,HOME:f.base},encoding:'utf8'}));assert.deepEqual(argv.slice(0,4),['/private/current node','/private/current package/bin/pdd.mjs',...PUBLIC_COMMAND_ROUTES.find(route=>route.id==='workflow.request-uptake').prefix]);assert.equal(argv[4],id);assert.equal(argv[5],'--summary');assert.equal(argv.length,7);assert.equal(fs.existsSync(f.base+'/injected'),false);assert.equal(f.bytes(),bytes);assert.equal(f.record().gate,null);
});
