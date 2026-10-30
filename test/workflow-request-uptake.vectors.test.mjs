import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { uptakeFixture,runner,fs,facts,viewOptions,hostname } from './helpers/workflow-uptake-fixture.mjs';
import { runPdd,renderHelp } from '../src/pdd-cli.mjs';
import { PUBLIC_COMMAND_ROUTES } from '../src/command-catalog.mjs';
import { renderCompletion } from '../src/completion.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
const vectors=JSON.parse(fs.readFileSync(new URL('./workflow-request-uptake/cases.json',import.meta.url),'utf8'));
for(const v of vectors.cases.filter(v=>!v.id.startsWith('probe-I')))test(`2722 vector: ${v.id}`,{timeout:20000},async t=>{
 const f=await uptakeFixture(t),e=v.expect;
 switch(v.id){
 case 'delivered-visible-in-chat-receipt-status':{
  const healthy=f.ports.herdr;f.clock=1000;f.ports.herdr=async a=>{const r=await healthy(a);if(a[0]==='agent'&&a[1]==='prompt')f.clock=1007;return r;};
  const result=await f.change();assert.equal(result.exitCode,e.exitCode);const entry=f.read()[0];
  const raw=f.sent()[0][3];assert.equal(raw.split('\n')[0],`The person asks for changes: ${entry.text} Revise in this chat, run done again for the step you changed, then show the result and ask again.`);assert.equal(raw.split('\n').filter(line=>line.startsWith('pdd workflow ack ')).length,1);facts(raw,[entry.id,'--summary','workflow ack']);facts(result.message,[entry.id,'1007','not yet']);
  const row=await f.row();assert.deepEqual(row.requests,[{id:entry.id,text:entry.text,area:entry.area,deliveredAt:1007,ackedAt:null,ackSummary:null}]);
  for(const opts of viewOptions.filter(o=>!o.json))facts((await f.status(opts)).message,[entry.id]);break;
 }
 case 'joined-delivery-receipt':{
  let release,entered;const start=new Promise(r=>entered=r),gate=new Promise(r=>release=r);let prompts=0;
  const healthy=f.ports.herdr;f.ports.herdr=async a=>{if(a[0]==='agent'&&a[1]==='get'){entered();await gate;}if(a[0]==='agent'&&a[1]==='prompt')prompts++;return healthy(a);};
  const first=f.change();await start;const second=f.change('Explain the chosen value',{...f.ports,herdr:async a=>{if(a[0]==='agent'&&a[1]==='get')await first;return healthy(a);}});await new Promise(r=>setTimeout(r,30));release();const results=await Promise.all([first,second]);
  assert.equal(prompts,1);const saved=f.read()[0];for(const r of results){assert.equal(r.exitCode,0);facts(r.message,[saved.id,saved.deliveredAt]);}break;
 }
 case 'explicit-first-and-repeat':{
  f.save([f.entry(),f.orphan()]);const before=f.read(),run=JSON.stringify(f.record());f.ports.now=()=>2000;
  assert.equal((await f.ack('r1','  Added\n the reason  ')).exitCode,0);assert.deepEqual(f.read(),[{...before[0],ackedAt:e.ackedAt,ackSummary:e.ackSummary},before[1]]);
  const bytes=f.bytes();f.ports.now=()=>3000;assert.equal((await f.ack('r1','Different note')).exitCode,0);assert.equal(f.bytes(),bytes);assert.equal(JSON.stringify(f.record()),run);
  assert.deepEqual((await f.row()).requests.filter(r=>r.ackedAt==null),[]);f.save([f.entry('epoch',{ackedAt:0,ackSummary:'At epoch'})]);const zero=f.bytes();assert.equal((await f.ack('epoch','Later')).exitCode,0);assert.equal(f.bytes(),zero);break;
 }
 case 'concurrent-first-wins':{
  f.save([f.entry()]);let entered,release;const ready=new Promise(r=>entered=r),gate=new Promise(r=>release=r);let writes=0;
  // Hold the first claim with an owned contender; both public ACK calls start
  // before releasing it, then the first acquired claim is the durable winner.
  const lock=f.record().runDir+'/.delivery-journal.lock';fs.mkdirSync(lock);const leaf=lock+'/owner-held.json';fs.writeFileSync(leaf,JSON.stringify({pid:process.pid,hostname:hostname(),token:'held'}));
  f.ports.journalSleep=async()=>{entered();await gate;};f.ports.now=()=>2000;
  const a=f.ack('r1','First');await Promise.race([ready,a]);const b=f.ack('r1','Second');fs.unlinkSync(leaf);release();
  const results=await Promise.all([a,b]);assert.deepEqual(results.map(r=>r.exitCode),e.exitCodes);assert.equal(f.read()[0].ackSummary,e.ackSummary);assert.equal(f.read()[0].ackedAt,e.ackedAt);break;
 }
 case 'earlier-area-current-run':{
  f.save([f.entry()]);const run=f.record();run.area=2;writeRun(run,f.ports);const original=JSON.stringify(f.record());assert.equal((await f.ack()).exitCode,e.exitCode);assert.equal(JSON.stringify(f.record()),original);assert.equal(f.read()[0].area,'story');break;
 }
 case 'reject-invalid-domain':{
  const cases=[{id:undefined},{id:''},{id:' '},{id:3},{id:'unknown'},{id:'foreign-run-id'},{state:'pending'},{state:'uncertain'},{state:'pending',inFlight:true},{kind:'answer'},{summary:undefined},{summary:' \n '},{summary:3},{cwd:f.source},{cwd:f.base},{ended:true}];
  for(const c of cases){const run=f.record();run.state=c.ended?'completed':'running';writeRun(run,f.ports);f.save([f.entry('r1',{...(c.state?{state:c.state}:{}),...(c.kind?{kind:c.kind}:{}),...(c.inFlight?{inFlight:true,owner:{pid:process.pid,hostname:hostname(),token:'active'}}:{})}),f.orphan()]);const bytes=f.bytes(),progress=JSON.stringify(f.record());
   const result=await f.ack('id'in c?c.id:'r1','summary'in c?c.summary:'Added reason',{cwd:c.cwd});assert.notEqual(result.exitCode,0);assert.equal(f.bytes(),bytes);assert.equal(JSON.stringify(f.record()),progress);}
  const run=f.record();run.state='running';writeRun(run,f.ports);await f.positive();break;
 }
 case 'status-filter-and-time-boundaries':{
  f.save(v.given.requests.map(r=>{const entry=f.entry(r.id,r);if(!('deliveredAt'in r))delete entry.deliveredAt;return entry;}));const bytes=f.bytes();const row=await f.row();assert.equal(row.requests?.length,2,'status lists both delivered changes');assert.deepEqual(row.requests.map(({id,deliveredAt,ackedAt,ackSummary})=>({id,deliveredAt,ackedAt,ackSummary})),e.jsonRequests);assert.equal('requestWarning'in row,false);
  for(const opts of viewOptions.filter(o=>!o.json))facts((await f.status(opts)).message,['legacy','unknown']);const run=f.record();run.state='cancelled';writeRun(run,f.ports);assert.equal((await f.row()).group,'cancelled');facts((await f.status({ref:undefined,cancelled:true})).message,['legacy','unknown']);assert.equal(f.bytes(),bytes);break;
 }
 case 'done-and-gate-only-warn':{
  f.save([f.entry()]);for(const step of ['unknown','reproduce','prompt-story']){const r=await f.done(step);assert.equal(r.exitCode,0);facts(r.message,['r1','1000','not yet']);assert.equal(f.read()[0].ackedAt,undefined);}assert.equal(f.record().gate.kind,'approve');
  // Repeat at an existing PR ending using only the private fixture's GitHub port.
  const run=f.record();run.areas=[{name:'story',steps:['reproduce'],optional:[],gate:'pr'}];run.area=0;run.done={};run.gate=null;run.state='running';writeRun(run,f.ports);fs.writeFileSync(run.root+'/value.mjs','export const value = 2;\n');f.git(run.root,'add','.');f.git(run.root,'commit','-qm','fixture change');
  const published=await f.done('reproduce');assert.equal(published.exitCode,0,published.message);facts(published.message,['r1','1000','not yet']);assert.equal(f.prs.length,1);const repeated=await f.done('reproduce');assert.equal(repeated.exitCode,0,repeated.message);facts(repeated.message,['r1','1000','not yet']);assert.equal(f.prs.length,1);break;
 }
 case 'journal-failures':{
  for(const mode of ['busy','read','malformed','write']){
   f.save([f.entry(),f.orphan()]);if(mode==='malformed')fs.writeFileSync(f.path,'{broken');const bytes=f.bytes();let elapsed=0;
   const ports={...f.ports,journalElapsedNow:()=>elapsed,journalSleep:async ms=>{elapsed+=ms;},deliveryFiles:{...fs,readFileSync:(path,...a)=>{if(path===f.path&&mode==='read')throw Error('read denied');return fs.readFileSync(path,...a);},writeFileSync:(path,...a)=>{if(String(path).includes('delivery-journal.json.')&&mode==='write')throw Error('write denied');return fs.writeFileSync(path,...a);}}};
   if(mode==='busy'){const lock=f.record().runDir+'/.delivery-journal.lock';fs.mkdirSync(lock,{recursive:true});fs.writeFileSync(lock+'/owner-held.json',JSON.stringify({pid:process.pid,hostname:hostname(),token:'held'}));}
   assert.notEqual((await f.ack('r1','Added reason',{ports})).exitCode,0);assert.equal(f.bytes(),bytes);
   if(['read','malformed'].includes(mode)){const row=await f.row({},ports);assert.equal(row.requests,null);assert.equal(row.inFlightRequests,null);assert.ok(row.requestWarning&&row.requestWarning.length<600);for(const opts of viewOptions.filter(o=>!o.json))facts((await f.status(opts,ports)).message,['unavailable']);facts((await f.done('unknown',ports)).message,['unavailable']);}
   fs.rmSync(f.record().runDir+'/.delivery-journal.lock',{recursive:true,force:true});
  }await f.positive();break;
 }
 case 'stale-writers-and-new-delivery':{
  f.save([f.entry()]);f.ports.now=()=>2000;assert.equal((await f.ack('r1','Updated value')).exitCode,0);await f.status();await f.done();await runner.askPerson({text:'Continue?',cwd:f.record().root},f.ports);
  // Clear the question through the real answer flow, then deliver independent change.
  assert.equal((await f.change('yes')).exitCode,0);assert.equal((await f.change('Add an example')).exitCode,0);const rows=(await f.row()).requests;
  assert.equal(rows[0].ackedAt,e.r1AckedAt);assert.equal(rows[0].ackSummary,e.r1AckSummary);assert.equal(rows.length,2);assert.notEqual(rows[1].id,'r1');assert.equal(rows[1].ackedAt,null);break;
 }
 case 'no-delivery-no-uptake':{
  for(const state of ['pending','uncertain','in-flight']){f.save([f.entry('r1',{state:state==='in-flight'?'pending':state,...(state==='in-flight'?{inFlight:true,owner:{pid:process.pid,hostname:hostname(),token:'alive'}}:{})})]);const run=f.record();run.deliveryRequests=[f.entry('fake')];writeRun(run,f.ports);const before=f.sent().length,healthy=f.ports.herdr;const ports=state==='pending'?{...f.ports,sleep:async ms=>f.tick(ms),herdr:async args=>{if(args[0]==='agent'&&args[1]==='get')throw Object.assign(Error('starting'),{code:'agent_not_found'});return healthy(args);}}:f.ports;const delivery=await f.change('Explain the chosen value',ports);assert.notEqual(delivery.exitCode,0);assert.equal(f.sent().length,before);const row=await f.row();assert.deepEqual(row.requests,e.jsonRequests);assert.notEqual((await f.ack()).exitCode,0);}await f.positive();break;
 }
 case 'cli-catalog-dispatch':{
  const calls=[];const spy={acknowledgeRequest:async input=>{calls.push(input);return {exitCode:0,message:'Recorded uptake'};}};const invoke=args=>runPdd(args,{cwd:f.record().root,stdout:{write(){}},stderr:{write(){}},workflowRunner:spy});
  assert.equal(await invoke(['workflow','ack','r1','--summary','Added reason']),e.validExitCode);assert.equal(calls[0].requestId,e.forwarded.requestId);assert.equal(calls[0].summary,e.forwarded.summary);
  const count=calls.length;for(const tail of [['r1'],['r1','--summary',' '],['r1','--summary','one','--summary','two'],['--summary','one'],['r1','extra','--summary','one']])assert.equal(await invoke(['workflow','ack',...tail]),2);assert.equal(calls.length,count);
  const route=PUBLIC_COMMAND_ROUTES.find(r=>r.id==='workflow.request-uptake');assert.deepEqual(route.prefix,['workflow','ack']);facts(renderHelp(),[route.forms[0].form]);facts(renderCompletion('bash'),['ack']);break;
 }
 case 'visibility-snapshot-has-no-journal-effects':{
  f.save([f.orphan(),f.entry('open')]);const bytes=f.bytes();let claims=0;const ports={...f.ports,deliveryFiles:{...fs,mkdirSync:()=>{claims++;throw Error('visibility must not claim');}}};
  for(const opts of viewOptions)assert.equal((await f.status(opts,ports)).exitCode,0);const result=await f.done('unknown',ports);assert.equal(result.exitCode,0);facts(result.message,['open']);assert.equal(claims,e.journalClaimCalls);assert.equal(f.bytes(),bytes);break;
 }
 case 'shell-safe-derived-hints':{
  for(const id of v.given.injectedRequestIds){let token=0;f.ports.deliveryToken=()=>++token===2?id:`safe${token}`;const result=await f.change();assert.equal(result.exitCode,0);const message=f.sent().at(-1)[3],line=message.split('\n').find(s=>s.startsWith('pdd workflow ack '));assert.ok(line,'chat includes a standalone catalog-derived hint');
   const argv=JSON.parse(execFileSync('bash',['-c',`set -- ${line}; node -e 'console.log(JSON.stringify(process.argv.slice(1)))' "$@"`],{env:{PATH:process.env.PATH,HOME:f.base},cwd:f.base,encoding:'utf8'}));assert.deepEqual(argv.slice(0,4),['pdd','workflow','ack',id]);assert.equal(argv.length,6);assert.equal(argv[4],'--summary');assert.equal(fs.existsSync(f.base+'/injected'),false);assert.equal(message.split('\n').filter(line=>line.startsWith('pdd workflow ack ')).length,1);facts(message,[id,'Explain the chosen value']);}
  f.save([f.entry()]);facts((await f.ack('r1',' ')).message,['workflow ack',"'r1'",'--summary']);break;
 }
 case 'invalid-done-keeps-original-result':{
  let reads=0;const ports={...f.ports,deliveryFiles:{...fs,readFileSync:()=>{reads++;throw Error('unreadable');}}};
  for(const cwd of [f.source,f.base]){const r=await runner.stepDone({step:'reproduce',cwd},ports);assert.notEqual(r.exitCode,0);assert.ok(!r.message.includes('unavailable'));}
  for(const state of ['completed','cancelled']){const run=f.record();run.state=state;writeRun(run,f.ports);const r=await f.done('reproduce',ports);assert.equal(r.exitCode,0);assert.ok(!r.message.includes('unavailable'));}assert.equal(reads,0);
  const run=f.record();run.state='running';writeRun(run,f.ports);f.save([f.entry()]);facts((await f.done('unknown')).message,['r1']);break;
 }
 default:assert.fail(`Unmapped native group ${v.id}`);
 }
});
