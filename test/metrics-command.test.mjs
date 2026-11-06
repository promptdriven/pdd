import test from 'node:test';
import assert from 'node:assert/strict';
import {runMetrics} from '../src/metrics-command.mjs';

const at = '2026-11-05T12:00:00.000Z';
function setup() {
  let out='', err='', saved=[];
  const ports={repository:async()=>({root:'/repo',repo:'owner/repo'}),now:()=>at,historical:async()=>[],store:{readEvents:async()=>({events:saved}),appendEvents:async({events})=>{saved.push(...events);},exportMetrics:async()=>({repo:'owner/repo'}),importMetrics:async()=>{}},selector:async()=>({snapshotId:'s',events:[{schema:'pdd.metrics.event.v1',id:'1',repo:'owner/repo',issue:1,type:'selection',at,observedAt:at,source:'test',data:{snapshotId:'s',inScope:true,state:'unknown',reasons:['unobserved']}}]})};
  return {ports, stdout:s=>out+=s,stderr:s=>err+=s,get out(){return out},get err(){return err},get saved(){return saved}};
}
test('queue JSON and text share calculation and save its membership',async()=>{
  const x=setup(); assert.equal(await runMetrics({...x,argv:['--json']}),0); const report=JSON.parse(x.out); assert.equal(report.issues[0].selection.state,'unknown'); assert.equal(x.saved.length,1);
  const y=setup(); assert.equal(await runMetrics({...y,argv:[]}),0); assert.match(y.out,/Scope: queue s/); assert.match(y.out,/#1/);
});
test('rejects malformed date and mismatched imported repository',async()=>{
  const x=setup(); assert.equal(await runMetrics({...x,argv:['--date','2026-02-30']}),1); assert.match(x.err,/date/);
  const y=setup(); y.ports.readFile=async()=>JSON.stringify({repo:'another/repo'}); assert.equal(await runMetrics({...y,argv:['import','bundle.json']}),1); assert.match(y.err,/another repository/);
});
test('record forwards explicit facts to ledger validation',async()=>{
  const x=setup(); x.ports.readFile=async()=>JSON.stringify({repo:'owner/repo',type:'report'}); assert.equal(await runMetrics({...x,argv:['record','fact.json']}),0); assert.equal(x.saved[0].type,'report');
});

test('real Git and gh boundary retains mapped merge and does not copy old queue state', async t => {
  const {mkdtemp, mkdir, writeFile, rm} = await import('node:fs/promises');
  const {tmpdir} = await import('node:os');
  const {join} = await import('node:path');
  const {execFileSync} = await import('node:child_process');
  const root=await mkdtemp(join(tmpdir(),'metrics-command-'));
  t.after(()=>rm(root,{recursive:true,force:true}));
  execFileSync('git',['init','-q',root]);
  execFileSync('git',['-C',root,'remote','add','origin','https://github.com/owner/repo.git']);
  const bindir=join(root,'bin'); await mkdir(bindir);
  const head='a'.repeat(40), oldPath=process.env.PATH;
  const pull=JSON.stringify({head:{sha:head},merged_at:'2026-11-04T00:00:00Z',html_url:'https://github.com/owner/repo/pull/9'});
  const comment=JSON.stringify({id:42,author_association:'OWNER',body:'```json\n'+JSON.stringify({verdict:'PASS',head,risk:2,family:'codex',session:'fresh-1',checker_mode:'same-family',evidence:['checked code']})+'\n```',html_url:'https://github.com/owner/repo/pull/9#issuecomment-42',created_at:at});
  await writeFile(join(bindir,'gh'),`#!/bin/sh\ncase "$*" in\n  *check-runs*) printf '%s\\n' '{"check_runs":[{"name":"unit","head_sha":"${head}","status":"completed","conclusion":"failure","html_url":"https://github.com/check/1"}]}' ;;\n  *pulls/9/files*) printf '%s\\n' '[]' ;;\n  *pulls/9*) printf '%s\\n' '${pull}' ;;\n  *comments*) printf '%s\\n' '${comment}' ;;\n  *) printf '%s\\n' '{"number":1}' ;;\nesac\n`,{mode:0o755});
  process.env.PATH=`${bindir}:${oldPath}`; t.after(()=>{process.env.PATH=oldPath;});
  const {appendEvents}=await import('../src/metrics-store.mjs');
  const base={schema:'pdd.metrics.event.v1',repo:'owner/repo',issue:1,at,observedAt:at,source:'test'};
  await appendEvents({root,events:[{...base,id:'old-selection',type:'selection',data:{snapshotId:'old',inScope:true,state:'ready',reasons:[]}},{...base,id:'mapping',type:'milestone',data:{stage:'code-pr',pr:9}}]});
  let out='',err=''; const code=await runMetrics({cwd:root,argv:['--json'],now:()=>at,stdout:s=>out+=s,stderr:s=>err+=s});
  assert.equal(code,0,err); const report=JSON.parse(out);
  assert.equal(report.issues[0].selection.state,'unknown');
  assert.equal(report.issues[0].checks[0].data.acceptance,'accepted');
  assert.equal(report.issues[0].ci[0].data.status,'failed');
  assert.equal(report.issues[0].deliveries[0].data.head,head);
  assert.equal(report.issues[0].deliveries[0].at,'2026-11-04T00:00:00.000Z');
});

test('declared absent sources and past cutoff remain visible',async()=>{
  const x=setup(); assert.equal(await runMetrics({...x,argv:['--json','--snapshot','s','--at','2026-11-04T12:00:00Z','--expected-source','install:missing']}),0);
  const report=JSON.parse(x.out); assert.equal(report.observedAt,'2026-11-04T12:00:00.000Z'); assert.ok(report.coverage.missingSources.includes('install:missing')); assert.equal(report.issues.length,0);
  const y=setup(); assert.equal(await runMetrics({...y,argv:['--at','2026-11-04T12:00:00Z']}),1); assert.match(y.err,/requires --date or --snapshot/);
});

test('equivalent head requires matching Git patch IDs and exact-head green full suite', async t => {
  const {mkdtemp, mkdir, writeFile, rm} = await import('node:fs/promises');
  const {tmpdir} = await import('node:os'); const {join} = await import('node:path');
  const {execFileSync} = await import('node:child_process');
  const root=await mkdtemp(join(tmpdir(),'metrics-equivalent-')); t.after(()=>rm(root,{recursive:true,force:true}));
  const git=(...args)=>execFileSync('git',['-C',root,...args],{encoding:'utf8'}).trim();
  execFileSync('git',['init','-q',root]); git('config','user.name','Fixture'); git('config','user.email','fixture@example.test'); git('remote','add','origin','https://github.com/owner/repo.git');
  git('commit','--allow-empty','-qm','base'); const base=git('rev-parse','HEAD');
  await writeFile(join(root,'example'),'same change\n'); git('add','example'); git('commit','-qm','first'); const old=git('rev-parse','HEAD');
  git('reset','--hard',base); git('commit','--allow-empty','-qm','other parent'); await writeFile(join(root,'example'),'same change\n'); git('add','example'); git('commit','-qm','second'); const head=git('rev-parse','HEAD');
  const comment=JSON.stringify({id:43,author_association:'OWNER',body:'```json\n'+JSON.stringify({verdict:'PASS',head:old,risk:2,family:'codex',session:'fresh-1',checker_mode:'same-family',evidence:['checked code']})+'\n```',html_url:'https://github.com/owner/repo/pull/9#issuecomment-43',created_at:at});
  const pull=JSON.stringify({head:{sha:head}}), suite=JSON.stringify({check_runs:[{name:'full suite',head_sha:head,status:'completed',conclusion:'success'}]});
  const bindir=join(root,'bin'); await mkdir(bindir); await writeFile(join(bindir,'gh'),`#!/bin/sh\ncase "$*" in\n *check-runs*) printf '%s\\n' '${suite}' ;;\n *pulls/9/files*) printf '%s\\n' 'src/example.mjs' ;;\n *pulls/9*) printf '%s\\n' '${pull}' ;;\n *comments*) printf '%s\\n' '${comment}' ;;\n *) printf '%s\\n' '{"number":1}' ;;\nesac\n`,{mode:0o755});
  const oldPath=process.env.PATH; process.env.PATH=`${bindir}:${oldPath}`; t.after(()=>{process.env.PATH=oldPath;});
  const {appendEvents}=await import('../src/metrics-store.mjs');
  await appendEvents({root,events:[{schema:'pdd.metrics.event.v1',id:'mapping',repo:'owner/repo',issue:1,type:'milestone',at,observedAt:at,source:'test',data:{stage:'implementation-ready',pr:9,head}}]});
  let out='',err=''; assert.equal(await runMetrics({cwd:root,argv:['--json'],stdout:s=>out+=s,stderr:s=>err+=s}),0,err);
  const checks=JSON.parse(out).issues[0].checks; assert.ok(checks.some(e=>e.data.head===old)); assert.ok(checks.some(e=>e.data.head===head && e.data.acceptance==='equivalent'));
});

test('remote observations retain actual time and cannot establish a past cutoff',async()=>{
  const x=setup(), cutoff='2026-11-04T12:00:00.000Z'; let actual;
  x.ports.historical=async()=>[{schema:'pdd.metrics.event.v1',id:'historic',repo:'owner/repo',issue:1,type:'selection',at:cutoff,observedAt:cutoff,source:'test',data:{snapshotId:'s',inScope:true,state:'ready',reasons:[]}}];
  x.ports.github=async({observedAt})=>{actual=observedAt; return [{schema:'pdd.metrics.event.v1',id:'later',repo:'owner/repo',issue:1,type:'delivery',at:cutoff,observedAt,source:'test',data:{pr:9,head:'abc',explicit:true,evidence:'https://github.com/owner/repo/pull/9'}}];};
  assert.equal(await runMetrics({...x,argv:['--json','--snapshot','s','--at',cutoff]}),0); assert.equal(actual,at);
  const report=JSON.parse(x.out); assert.equal(report.issues[0].deliveries.length,0);
});
