import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,writeFileSync,readFileSync,rmSync,realpathSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {execFileSync,execFile as cb} from 'node:child_process';
import {promisify} from 'node:util';
import {startRun,stepDone,approveRun,cancelRun,retryPrDescription} from '../src/workflow-runner.mjs';
import {runPdd} from '../src/pdd-cli.mjs';
import {fakeHerdr} from './helpers/fake-herdr.mjs';
const exec=promisify(cb), packageRoot=realpathSync(new URL('..',import.meta.url).pathname);
async function scenario(mode="retry") {
 const dir=realpathSync(mkdtempSync(join(tmpdir(),'pdd-repair-'))),source=join(dir,'source'),state=join(dir,'state'),home=join(dir,'home');
 for(const path of [source,state,home])mkdirSync(path);
 const git=(cwd,...args)=>execFileSync('git',args,{cwd,encoding:'utf8'}).trim();
 try {
  git(source,'init','-q','-b','main');git(source,'config','user.email','test@example.invalid');git(source,'config','user.name','Test');git(source,'remote','add','origin','https://github.com/example/project.git');
  mkdirSync(join(source,'test'));writeFileSync(join(source,'test/value.test.mjs'),"test('one', () => {});\n");
  const skill=join(source,'.agents/skills/pdd-small-change');mkdirSync(skill,{recursive:true});writeFileSync(join(skill,'workflow.json'),JSON.stringify({version:2,areas:[{name:'plan',steps:['scope'],optional:[],gate:'approve'},{name:'build',steps:['change','verify','formal'],optional:[],gate:'pr'}]}));
  git(source,'add','.');git(source,'commit','-qm','base');git(source,'update-ref','refs/remotes/origin/main',git(source,'rev-parse','HEAD'));
  const h=fakeHerdr();let clock=Date.parse('2026-10-27T17:00:00Z'),pr,patches=0,failAt=0,failedBody,injectCancel=false,injectProgress=false,patchError=null,failFetch=false;h.now=()=>clock;
  const ports={stateDir:state,layoutDirectory:join(state,'layout'),now:()=>clock,sleep:async ms=>{clock+=ms},findNativeSessions:s=>h.findNativeSessions(s),env:{HOME:home},isTTY:true,pdd:'/abs/node /abs/pdd.mjs',confirm:async()=>true,attach:async()=>0,herdr:h.herdr};
  ports.execFile=async(file,args,opts)=>{
   if(file==='git'&&args[0]==='push'){const [from,to]=args[2].split(':');const sha=(await exec('git',['rev-parse',from],{cwd:opts.cwd})).stdout.trim();await exec('git',['update-ref',to.replace('refs/heads/','refs/remotes/origin/'),sha],{cwd:opts.cwd});return {stdout:''};}
   if(file==='git'&&args[0]==='fetch'){if(failFetch)throw Error('fetch failed');return {stdout:''};}
   if(file==='git'&&args[0]==='ls-remote'){const ref=args.at(-1);const r=await exec('git',['rev-parse','--verify','--quiet',ref.replace('refs/heads/','refs/remotes/origin/')],{cwd:opts.cwd}).catch(()=>({stdout:''}));return {stdout:r.stdout.trim()?`${r.stdout.trim()}\t${ref}\n`:'',code:r.stdout.trim()?0:2};}
   if(file==='git'){
    const result=await exec(file,args,{...opts,encoding:'utf8'});
    if(injectCancel&&args[0]==='merge-base'&&args[2]==='refs/remotes/origin/main'){injectCancel=false;const stopped=await cancelRun({ref:'17',cwd:source},ports);assert.equal(stopped.exitCode,0,stopped.message);}
    return result;
   }
   assert.equal(file,'gh');const flag=x=>args[args.indexOf(x)+1];
   if(args[0]==='repo')return {stdout:JSON.stringify({nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'})};
   if(args[0]==='api'&&args.includes('PATCH')){if(patchError)throw patchError;const body=JSON.parse(opts.input).body;patches++;if(patches===failAt){failedBody=body;return {stderr:'update denied',code:1};}pr.body=body;return {stdout:'{}'};}
   if(args[0]==='api')return {stdout:JSON.stringify({number:17,html_url:'https://github.com/example/project/issues/17',title:'Improve café 🧪',body:'Change tests.'})};
   if(args[0]==='pr'&&args[1]==='list')return {stdout:JSON.stringify(pr?[pr]:[])};
   if(args[0]==='pr'&&args[1]==='create'){pr={number:23,url:'https://github.com/example/project/pull/23',state:'OPEN',headRefName:flag('--head'),baseRefName:flag('--base'),headRefOid:git(opts.cwd,'rev-parse','HEAD'),body:String(opts.input??''),title:flag('--title'),headRepository:{name:'project'},headRepositoryOwner:{login:'example'},isCrossRepository:false};return {stdout:pr.url+'\n'};}
   if(args[0]==='pr'&&args[1]==='view'&&injectProgress){injectProgress=false;const advanced=await done('formal','Later publication');assert.equal(advanced.exitCode,0,advanced.message);}
   if(args[0]==='pr'&&args[1]==='view')return {stdout:JSON.stringify({state:'OPEN',body:pr.body,headRefOid:git(opts.cwd,'rev-parse','refs/remotes/origin/'+pr.headRefName)})};
   throw Error(`unexpected ${file} ${args.join(' ')}`);
  };
  const agent={...ports,isTTY:false,env:{HOME:home,PDD_AGENT_SESSION:'1'}};
  const started=await startRun({name:'small-change',issue:'17',agent:'codex',cwd:source,packageRoot},ports);assert.equal(started.exitCode,0,started.message);
  const record=()=>JSON.parse(readFileSync(join(source,'.git/pdd/runs/17/status.json'),'utf8')),run=record();
  const done=async(step,summary)=>{clock+=1000;return stepDone({step,summary,cwd:run.root},agent);};
  assert.equal((await done('scope','Scope café 🧪\nsecond line')).exitCode,0);clock+=1000;let out=await approveRun({ref:'17',cwd:source},ports);assert.equal(out.exitCode,0,out.message);
  assert.equal((await done('change','Changed')).exitCode,0);assert.equal((await done('verify','Verified')).exitCode,0);
  writeFileSync(join(run.root,'test/value.test.mjs'),"test('two', () => {});\n");out=await done('formal','Formal café 🧪\nsecond line');assert.equal(out.exitCode,0,out.message);assert.ok(pr);
  const old=pr.body,oldHead=record().testInventory.headSha;writeFileSync(join(run.root,'test/value.test.mjs'),"test('three', () => {});\ntest('four', () => {});\n");
  if(mode==='cancel'){injectCancel=true;const count=patches;out=await done('formal','Formal café 🧪\nsecond line');assert.equal(out.exitCode,1);assert.equal(patches,count);assert.equal(pr.body,old);assert.equal(record().state,'cancelled');return;}
  failAt=patches+2;out=await done('formal','Formal café 🧪\nsecond line');assert.equal(out.exitCode,1,out.message);const command=out.message.match(/pdd workflow refresh-description 17 23/)[0];assert.match(pr.body,/publication-pending/);assert.equal(record().testInventory.headSha,oldHead);
  const head=git(run.root,'rev-parse','HEAD');assert.notEqual(head,oldHead);let stderr='';
  const call=()=>runPdd(command.split(' ').slice(1),{cwd:source,stdout:{write(){}},stderr:{write:x=>stderr+=x},workflowRunner:{retryPrDescription:input=>retryPrDescription(input,ports)}});
  if(mode==='unavailable') {const before=JSON.stringify(record()),body=pr.body;failFetch=true;assert.equal(await call(),1);assert.equal(pr.body,body);assert.equal(JSON.stringify(record()),before);return;}
  if(mode==='concurrent') {injectProgress=true;const rc=await call();assert.equal(rc,1);assert.match(stderr,/workflow changed/);assert.equal(record().done.formal.summary,'Later publication');assert.match(pr.body,/Later publication/);return;}
  patchError=Object.assign(new Error('denied ghp_ABC123 \u001b[31m /home/person/private.txt'),{code:0});
  assert.equal(await call(),1);assert.match(stderr,/denied/);assert.doesNotMatch(stderr,/ghp_ABC123|\u001b|\/home\/person/);assert.match(pr.body,/publication-pending/);
  patchError=null;stderr='';const rc=await call();
  assert.equal(rc,0,stderr);assert.equal(pr.body,failedBody);assert.ok(pr.body.includes(`→ ${head.slice(0,7)}.`));assert.match(pr.body,/café 🧪`<br>`second line/);assert.doesNotMatch(pr.body,/publication-pending/);
 } finally {rmSync(dir,{recursive:true,force:true});}
}
for (const mode of process.env.PDD_REPAIR_CASE ? [process.env.PDD_REPAIR_CASE] : ['retry','cancel','concurrent','unavailable']) await scenario(mode);
console.log('repair boundary and retry passed');
