import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,writeFileSync,readFileSync,rmSync,realpathSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {execFileSync,execFile as cb} from 'node:child_process';
import {promisify} from 'node:util';
import {startRun,stepDone,approveRun} from '../src/workflow-runner.mjs';
import * as runner from '../src/workflow-runner.mjs';
import {runPdd} from '../src/pdd-cli.mjs';
import {fakeHerdr} from './helpers/fake-herdr.mjs';
const exec=promisify(cb), root=realpathSync(new URL('..',import.meta.url).pathname);
const base=realpathSync(mkdtempSync(join(tmpdir(),'pdd2830-'))), source=join(base,'project'), state=join(base,'state'), home=join(base,'home');
for(const dir of [source,state,home]) mkdirSync(dir);
const git=(cwd,...args)=>execFileSync('git',args,{cwd,encoding:'utf8'}).trim();
try {
 git(source,'init','-q','-b','main');git(source,'config','user.email','test@example.invalid');git(source,'config','user.name','Test');git(source,'remote','add','origin','https://github.com/example/project.git');
 writeFileSync(join(source,'value.mjs'),'export const value = 1;\n');
 const skill=join(source,'.agents/skills/pdd-feature');mkdirSync(skill,{recursive:true});writeFileSync(join(skill,'workflow.json'),JSON.stringify({version:2,areas:[{name:'story',steps:['understand','prompt-story'],optional:[],gate:'approve'},{name:'prompt-pr',steps:['check','try'],optional:['try'],gate:'pr',then:'ask-code'},{name:'code',steps:['build','verify'],optional:[],gate:'pr'}]}));
 git(source,'add','.');git(source,'commit','-qm','initial');git(source,'update-ref','refs/remotes/origin/main',git(source,'rev-parse','HEAD'));
 const h=fakeHerdr(); let clock=Date.parse('2026-10-27T17:00:00Z');h.now=()=>clock;let pr, editArgs, intended, edits=0, rejectRetry=false, staleHead=false;const reason='GraphQL: Projects (classic) is being deprecated in favor of the new Projects experience, see: https://github.blog/changelog/2024-05-23-sunset-notice-projects-classic/ (repository.pullRequest.projectCards)';
 async function execFile(file,args,opts){
  if(file==='git'&&args[0]==='push'){const [from,to]=args[2].split(':');const sha=(await exec('git',['rev-parse',from],{cwd:opts.cwd})).stdout.trim();await exec('git',['update-ref',to.replace('refs/heads/','refs/remotes/origin/'),sha],{cwd:opts.cwd});return {stdout:''};}
  if(file==='git'&&args[0]==='fetch')return {stdout:''};
  if(file==='git'&&args[0]==='ls-remote'){const ref=args.at(-1);const r=await exec('git',['rev-parse','--verify','--quiet',ref.replace('refs/heads/','refs/remotes/origin/')],{cwd:opts.cwd}).catch(()=>({stdout:''}));return {stdout:r.stdout.trim()?`${r.stdout.trim()}\t${ref}\n`:'',code:r.stdout.trim()?0:2};}
  if(file==='git')return exec(file,args,{...opts,encoding:'utf8'});
  assert.equal(file,'gh');const flag=x=>args[args.indexOf(x)+1];
  if(args[0]==='repo')return {stdout:JSON.stringify({nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'})};
  if(args[0]==='api' && args.includes('PATCH')){editArgs=args;intended=JSON.parse(opts.input).body;if(++edits===2 || rejectRetry)return {stderr:reason,code:1};pr.body=intended;return {stdout:'{}'};}
  if(args[0]==='api')return {stdout:JSON.stringify({number:17,html_url:'https://github.com/example/project/issues/17',title:'Use value two',body:'Value must be two.'})};
  if(args[0]==='pr'&&args[1]==='list')return {stdout:JSON.stringify(pr?[pr]:[])};
  if(args[0]==='pr'&&args[1]==='create'){pr={number:23,url:'https://github.com/example/project/pull/23',state:'OPEN',headRefName:flag('--head'),baseRefName:flag('--base'),headRefOid:git(opts.cwd,'rev-parse','HEAD'),body:String(opts.input??''),title:flag('--title'),headRepository:{name:'project'},headRepositoryOwner:{login:'example'},isCrossRepository:false};return {stdout:pr.url+'\n'};}
  if(args[0]==='pr'&&args[1]==='view')return {stdout:JSON.stringify({state:'OPEN',body:pr.body,headRefOid:staleHead ? 'a'.repeat(40) : git(opts.cwd,'rev-parse','refs/remotes/origin/'+pr.headRefName)})};
  if(args[0]==='pr'&&args[1]==='edit'){editArgs=args;intended=String(opts.input??'');if(++edits===1){pr.body=intended;return {stdout:''};}return {stdout:'',stderr:reason,code:1};}
  throw Error(`unexpected ${file} ${args.join(' ')}`);
 }
 const ports={execFile,herdr:h.herdr,stateDir:state,layoutDirectory:join(state,'layout'),now:()=>clock,sleep:async ms=>{clock+=ms},findNativeSessions:s=>h.findNativeSessions(s),env:{HOME:home},isTTY:true,pdd:'/abs/node /abs/pdd.mjs',confirm:async()=>true,attach:async()=>0};
 const agent={...ports,isTTY:false,env:{HOME:home,PDD_AGENT_SESSION:'1'}};
 const started=await startRun({name:'feature',issue:'17',agent:'codex',cwd:source,packageRoot:root},ports);assert.equal(started.exitCode,0,started.message);
 const record=()=>JSON.parse(readFileSync(join(source,'.git/pdd/runs/17/status.json'),'utf8'));const run=record();
 async function done(step,summary){clock+=1000;const out=await stepDone({step,summary,cwd:run.root},agent);assert.equal(out.exitCode,0,out.message);return out;}
 await done('understand','understood');writeFileSync(join(run.root,'feature.prompt.md'),'Return two.\n');git(run.root,'add','.');git(run.root,'commit','-qm','prompt');await done('prompt-story','Story');clock+=1000;let out=await approveRun({ref:'17',cwd:source},ports);assert.equal(out.exitCode,0,out.message);
 writeFileSync(join(run.root,'feature.prompt.md'),'# Value\n\nReturn two.\n\n<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify({status:'draft',prose_sha256:'',entries:[],limits:{max_steps:1,max_model_calls:1}})+'\n```\n</details>\n');
 await done('check','Synthetic evidence café 🧪\nsecond line');await done('try','skipped');assert.ok(pr,'synthetic PR 1 created');assert.match(pr.body,/Draft prompts: feature\.prompt\.md/);h.idle();clock+=1000;
 out=await approveRun({ref:'17',cwd:source},ports);
 assert.match(out.message,/Projects \(classic\)/);
 const command=out.message.match(/pdd workflow refresh-description 17 23/)[0];
 assert.equal(record().areas[record().area].name,'code');
 await done('build','later progress');
 const before=record(); let stdout='',stderr='';
 const streams={stdout:{write:x=>stdout+=x},stderr:{write:x=>stderr+=x}};
 const call = async args => { stdout='';stderr='';return runPdd(args,{...streams,cwd:source,workflowRunner:{retryPrDescription:(input)=>runner.retryPrDescription(input,ports)}}); };
 for (const args of [['workflow','refresh-description','17'],['workflow','refresh-description','17','23','extra'],['workflow','refresh-description','17','23','--bad']]) assert.equal(await call(args),2);
 const priorBody=pr.body;
 assert.equal(await call(['workflow','refresh-description','17','99']),1);assert.equal(pr.body,priorBody);
 staleHead=true;assert.equal(await call(command.split(' ').slice(1)),1);assert.equal(pr.body,priorBody);staleHead=false;
 rejectRetry=true;assert.equal(await call(command.split(' ').slice(1)),1);assert.match(stderr,/Projects \(classic\)/);assert.match(stderr,/pdd workflow refresh-description 17 23/);assert.equal(pr.body,priorBody);rejectRetry=false;
 const rc=await runPdd(command.split(' ').slice(1),{...streams,cwd:source,workflowRunner:{retryPrDescription:(input)=>runner.retryPrDescription(input,ports)}});
 assert.equal(rc,0,stderr);assert.doesNotMatch(pr.body,/Draft prompts:/);
 const after=record(); for(const key of ['gate','done','area','chats','decisions'])assert.deepEqual(after[key],before[key]);
 assert.match(pr.body,/pdd-workflow:/);assert.match(pr.body,/café 🧪/);assert.match(pr.body,/\n/);
 console.log('native retry passed');
} finally {rmSync(base,{recursive:true,force:true});}
