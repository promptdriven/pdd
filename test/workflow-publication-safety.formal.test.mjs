import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync, existsSync, realpathSync, chmodSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFile as callbackExec, execFileSync } from 'node:child_process';
import { promisify } from 'node:util';
import { stepDone } from '../src/workflow-runner.mjs';
import { inventoryModule } from './workflow-inventory-replay-helper.mjs';
import { codeLiteral as span } from './workflow-inventory-code-spans-oracle.mjs';
import { readRun, writeRun } from '../src/workflow-runs.mjs';

const exec = promisify(callbackExec);
const initial=`test('keep', () => {\nassert.equal(value, 1);\n});\ntest('gone', () => {});\n`;
const changed=`test('keep', () => {\nassert.equal(value, 2);\n});\ntest.todo('later');\n`;
// Git is never stubbed. Only network addressing for real push/ls-remote is
// routed to a disposable local bare repository; identity reads see GitHub.
function fixture(t,{workflow='small-change',opted=false,promptPr=false,before=initial}={}) {
  const directory=realpathSync(mkdtempSync(join(tmpdir(),'pdd-inventory-pr-')));t.after(()=>rmSync(directory,{recursive:true,force:true}));
  const root=join(directory,'checkout'),remote=join(directory,'remote.git');mkdirSync(root);
  const git=(...args)=>execFileSync('git',args,{cwd:root,encoding:'utf8'}).trim();
  git('init','--bare','-q',remote);git('init','-q','-b','main');git('config','user.email','test@example.invalid');git('config','user.name','Inventory Test');
  git('remote','add','origin','https://github.com/example/project.git');mkdirSync(join(root,'test'));writeFileSync(join(root,'test/a.mjs'),before);git('add','.');git('commit','-qm','base');
  const baseSha=git('rev-parse','HEAD');git('push','-q',remote,'main');git('update-ref','refs/remotes/origin/main',baseSha);
  git('checkout','-qb','prompt');writeFileSync(join(root,'prompt.txt'),'published prompt\n');git('add','.');git('commit','-qm','prompt');const promptSha=git('rev-parse','HEAD');git('push','-q',remote,'prompt');git('update-ref','refs/remotes/origin/prompt',promptSha);
  git('checkout','-qb','topic');
  const commonDir=git('rev-parse','--path-format=absolute','--git-common-dir'),runDir=join(commonDir,'pdd/runs/17'),stateDir=join(directory,'state');
  const area={name:promptPr?'prompt-pr':'code',steps:['reproduce','scope','build','verify','review','formal'],optional:[],gate:'pr',...(promptPr?{then:'ask-code'}:{}),...(opted?{replay_evidence:'pdd.replay-evidence.v1'}:{})};
  const areas=workflow==='small-change'||promptPr?[area]:[{name:'prompt-pr',steps:['check'],optional:[],gate:'pr',then:'ask-code'},area];
  const run={runId:'inventory-run',workflow,repo:'example/project',number:17,issue:{number:17,title:'Inventory review',url:'https://github.com/example/project/issues/17'},root,sourceRoot:root,branch:'topic',baseBranch:'main',baseSha,commonDir,runDir,state:'running',areas,area:areas.length-1,done:Object.fromEntries(area.steps.filter(step=>step!=='formal').map(step=>[step,{summary:'completed'}])),chats:[],pr:workflow==='small-change'||promptPr?[]:[{stage:'prompt-pr',number:22,url:'https://github.com/example/project/pull/22',branch:'prompt',base:'main'}],...(workflow==='small-change'?{}:{prBase:'prompt'})};
  const f={root,remote,git,run,baseSha,promptSha,prs:[],events:[],edits:[],failCreate:false,failEdit:false};
  const ports={stateDir,env:{HOME:directory},now:()=>Date.now(),execFile:async(file,args,opts)=>{
    if(file==='git') {
      f.events.push({kind:'git',args:[...args]});
      const route=['push','ls-remote','fetch'].includes(args[0]);
      return exec('git',route?['-c',`url.${remote}.insteadOf=https://github.com/example/project.git`,...args]:args,{...opts,encoding:args[0]==='cat-file'?'buffer':'utf8'});
    }
    assert.equal(file,'gh');f.events.push({kind:'gh',args:[...args],...(args[0]==='api'&&args[2]==='PATCH'?{remote:git('--git-dir',remote,'rev-parse','refs/heads/topic'),body:JSON.parse(opts.input).body}:{})});
    const flag=name=>args[args.indexOf(name)+1];
    if(args[0]==='repo')return {stdout:JSON.stringify({nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'})};
    if(args[1]==='list')return {stdout:JSON.stringify(f.prs)};
    if(args[1]==='create') {
      if(f.failCreate)return {stdout:'',stderr:'GraphQL: temporarily denied (createPullRequest)',code:1};
      assert.equal(flag('--body-file'),'-');assert.equal(typeof opts.input,'string');
      const body=opts.input,headRefOid=git('rev-parse','HEAD');
      const pr={number:23,url:'https://github.com/example/project/pull/23',state:'OPEN',headRefName:flag('--head'),baseRefName:flag('--base'),headRefOid,body,isCrossRepository:false,headRepositoryOwner:{login:'example'},headRepository:{name:'project'},mergeCommit:null};
      f.prs.push(pr);return {stdout:pr.url};
    }
    if(args[0]==='pr' && args[1]==='edit') {
      f.editAttempts=(f.editAttempts??0)+1;
      if(f.editAttempts===f.failEditAt) { if(f.failure==='reject') throw Object.assign(new Error('Projects (classic) denied'),{code:0,stderr:'Projects (classic) denied'}); return {stdout:'',stderr:'Projects (classic) denied',code:1}; }
      f.prs[0].body=opts.input; return {stdout:''};
    }
    if(args[0]==='api'&&args[2]==='PATCH') {
      f.editAttempts=(f.editAttempts??0)+1;
      if(f.editAttempts===f.failEditAt) { if(f.failure==='reject') throw Object.assign(new Error('Projects (classic) denied'),{code:0,stderr:'Projects (classic) denied'}); return {stdout:'',stderr:'Projects (classic) denied',code:1}; }
      assert.equal(flag('--input'),'-');assert.equal(typeof opts.input,'string');
      const body=JSON.parse(opts.input).body;f.edits.push(body);f.prs[0].body=body;return {stdout:''};
    }
    assert.fail(`Unexpected gh ${args.join(' ')}`);
  }};
  writeRun(run,ports);f.ports=ports;f.record=()=>readRun(runDir);
  f.done=(summary='formal done')=>{
    const rows=summary.split('\n');
    for(const [step,select] of [['review',r=>r.startsWith('Review:')],['verify',r=>/^(?:Not fixed yet:|Proof \()/.test(r)],[workflow==='bug'?'reproduce':'scope',r=>/^(?:Defect:|Not caught because:)/.test(r)]]){
      const text=rows.filter(select).join('\n');if(text){const path=join(runDir,step+'.md');const warning=step==='verify'&&existsSync(path)?readFileSync(path,'utf8').split('\n').filter(row=>row.startsWith('✗ ')).join('\n'):'';writeFileSync(path,[warning,text].filter(Boolean).join('\n'));}
    }
    return stepDone({cwd:root,step:'formal',summary},ports);
  };
  f.remoteHead=()=>git('--git-dir',remote,'rev-parse','refs/heads/topic');
  return f;
}

test('bounded Story publication safety across phases and update outcomes', async t => {
  for (const phase of ['pending', 'final', 'informational']) for (const outcome of ['success', 'nonzero', 'reject']) {
    const f=fixture(t); writeFileSync(join(f.root,'test/a.mjs'),changed); assert.equal((await f.done()).exitCode,0);
    const before=f.remoteHead(), body=f.prs[0].body; f.events=[];
    if(phase!=='informational') writeFileSync(join(f.root,'test/a.mjs'),`test('new', () => {});\n`);
    f.failure=outcome; if(outcome!=='success') f.failEditAt=(f.editAttempts??0)+(phase==='final'?2:1);
    const result=await f.done(), pushed=f.remoteHead()!==before;
    const failed=outcome!=='success';
    assert.equal(pushed, phase!=='informational' && !(phase==='pending' && failed), `${phase}/${outcome} push`);
    assert.equal(result.exitCode, failed && phase!=='informational' ? 1 : 0, `${phase}/${outcome} exit`);
    if(failed) { assert.match(result.message,/Projects \(classic\)/); assert.match(result.message,/pdd workflow refresh-description 17 23/); }
    if(failed && phase!=='final') assert.equal(f.prs[0].body,body,`${phase}/${outcome} preserves body`);
    if(failed && phase==='final') assert.match(f.prs[0].body,/publication-pending/);
  }
});
