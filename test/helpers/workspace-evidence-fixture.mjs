import './test-home.mjs';
// Synthetic local repositories and receipts. No hosted result or remote authority.
import assert from 'node:assert/strict';
import {execFileSync,execFile as callbackExec} from 'node:child_process';
import {promisify} from 'node:util';
import {cpSync,mkdirSync,mkdtempSync,readFileSync,realpathSync,rmSync,writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join,resolve} from 'node:path';
import {captureSource} from '../../src/runtime-preflight.mjs';
import {renderJson} from '../../src/runtime-output.mjs';
import * as runner from '../../src/workflow-runner.mjs';
const {associateEvidenceWorkspace}=runner;
const exec=promisify(callbackExec);
const packageRoot=resolve(import.meta.dirname,'../..');
export const selection=['tests/place-order.json'];
export async function evidenceFixture(t) {
  const base=realpathSync(mkdtempSync(join(tmpdir(),'pdd-evidence-')));
  t.after(()=>rmSync(base,{recursive:true,force:true}));
  const root=join(base,'owned'),clone=join(base,'clone'),other=join(base,'other'),nested=join(root,'.pdd-runtime/project');
  mkdirSync(root); const git=(cwd,...args)=>execFileSync('git',args,{cwd,encoding:'utf8'}).trim();
  git(root,'init','-q','-b','main');git(root,'config','user.name','Native fixture');git(root,'config','user.email','native@example.invalid');
  git(root,'remote','add','origin','https://github.com/example/project.git');
  for(const dir of ['prompts','tests','user_stories'])cpSync(join(packageRoot,'test/fixtures/harbor',dir),join(root,dir),{recursive:true});
  const prompt=join(root,'prompts/place_order.prompt.md');
  writeFileSync(prompt,readFileSync(prompt,'utf8').replace('## Dependencies\n\nNone.','## Dependencies\n\n[Menu rules](../docs/menu.md): required authored context.\n[Palette](../docs/palette.bin): required bytes.'));
  mkdirSync(join(root,'docs'));writeFileSync(join(root,'docs/menu.md'),'Authored menu rules.\n');writeFileSync(join(root,'docs/palette.bin'),Buffer.from([0,255,128,10,13,42]));
  git(root,'add','.');git(root,'commit','-qm','Synthetic authored source');const head=git(root,'rev-parse','HEAD');
  for(const dir of [clone,other]) {git(base,'clone','-q',root,dir);git(dir,'remote','set-url','origin','https://github.com/example/project.git');}
  mkdirSync(nested,{recursive:true});git(nested,'init','-q');
  for(const dir of ['prompts','tests','user_stories','docs'])cpSync(join(root,dir),join(nested,dir),{recursive:true});
  git(nested,'add','.');
  const commonDir=realpathSync(join(root,'.git')),runDir=join(commonDir,'pdd/runs/17');mkdirSync(runDir,{recursive:true});
  const status=join(runDir,'status.json'),run={v:1,number:17,repo:'example/project',runId:'synthetic-evidence-run',root,sourceRoot:root,commonDir,runDir,
    issue:{title:'Synthetic evidence import',number:17,url:'https://github.com/example/project/issues/17'},workflow:'bug',agent:'codex',branch:'main',baseBranch:'main',baseSha:head,state:'waiting',area:0,
    areas:[{name:'prompt-pr',steps:['check'],optional:[],gate:'pr',then:'ask-code'},{name:'code',steps:['build','verify'],optional:[],gate:'pr'}],
    done:{check:{at:1,summary:'Synthetic completed step'}},gate:{id:'gate-sentinel',kind:'approve-pr',area:'prompt-pr',at:2},
    question:{text:'Protected question',at:3},decisions:[{words:'Protected fixture decision'}],approvalRecord:{words:'Protected fixture approval'},
    chats:[],pr:[],startedAt:1,updatedAt:2};
  const f={base,root,clone,other,nested,runDir,status,head,git,read:()=>JSON.parse(readFileSync(status,'utf8')),save:r=>writeFileSync(status,JSON.stringify(r,null,2)+'\n'),clock:1000,effects:[]};
  f.save(run);
  f.ports={stateDir:join(base,'state'),env:{HOME:join(base,'home')},now:()=>++f.clock,readPrStatus:async()=>({}),
    herdr:async()=>assert.fail('Evidence must not invoke Herdr'),confirm:async()=>assert.fail('Registration adds no approval gate'),
    execFile:async(file,args,opts)=>{
      f.effects.push([file,...args]);assert.equal(file,'git','No network, model, publication or other program');
      assert.ok(['rev-parse','ls-files','ls-tree','cat-file','init','update-index'].includes(args[0]),`Unexpected effect: ${args}`);
      // Only the retained snapshot may receive local Git writes.
      if(['init','update-index'].includes(args[0]))assert.ok(opts.cwd.startsWith(join(runDir,'evidence-pr1/')));
      if(opts.input!==undefined)return new Promise((resolve,reject)=>{
        const {input,...options}=opts;
        const child=callbackExec(file,args,{...options,encoding:opts.encoding??'utf8'},(error,stdout,stderr)=>error?reject(error):resolve({stdout,stderr}));
        child.stdin.on('error',reject);child.stdin.end(input);
      });
      return exec(file,args,{...opts,encoding:opts.encoding??'utf8'});
    }};
  f.register=async(workspace,stage='current',tests=selection)=>{
    assert.equal(typeof associateEvidenceWorkspace,'function','Native evidence registration must exist');
    const before=f.read();const result=await associateEvidenceWorkspace({ref:'17',workspace,stage,tests,cwd:root},f.ports);
    assert.equal(result.exitCode,0,result.message);assertProtected(before,f.read());return f.read().evidenceAssociations.at(-1);
  };
  f.receipt=(producer,tests=selection)=>{
    const captured=captureSource(producer,{tests,appMap:null});
    const rows=tests.map(test=>{const doc=JSON.parse(readFileSync(join(producer,test),'utf8'));return {test,story:doc.story_path.split('/').at(-1).replace('.md',''),phase:'server',state:'passed',calls:0,
      criteria_total:doc.criteria.length,criteria:{passed:doc.criteria.length,total:doc.criteria.length},checks:{passed:10,total:10},
      criterion_results:doc.criteria.map(c=>({criterion_id:c.id,passed:true})),steps:doc.steps,criterion_texts:doc.criteria,
      request_id:'synthetic-request',report_url:'https://runtime.example.invalid/r/synthetic-report'};});
    const doc=renderJson({repo:producer,sourceSha256:captured.sha256,rows,exitCode:0});
    const bytes=JSON.stringify({...doc,batch:'synthetic-original-batch'},null,2)+'\n';
    const file=join(base,`receipt-${++f.clock}.json`);writeFileSync(file,bytes);return {file,bytes,doc:JSON.parse(bytes)};
  };
  f.pr1=()=>{const r=f.read();r.pr=[{stage:'prompt-pr',number:23,url:'https://github.com/example/project/pull/23',branch:'main',publishedHeadSha:head,state:'open'}];f.save(r);};
  f.enterCode=()=>{const r=f.read();r.area=1;r.state='running';r.gate=null;r.question=null;f.save(r);for(const path of ['prompts/place_order.prompt.md','user_stories/place-order.md','tests/place-order.json'])writeFileSync(join(root,path),readFileSync(join(root,path),'utf8')+'\n');};
  return f;
}
export function assertProtected(before,after) {
  for(const key of ['done','state','area','gate','question','decisions','approvalRecord','chats','pr','prState','branch'])assert.deepEqual(after[key],before[key],`Protected workflow ${key}`);
}
