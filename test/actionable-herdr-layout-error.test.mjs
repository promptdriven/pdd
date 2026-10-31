import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,realpathSync,readFileSync,writeFileSync,rmSync,existsSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join,resolve} from 'node:path';
import {pathToFileURL} from 'node:url';
import {execFileSync,spawnSync} from 'node:child_process';
// Run outside SOURCE: PDD_LAYOUT_SOURCE=/absolute/checkout node --test /absolute/draft.
// Builder copies this unchanged to test/actionable-herdr-layout-error.test.mjs before code.
const source=resolve(process.env.PDD_LAYOUT_SOURCE ?? new URL('..',import.meta.url).pathname);
const layoutModule=await import(pathToFileURL(join(source,'src/workflow-herdr-layout.mjs')));
const {openRun,approveRun}=await import(pathToFileURL(join(source,'src/workflow-runner.mjs')));
const {closeChats}=await import(pathToFileURL(join(source,'src/workflow-chat.mjs')));
async function fixture(t){
 const root=realpathSync(mkdtempSync(join(tmpdir(),'pdd-actionable-layout-')));t.after(()=>rmSync(root,{recursive:true,force:true}));
 const parent=join(root,'repo'),cwd=join(root,'run'),home=join(root,'home'),directory=join(home,'layout');mkdirSync(parent);mkdirSync(home);
 const git=(where,...args)=>execFileSync('git',args,{cwd:where,encoding:'utf8',env:{...process.env,HOME:home,GIT_CONFIG_NOSYSTEM:'1'}}).trim();
 git(parent,'init','-q','-b','main');git(parent,'-c','user.name=Test','-c','user.email=test@example.invalid','commit','--allow-empty','-qm','Base');git(parent,'remote','add','origin','https://github.com/example/project.git');git(parent,'worktree','add','-q','-b','test-run',cwd);
 const commonDir=join(parent,'.git'),runId='11111111-1111-4111-8111-111111111111',calls=[],rows=[],panes=[];let n=0,patchReply=x=>x;
 const command=async args=>{
  calls.push(args);const [group,verb]=args,flag=k=>args[args.indexOf(k)+1];let result;
  if(group==='status')return {running:true};
  if(group==='workspace'&&verb==='list')return {id:'cli:workspace:list',result:{type:'workspace_list',workspaces:structuredClone(rows)}};
  if(group==='workspace'&&verb==='create'||group==='worktree'&&verb==='open'){
   const w={workspace_id:`w${++n}`,worktree:{checkout_path:group==='workspace'?flag('--cwd'):flag('--path'),repo_key:commonDir,is_linked_worktree:group==='worktree'},label:flag('--label')};rows.push(w);
   const pane={workspace_id:w.workspace_id,tab_id:`t${n}`,pane_id:`p${n}`,terminal_id:`term${n}`,cwd:w.worktree.checkout_path};panes.push(pane);
   return {id:`cli:${group}:${verb}`,result:{workspace:w,tab:{tab_id:pane.tab_id},root_pane:pane}};
  }
  if(group==='pane'&&verb==='list')result={id:'cli:pane:list',result:{type:'pane_list',panes:structuredClone(panes.filter(p=>p.workspace_id===flag('--workspace')))}};
  if(group==='tab'&&verb==='list')result={id:'cli:tab:list',result:{type:'tab_list',tabs:[{tab_id:panes.find(p=>p.workspace_id===flag('--workspace')).tab_id}]}};
  if(group==='tab'&&verb==='create')return {id:'cli:tab:create',result:{tab:{tab_id:'area-tab'},root_pane:{pane_id:'area-pane',terminal_id:'area-term'}}};
  if(group==='tab'&&verb==='close')return {id:'cli:tab:close',result:{type:'ok'}};
  if(result)return patchReply(result);
  assert.fail(`Unexpected external call ${JSON.stringify(args)}`);
 };
 const input={repository:'example/project',issueNumber:17,runId,workflowName:'small-change',stageId:'plan',sourceRoot:parent,commonDir,cwd};
 const ports={directory,command,checkpoint:async()=>{}};
 const open=()=>layoutModule.withHerdrLayoutLock(()=>layoutModule.openHerdrRunLayout(input,ports),ports);
 const layout=await open(),runDir=join(commonDir,'pdd','runs','17');mkdirSync(runDir,{recursive:true});
 const run={v:1,skill:'pdd-small-change',branch:'test-run',issue:{title:'Layout diagnostic',url:'https://github.com/example/project/issues/17'},repo:input.repository,number:17,runId,workflow:'small-change',root:cwd,sourceRoot:parent,commonDir,runDir,agent:'codex',area:0,areas:[{name:'plan',steps:['plan'],optional:[],gate:'approve'}],state:'waiting',decisions:[],done:{},chats:[],pr:[],warnings:[],baseBranch:'main',baseSha:git(parent,'rev-parse','HEAD')};
 const save=()=>writeFileSync(join(runDir,'status.json'),JSON.stringify(run));save();
 const runnerPorts={env:{HOME:home},herdr:command,layoutDirectory:directory,isTTY:false,stateDir:join(home,'state')};
 return {root,home,parent,cwd,input,ports,layout,rows,panes,calls,open,run,save,runnerPorts,patch:f=>{patchReply=f;},registry:()=>readFileSync(join(directory,'registry.json'),'utf8')};
}
function diagnostic(message,{workspace,field,expected,found}){
 assert.ok(message.includes(workspace),`workspace ${workspace}: ${message}`);
 assert.ok(message.includes(field),`field ${field}: ${message}`);
 assert.match(message,/expected/i);assert.match(message,/found/i);
 assert.ok(message.includes(expected),`expected value ${expected}: ${message}`);
 assert.ok(message.includes(found),`found value ${found}: ${message}`);
 assert.match(message,/Herdr/);assert.match(message,/pdd/);assert.match(message,/inspect/i);assert.match(message,/restor/i);assert.match(message,/retry/i);
 assert.equal(message.split('\n').length,1,'one-line diagnostic');assert.ok(message.length<3000,'bounded diagnostic');
}
for(const kind of ['checkout_path','repo_key','is_linked_worktree','missing-metadata','missing-workspace','terminal_id','pane-count']){
 test(`actionable layout refusal: ${kind} retains ownership and shows expected/found`,async t=>{
  const f=await fixture(t),w=f.rows.find(w=>w.workspace_id===f.layout.workspaceId),p=f.panes.find(p=>p.workspace_id===w.workspace_id);let field=kind,expected,found;
  if(kind==='checkout_path'||kind==='repo_key'){expected=w.worktree[kind];found='/different';w.worktree[kind]=found;}
  if(kind==='is_linked_worktree'){expected='true';found='false';w.worktree.is_linked_worktree=false;}
  if(kind==='missing-metadata'){field='worktree';expected='present';found='missing';delete w.worktree;}
  if(kind==='missing-workspace'){field='workspace';expected=w.workspace_id;found='missing';f.rows.splice(f.rows.indexOf(w),1);}
  if(kind==='terminal_id'){expected=p.terminal_id;found='changed-terminal';p.terminal_id=found;}
  if(kind==='pane-count'){field='panes';expected='1';found='2';f.panes.push({...p,pane_id:'extra'});}
  const before=f.registry(),count=f.calls.length;
  const action=kind==='pane-count'?()=>layoutModule.withHerdrLayoutLock(()=>layoutModule.closeHerdrRunLayout({...f.input,layout:f.layout},f.ports),f.ports):f.open;
  let caught;try{await action();}catch(e){caught=e;}
  assert.equal(caught?.code,'herdr_layout_identity_changed');
  assert.equal(f.registry(),before);assert.ok(existsSync(join(f.cwd,'.git')));assert.ok(f.calls.slice(count).every(c=>c[1]==='list'),'refusal makes no mutations');
  diagnostic(caught.message,{workspace:f.layout.workspaceId,field,expected,found});
 });
}
test('public workflow open retains actionable error, escaped values and same custody',async t=>{
 const f=await fixture(t),w=f.rows.find(w=>w.workspace_id===f.layout.workspaceId);w.worktree.checkout_path='/bad "quote"\n\u001b[31m';w.worktree.repo_key='/second-mismatch';
 const before=f.registry(),count=f.calls.length,result=await openRun({ref:'17',cwd:f.parent,packageRoot:source},f.runnerPorts);
 assert.equal(result.exitCode,1);assert.equal(f.registry(),before);assert.ok(f.calls.slice(count).every(c=>['status','list'].includes(c[0])||c[1]==='list'));
 assert.match(result.message,/herdr_layout_identity_changed/);
 diagnostic(result.message,{workspace:f.layout.workspaceId,field:'checkout_path',expected:f.cwd,found:'\\n'});
 assert.ok(result.message.includes('\\"quote\\"'),'quotes escaped');assert.ok(!result.message.includes('\u001b'),'control characters escaped');assert.ok(!result.message.includes('/second-mismatch'),'deterministic first field');
 const saved=JSON.parse(readFileSync(join(f.run.runDir,'status.json'),'utf8'));assert.equal(saved.runId,f.run.runId);assert.equal(saved.root,f.cwd);assert.equal(saved.area,0);assert.deepEqual(saved.chats,[]);
});
test('cleanup warning preserves layout diagnostic rather than dropping message at caller',async t=>{
 const f=await fixture(t),p=f.panes.find(p=>p.workspace_id===f.layout.workspaceId),expected=p.terminal_id;p.terminal_id='replacement';
 f.run.chats=[{area:'plan',tabId:'area-tab',...f.layout}];const before=f.registry(),count=f.calls.length;
 const out=await closeChats(f.run,f.runnerPorts);assert.equal(f.registry(),before);assert.ok(!f.calls.slice(count).some(c=>c[0]==='workspace'&&c[1]==='close'));
 assert.equal(out.warnings.length,1);assert.match(out.warnings[0],/herdr_layout_identity_changed/);
 diagnostic(out.warnings[0],{workspace:f.layout.workspaceId,field:'terminal_id',expected,found:'replacement'});
});

test('next-area public failure forwards layout diagnostic after explicit approval',async t=>{
 const f=await fixture(t),w=f.rows.find(w=>w.workspace_id===f.layout.workspaceId);w.worktree.repo_key='/other.git';
 f.run.areas.push({name:'build',steps:['build'],optional:[],gate:'pr'});f.run.done={plan:{summary:'Plan ready',at:1}};f.run.gate={id:'gate',area:'plan',at:2,kind:'approve'};f.save();
 const before=f.registry(),out=await approveRun({ref:'17',cwd:f.parent,said:'looks good',packageRoot:source},f.runnerPorts);
 assert.equal(out.exitCode,1);assert.equal(f.registry(),before);assert.match(out.message,/herdr_layout_identity_changed/);
 diagnostic(out.message,{workspace:f.layout.workspaceId,field:'repo_key',expected:f.input.commonDir,found:'/other.git'});
 const saved=JSON.parse(readFileSync(join(f.run.runDir,'status.json'),'utf8'));assert.equal(saved.runId,f.run.runId);assert.equal(saved.root,f.cwd);assert.equal(saved.area,1);assert.equal(saved.gate,null);assert.deepEqual(saved.chats,[]);
});

test('actual CLI workflow open exposes the saved workspace mismatch without live Herdr',async t=>{
 const f=await fixture(t),w=f.rows.find(w=>w.workspace_id===f.layout.workspaceId);w.worktree.checkout_path='/other-checkout';
 const dir=join(f.home,'.local','state','pdd','herdr-layout'),bin=join(f.home,'bin');mkdirSync(dir,{recursive:true});mkdirSync(bin);
 writeFileSync(join(dir,'registry.json'),f.registry());
 const fake=`#!${process.execPath}\nconst args=process.argv.slice(2);if(args[0]!=='--session'||args[1]!=='pdd')process.exit(91);const command=args.slice(2);if(command[0]==='status')console.log(JSON.stringify({running:true}));else if(command[0]==='workspace'&&command[1]==='list')console.log(JSON.stringify({id:'cli:workspace:list',result:{type:'workspace_list',workspaces:${JSON.stringify(f.rows)}}}));else process.exit(92);`;
 writeFileSync(join(bin,'herdr'),fake,{mode:0o755});
 const before=readFileSync(join(dir,'registry.json'),'utf8');
 const out=spawnSync(process.execPath,[join(source,'bin','pdd.mjs'),'workflow','open','17'],{cwd:f.parent,env:{...process.env,HOME:f.home,PATH:bin+':'+process.env.PATH,CODEX_HOME:f.home,CLAUDE_CONFIG_DIR:f.home},encoding:'utf8',timeout:15000});
 assert.equal(out.status,1,out.stderr);assert.equal(readFileSync(join(dir,'registry.json'),'utf8'),before);
 const message=(out.stdout+out.stderr).split('\n').find(line=>line.includes('herdr_layout_identity_changed')) ?? '';assert.match(message,/herdr_layout_identity_changed/);
 diagnostic(message,{workspace:f.layout.workspaceId,field:'checkout_path',expected:f.cwd,found:'/other-checkout'});
});
