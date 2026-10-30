import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, rmSync, readFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { chooseWorkflowAgent, checkWorkflowAgents } from '../src/workflow-agents.mjs';

// Expected choices are the issue's matrix, including a failed optional status probe.
const matrix=JSON.parse(readFileSync(new URL('./fixtures/workflow-agent-cases.json',import.meta.url),'utf8')).selection;
for (const [codex,claude,agent] of matrix) test(`2451 selection: ${codex}/${claude}`,()=>{
 const result=chooseWorkflowAgent({codex,claude});assert.equal(result.agent,agent);assert.equal(result.ok,agent!==null);
 assert.equal(result.message==='',agent!==null);
});
for (const requested of ['codex','claude']) for (const state of ['ready','missing','signed_out','unavailable']) {
 test(`2451 explicit ${requested}: ${state} cannot fall back to the other ready agent`,()=>{
  const result=chooseWorkflowAgent({codex:'ready',claude:'ready',[requested]:state,requested});
  assert.equal(result.ok,state==='ready');assert.equal(result.agent,state==='ready'?requested:null);
  if(state!=='ready')assert.ok(result.message.includes(requested==='codex'?'Codex':'Claude Code'));
 });
}
test('2451 guidance distinguishes installation, sign-in and an unknown status',()=>{
 const missing=chooseWorkflowAgent({codex:'missing',claude:'missing'});
 assert.match(missing.message,/Install Codex or Claude Code first/);assert.match(missing.message,/https:\/\//);
 const out=chooseWorkflowAgent({codex:'signed_out',claude:'signed_out'});
 assert.deepEqual(out.message.split('\n'),['Codex is not signed in. Run: codex login','Claude Code is not signed in. Run: claude auth login']);
 assert.match(chooseWorkflowAgent({codex:'unavailable',claude:'missing',requested:'codex'}).message,/codex login status/);
});
test('2451 invalid explicit choice refuses without a process call',async()=>{
 const reply=await checkWorkflowAgents({requested:'other'},{run:()=>assert.fail('no native command')});assert.equal(reply.ok,false);
});
const response=(code,stdout='',stderr='')=>({code,stdout,stderr});
test('2451 native status commands preserve the exact caller configuration and use no model/interactive command',async()=>{
 const env={HOME:'/scratch/home',CODEX_HOME:'/scratch/codex',CLAUDE_CONFIG_DIR:'/scratch/custom-claude',PATH:'/scratch/bin'};
 const calls=[];
 const result=await checkWorkflowAgents({cwd:'/scratch/project',env},{run:async(command,args,options)=>{
  calls.push({command,args,options});return command==='codex'?response(1,'','Not logged in'):response(0,'{"loggedIn":true,"private":"not exposed"}');
 }});
 assert.deepEqual(result,{ok:true,agent:'claude',message:''});
 assert.deepEqual(calls.map(c=>[c.command,c.args]),[['codex',['login','status']],['claude',['auth','status']]]);
 for(const {options} of calls){assert.equal(options.env,env);assert.equal(options.cwd,'/scratch/project');assert.equal(options.input,'');assert.equal(options.maxBytes,16384);}
 assert.doesNotMatch(JSON.stringify(result),/private|exposed/);
});
for(const [name,agent,result,ready] of [
 ['Codex stderr login','codex',response(0,'','Logged in using ChatGPT'),true],
 ['Codex negative success','codex',response(0,'Not logged in'),false],
 ['Codex nonzero success','codex',response(1,'Logged in'),false],
 ['Codex unrelated output','codex',response(0,'hello'),false],
 ['Claude typed true','claude',response(0,'{"loggedIn":true}'),true],
 ['Claude string true','claude',response(0,'{"loggedIn":"true"}'),false],
 ['Claude missing field','claude',response(0,'{}'),false],
 ['Claude malformed','claude',response(0,'not JSON'),false],
 ['Claude nonzero true','claude',response(1,'{"loggedIn":true}'),false],
 ['Claude valid false','claude',response(1,'{"loggedIn":false}'),false],
])test(`2451 probe: ${name}`,async()=>{
 const calls=[];const reply=await checkWorkflowAgents({requested:agent},{run:async(...args)=>{calls.push(args);return result;}});
 assert.equal(reply.ok,ready);assert.equal(calls.length,1);assert.equal(calls[0][0],agent);
 if(!ready)assert.doesNotMatch(reply.message,/not JSON|loggedIn|hello/);
});
test('2451 a failed optional process does not veto a signed-in agent; private diagnostics stay private',async()=>{
 const reply=await checkWorkflowAgents({}, {run:async agent=>{
  if(agent==='codex')throw Object.assign(Error('private credential path'),{code:'EACCES'});
  return response(0,'{"loggedIn":true}');
 }});assert.deepEqual(reply,{ok:true,agent:'claude',message:''});
 const absent=await checkWorkflowAgents({}, {run:async()=>{throw Object.assign(Error('private token'),{code:'ENOENT'});}});
 assert.equal(absent.ok,false);assert.match(absent.message,/Install Codex or Claude Code first/);assert.doesNotMatch(absent.message,/private|token/);
});
test('2451 real process port runs only scratch status stubs, honoring a custom Claude config folder',async t=>{
 const root=mkdtempSync(join(tmpdir(),'pdd-workflow-auth-'));t.after(()=>rmSync(root,{recursive:true,force:true}));
 const bin=join(root,'bin'),home=join(root,'home'),config=join(root,'my Claude');for(const p of [bin,home,config])mkdirSync(p);
 writeFileSync(join(config,'signed-in'),'synthetic');
 writeFileSync(join(bin,'codex'),`#!${process.execPath}\nif(process.argv.slice(2).join(' ')!=='login status')process.exit(99);process.stderr.write('Not logged in');process.exitCode=1;\n`,{mode:0o755});
 writeFileSync(join(bin,'claude'),`#!${process.execPath}\nconst fs=require('node:fs');if(process.argv.slice(2).join(' ')!=='auth status')process.exit(99);process.stdout.write(JSON.stringify({loggedIn:fs.existsSync(process.env.CLAUDE_CONFIG_DIR+'/signed-in')}));\n`,{mode:0o755});
 const result=await checkWorkflowAgents({cwd:root,env:{HOME:home,CLAUDE_CONFIG_DIR:config,PATH:bin}});
 assert.deepEqual(result,{ok:true,agent:'claude',message:''});
});
