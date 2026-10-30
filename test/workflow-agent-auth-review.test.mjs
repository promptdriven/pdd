import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import * as adapters from '../src/agent-adapters.mjs';
import {checkWorkflowAgents} from '../src/workflow-agents.mjs';
const apiText='API key configured - sk-proj-***ABCDE\nAuthentication is checked when you send a request.';
test('2451 shared credential parser recognizes current API-key status without leaking text',()=>{
 assert.equal(typeof adapters.parseAgentAuthStatus,'function');
 assert.equal(adapters.parseAgentAuthStatus({agent:'codex',result:{code:0,stdout:'',stderr:apiText}}),'ready');
});
test('2451 Try discovery uses the same API-key credential interpretation',async()=>{
 const rows=await adapters.discoverAgents({definitions:[{id:'codex',name:'Codex',kind:'codex',command:'codex'}],run:async(c,args)=>args[0]==='--help'?{code:0,stdout:'--sandbox',stderr:''}:{code:0,stdout:'',stderr:apiText}});
 assert.deepEqual(rows,[{id:'codex',name:'Codex',state:'ready'}]);
});
for(const mode of ['missing-executable','missing-cwd','broken-shebang'])test(`2451 native status ENOENT classification: ${mode}`,async t=>{
 const root=mkdtempSync(join(tmpdir(),'pdd2451-enoent-'));t.after(()=>rmSync(root,{recursive:true,force:true}));
 const bin=join(root,'bin');mkdirSync(bin);
 if(mode==='broken-shebang')writeFileSync(join(bin,'codex'),'#!/nonexistent-pdd-test-interpreter\n',{mode:0o755});
 const cwd=mode==='missing-cwd'?join(root,'gone'):root,env={HOME:join(root,'home'),PATH:bin};
 let caught;try{await adapters.runAgentProcess('codex',['login','status'],{cwd,env,input:'',timeoutMs:1000});}catch(error){caught=error;}
 assert.equal(caught?.code,'ENOENT');assert.equal(caught.executableMissing,mode==='missing-executable');
 const reply=await checkWorkflowAgents({cwd,env,requested:'codex'});
 assert.equal(reply.ok,false);
 assert.match(reply.message,mode==='missing-executable'?/not installed/:/could not be checked/);
});
test('2451 native Codex API-key status keeps exact CODEX_HOME and private output',async t=>{
 const root=mkdtempSync(join(tmpdir(),'pdd2451-key-status-'));t.after(()=>rmSync(root,{recursive:true,force:true}));
 const bin=join(root,'bin'),config=join(root,'custom codex');mkdirSync(bin);mkdirSync(config);
 writeFileSync(join(config,'synthetic-marker'),'configured');
 writeFileSync(join(bin,'codex'),`#!${process.execPath}\nconst fs=require('node:fs');if(process.argv.slice(2).join(' ')!=='login status')process.exit(99);if(!fs.existsSync(process.env.CODEX_HOME+'/synthetic-marker'))process.exit(2);process.stderr.write(${JSON.stringify(apiText)});\n`,{mode:0o755});
 const reply=await checkWorkflowAgents({cwd:root,env:{HOME:root,PATH:bin,CODEX_HOME:config},requested:'codex'});
 assert.deepEqual(reply,{ok:true,agent:'codex',message:''});
});

for(const [agent,result,state] of [
 ['codex',{code:0,stdout:'',stderr:'\u001b[32mLogged in using ChatGPT\u001b[0m'},'ready'],
 ['codex',{code:0,stdout:'Logged in',stderr:'Not logged in'},'unavailable'],
 ['codex',{code:0,stdout:apiText,stderr:'Sign-in required'},'unavailable'],
 ['codex',{code:1,stdout:'',stderr:'Not signed in'},'signed_out'],
 ['codex',{code:2,stdout:'',stderr:'Not logged in'},'unavailable'],
 ['codex',{code:1,stdout:apiText,stderr:''},'unavailable'],
 ['claude',{code:0,stdout:'{"loggedIn":false}',stderr:''},'signed_out'],
 ['claude',{code:1,stdout:'{"loggedIn":true}',stderr:''},'unavailable'],
 ['claude',{code:0,stdout:'banner\n{"loggedIn":true}',stderr:''},'unavailable'],
])test(`2451 shared parser states ${agent}/${state}: ${JSON.stringify(result)}`,()=>{
 assert.equal(typeof adapters.parseAgentAuthStatus,'function');assert.equal(adapters.parseAgentAuthStatus({agent,result}),state);
});
test('2451 Try discovery does not claim ready on a nonzero Claude success payload',async()=>{
 const rows=await adapters.discoverAgents({definitions:[{id:'claude',name:'Claude',kind:'claude',command:'claude'}],run:async(c,args)=>args[0]==='--help'?{code:0,stdout:'--safe-mode --tools --permission-prompts',stderr:''}:{code:1,stdout:'{"loggedIn":true}',stderr:''}});
 assert.equal(rows[0].state,'error');
});
