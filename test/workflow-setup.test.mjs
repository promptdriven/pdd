import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, statSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {setupSkills} from '../src/skills-install.mjs';
import {setupProject} from '../src/project-setup.mjs';
import {setupWithWorkflowAgent} from '../src/workflow-setup.mjs';
const fixture=state=>async agent=>{
 const value=state[agent];
 if(value==='missing')throw Object.assign(Error('synthetic private command path'),{code:'ENOENT',executableMissing:true});
 return agent==='codex'?{code:value==='ready'?0:1,stdout:'',stderr:value==='ready'?'Logged in using ChatGPT':'Not logged in'}
 :{code:value==='ready'?0:1,stdout:JSON.stringify({loggedIn:value==='ready'}),stderr:''};
};
const cases=JSON.parse(readFileSync(new URL('./fixtures/workflow-agent-cases.json',import.meta.url),'utf8')).setup;
for(const [codex,claude,agent] of cases)test(`2451 setup adapter: ${codex}/${claude}`,async()=>{
 const env={HOME:'/scratch',CLAUDE_CONFIG_DIR:'/scratch/nondefault',PATH:'/scratch/bin'},calls=[],out=[];
 const code=await setupWithWorkflowAgent({cwd:'/scratch/project',env},{run:fixture({codex,claude}),stderr:{write:s=>out.push(s)},setup:async input=>{calls.push(input);return 0;}});
 assert.equal(code,agent?0:1);assert.equal(calls.length,agent?1:0);
 if(agent){assert.equal(calls[0].agent,agent);assert.equal(calls[0].env,env);assert.equal(calls[0].cwd,'/scratch/project');assert.equal(out.join(''),'');}
 else if(codex==='missing')assert.match(out.join(''),/Install Codex or Claude Code first/);
 else {assert.match(out.join(''),/codex login/);assert.match(out.join(''),/claude auth login/);}
});
test('2451 setup adapter preserves nonzero action results without repeating effects',async()=>{
 let calls=0;const code=await setupWithWorkflowAgent({}, {run:fixture({codex:'ready',claude:'signed_out'}),setup:async()=>{calls++;return 7;}});
 assert.equal(code,7);assert.equal(calls,1);
});
for(const result of [undefined,-1,256,'0',new Error('private credentials')])test(`2451 invalid setup result remains finite and private: ${String(result)}`,async()=>{
 let calls=0;const text=[];const code=await setupWithWorkflowAgent({}, {run:fixture({codex:'ready',claude:'signed_out'}),stderr:{write:s=>text.push(s)},setup:async()=>{calls++;if(result instanceof Error)throw result;return result;}});
 assert.equal(code,1);assert.equal(calls,1);assert.doesNotMatch(text.join(''),/credentials/);
});
test('2451 no setup action means no auth process, no throw and no claimed success',async()=>{
 let calls=0;const code=await setupWithWorkflowAgent({}, {run:async()=>{calls++;return {code:0,stdout:'Logged in',stderr:''};},stderr:{write(){}}});assert.equal(code,1);assert.equal(calls,0);
});

// Exercise the existing setup writers behind the admission boundary, in scratch folders only.
for (const ready of [false,true]) test(`2451 setup admission before real skill/project writes: ready=${ready}`,async t=>{
 const root=mkdtempSync(join(tmpdir(),'pdd-admitted-setup-'));
 t.after(()=>rmSync(root,{recursive:true,force:true}));
 const cwd=join(root,'project'),home=join(root,'home'),custom=join(root,'custom-claude');
 for(const dir of [cwd,home])mkdirSync(dir);
 const packageRoot=fileURLToPath(new URL('..',import.meta.url));
 const env={HOME:home,CLAUDE_CONFIG_DIR:custom,PATH:join(root,'no-executables')};
 const options={cwd,env};
 const ports={stderr:{write(){}},run:fixture({codex:ready?'missing':'signed_out',claude:ready?'ready':'signed_out'}),setup:async input=>{
  const installed=setupSkills({packageRoot,cwd:input.cwd,home:input.env.HOME,claudeConfigDir:input.env.CLAUDE_CONFIG_DIR});
  assert.equal(installed.some(item=>item.error),false);
  setupProject({cwd:input.cwd,packageRoot});
  return 0;
 }};
 assert.equal(await setupWithWorkflowAgent(options,ports),ready?0:1);
 if(!ready){assert.deepEqual(readdirSync(cwd),[]);assert.deepEqual(readdirSync(home),[]);assert.equal(existsSync(custom),false);return;}
 const file=join(cwd,'AGENTS.md'),text=readFileSync(file,'utf8'),modified=statSync(file).mtimeMs;
 assert.match(text,/<!-- pdd:start -->/);assert.ok(text.trimEnd().split('\n').length<=10);
 for(const base of [join(home,'.agents/skills'),join(custom,'skills')])
  assert.equal(existsSync(join(base,'pdd-bug/SKILL.md')),true);
 assert.equal(existsSync(join(home,'.claude')),false);
 assert.equal(await setupWithWorkflowAgent(options,ports),0);
 assert.equal(readFileSync(file,'utf8'),text);assert.equal(statSync(file).mtimeMs,modified);
});

test('2451 API-key-configured Codex admits setup when Claude is missing',async()=>{
 let calls=0;const code=await setupWithWorkflowAgent({}, {run:async agent=>{
  if(agent==='claude')throw Object.assign(Error('synthetic missing'),{code:'ENOENT',executableMissing:true});
  return {code:0,stdout:'',stderr:'API key configured - sk-proj-***ABCDE\nAuthentication is checked when you send a request.'};
 },stderr:{write:s=>assert.fail('no private status output: '+s)},setup:async({agent})=>{assert.equal(agent,'codex');calls++;return 0;}});
 assert.equal(code,0);assert.equal(calls,1);
});
