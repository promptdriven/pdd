import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { chooseWorkflowAgent, checkWorkflowAgents } from '../src/workflow-agents.mjs';
import { setupWithWorkflowAgent } from '../src/workflow-setup.mjs';
import { setupSkills, PDD_SKILL_NAMES } from '../src/skills-install.mjs';
import { chatCommand, ownSession } from '../src/workflow-chat.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { stepDone, approveRun, openRun } from '../src/workflow-runner.mjs';
import { discoverAgents, askAgent } from '../src/agent-adapters.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';
const result = (stdout, code = 0) => ({code, stdout, stderr:''});
const controls = '--approval-mode --admin-policy --extensions --allowed-mcp-server-names --output-format';
const missing = () => { throw Object.assign(Error('not installed'), {code:'ENOENT', executableMissing:true}); };

test('Gemini-only installation admits workflow selection and setup without an authentication/model request', async t => {
 const root=mkdtempSync(join(tmpdir(),'pdd-gemini-setup-'));t.after(()=>rmSync(root,{recursive:true,force:true}));
 const calls=[],env={HOME:root,GOOGLE_GENAI_USE_VERTEXAI:'true'};
 const run=async (command,args,opts)=>{calls.push([command,args]);assert.equal(opts.env,env);return command==='gemini'?result('0.67.1'):missing();};
 assert.deepEqual(await checkWorkflowAgents({env},{run}),{ok:true,agent:'gemini',message:''});
 let selected;
 assert.equal(await setupWithWorkflowAgent({cwd:root,env},{run,setup:async input=>{
  selected=input.agent;setupSkills({packageRoot,cwd:root,home:root});return 0;
 }}),0);
 assert.equal(selected,'gemini');
 for(const name of PDD_SKILL_NAMES)assert.match(readFileSync(join(root,'.agents/skills',name,'SKILL.md'),'utf8'),/^---/);
 assert.deepEqual(calls.filter(([c])=>c==='gemini').map(([,a])=>a),[['--version'],['--version']]);
 for(const requested of ['codex','claude','gemini'])assert.equal(chooseWorkflowAgent({codex:'ready',claude:'ready',gemini:'ready',requested}).agent,requested);
 assert.equal(chooseWorkflowAgent({codex:'ready',claude:'ready',gemini:'ready'}).agent,'codex');
 assert.equal(chooseWorkflowAgent({codex:'missing',claude:'ready',gemini:'ready'}).agent,'claude');
 assert.equal(chooseWorkflowAgent({codex:'ready',gemini:'missing',requested:'gemini'}).ok,false);
});

test('Gemini workflow and product agent choices reach the public command dispatch', async()=>{
 let started;
 const stdout={write(){}},stderr={write(){}},env={HOME:'/test'};
 const common={cwd:packageRoot,env,stdout,stderr};
 assert.equal(await runPdd(['workflow','run','small-change','17','--agent','gemini'],{
  ...common,workflowAgents:{checkWorkflowAgents:async input=>{assert.equal(input.requested,'gemini');return {ok:true,agent:'gemini'};}},
  workflowRunner:{startRun:async input=>{started=input.agent;return {exitCode:0,message:'started'};}}
 }),0);
 assert.equal(started,'gemini');
 // Product startup forwards the same catalog choice without running a real workflow.
 let productAgent;
 assert.equal(await runPdd(['product','start','G-1','--agent','gemini'],{...common,product:{runProduct:async input=>{productAgent=input.agent;return {exitCode:0,message:'started'};}}}),0);
 assert.equal(productAgent,'gemini');
});

test('Gemini shell launch preserves message, configuration, Vertex and model environment, with interactive full access',t=>{
 const root=mkdtempSync(join(tmpdir(),"pdd-gemini 'launch'-"));t.after(()=>rmSync(root,{recursive:true,force:true}));
 const bin=join(root,'bin');mkdirSync(bin);
 for(const cli of ['gemini','codex'])writeFileSync(join(bin,cli),`#!${process.execPath}\nconsole.log(JSON.stringify({args:process.argv.slice(2),config:process.env.GEMINI_CLI_HOME,project:process.env.GOOGLE_CLOUD_PROJECT,model:process.env.GEMINI_MODEL,marker:process.env.PDD_AGENT_SESSION}));`,{mode:0o755});
 const messageFile=join(root,"start 'message'.md"),message='Use pdd-small-change.\nLiteral $(touch broken) `text`';writeFileSync(messageFile,message);
 const command=chatCommand({agent:'gemini',cwd:root,messageFile,configDir:join(root,'config')});
 const out=JSON.parse(execFileSync('/bin/sh',['-c',command],{cwd:root,env:{PATH:`${bin}:/usr/bin:/bin`,GOOGLE_CLOUD_PROJECT:'test-project',GEMINI_MODEL:'test-model'},encoding:'utf8'}));
 assert.deepEqual(out,{args:['--yolo','--prompt-interactive',message],config:join(root,'config'),project:'test-project',model:'test-model',marker:'1'});
 assert.match(chatCommand({agent:'gemini',cwd:root,resumeId:'11111111-1111-4111-8111-111111111111'}),/gemini --yolo --resume '11111111-1111-4111-8111-111111111111'$/);
});

test('Gemini start and resume trust the run worktree, so a new worktree never stops at the folder-trust question',t=>{
 const root=mkdtempSync(join(tmpdir(),'pdd-gemini-trust-'));t.after(()=>rmSync(root,{recursive:true,force:true}));
 const bin=join(root,'bin');mkdirSync(bin);
 writeFileSync(join(bin,'gemini'),`#!${process.execPath}\nconsole.log(JSON.stringify({trust:process.env.GEMINI_CLI_TRUST_WORKSPACE??null}));`,{mode:0o755});
 const messageFile=join(root,'start.md');writeFileSync(messageFile,'Use pdd-small-change.');
 const launch=command=>JSON.parse(execFileSync('/bin/sh',['-c',command],{cwd:root,env:{PATH:`${bin}:/usr/bin:/bin`},encoding:'utf8'}));
 assert.deepEqual(launch(chatCommand({agent:'gemini',cwd:root,messageFile})),{trust:'true'});
 assert.deepEqual(launch(chatCommand({agent:'gemini',cwd:root,resumeId:'11111111-1111-4111-8111-111111111111'})),{trust:'true'});
});

test('Gemini run opens and reopens the same Herdr chat; recorded words approve without any chat-file evidence',async t=>{
 const f=await fixture(t,{agent:'gemini'});
 // The fake server recognizes a Gemini process without inventing any native transcript.
 const herdr=f.ports.herdr;f.ports.herdr=async args=>{
  const reply=await herdr(args);
  if(args[0]==='pane'&&args[1]==='run'&&args[3].includes(' gemini '))f.herdr.panes.find(p=>p.pane_id===args[2]).agent={agent:'gemini',agent_status:'idle',prompts:[]};
  return reply;
 };
 f.ports.findNativeSessions=async()=>assert.fail('Gemini has no native chat-file evidence reader');
 assert.equal((await f.run()).exitCode,0);
 let run=f.record();assert.equal(run.agent,'gemini');
 const launches=()=>f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run');
 assert.match(launches()[0][3],/gemini --yolo .*--prompt-interactive/);
 assert.ok(launches()[0][3].includes(`'${join(run.commonDir,'pdd/runs')}'`));
 assert.ok(launches()[0][3].includes(`'${run.sourceRoot}.pdd-worktrees'`));
 assert.match(readFileSync(run.chats[0].messageFile,'utf8'),/pdd-small-change.*SKILL\.md/);
 assert.equal((await openRun({ref:'17',cwd:run.root},f.ports)).exitCode,0);assert.equal(launches().length,1);
 assert.equal((await stepDone({step:'scope',summary:'Scope ready',cwd:run.root},f.agentPorts())).exitCode,0);
 const words='Yes, this scope is right.\nContinue.';
 const approved=await approveRun({ref:'17',cwd:run.root,said:words},f.agentPorts());
 assert.equal(approved.exitCode,0,approved.message);run=f.record();assert.equal(run.decisions[0].evidence.words,words);assert.equal(run.decisions[0].evidence.route,'said');assert.equal(run.agent,'gemini');
 assert.ok(launches().every(a=>a[3].includes(' gemini ')));
 assert.deepEqual(await ownSession({run,chat:run.chats[0],since:0,ports:f.ports}),{kind:'unknown'});
});

for(const version of ['0.65.0','0.66.0','0.67.1','1.0.0'])test(`Gemini Try accepts feature-compatible CLI ${version} without a version pin`,async()=>{
 const calls=[];const run=async(c,a)=>{calls.push(a);if(a.includes('--help'))return result(controls);if(a.includes('--version'))return result(version);return result(JSON.stringify({response:JSON.stringify({say:'Ready.',fill:null})}));};
 const definitions=[{id:'gemini',name:'Gemini',kind:'gemini',command:'gemini',env:{}}];
 assert.equal((await discoverAgents({definitions,run}))[0].state,'available');
 assert.deepEqual(await askAgent({agent:'gemini',env:{},run}),{say:'Ready.',fill:null});
 assert.ok(calls.every(a=>!a.includes('--version')),'capabilities, rather than version strings, select compatibility');
});

test('Gemini missing read-only feature names that feature in one line and never invokes a model',async()=>{
 for(const flag of controls.split(' ')){
  const calls=[],run=async(c,a)=>{calls.push(a);return result(controls.split(' ').filter(x=>x!==flag).join(' '));};
  const expected=`Gemini Try read-only mode requires ${flag}; update Gemini CLI.`;
  const got=await askAgent({agent:'gemini',env:{},run});assert.equal(got.error.message,expected);assert.deepEqual(calls,[['--help']]);
  const discovered=await discoverAgents({definitions:[{id:'gemini',name:'Gemini',kind:'gemini',command:'gemini',env:{}}],run});assert.equal(discovered[0].detail,expected);
 }
});


test('Gemini passes both external folders as separate shell arguments on start and resume', t => {
 const root=mkdtempSync(join(tmpdir(), "pdd paths '$-"));t.after(()=>rmSync(root,{recursive:true,force:true}));
 const bin=join(root,'bin');mkdirSync(bin);
 writeFileSync(join(bin,'gemini'),`#!${process.execPath}\nconsole.log(JSON.stringify(process.argv.slice(2)));`,{mode:0o755});
 const commonDir=join(root,"clone '$;/.git"),sourceRoot=join(root,"clone '$;");
 for(const options of [{messageFile:join(root,'msg')},{resumeId:'11111111-1111-4111-8111-111111111111'}]) {
  if(options.messageFile)writeFileSync(options.messageFile,'hello');
  const cmd=chatCommand({agent:'gemini',cwd:root,commonDir,sourceRoot,...options});
  const args=JSON.parse(execFileSync('/bin/sh',['-c',cmd],{env:{PATH:`${bin}:/usr/bin:/bin`},encoding:'utf8'}));
  assert.deepEqual(args.slice(0,5),['--yolo','--include-directories',join(commonDir,'pdd/runs'),'--include-directories',`${sourceRoot}.pdd-worktrees`]);
 }
});
