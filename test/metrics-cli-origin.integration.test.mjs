import test from 'node:test';
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {join} from 'node:path';
import {mkdtempSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {runPdd} from '../src/pdd-cli.mjs';
const bin=join(import.meta.dirname,'..','bin','pdd.mjs');
test('public workflow command accepts metadata before native startup preflight',t=>{
 const isolated=mkdtempSync(join(tmpdir(),'pdd-cli-origin-')); t.after(()=>rmSync(isolated,{recursive:true,force:true}));
 const help=spawnSync(process.execPath,[bin,'workflow','run','--help'],{encoding:'utf8'}); assert.equal(help.status,0); assert.match(help.stdout,/--decision-id/);
 const run=spawnSync(process.execPath,[bin,'workflow','run','small-change','17','--origin','autopilot','--decision-id','11234567-89ab-4cde-8fab-123456789abc','--outcome','code'],{encoding:'utf8',cwd:isolated,env:{HOME:isolated,PATH:'',CODEX_HOME:join(isolated,'missing')}});
 assert.equal(run.status,1); assert.match(run.stderr,/Install Codex/); assert.doesNotMatch(run.stderr,/Unknown option/);
});
test('workflow dispatch forwards parsed metadata to native runner',async()=>{
 let received; const stream={write(){}};
 const status=await runPdd(['workflow','run','small-change','17','--origin','autopilot','--decision-id','token','--outcome','code'],{stdout:stream,stderr:stream,workflowRunner:{startRun:async input=>{received=input;return {exitCode:0,message:'ok'};}},workflowAgents:{checkWorkflowAgents:async()=>({ok:true,agent:'codex'})},pathDiagnostic:async()=>null});
 assert.equal(status,0); assert.deepEqual([received.origin,received.decisionId,received.outcome],['autopilot','token','code']);
});
