import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, cpSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { loadGuidance } from '../src/guidance.mjs';
import { launchNativeSession } from '../src/native-session.mjs';
import { renderSessionIntro } from '../src/session-intro.mjs';

const root = fileURLToPath(new URL('..',import.meta.url));
test('native session intro and runner stage context pin real absolute executable despite older shell PATH',async t=>{
 const tmp=mkdtempSync(join(tmpdir(),"pdd-entry ' quoted-"));t.after(()=>rmSync(tmp,{recursive:true,force:true}));
 const pkg=join(tmp,'installed package'),old=join(tmp,'old-bin'),home=join(tmp,'home');mkdirSync(pkg);mkdirSync(old);mkdirSync(home);
 for(const name of ['src','bin','package.json','docs','skills','.pdd'])cpSync(join(root,name),join(pkg,name),{recursive:true});
 writeFileSync(join(old,'pdd'),'#!/bin/sh\necho OLD_PRIVATE_PDD\nexit 77\n',{mode:0o755});
 const env={...process.env,HOME:home,PATH:old};
 const context=loadGuidance({packageRoot:pkg,cwd:tmp});
 const encoded=context.match(/Exact installed PDD argv prefix: (.+)/)[1];
 assert.deepEqual(JSON.parse(encoded),[process.execPath,resolve(pkg,'bin/pdd.mjs')]);
 const stagePrefix=context.match(/absolute executable prefix: (.+)\. Append only/)[1];
 const intro=renderSessionIntro({packageRoot:pkg,cwd:tmp});
 const sessionPrefix=intro.match(/^Use this pdd: (.+)$/m)[1];
 const bare=spawnSync('/bin/sh',['-c','pdd --help'],{env,encoding:'utf8'});assert.equal(bare.status,77);
 for(const prefix of [stagePrefix,sessionPrefix]){
  const actual=spawnSync('/bin/sh',['-c',prefix+' --help'],{cwd:tmp,env,encoding:'utf8'});
  assert.equal(actual.status,0,actual.stderr);assert.match(actual.stdout,/^PDD: prompt-driven development for your coding agent\.\n/);assert.doesNotMatch(actual.stdout,/OLD_PRIVATE/);
 }
 let captured;
 const status=await launchNativeSession({agent:'codex',cwd:tmp,message:intro}, {spawn:(agent,args,opts)=>{
  captured={agent,args,opts};const child=new (class {once(name,fn){if(name==='close')queueMicrotask(()=>fn(0));return this;}kill(){}})();return child;
 }});
 assert.equal(status,0);assert.equal(captured.args.at(-1),intro);assert.equal(captured.opts.cwd,tmp);assert.equal('env' in captured.opts,false);
 assert.ok(context.includes('Read the ENTIRE Prompting guide'));assert.ok(context.includes('--- '+join(pkg,'docs/prompting-guide.md')));
});
