import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, cpSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { loadGuidance } from '../src/guidance.mjs';
import { launchNativeSession } from '../src/native-session.mjs';

const root = fileURLToPath(new URL('..',import.meta.url));
test('native session and runner stage context pin real absolute executable despite older shell PATH',async t=>{
 const tmp=mkdtempSync(join(tmpdir(),"pdd-entry ' quoted-"));t.after(()=>rmSync(tmp,{recursive:true,force:true}));
 const pkg=join(tmp,'installed package'),old=join(tmp,'old-bin');mkdirSync(pkg);mkdirSync(old);
 for(const name of ['src','bin','package.json','docs','skills','.pdd'])cpSync(join(root,name),join(pkg,name),{recursive:true});
 writeFileSync(join(old,'pdd'),'#!/bin/sh\necho OLD_PRIVATE_PDD\nexit 77\n',{mode:0o755});
 for(const workflows of [true,false]){
  const context=loadGuidance({packageRoot:pkg,cwd:tmp,workflows});
  const encoded=context.match(/Exact installed PDD argv prefix: (.+)/)[1];
  assert.deepEqual(JSON.parse(encoded),[process.execPath,resolve(pkg,'bin/pdd.mjs')]);
  const prefix=context.match(/absolute executable prefix: (.+)\. Append only/)[1];
  const bare=spawnSync('/bin/sh',['-c','pdd --help'],{env:{...process.env,PATH:old},encoding:'utf8'});assert.equal(bare.status,77);
  const actual=spawnSync('/bin/sh',['-c',prefix+' --help'],{cwd:tmp,env:{...process.env,PATH:old},encoding:'utf8'});
  assert.equal(actual.status,0,actual.stderr);assert.match(actual.stdout,/^PDD: prompt-driven development for your coding agent\.\n/);assert.doesNotMatch(actual.stdout,/OLD_PRIVATE/);
  let captured;
  const status=await launchNativeSession({agent:'codex',cwd:tmp,context,request:'Inspect help only'}, {spawn:(agent,args,opts)=>{
   captured={agent,args,opts};const child=new (class {once(name,fn){if(name==='close')queueMicrotask(()=>fn(0));return this;}kill(){}})();return child;
  }});
  assert.equal(status,0);assert.ok(captured.args.at(-1).includes(encoded));assert.equal(captured.opts.cwd,tmp);assert.equal('env' in captured.opts,false);
  assert.ok(context.includes('Read the ENTIRE Prompting guide'));assert.ok(context.includes('--- '+join(pkg,'docs/prompting-guide.md')));
 }
});
