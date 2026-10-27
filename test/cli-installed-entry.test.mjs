import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, cpSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { pddCommand } from '../src/workflow-runner.mjs';

const root = fileURLToPath(new URL('..',import.meta.url));
test('runner area-chat commands pin the real absolute executable despite an older shell PATH',async t=>{
 const tmp=mkdtempSync(join(tmpdir(),"pdd-entry ' quoted-"));t.after(()=>rmSync(tmp,{recursive:true,force:true}));
 const pkg=join(tmp,'installed package'),old=join(tmp,'old-bin'),home=join(tmp,'home');mkdirSync(pkg);mkdirSync(old);mkdirSync(home);
 for(const name of ['src','bin','package.json','docs','skills'])cpSync(join(root,name),join(pkg,name),{recursive:true});
 writeFileSync(join(old,'pdd'),'#!/bin/sh\necho OLD_PRIVATE_PDD\nexit 77\n',{mode:0o755});
 const env={...process.env,HOME:home,CLAUDE_CONFIG_DIR:'',PATH:old};
 const stagePrefix=pddCommand(pkg);
 assert.ok(stagePrefix.includes(resolve(pkg,'bin/pdd.mjs').replace(/'/g,"'\\''")));
 const bare=spawnSync('/bin/sh',['-c','pdd --help'],{env,encoding:'utf8'});assert.equal(bare.status,77);
 const actual=spawnSync('/bin/sh',['-c',stagePrefix+' --help'],{cwd:tmp,env,encoding:'utf8'});
 assert.equal(actual.status,0,actual.stderr);assert.match(actual.stdout,/^PDD: prompt-driven development for your coding agent\.\n/);assert.doesNotMatch(actual.stdout,/OLD_PRIVATE/);
});
