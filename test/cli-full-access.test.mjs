import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync,mkdirSync,writeFileSync,readdirSync,rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
const bin=fileURLToPath(new URL('../bin/pdd.mjs',import.meta.url));

test('actual public native entry uses explicit full access for both agents with inherited input/env and real exit',t=>{
 const root=mkdtempSync(join(tmpdir(),'pdd-full-access-'));t.after(()=>rmSync(root,{recursive:true,force:true}));
 const home=join(root,'home'),cwd=join(root,'project with spaces'),native=join(root,'native');for(const d of [home,cwd,native])mkdirSync(d);
 const script=`#!${process.execPath}\nconst fs=require('node:fs');process.stdout.write(JSON.stringify({args:process.argv.slice(2),cwd:process.cwd(),input:fs.readFileSync(0,'utf8'),setting:process.env.NATIVE_SETTING_EXAMPLE}));process.exit(Number(process.env.FIXTURE_EXIT||0));\n`;
 for(const agent of ['codex','claude'])writeFileSync(join(native,agent),script,{mode:0o755});
 const request='Summarize guide only; $(touch no-shell-effect)';
 for(const agent of ['codex','claude']){
  const r=spawnSync(process.execPath,[bin,'session','--agent',agent,request],{cwd,env:{...process.env,HOME:home,PATH:native,NATIVE_SETTING_EXAMPLE:'ordinary',FIXTURE_EXIT:agent==='claude'?'7':'0'},input:'native terminal input\n',encoding:'utf8',timeout:5000});
  assert.equal(r.status,agent==='claude'?7:0,r.stderr);assert.equal(r.stderr,'');const actual=JSON.parse(r.stdout);
  assert.equal(actual.args.length,2);assert.equal(actual.args[0],agent==='codex'?'--dangerously-bypass-approvals-and-sandbox':'--dangerously-skip-permissions');
  assert.ok(actual.args[1].includes('Read the ENTIRE Prompting guide'));assert.ok(actual.args[1].includes(request));assert.equal(actual.cwd,cwd);assert.equal(actual.input,'native terminal input\n');assert.equal(actual.setting,'ordinary');
 }
 assert.deepEqual(readdirSync(home),[]);assert.deepEqual(readdirSync(cwd),[]);
});
