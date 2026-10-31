import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {Readable} from 'node:stream';
import {runPdd} from '../src/pdd-cli.mjs';
import {harbor,portsFor,PLACE} from './runtime-fake.mjs';
test('C null classifier keeps HTTP titled typed entry local',async t=>{
 const setup=harbor(t,root=>{const p=join(root,PLACE);const text=readFileSync(p,'utf8');assert.ok(text.includes('"input_schema": {'));writeFileSync(p,text.replace('"input_schema": {','"input_schema": {"title":"HTTP POST /typed",'));});
 const env={HOME:setup.home,PDD_STATE_DIR:setup.state};let kinds=0,runs=0;
 const io=portsFor(env,{stdin:Readable.from([]),programApp:{appKind(){kinds++;return null;},runApp(){runs++;return 7;}}});
 const code=await runPdd([PLACE,'--help'],{cwd:setup.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});
 assert.equal(kinds,1);assert.equal(runs,0,'C returned null, so B must retain the typed operation');assert.equal(code,0,io.ports.stderr.text);assert.match(io.ports.stdout.text,/Usage:/);assert.equal(io.clock.gh.length,0);
});
