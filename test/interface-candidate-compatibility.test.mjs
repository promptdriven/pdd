import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {bindingCoverage} from '../src/runtime/runtime-bindings.mjs';
import {proseSha256,findTests} from '../src/runtime/runtime-preflight.mjs';
import {runCheck} from '../src/runtime-seam.mjs';
import {harbor,portsFor,PLACE} from './runtime-fake.mjs';

function native(repo) {
  let text='# Kernel identity\n\n<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify({kind:'native-only',reason:'cross-process filesystem locks',status:'draft',prose_sha256:''})+'\n```\n</details>\n';
  text=text.replace('"prose_sha256":""',`"prose_sha256":"${proseSha256(text)}"`);
  writeFileSync(join(repo,PLACE),text);
}
const offline=setup=>portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state},{gh:()=>assert.fail('unexpected authentication'),fetch:()=>assert.fail('unexpected network')}).ports;

test('candidate: binding inventory keeps its public shape while command coverage is opt in',t=>{
  const setup=harbor(t),found=findTests({root:setup.repo});
  const input={root:setup.repo,found,selected:found.tests};
  assert.deepEqual(bindingCoverage(input),{available:false,bound:null,total:null,modules:[]});
  assert.deepEqual(bindingCoverage({...input,includeRuntime:true}).runtime,{checkable:1,total:1,native_only:0});
});

test('candidate: valid native omissions do not become broken-test counts',async t=>{
  const setup=harbor(t,native),ports=offline(setup);
  assert.equal(await runCheck({cwd:setup.repo,options:{'--lint':true,'--json':true}},ports),5);
  const result=JSON.parse(ports.stdout.text);
  assert.equal(result.rows.length,2);
  assert.ok(result.rows.every(row=>row.reason.code==='native-only' && row.refusals.length===0));
  assert.doesNotMatch(result.summary_line,/could not run/);
  assert.match(result.summary_line,/2 native-only/);
});

test('candidate: locally refused mixed inventory does not claim interpreter findings',async t=>{
  const setup=harbor(t,repo=>{native(repo);writeFileSync(join(repo,'missing.prompt.md'),'# New behavior\n');}),ports=offline(setup);
  assert.equal(await runCheck({cwd:setup.repo,options:{'--lint':true}},ports),4);
  assert.ok(ports.stdout.text.includes('missing.prompt.md'));
  assert.ok(ports.stdout.text.includes('cross-process filesystem locks'));
  assert.doesNotMatch(ports.stdout.text,/from the PDD interpreter/);
});
