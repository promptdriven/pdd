import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { captureSource, sourceFilePort, findTests } from '../src/runtime-preflight.mjs';
import { bindingCoverage } from '../src/runtime-bindings.mjs';
import { harbor, portsFor } from './runtime-fake.mjs';
import { runCheck } from '../src/runtime-client.mjs';
const ORDER = 'tests/place-order.json';
const write = (root,path,bytes) => { mkdirSync(join(root,path,'..'),{recursive:true}); writeFileSync(join(root,path),bytes); };
const refusal = (action, reason) => assert.throws(action, error => error.exitCode === 4 && reason.test(error.message));
function child(mode, repo, outside) {
  const run = spawnSync(process.execPath, [fileURLToPath(new URL('./helpers/source-links-review-probe.mjs', import.meta.url)), mode, repo, new URL('../src/runtime-preflight.mjs', import.meta.url).href, outside ?? ''], {encoding:'utf8', timeout:3000, killSignal:'SIGKILL'});
  assert.equal(run.error, undefined, `resolver must terminate before parent kills it: ${run.error}`);
  assert.equal(run.status,0,run.stderr);
  return JSON.parse(run.stdout);
}
for (const path of ['gen/.env','gen/id_rsa','gen/server.pem','newdir/secrets/x.md']) {
  test(`LINK review generated secret below missing ancestor: ${path}`, t => {
    const {repo}=harbor(t);
    refusal(()=>captureSource(repo,{tests:[],prepareSource:()=>[{path,bytes:'SYNTHETIC-SECRET'}]}), /name looks like a secret/);
  });
}
test('LINK review missing secret stat refuses before absence',t=>{
  const {repo}=harbor(t);
  refusal(()=>sourceFilePort(repo).stat({path:'nodir/.env'}), /name looks like a secret/);
});
test('LINK review linked Story title uses target size limit',t=>{
  const {repo}=harbor(t);
  write(repo,'shared/story.md','# BIG TITLE\n'+'x'.repeat(10_485_761));
  write(repo,'tests/title.json',JSON.stringify({schema_version:'prompt-runtime.program-scenario.v1',story_path:'docs/story.md'}));
  mkdirSync(join(repo,'docs'));symlinkSync('../shared/story.md',join(repo,'docs/story.md'));
  assert.equal(findTests({root:repo}).tests.find(t=>t.path==='tests/title.json').title,'story');
});
test('LINK review linked Story title never follows unchecked path at read time',t=>{
  const {repo,sandbox}=harbor(t);
  write(repo,'shared/story.md','# SAFE TITLE\n');write(sandbox,'external/story.md','# OUTSIDE TITLE\n');
  write(repo,'tests/title.json',JSON.stringify({schema_version:'prompt-runtime.program-scenario.v1',story_path:'docs/story.md'}));
  mkdirSync(join(repo,'docs'));symlinkSync('../shared/story.md',join(repo,'docs/story.md'));
  assert.equal(child('title-race',repo,join(sandbox,'external')).title,'SAFE TITLE');
});
test('LINK review nested destination failure names the escaping link itself',t=>{
  const {repo}=harbor(t);mkdirSync(join(repo,'deep/x'),{recursive:true});
  symlinkSync('deep/x',join(repo,'d'));symlinkSync('d/../../../out.md',join(repo,'e.md'));
  refusal(()=>sourceFilePort(repo).read({path:'e.md'}), /link e\.md -> d\/\.\.\/\.\.\/\.\.\/out\.md:.*outside the repository/);
});
test('LINK review ignored authored chain names the invisible link itself',t=>{
  const {repo}=harbor(t);write(repo,'target.md','visible');write(repo,'.gitignore','hid.md\n');
  symlinkSync('target.md',join(repo,'vis.md'));symlinkSync('vis.md',join(repo,'hid.md'));
  refusal(()=>sourceFilePort(repo).read({path:'hid.md'}), /link hid\.md -> vis\.md:.*link itself is not (?:a )?Git-visible/);
});
test('LINK review plain non-link refusal text preserves alpha exactly',t=>{
  const {repo}=harbor(t);write(repo,'ign.md','ignored');write(repo,'.gitignore','ign.md\n');write(repo,'f.md','file');
  for(const [path,tail] of [
    ['ign.md','is not a Git-visible file. Add it to Git or correct the declared dependency.'],
    ['nope.md','is not a Git-visible file on disk. Restore it or correct the declared dependency.'],
    ['f.md/x.md','has a non-directory ancestor (f.md).'],
  ]) assert.throws(()=>sourceFilePort(repo).read({path}), error=>error.exitCode===4 && error.message===`Source: ${path} ${tail}`);
});
test('LINK review bindings inventory remains strict while regular inventory works',async t=>{
  const {repo,home}=harbor(t);write(repo,'inventory.json','{"schema_version":"pdd.bindings.v1","modules":[]}');
  write(repo,'pdd-bindings.json',readFileSync(join(repo,'inventory.json')));
  const found=()=>findTests({root:repo});
  assert.deepEqual(bindingCoverage({root:repo,found:found(),selected:[]}),{available:true,bound:0,total:0,modules:[]});
  const fs=await import('node:fs');fs.unlinkSync(join(repo,'pdd-bindings.json'));symlinkSync('inventory.json',join(repo,'pdd-bindings.json'));
  refusal(()=>bindingCoverage({root:repo,found:found(),selected:[]}),/symlink|symbolic link/);
  const {ports}=portsFor({HOME:home},{gh:()=>assert.fail('no auth'),fetch:()=>assert.fail('no upload')});
  assert.equal(await runCheck({cwd:repo,words:['place-order'],options:{'--files':true}},ports),4);
  assert.match(ports.stderr.text,/pdd-bindings\.json/);
});
test('LINK review bindings declarations refuse linked ancestors',t=>{
  const {repo}=harbor(t);write(repo,'native/module.mjs','export const n=1;');symlinkSync('native',join(repo,'alias'));
  write(repo,'pdd-bindings.json',JSON.stringify({schema_version:'pdd.bindings.v1',modules:[{module:'alias/module.mjs',stories:['user_stories/place-order.md'],reason:'native',port_attempt:'real OS'}]}));
  const found=findTests({root:repo});found.visible.add('alias/module.mjs');
  refusal(()=>bindingCoverage({root:repo,found,selected:[]}),/symlink|symbolic link/);
});
test('LINK review absolute outside link cannot resolve against benign repository shadow',t=>{
  const {repo}=harbor(t);write(repo,'etc/hosts','benign shadow');symlinkSync('/etc/hosts',join(repo,'a.md'));
  refusal(()=>sourceFilePort(repo).read({path:'a.md'}), /link a\.md -> \/etc\/hosts:.*outside the repository/);
});
test('LINK review public read refuses parent substitution between internal stat and open',t=>{
  const {repo,sandbox}=harbor(t);write(repo,'shared/data.md','SAFE-IN');write(sandbox,'external/data.md','SECRET-OUT');
  const result=child('race',repo,join(sandbox,'external'));
  assert.equal(result.swapped,true,'probe must reach the public read/open boundary');
  assert.equal(result.exitCode,5,JSON.stringify(result));assert.equal(result.content,undefined,'outside bytes must never return');
});
for(const count of [40,41]) test(`LINK review chain boundary ${count}`,t=>{
  const {repo}=harbor(t);write(repo,'target.md','safe');
  for(let n=0;n<count;n++)symlinkSync(n===count-1?'target.md':`l${n+1}.md`,join(repo,`l${n}.md`));
  const result=child('chain',repo);
  if(count===40)assert.equal(result.content,'safe',JSON.stringify(result));
  else {assert.equal(result.exitCode,4,JSON.stringify(result));assert.match(result.message,/too many links.*40|40.*too many links/);}
});
test('LINK review expanding loop is bounded by a parent child-process deadline',t=>{
  const {repo}=harbor(t);symlinkSync('d/d',join(repo,'d'));
  const result=child('expanding',repo);
  assert.equal(result.exitCode,4,JSON.stringify(result));assert.match(result.message,/loop|too many links/);
});
