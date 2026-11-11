import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cpSync, existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runTry, readTryOwner } from '../src/runtime-client.mjs';
import { fakeRuntime, portsFor, sha, temp } from './runtime-fake.mjs';

function coffee(t) {
  const folder = temp(t), repo = join(folder, 'repo'), home = join(folder, 'home'), state = join(folder, 'state');
  cpSync(new URL('../examples/coffee-pickup/', import.meta.url), repo, { recursive: true }); mkdirSync(home);
  for (const part of ['phone', 'server', 'barista']) {
    const path = join(repo, `app/maps/${part}.json`);
    if (existsSync(path)) writeFileSync(path, readFileSync(path, 'utf8').replaceAll('examples/coffee-pickup/', ''));
    const prompt = join(repo, `prompts/${part}/${part === 'barista' ? 'board' : part}.prompt.md`);
    writeFileSync(prompt, readFileSync(prompt, 'utf8').replaceAll('examples/coffee-pickup/', ''));
  }
  const plan = join(repo, 'product/plan.md'); writeFileSync(plan, readFileSync(plan, 'utf8').replaceAll('examples/coffee-pickup/', ''));
  mkdirSync(join(repo, 'tests')); mkdirSync(join(repo, 'user_stories/journeys'), { recursive: true });
  const scenario = JSON.parse(readFileSync(new URL('./runtime/J1-coffee-pickup.json', import.meta.url), 'utf8').replaceAll('examples/coffee-pickup/', ''));
  scenario.initial_world.set['/journeyOnly'] = true;
  scenario.initial_world.set['/menu/0/priceCents'] = 999;
  writeFileSync(join(repo, 'tests/J1-coffee-pickup.json'), JSON.stringify(scenario));
  cpSync(new URL('../user_stories/journeys/J1-coffee-pickup.md', import.meta.url), join(repo, scenario.story_path));
  writeFileSync(join(repo, 'prompts/phone/seed.json'), '{"enabled":false}');
  for (const args of [['init', '-q'], ['add', '-A']]) assert.equal(spawnSync('git', args, { cwd: repo }).status, 0);
  return { repo, home, state, scenario, authored: readFileSync(join(repo, 'tests/J1-coffee-pickup.json'), 'utf8') };
}
const extract = (tar, path) => {
  const result = spawnSync('tar', ['-xOf', '-', path], { input: tar });
  assert.equal(result.status, 0, result.stderr.toString()); return result.stdout.toString('utf8');
};
function trying(entry, fake) {
  if(entry.url==='/v1/version')return {status:200,json:{features:['product-parts-v1']}};
  if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: fake.lint(entry.request.requestId,
    ['phone/phone', 'server/server', 'barista/board'].map(name => ({ path: `prompts/${name}.prompt.md`, state: 'draft', admission_state: 'draft', interface: { calls: [] } }))) };
  if (entry.method === 'POST') return { status: 200, json: fake.tryJob(entry.request.requestId) };
  if (entry.method === 'DELETE') return { status: 200, json: fake.stopJob(entry.headers['x-request-id'], entry.url.split('/').at(-1)) };
  if (entry.url.endsWith('/tests') || entry.url.endsWith('/approvals')) return { status: 200, json: { tests: [], approvals: [] } };
  return { status: 200, json: fake.tryJob(entry.url.split('/').at(-1)) };
}
async function open(setup, fake, options, words = []) {
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, { openUrl: async () => true });
  const code = await runTry({ cwd: setup.repo, words, options: { '--no-open': true, '--no-wait': true, ...options } }, ports);
  return { code, out: ports.stdout.text, err: ports.stderr.text };
}


test('whole product sends a composed map and source-bound owners, without authored writes',async t=>{
 const setup=coffee(t),fake=await fakeRuntime(t,trying);
 const result=await open(setup,fake,{'--product':true,'--journey':'J1'});
 assert.equal(result.code,0,result.err+result.out);
 assert.deepEqual(fake.posts.map(x=>x.command),['lint','try']);
 const {request,tar}=fake.posts[1];
 assert.equal(request.seed,'tests/J1-coffee-pickup.json');
 const map=JSON.parse(extract(tar,request.app_map));
 assert.deepEqual(map.screens.map(x=>x.id),['phone/menu','barista/board']);
 assert.equal(map.handlers[0].after.length,2);
 const world=JSON.parse(extract(tar,'contracts/product-seed.json'));
 assert.equal(world.journeyOnly,true);assert.equal(world.menu[0].priceCents,999);
 assert.equal(JSON.parse(extract(tar,request.seed)).initial_world.journeyOnly,true);
 assert.deepEqual(request.product_parts.map(p=>p.name),['phone','server','barista']);
 assert.ok(request.product_parts.find(p=>p.name==='server').prompt_paths.includes('prompts/server/server.prompt.md'));
 assert.equal(readFileSync(join(setup.repo,request.seed),'utf8'),setup.authored);
 assert.equal(existsSync(join(setup.repo,request.app_map)),false);
 assert.match(result.err,/up to 40 AI calls/);
 assert.match(result.err,/Product screens: phone · menu, barista · board/);
 assert.match(result.err,/3 handler\/background operations per tap, before drawing/);
 assert.equal((await open(setup,fake,{},[request.seed])).code,0);
 assert.equal(fake.posts.length,2,'ordinary owner reuse must not create a standalone product');
 assert.equal((await open(setup,fake,{'--product':true,'--journey':setup.scenario.story_path})).code,0);
 assert.equal(fake.posts.length,2,'an equivalent journey selector retains the uploaded session');
 const changed=await open(setup,fake,{'--product':true,'--parts':'phone'});
 assert.equal(changed.code,4);assert.equal(fake.posts.length,2);assert.equal(fake.deletes.length,0);
});
test('missing product capability stops before upload and old ignored names remain private',async t=>{
 const setup=coffee(t);
 let supported=false;
 const fake=await fakeRuntime(t,(entry,f)=>entry.url==='/v1/version'?{status:200,json:{features:supported?['product-parts-v1']:[]}}:trying(entry,f));
 assert.equal((await open(setup,fake,{'--product':true})).code,5);
 assert.equal(fake.posts.length,0);
 supported=true;
 writeFileSync(join(setup.repo,'.gitignore'),'app/maps/product.json\n');
 writeFileSync(join(setup.repo,'app/maps/product.json'),'PRIVATE-CONTENT');
 const result=await open(setup,fake,{'--product':true});
 assert.equal(result.code,0,result.err+result.out);
 assert.equal(fake.posts[1].request.app_map,'app/maps/product_1.json');
 assert.ok(!fake.posts[1].tar.includes(Buffer.from('PRIVATE-CONTENT')));
});
test('paused product is reopened with its same ID and no new upload',async t=>{
 const setup=coffee(t);let id=null,paused=false;
 const fake=await fakeRuntime(t,(entry,f)=>{
  if(entry.url==='/v1/version')return {status:200,json:{features:['product-parts-v1']}};
  if(entry.url.endsWith('/reopen')){paused=false;return {status:200,json:f.tryJob(id)};}
  if(entry.method==='GET'&&entry.url.startsWith('/v1/runs/'))return {status:200,json:f.tryJob(id,undefined,paused?'paused':'running')};
  const result=trying(entry,f);if(entry.command==='try')id=entry.request.requestId;return result;
 });
 assert.equal((await open(setup,fake,{'--product':true,'--journey':'J1'})).code,0);paused=true;
 const count=fake.posts.length;
 assert.equal((await open(setup,fake,{},['tests/J1-coffee-pickup.json'])).code,0);
 assert.equal(fake.posts.length,count);assert.equal(fake.jsonPosts.length,1);
 assert.ok(fake.jsonPosts[0].url.includes(id));
});

test('owner-tool access reopens the same paused product without resetting its world',async t=>{
 const setup=coffee(t);let paused=false,id=null,parts;
 const fake=await fakeRuntime(t,(entry,f)=>{
  if(entry.url.endsWith('/model'))return paused?{status:409,json:{error:{code:'session-stopped'}}}:{status:200,json:{entries:[],product_parts:parts}};
  if(entry.url.endsWith('/state'))return {status:200,json:{world:{retained:'data'},actions:[]}};
  if(entry.url.endsWith('/reopen')){paused=false;return {status:200,json:f.tryJob(id)};}
  if(entry.method==='GET'&&entry.url.startsWith('/v1/runs/'))return {status:200,json:f.tryJob(id,undefined,paused?'paused':'running')};
  if(entry.command==='try'){id=entry.request.requestId;parts=entry.request.product_parts;}
  return trying(entry,f);
 });
 assert.equal((await open(setup,fake,{'--product':true,'--journey':'J1'})).code,0);paused=true;
 const {ports}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
 const owner=await readTryOwner({cwd:setup.repo,story:'tests/J1-coffee-pickup.json'},ports);
 assert.equal(owner.record.id,id);assert.deepEqual(owner.data,{retained:'data'});
 assert.deepEqual(owner.model.product_parts,parts);assert.equal(fake.posts.length,2);assert.equal(fake.jsonPosts.length,1);
});
test('an unknown product setup is read by its original ID and never resent',async t=>{
 const setup=coffee(t);let id=null;
 const fake=await fakeRuntime(t,(entry,f)=>{
  if(entry.command==='try'){id=entry.request.requestId;return {status:200,json:f.job(id,'try','unknown',{session:{id,state:'unknown'}})};}
  if(entry.method==='GET'&&entry.url.startsWith('/v1/runs/'))return {status:200,json:f.job(id,'try','unknown',{session:{id,state:'unknown'}})};
  return trying(entry,f);
 });
 assert.equal((await open(setup,fake,{'--product':true,'--journey':'J1'})).code,3);
 const before=fake.posts.length;
 const result=await open(setup,fake,{},['tests/J1-coffee-pickup.json']);
 assert.equal(result.code,3,result.err);assert.ok(result.err.includes(id));
 assert.equal(fake.posts.length,before);assert.equal(fake.deletes.length,0);
});

test('a default selected journey retains its explicit starting values',async t=>{
 const setup=coffee(t),fake=await fakeRuntime(t,trying);
 const result=await open(setup,fake,{'--product':true});
 assert.equal(result.code,0,result.err+result.out);
 const posted=fake.posts.find(entry=>entry.command==='try');
 const world=JSON.parse(extract(posted.tar,posted.request.seed)).initial_world;
 assert.equal(world.journeyOnly,true);assert.equal(world.menu[0].priceCents,999);
});
