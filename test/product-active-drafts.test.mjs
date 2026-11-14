import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cpSync, existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fillHashes, runTry } from '../src/runtime-seam.mjs';
import { fakeRuntime, portsFor, temp } from './helpers/runtime-fake.mjs';

const read = path => readFileSync(path, 'utf8');
const write = (root, path, text) => { mkdirSync(dirname(join(root, path)), {recursive:true}); writeFileSync(join(root, path), text); };
function git(root, ...args) {
  const result = spawnSync('git', args, {cwd:root, encoding:'utf8'});
  assert.equal(result.status, 0, result.stderr);
  return result.stdout.trim();
}
function fixture(t) {
  const folder = temp(t), root = join(folder, 'product');
  cpSync(new URL('../examples/coffee-pickup/', import.meta.url), root, {recursive:true});
  for (const part of ['phone', 'server', 'barista']) {
    const prompt = `prompts/${part}/${part === 'barista' ? 'board' : part}.prompt.md`;
    write(root, prompt, read(join(root, prompt)).replaceAll('examples/coffee-pickup/', ''));
    const map = `app/maps/${part}.json`;
    if (existsSync(join(root, map))) write(root, map, read(join(root, map)).replaceAll('examples/coffee-pickup/', ''));
  }
  write(root, 'product/plan.md', read(join(root, 'product/plan.md')).replaceAll('examples/coffee-pickup/', ''));
  const scenario = read(new URL('./runtime/J1-coffee-pickup.json', import.meta.url)).replaceAll('examples/coffee-pickup/', '');
  write(root, 'tests/J1-coffee-pickup.json', scenario);
  write(root, 'user_stories/journeys/J1-coffee-pickup.md', read(new URL('../user_stories/journeys/J1-coffee-pickup.md', import.meta.url)));
  git(root, 'init', '-q');
  git(root, 'add', '-A');
  git(root, '-c', 'user.name=Draft test', '-c', 'user.email=draft@example.test', 'commit', '-qm', 'Product plan');
  const commonDir = git(root, 'rev-parse', '--path-format=absolute', '--git-common-dir');
  const records = new Map(), drafts = {};
  function record(part, number, extra = {}) {
    const value = {v:1, number, runId:`draft-${number}`, workflow:'feature', state:'waiting',
      productMarker:`<!-- pdd-product: run=${part}-1 -->`, root:drafts[part], commonDir, ...extra};
    const path = join(commonDir, 'pdd/runs', String(number), 'status.json');
    mkdirSync(dirname(path), {recursive:true});
    writeFileSync(path, JSON.stringify(value));
    records.set(number, path);
    return value;
  }
  for (const [index, part] of ['phone', 'server'].entries()) {
    drafts[part] = join(folder, part);
    git(root, 'worktree', 'add', '-qb', `${part}-draft`, drafts[part]);
    record(part, index + 1);
  }
  const home = join(folder, 'home'); mkdirSync(home);
  return {root, home, state:join(folder, 'state'), drafts, record, records};
}
const extract = (tar, path) => {
  const result = spawnSync('tar', ['-xOf', '-', path], {input:tar});
  assert.equal(result.status, 0, result.stderr.toString());
  return result.stdout.toString('utf8');
};
function answer(entry, fake) {
  if (entry.url === '/v1/version') return {status:200, json:{features:['product-parts-v1']}};
  if (entry.command === 'lint') {
    const listed=spawnSync('tar',['-tf','-'],{input:entry.tar,encoding:'utf8'});
    assert.equal(listed.status,0,listed.stderr);
    return {status:200, json:fake.lint(entry.request.requestId,
      listed.stdout.split('\n').filter(path=>path.endsWith('.prompt.md')).map(path=>({path,state:'draft',admission_state:'draft',interface:{calls:[]}})))};
  }
  if (entry.method === 'POST') return {status:200, json:fake.tryJob(entry.request.requestId)};
  if (entry.url.endsWith('/tests') || entry.url.endsWith('/approvals')) return {status:200,json:{tests:[],approvals:[]}};
  return {status:200,json:fake.tryJob(entry.url.split('/').at(-1))};
}
async function open(setup, fake, options = {}) {
  const {ports} = portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin}, {openUrl:async()=>true});
  const code = await runTry({cwd:setup.root,words:[],options:{'--product':true,'--journey':'J1','--no-open':true,'--no-wait':true,...options}}, ports);
  return {code, text:ports.stdout.text + ports.stderr.text};
}

test('product Try uploads two unmerged drafts, referenced views and root contracts as one connected source', async t => {
  const setup = fixture(t), fake = await fakeRuntime(t, answer);
  const phone = 'prompts/phone/phone.prompt.md', server = 'prompts/server/server.prompt.md';
  write(setup.drafts.phone, phone, read(join(setup.drafts.phone, phone)) + '\nDraft phone text.\n');
  write(setup.drafts.server, server, read(join(setup.drafts.server, server)) + '\nDraft server text.\n');
  for (const [part,path] of [['phone',phone],['server',server]]) {
    const hashes = fillHashes({root:setup.drafts[part],targets:[path]});
    assert.deepEqual(hashes.refused,[]);
  }
  write(setup.drafts.phone, 'views/phone-menu__stacked.ui.svg', read(join(setup.drafts.phone,'views/phone-menu__stacked.ui.svg')).replace('phone · Menu', 'Draft phone · Menu'));
  write(setup.drafts.phone, 'contracts/phone-server.md', 'INVALID DRAFT CONTRACT MUST NOT UPLOAD');
  write(setup.drafts.server, phone, 'UNRELATED PART MUST NOT UPLOAD');
  write(setup.drafts.server, 'unrelated.txt', 'UNRELATED FILE MUST NOT UPLOAD');
  // No checkout holds both selected prompt drafts; the root has only the plan and journey.
  rmSync(join(setup.root, 'prompts/phone'), {recursive:true});
  rmSync(join(setup.root, 'prompts/server'), {recursive:true});
  rmSync(join(setup.root, 'app/maps/phone.json'));
  const before = [setup.root, ...Object.values(setup.drafts)].map(root=>git(root,'status','--porcelain'));
  const records = [...setup.records.values()].map(read);
  const result = await open(setup, fake);
  assert.equal(result.code, 0, result.text);
  const posted = fake.posts.find(entry=>entry.command==='try');
  const map = JSON.parse(extract(posted.tar, posted.request.app_map));
  assert.deepEqual(map.screens.map(screen=>screen.id), ['phone/menu','barista/board']);
  const handler = map.handlers.find(item=>item.screen==='phone/menu');
  assert.deepEqual(handler.after.map(step=>step.handler), [
    {prompt_path:server,operation:'forward_tickets'},
    {prompt_path:'prompts/barista/board.prompt.md',operation:'refresh'}
  ]);
  assert.match(extract(posted.tar,phone), /Draft phone text/);
  assert.match(extract(posted.tar,server), /Draft server text/);
  assert.equal(extract(posted.tar,'contracts/phone-server.md'), read(join(setup.root,'contracts/phone-server.md')));
  assert.match(extract(posted.tar,'views/phone-menu__stacked.ui.svg'), /Draft phone/);
  assert.equal(posted.tar.includes(Buffer.from('UNRELATED FILE MUST NOT UPLOAD')), false);
  assert.equal(posted.tar.includes(Buffer.from('UNRELATED PART MUST NOT UPLOAD')), false);
  // Controlled operation executor: the real composed chain and uploaded seed determine dispatch.
  // Hosted interpretation itself is outside this offline integration test.
  const world = JSON.parse(extract(posted.tar,'contracts/product-seed.json'));
  const operations = new Map([
    [phone+'#order', () => world.order_requests.push({id:'order-1',drink:'latte',size:'M'})],
    [server+'#forward_tickets', () => world.tickets.push({id:world.order_requests[0].id,drink:'latte',size:'M'})],
    ['prompts/barista/board.prompt.md#refresh', () => assert.equal(world.tickets[0].id,'order-1')]
  ]);
  for (const target of [handler.handler,...handler.after.map(step=>step.handler)]) operations.get(target.prompt_path+'#'+target.operation)();
  assert.equal(world.tickets[0].id, 'order-1');
  assert.deepEqual([setup.root,...Object.values(setup.drafts)].map(root=>git(root,'status','--porcelain')), before);
  assert.deepEqual([...setup.records.values()].map(read), records);
  assert.equal(existsSync(join(setup.root,posted.request.app_map)), false);
});

test('ambiguous active runs name the part and both checkout paths before upload', async t => {
  const setup = fixture(t), fake = await fakeRuntime(t, answer);
  setup.record('phone',3,{runId:'other-phone'});
  const result = await open(setup,fake);
  assert.notEqual(result.code,0);
  assert.match(result.text,/phone.*(?:multiple|ambiguous)/i);
  assert.ok(result.text.includes(setup.drafts.phone));
  assert.match(result.text,/draft-1/); assert.match(result.text,/other-phone/);
  assert.equal(fake.posts.length,0);
});

for (const missing of ['prompts/phone/phone.prompt.md','app/maps/phone.json','views/phone-menu__stacked.ui.svg']) {
  test(`missing draft input ${missing} refuses root fallback`, async t=>{
    const setup=fixture(t),fake=await fakeRuntime(t,answer);
    rmSync(join(setup.drafts.phone,missing));
    const result=await open(setup,fake);
    assert.notEqual(result.code,0,result.text);
    assert.match(result.text,/phone/);
    assert.ok(result.text.includes(missing) || result.text.includes('prompts/phone'));
    assert.equal(fake.posts.length,0);
  });
}

test('two draft parts claiming one referenced view refuse even with identical bytes', async t=>{
  const setup=fixture(t),fake=await fakeRuntime(t,answer);
  const server='prompts/server/server.prompt.md';
  write(setup.drafts.server,server,read(join(setup.drafts.server,server))+'\n![Shared](../../views/phone-menu__stacked.ui.svg)\n');
  const result=await open(setup,fake);
  assert.notEqual(result.code,0);
  assert.match(result.text,/phone/); assert.match(result.text,/server/);
  assert.match(result.text,/views\/phone-menu__stacked.ui.svg/);
  assert.equal(fake.posts.length,0);
});

test('ended runs and near-prefix planned markers preserve single-checkout composition', async t=>{
  const setup=fixture(t),fake=await fakeRuntime(t,answer);
  setup.record('phone',1,{state:'completed'});
  setup.record('server',2,{productMarker:'<!-- pdd-product: run=server-10 -->'});
  rmSync(join(setup.drafts.phone,'prompts/phone'),{recursive:true});
  rmSync(join(setup.drafts.server,'prompts/server'),{recursive:true});
  const result=await open(setup,fake);
  assert.equal(result.code,0,result.text);
  const posted=fake.posts.find(entry=>entry.command==='try');
  assert.match(extract(posted.tar,'prompts/server/server.prompt.md'),/forward_tickets/);
});

test('a scenario-only dependency cannot fall back to a root prompt owned by an active draft', async t=>{
  const setup=fixture(t),fake=await fakeRuntime(t,answer);
  const path='prompts/phone/journey-only.prompt.md';
  write(setup.root,path,read(join(setup.root,'prompts/phone/phone.prompt.md')));
  const scenario=JSON.parse(read(join(setup.root,'tests/J1-coffee-pickup.json')));
  scenario.steps[0].entry_path=path;
  write(setup.root,'tests/J1-coffee-pickup.json',JSON.stringify(scenario));
  const result=await open(setup,fake);
  assert.notEqual(result.code,0,result.text);
  assert.match(result.text,/phone/);
  assert.ok(result.text.includes(path),result.text);
  assert.equal(fake.posts.length,0);
});

test('drafts from another Git repository refuse before uploading any source', async t=>{
  const setup=fixture(t),fake=await fakeRuntime(t,answer);
  setup.record('phone',1,{root:setup.home});
  const result=await open(setup,fake);
  assert.notEqual(result.code,0);
  assert.match(result.text,/phone/);
  assert.ok(result.text.includes(setup.home));
  assert.equal(fake.posts.length,0);
});

test('reference expansion cannot hide root fallback inside a draft-owned folder', async t=>{
  const setup=fixture(t),fake=await fakeRuntime(t,answer);
  const contract='prompts/phone/root-only-contract.md';
  write(setup.root,contract,read(join(setup.root,'contracts/phone-server.md')));
  const prompt='prompts/journey-only.prompt.md';
  write(setup.root,prompt,read(join(setup.root,'prompts/phone/phone.prompt.md')).replaceAll('contracts/phone-server.md',contract).replaceAll('../../','../'));
  assert.deepEqual(fillHashes({root:setup.root,targets:[prompt]}).refused,[]);
  const scenario=JSON.parse(read(join(setup.root,'tests/J1-coffee-pickup.json')));
  scenario.steps[0].entry_path=prompt;
  write(setup.root,'tests/J1-coffee-pickup.json',JSON.stringify(scenario));
  const result=await open(setup,fake);
  assert.notEqual(result.code,0,result.text);
  assert.match(result.text,/phone/);
  assert.ok(result.text.includes(contract),result.text);
  assert.equal(fake.posts.length,0);
});

test('a new draft-only prompt retains its saved source baseline on product Try reuse', async t=>{
  const setup=fixture(t),fake=await fakeRuntime(t,answer);
  const original='prompts/phone/phone.prompt.md',added='prompts/phone/draft-only.prompt.md';
  write(setup.drafts.phone,added,read(join(setup.drafts.phone,original)));
  const map=read(join(setup.drafts.phone,'app/maps/phone.json')).replaceAll(original,added);
  write(setup.drafts.phone,'app/maps/phone.json',map);
  write(setup.root,'tests/J1-coffee-pickup.json',read(join(setup.root,'tests/J1-coffee-pickup.json')).replaceAll(original,added));
  assert.equal(existsSync(join(setup.root,added)),false);
  const first=await open(setup,fake);
  assert.equal(first.code,0,first.text);
  const second=await open(setup,fake);
  assert.equal(second.code,0,second.text);
  const door=await open(setup,fake,{'--cli':true});
  // The fixture has no terminal entry. Reuse must reach that eligibility check,
  // rather than reject a draft prompt that is present in its captured baseline.
  assert.equal(door.code,125,door.text);
  assert.doesNotMatch(door.text,/A prompt changed or this Try has no source record/);
  assert.match(door.text,/CLI|command.line|terminal/i);
  assert.equal(fake.posts.length,2);
  assert.equal(fake.deletes.length,0);
});
