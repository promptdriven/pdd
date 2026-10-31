import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync, symlinkSync, unlinkSync } from 'node:fs';
import { join } from 'node:path';
import { harbor } from './runtime-fake.mjs';

async function helpers() {
  try { return await import('../src/program-data.mjs'); }
  catch (error) { assert.fail(`Public programData module is required: ${error.code}`); }
}
function repository(t) {
  return harbor(t, root => {
    writeFileSync(join(root, 'first.prompt.md'), '# First program\n');
    writeFileSync(join(root, 'second.prompt.md'), '# Second program\n');
  });
}
const selection = (programData, root, program) => programData({root, program, flags:{}}, {});

test('program mapping initializes and reuses a world while unrelated mapping work owns a lock', async t => {
  const {programData, acquireProgramLock} = await helpers();
  const h = repository(t);
  selection(programData, h.repo, 'first');
  const release = acquireProgramLock(join(h.repo, '.pdd/run'));
  try {
    const second = selection(programData, h.repo, 'second');
    assert.deepEqual(second.startingData.initial_world, {});
    const bytes = '{"second":"saved world"}\n';
    writeFileSync(join(second.dir, 'world.json'), bytes);
    const reused = selection(programData, h.repo, 'second');
    assert.equal(reused.dir, second.dir);
    assert.deepEqual(reused.startingData.initial_world, {second:'saved world'});
    assert.equal(readFileSync(join(second.dir, 'world.json'), 'utf8'), bytes);
  } finally { release(); }
});

for (const metadata of ['program.json', 'session.json']) {
  test(`malformed unrelated ${metadata} cannot block another program's initialization or saved world`, async t => {
    const {programData} = await helpers();
    const h = repository(t);
    const first = selection(programData, h.repo, 'first');
    // Legacy session ownership is also supported when no program record exists.
    const brokenDir = metadata === 'program.json' ? first.dir : join(h.repo, '.pdd/run/legacy-unrelated');
    if (brokenDir !== first.dir) mkdirSync(brokenDir);
    const bytes = '{"unfinished":';
    writeFileSync(join(brokenDir, metadata), bytes);
    const second = selection(programData, h.repo, 'second');
    assert.deepEqual(second.startingData.initial_world, {});
    writeFileSync(join(second.dir, 'world.json'), '{"kept":true}\n');
    const reused = selection(programData, h.repo, 'second');
    assert.equal(reused.dir, second.dir);
    assert.deepEqual(reused.startingData.initial_world, {kept:true});
    assert.equal(readFileSync(join(brokenDir, metadata), 'utf8'), bytes);
  });
}

for (const metadata of ['program.json', 'session.json']) {
  test(`malformed selected ${metadata} refuses locally and preserves its bytes and world`, async t => {
    const {programData} = await helpers();
    const h = repository(t);
    const run = join(h.repo, '.pdd/run');
    mkdirSync(join(run, 'second'), {recursive:true});
    const dir = join(run, 'second'), bad = '{"unfinished":', world = '{"keep":"exact"}\n';
    writeFileSync(join(dir, metadata), bad);
    writeFileSync(join(dir, 'world.json'), world);
    assert.throws(() => selection(programData, h.repo, 'second'), error => {
      assert.equal(error.exitCode, 2);
      assert.match(error.message, /metadata|JSON|parse|program|session/i);
      return true;
    });
    assert.equal(readFileSync(join(dir, metadata), 'utf8'), bad);
    assert.equal(readFileSync(join(dir, 'world.json'), 'utf8'), world);
  });
}

test('unsafe selected directory refuses without altering the linked world', async t => {
  const {programData} = await helpers();
  const h = repository(t), outside = join(h.home, 'outside');
  mkdirSync(outside);
  const bytes = '{"keep":"outside"}\n';
  writeFileSync(join(outside, 'world.json'), bytes);
  mkdirSync(join(h.repo, '.pdd/run'), {recursive:true});
  symlinkSync(outside, join(h.repo, '.pdd/run/second'), 'dir');
  assert.throws(() => selection(programData, h.repo, 'second'), error => {
    assert.equal(error.exitCode, 2);
    assert.match(error.message, /unsafe|symlink|directory/i);
    return true;
  });
  assert.equal(readFileSync(join(outside, 'world.json'), 'utf8'), bytes);
});

test('a live selected program owner still refuses a second owner and preserves its world', async t => {
  const {programData, acquireProgramLock} = await helpers();
  const h = repository(t), second = selection(programData, h.repo, 'second');
  const bytes = '{"keep":"owned world"}\n';
  writeFileSync(join(second.dir, 'world.json'), bytes);
  const release = acquireProgramLock(second.dir);
  try {
    assert.throws(() => acquireProgramLock(second.dir), error => {
      assert.equal(error.exitCode, 125);
      assert.match(error.message, /active|busy|finish/i);
      return true;
    });
    assert.equal(readFileSync(join(second.dir, 'world.json'), 'utf8'), bytes);
  } finally { release(); }
  const next = acquireProgramLock(second.dir);
  next();
});

for(const newcomer of ['place_order','later/place_order'])test(`base folder owned by another program isolates ${newcomer}`,async t=>{
 const {programData}=await helpers();const h=repository(t);
 mkdirSync(join(h.repo,'prompts'),{recursive:true});
 writeFileSync(join(h.repo,'prompts/place_order.prompt.md'),'# Existing owner\n');
 const owner=selection(programData,h.repo,'prompts/place_order');
 writeFileSync(join(owner.dir,'world.json'),'{"owner":"unchanged"}\n');
 if(newcomer.includes('/'))mkdirSync(join(h.repo,'later'));
 writeFileSync(join(h.repo,newcomer+'.prompt.md'),'# Newcomer\n');
 const next=selection(programData,h.repo,newcomer);
 assert.notEqual(next.dir,owner.dir);assert.deepEqual(next.startingData.initial_world,{});
 writeFileSync(join(next.dir,'world.json'),' {"newcomer":true}');
 const reused=selection(programData,h.repo,'prompts/place_order');
 assert.equal(reused.dir,owner.dir);assert.deepEqual(reused.startingData.initial_world,{owner:'unchanged'});
 const literal='%r__place_order';writeFileSync(join(h.repo,literal+'.prompt.md'),'# Literal escape marker\n');
 const escaped=selection(programData,h.repo,literal);assert.notEqual(escaped.dir,next.dir);assert.notEqual(escaped.dir,owner.dir);
});

test('base owner survives removal of its prompt when a sole visible newcomer arrives',async t=>{
 const {programData}=await helpers();const h=repository(t);
 mkdirSync(join(h.repo,'prompts'),{recursive:true});const oldPath=join(h.repo,'prompts/place_order.prompt.md');
 writeFileSync(oldPath,'# Old owner\n');const owner=selection(programData,h.repo,'prompts/place_order');
 const bytes='{"old":"preserve exact bytes"}\n';writeFileSync(join(owner.dir,'world.json'),bytes);
 unlinkSync(oldPath);mkdirSync(join(h.repo,'later'));
 writeFileSync(join(h.repo,'later/place_order.prompt.md'),'# Sole visible newcomer\n');
 const newcomer=selection(programData,h.repo,'later/place_order');assert.notEqual(newcomer.dir,owner.dir);
 assert.deepEqual(newcomer.startingData.initial_world,{});assert.equal(readFileSync(join(owner.dir,'world.json'),'utf8'),bytes);
 assert.deepEqual(JSON.parse(readFileSync(join(owner.dir,'program.json'),'utf8')),{program:'prompts/place_order'});
});
