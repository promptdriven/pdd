import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import * as fs from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {findNativeSessions, readApprovalEvidence} from '../src/approval-evidence.mjs';

const id = 'aaaaaaaa-aaaa-4aaa-8aaa-aaaaaaaaaaaa';
const other = 'bbbbbbbb-bbbb-4bbb-8bbb-bbbbbbbbbbbb';
async function fixture(t) {
  const home = await fs.mkdtemp(join(tmpdir(), 'pdd-gemini-reader-'));
  t.after(() => fs.rm(home, {recursive:true,force:true}));
  const root = join(home, 'worktree'), startedAt = Date.parse('2026-01-01T00:00:00Z');
  const projectHash = createHash('sha256').update(root).digest('hex');
  const project = join(home, '.gemini', 'tmp', projectHash), dir = join(project,'chats');
  await fs.mkdir(dir, {recursive:true});
  const stage = {agent:'gemini',root,startedAt,endedAt:startedAt+1000};
  const meta = {sessionId:id,projectHash,startTime:new Date(startedAt).toISOString()};
  const file = join(dir, 'session-short-id.jsonl');
  return {home,project,dir,file,stage,meta,ports:{env:{HOME:home}}};
}

test('Gemini JSONL merges metadata updates and ignores a partial final write; migrated copies deduplicate', async t => {
  const f = await fixture(t);
  await fs.writeFile(f.file, [f.meta, {$set:{sessionId:other}}, {id:'message',type:'user',content:'approve'}].map(JSON.stringify).join('\n')+'\n{"sessionId":');
  await fs.writeFile(join(f.dir,'session-legacy.json'), JSON.stringify({...f.meta,sessionId:other,messages:[]}));
  assert.deepEqual(await findNativeSessions(f.stage,f.ports), [{id:other,startedAt:f.stage.startedAt}]);
  assert.deepEqual(await findNativeSessions({...f.stage,sessionId:id},f.ports), []);
});

for (const content of ['{}\n', '{bad}\n', 'null\n', '{"$set":null}\n']) test(`Gemini refuses damaged session evidence ${content.trim()}`, async t => {
  const f = await fixture(t); await fs.writeFile(f.file, content);
  await assert.rejects(findNativeSessions(f.stage,f.ports), {code:'session_unreadable'});
});

test('Gemini does not manufacture uniqueness when one session file is unreadable', async t => {
  const f = await fixture(t); await fs.writeFile(f.file, JSON.stringify(f.meta)+'\n');
  await assert.rejects(findNativeSessions(f.stage,{...f.ports,fs:{...fs,readFile:async(path,...args)=>{
    if(path===f.file) throw Object.assign(Error('permission denied'),{code:'EACCES'});
    return fs.readFile(path,...args);
  }}}), {code:'session_unreadable'});
});

test('Gemini skips symlink files and selected chats directories', async t => {
  const f = await fixture(t), target = join(f.home, 'foreign.json');
  await fs.writeFile(target, JSON.stringify(f.meta));
  await fs.symlink(target,join(f.dir,'session-symlink.json'));
  assert.deepEqual(await findNativeSessions(f.stage,f.ports), []);
  await fs.rm(f.dir,{recursive:true});
  const foreign = join(f.home,'foreign'); await fs.mkdir(foreign);
  await fs.writeFile(join(foreign,'session-one.json'),JSON.stringify(f.meta));
  await fs.symlink(foreign,f.dir);
  assert.deepEqual(await findNativeSessions(f.stage,f.ports), []);
});

test('Gemini refuses malformed or traversal project registries', async t => {
  const f = await fixture(t), registry = join(f.home,'.gemini','projects.json');
  for(const text of ['{', JSON.stringify({projects:{[f.stage.root]:'../../foreign'}})]) {
    await fs.writeFile(registry,text);
    await assert.rejects(findNativeSessions(f.stage,f.ports),{code:'session_unreadable'});
  }
});

test('Gemini native sessions never become approval evidence', async () => {
  const actual = await readApprovalEvidence({stage:{agent:'gemini',root:'/worktree',startedAt:0,endedAt:1},gateAskedAt:0,decision:'approve'},
    {now:()=>2,fs:{readFile:()=>assert.fail('Approval must refuse without reading Gemini messages')}});
  assert.equal(actual.ok,false); assert.equal(actual.code,'invalid_request');
});
