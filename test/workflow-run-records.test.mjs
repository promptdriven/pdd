import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, writeFile } from 'node:fs/promises';
import { execFileSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { matchStageSessionFiles, readRunIndex, reopenCommand } from '../src/workflow-run-records.mjs';

test('run lookup sees journals from a main checkout and its linked worktree', async t => {
  const root = await mkdtemp(join(tmpdir(), 'pdd-records-')); t.after(async () => execFileSync('rm', ['-rf', root]));
  execFileSync('git', ['init', '-q', root]); execFileSync('git', ['-C', root, 'config', 'user.email', 'test@example.com']); execFileSync('git', ['-C', root, 'config', 'user.name', 'Test']);
  await writeFile(join(root, 'file'), 'x'); execFileSync('git', ['-C', root, 'add', 'file']); execFileSync('git', ['-C', root, 'commit', '-qm', 'init']);
  const linked = `${root}-linked`; execFileSync('git', ['-C', root, 'worktree', 'add', '-q', linked]);
  const id = '123e4567-e89b-42d3-a456-426614174000', runDir = join(root, '.git', 'pdd', 'workflows', id);
  await mkdir(runDir, { recursive: true });
  const state = { runId: id, seq: 1, name: 'small-change', repo: 'one/app', issue: { number: 2, title: 'Test' }, agent: 'codex', root: linked, startedAt: 1000,
    definitions: [{ id: 'scope', kind: 'agent' }], index: 1, completed: [] };
  await writeFile(join(runDir, 'journal.jsonl'), JSON.stringify({ seq: 1, state }) + '\n');
  const main = await readRunIndex({ cwd: root }); const fromLinked = await readRunIndex({ cwd: linked });
  assert.equal(main.entries.length, 1); assert.equal(fromLinked.entries[0].runId, id);
});

test('session-file evidence matches exactly one Codex session and gives a reopen command', async t => {
  const home = await mkdtemp(join(tmpdir(), 'pdd-session-')); t.after(async () => execFileSync('rm', ['-rf', home]));
  const sessions = join(home, '.codex', 'sessions', '2026'); await mkdir(sessions, { recursive: true });
  const id = '123e4567-e89b-42d3-a456-426614174000';
  await writeFile(join(sessions, 'rollout-one.jsonl'), JSON.stringify({ type: 'session_meta', id, cwd: '/tmp/worktree', timestamp: 1500 }) + '\n');
  const found = await matchStageSessionFiles({ agent: 'codex', root: '/tmp/worktree', startedAt: 1000, endedAt: 2000 }, { home, codexHome: join(home, '.codex') });
  assert.deepEqual(found.matches, [{ agent: 'codex', id, source: 'session-file' }]);
  assert.equal(reopenCommand('/tmp/worktree', found.matches[0]), `cd '/tmp/worktree' && codex resume ${id}`);
});

test('session-file evidence refuses zero and multiple matches with reasons', async t => {
  const home = await mkdtemp(join(tmpdir(), 'pdd-session-cardinality-')); t.after(async () => execFileSync('rm', ['-rf', home]));
  const sessions = join(home, '.codex', 'sessions'); await mkdir(sessions, { recursive: true });
  const base = { type: 'session_meta', cwd: '/tmp/worktree', timestamp: 1500 };
  const none = await matchStageSessionFiles({ agent: 'codex', root: '/tmp/worktree', startedAt: 1000, endedAt: 2000 }, { home, codexHome: join(home, '.codex') });
  assert.equal(none.matches.length, 0); assert.match(none.reason, /no session file/);
  await writeFile(join(sessions, 'rollout-one.jsonl'), JSON.stringify({ ...base, id: '123e4567-e89b-42d3-a456-426614174000' }) + '\n');
  await writeFile(join(sessions, 'rollout-two.jsonl'), JSON.stringify({ ...base, id: '123e4567-e89b-42d3-a456-426614174001' }) + '\n');
  const many = await matchStageSessionFiles({ agent: 'codex', root: '/tmp/worktree', startedAt: 1000, endedAt: 2000 }, { home, codexHome: join(home, '.codex') });
  assert.equal(many.matches.length, 2); assert.match(many.reason, /2 session files/);
});

test('Claude reopen evidence uses native user records and its escaped project directory', async t => {
  const home = await mkdtemp(join(tmpdir(), 'pdd-claude-session-')); t.after(async () => execFileSync('rm', ['-rf', home]));
  const root='/tmp/work.tree_5', sessions=join(home,'.claude','projects',root.replace(/[^a-zA-Z0-9]/g,'-'));
  await mkdir(sessions,{recursive:true});
  const id='123e4567-e89b-42d3-a456-426614174000';
  await writeFile(join(sessions,`${id}.jsonl`),JSON.stringify({type:'user',sessionId:id,cwd:root,timestamp:new Date(1500).toISOString(),message:{role:'user',content:'Synthetic request'}})+'\n');
  const found=await matchStageSessionFiles({agent:'claude',root,startedAt:1000,endedAt:2000},{home});
  assert.deepEqual(found.matches,[{agent:'claude',id,source:'session-file'}]);
});
