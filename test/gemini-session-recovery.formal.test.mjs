import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {mkdtempSync, mkdirSync, writeFileSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {ownSession} from '../src/workflow-chat.mjs';

const digest = value => createHash('sha256').update(value).digest('hex');
const ids = ['aaaaaaaa-aaaa-4aaa-8aaa-aaaaaaaaaaaa', 'bbbbbbbb-bbbb-4bbb-8bbb-bbbbbbbbbbbb'];
const start = Date.parse('2024-01-01T00:00:00Z');

// Two records, each absent or one of these independent eligibility classes. Both
// file formats and distinct versus duplicate identities are enumerated below.
const classes = ['absent', 'start', 'end', 'before', 'after', 'foreign', 'subagent', 'account'];
test('bounded Gemini ownership selects exactly one distinct eligible main session', async t => {
  const base = mkdtempSync(join(tmpdir(), 'pdd-gemini-formal-'));
  t.after(() => rmSync(base, {recursive:true, force:true}));
  const root = join(base, 'worktree'), saved = join(base, 'saved'), incoming = join(base, 'incoming');
  const directory = home => join(home, '.gemini', 'tmp', digest(root), 'chats');
  const chat = {agent:'gemini', configDir:saved, startedAt:start};
  const run = {agent:'gemini', root, chats:[chat]};
  for (const format of ['json', 'jsonl']) for (const first of classes) for (const second of classes) for (const duplicate of [false, true]) {
    rmSync(join(saved, '.gemini'), {recursive:true, force:true});
    rmSync(join(incoming, '.gemini'), {recursive:true, force:true});
    const expected = new Set();
    for (const [index, kind] of [first, second].entries()) {
      if (kind === 'absent') continue;
      const id = ids[index && !duplicate ? 1 : 0];
      const at = start + ({start:0, end:1000, before:-1, after:1001}[kind] ?? 500);
      const record = {sessionId:id, projectHash:digest(kind === 'foreign' ? root + '-other' : root), startTime:new Date(at).toISOString(), kind:kind === 'subagent' ? 'subagent' : 'main'};
      const dir = directory(kind === 'account' ? incoming : saved);
      mkdirSync(dir, {recursive:true});
      writeFileSync(join(dir, `session-${index}.${format}`), JSON.stringify(record) + (format === 'jsonl' ? '\n' : ''));
      if (kind === 'start' || kind === 'end') expected.add(id);
    }
    const actual = await ownSession({run, chat, since:start, ports:{env:{HOME:base, GEMINI_CLI_HOME:incoming}, now:() => start + 1000}});
    const context = `${format} ${first} ${second} duplicate=${duplicate}`;
    if (expected.size === 1) assert.deepEqual(actual, {kind:'match', id:[...expected][0]}, context);
    else assert.notEqual(actual.kind, 'match', context);
  }
});

test('the next launch or resume excludes its timestamp and later sessions', async t => {
  const base = mkdtempSync(join(tmpdir(), 'pdd-gemini-next-'));
  t.after(() => rmSync(base, {recursive:true, force:true}));
  const root = join(base, 'worktree'), dir = join(base, '.gemini', 'tmp', digest(root), 'chats');
  mkdirSync(dir, {recursive:true});
  const chat = {agent:'gemini', startedAt:start};
  for (const key of ['startedAt', 'resumedAt']) for (const delta of [499, 500, 501]) {
    writeFileSync(join(dir, 'session-one.json'), JSON.stringify({sessionId:ids[0], projectHash:digest(root), startTime:new Date(start + delta).toISOString(), kind:'main'}));
    const run = {agent:'gemini', root, chats:[chat, {[key]:start + 500}]};
    const actual = await ownSession({run, chat, since:start, ports:{env:{HOME:base}, now:() => start + 1000}});
    if (delta === 499) assert.deepEqual(actual, {kind:'match', id:ids[0]}, `${key} ${delta}`);
    else assert.notEqual(actual.kind, 'match', `${key} ${delta}`);
  }
});
