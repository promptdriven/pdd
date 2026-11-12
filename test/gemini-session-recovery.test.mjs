import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {mkdirSync, writeFileSync, readFileSync, readdirSync, statSync} from 'node:fs';
import {join} from 'node:path';
import {openRun, runStatus, stepDone, approveRun} from '../src/workflow-runner.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const id = 'aaaaaaaa-aaaa-4aaa-8aaa-aaaaaaaaaaaa';
const other = 'bbbbbbbb-bbbb-4bbb-8bbb-bbbbbbbbbbbb';
const hash = root => createHash('sha256').update(root).digest('hex');
const launches = f => f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run');
async function setup(t, {format = 'json', custom = false, slug = false} = {}) {
  const f = await fixture(t, {agent:'gemini'});
  if (custom) { f.ports.env.GEMINI_CLI_HOME = join(f.base, 'saved-account'); mkdirSync(f.ports.env.GEMINI_CLI_HOME); }
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), chat = run.chats.at(-1);
  f.herdr.paneOf(chat).agent = null;
  delete f.ports.findNativeSessions;
  const home = custom ? f.ports.env.GEMINI_CLI_HOME : f.ports.env.HOME;
  const base = join(home, '.gemini');
  const dir = join(base, 'tmp', slug ? 'saved-worktree' : hash(run.root), 'chats');
  mkdirSync(dir, {recursive:true});
  if (slug) writeFileSync(join(base, 'projects.json'), JSON.stringify({projects:{[run.root]:'saved-worktree'}}));
  const file = join(dir, `session-synthetic.${format}`);
  const record = {sessionId:id, projectHash:hash(run.root), startTime:new Date(chat.startedAt + 1).toISOString(), kind:'main', messages:[{type:'user',content:'Continue the same work.'}]};
  const save = (value = record) => writeFileSync(file, JSON.stringify(value) + (format === 'jsonl' ? '\n' : ''));
  save(); f.tick(31_000);
  f.ports.env.GEMINI_CLI_HOME = join(f.base, 'incoming-other-account');
  return {f, run, chat, file, dir, record, save};
}

for (const format of ['json', 'jsonl']) for (const custom of [false, true]) for (const closed of [false, true]) {
  test(`Gemini ${format}, ${custom ? 'saved' : 'default'} account, ${closed ? 'closed' : 'existing'} workspace resumes unobserved history`, async t => {
    const {f, run, chat, file} = await setup(t, {format, custom, slug:format === 'jsonl'});
    const bytes = readFileSync(file), mtime = statSync(file).mtimeMs;
    if (closed) await f.herdr.herdr(['workspace','close',chat.workspaceId]);
    const before = launches(f).length;
    const result = await openRun({ref:'17', cwd:f.source, packageRoot}, f.ports);
    assert.equal(result.exitCode, 0, result.message);
    const sent = launches(f).slice(before);
    assert.equal(sent.length, 1);
    assert.match(sent[0][3], new RegExp(`--resume '${id}'`), 'Resume the recovered Gemini UUID');
    assert.equal(sent[0][3].includes(f.ports.env.GEMINI_CLI_HOME), false, 'Incoming account never replaces saved account');
    const current = f.record();
    assert.equal(current.chats.at(-1).session.id, id);
    assert.equal(current.chats.at(-1).area, chat.area);
    assert.equal(current.root, run.root);
    assert.deepEqual(current.done, run.done);
    assert.deepEqual(readFileSync(file), bytes);
    assert.equal(statSync(file).mtimeMs, mtime);
  });
}

test('status discovers the ended Gemini session before ordinary open, without a Herdr UUID', async t => {
  const {f} = await setup(t);
  const status = await runStatus({ref:'17', cwd:f.source}, f.ports);
  assert.equal(status.exitCode, 0, status.message);
  const chat = f.record().chats.at(-1);
  assert.equal(chat.state, 'ended');
  assert.equal(chat.session.id, id);
  const before = launches(f).length;
  assert.equal((await openRun({ref:'17',cwd:f.source,packageRoot}, f.ports)).exitCode, 0);
  assert.equal(launches(f).length, before + 1);
  assert.match(launches(f).at(-1)[3], /--resume/);
});

for (const closed of [false, true]) for (const mode of ['missing', 'ambiguous', 'malformed']) {
  test(`Gemini ${mode} session, ${closed ? 'closed' : 'existing'} workspace offers a fresh chat without guessing`, async t => {
    const {f, chat, file, dir, record} = await setup(t);
    if (mode === 'missing') writeFileSync(file, JSON.stringify({...record, projectHash:hash('/somewhere-else')}));
    if (mode === 'ambiguous') writeFileSync(join(dir, 'session-other.json'), JSON.stringify({...record, sessionId:other}));
    if (mode === 'malformed') writeFileSync(file, '{');
    // This chat was seen running, but never supplied a UUID.
    const saved = f.record(); saved.chats.at(-1).state = 'running';
    writeFileSync(join(saved.runDir, 'status.json'), JSON.stringify(saved));
    if (closed) await f.herdr.herdr(['workspace','close',chat.workspaceId]);
    const before = launches(f).length;
    const result = await openRun({ref:'17',cwd:f.source,packageRoot}, f.ports);
    assert.equal(result.exitCode, 1);
    assert.match(result.message, new RegExp(`${chat.area}.*pdd workflow open 17 --new`));
    assert.equal(result.message.trim().split('\n').length, 1);
    assert.equal(launches(f).length, before);
    // Explicit fresh open still works in the same area, using the saved account.
    delete f.ports.env.GEMINI_CLI_HOME;
    const fresh = await openRun({ref:'17',cwd:f.source,packageRoot,newSession:true}, f.ports);
    assert.equal(fresh.exitCode, 0, fresh.message);
    assert.equal(f.record().chats.at(-1).area, chat.area);
    assert.doesNotMatch(launches(f).at(-1)[3], /--resume/);
    assert.ok(readdirSync(dir).includes('session-synthetic.json'));
  });
}


test('a historical Gemini recovery refusal never offers to replace the current area', async t => {
  const {f, chat, save, record} = await setup(t);
  delete f.ports.env.GEMINI_CLI_HOME;
  f.herdr.paneOf(chat).agent = {agent:'gemini', agent_status:'idle', prompts:[]};
  const scope = await stepDone({step:'scope',summary:'Keep the saved Gemini history.',cwd:f.record().root}, f.agentPorts());
  assert.equal(scope.exitCode,0,scope.message);
  const approved = await approveRun({ref:'17',cwd:f.source},f.ports);
  assert.equal(approved.exitCode,0,approved.message);
  const current = f.record().chats.at(-1);
  assert.notEqual(current.area,chat.area);
  f.herdr.paneOf(chat).agent = null;
  save({...record,projectHash:hash('/another-worktree')});
  const ended = f.record(), historical = ended.chats.find(item => item.area === chat.area);
  historical.state = 'running'; historical.session = null;
  writeFileSync(join(ended.runDir,'status.json'),JSON.stringify(ended));
  const before = launches(f).length;
  const result = await openRun({ref:'17',cwd:f.source,area:chat.area,packageRoot},f.ports);
  assert.equal(result.exitCode,1,result.message);
  assert.match(result.message,/fresh chat is available only in the current area/);
  assert.doesNotMatch(result.message,/workflow open 17 --new/);
  assert.equal(result.message.trim().split('\n').length,1);
  assert.equal(launches(f).length,before);
  assert.equal(f.record().chats.at(-1).paneId,current.paneId);
});
