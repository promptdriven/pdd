import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs/promises';
import { join, dirname } from 'node:path';
import { tmpdir } from 'node:os';
import { readApprovalEvidence, findNativeSessions } from '../src/approval-evidence.mjs';

const id = '11111111-1111-4111-8111-111111111111';
const otherId = '22222222-2222-4222-8222-222222222222';
const start = Date.parse('2026-10-26T10:00:00Z');
const gate = start + 1000;
const now = start + 10000;
const cwd = '/tmp/project.work_tree';
const iso = ms => new Date(ms).toISOString();
const meta = (extra = {}) => ({ type: 'session_meta', payload: { id, cwd, timestamp: iso(start), ...extra } });
const user = (text = 'I approve this plan.', at = gate + 1) => ({
  type: 'response_item', timestamp: iso(at),
  payload: { type: 'message', role: 'user', content: [{ type: 'input_text', text }] },
});
const claude = (text, at, extra = {}) => ({
  type: 'user', sessionId: id, cwd, timestamp: iso(at),
  message: { role: 'user', content: [{ type: 'text', text }] }, ...extra,
});

async function fixture(t, agent = 'codex') {
  const home = await fs.mkdtemp(join(tmpdir(), 'pdd-evidence-'));
  t.after(() => fs.rm(home, { recursive: true, force: true }));
  const ports = { home, env: {}, now: () => now };
  const request = { stage: { agent, root: cwd, startedAt: start, endedAt: gate }, gateAskedAt: gate, decision: 'approve' };
  const directory = agent === 'codex' ? join(home, '.codex', 'sessions', '2026', '10', '26')
    : join(home, '.claude', 'projects', '-tmp-project-work-tree');
  const file = join(directory, agent === 'codex' ? 'rollout-one.jsonl' : `${id}.jsonl`);
  const write = async (rows, path = file, tail = '') => {
    await fs.mkdir(dirname(path), { recursive: true });
    await fs.writeFile(path, rows.map(row => JSON.stringify(row)).join('\n') + '\n' + tail);
  };
  return { home, ports, request, file, directory, write, read: () => readApprovalEvidence(request, ports) };
}

test('Codex user after gate returns exact text and session identity for the journal', async t => {
  const f = await fixture(t);
  await f.write([meta(), user('  approved\nwith context  ')]);
  assert.deepEqual(await f.read(), { ok: true, decision: 'approve', agent: 'codex', sessionId: id,
    userMessage: '  approved\nwith context  ', userMessageAt: gate + 1 });
});

for (const [label, rows] of [
  ['none', [meta()]],
  ['only before gate', [meta(), user('yes', gate - 1)]],
  ['exactly at gate', [meta(), user('yes', gate)]],
  ['in the future', [meta(), user('yes', now + 1)]],
  ['blank', [meta(), user(' \n ')]],
  ['assistant only', [meta(), { ...user(), payload: { type: 'message', role: 'assistant', content: 'approved' } }]],
  ['developer only', [meta(), { ...user(), payload: { type: 'message', role: 'developer', content: 'approved' } }]],
]) test(`refuses when user evidence is ${label}`, async t => {
  const f = await fixture(t);
  await f.write(rows);
  const result = await f.read();
  assert.equal(result.ok, false);
  assert.equal(result.code, 'user_message_missing');
  assert.doesNotMatch(result.message, /[\r\n]/);
});

test('two candidate sessions refuse even when only one has a reply', async t => {
  const f = await fixture(t);
  await f.write([meta(), user()]);
  await f.write([meta({ id: otherId })], join(f.directory, 'rollout-two.jsonl'));
  assert.equal((await f.read()).code, 'session_ambiguous');
});

test('Codex generated environment and AGENTS user-role records do not prove a person replied', async t => {
  const f = await fixture(t);
  await f.write([meta(), user('<environment_context>\n<current_date>2026-10-27</current_date>\n</environment_context>'),
    user('# AGENTS.md instructions for /tmp/project\n\n<INSTRUCTIONS>generated</INSTRUCTIONS>', gate + 2)]);
  assert.equal((await f.read()).code, 'user_message_missing');
});

test('unrelated cwd and sessions outside inclusive stage window are not candidates', async t => {
  const f = await fixture(t);
  await f.write([meta({ cwd: cwd + '-other' }), user()]);
  await f.write([meta({ timestamp: iso(start - 1) }), user()], join(f.directory, 'rollout-before.jsonl'));
  await f.write([meta({ timestamp: iso(gate + 1) }), user()], join(f.directory, 'rollout-after.jsonl'));
  assert.equal((await f.read()).code, 'session_not_found');
  await f.write([meta({ timestamp: iso(gate) }), user()], join(f.directory, 'rollout-boundary.jsonl'));
  assert.equal((await f.read()).ok, true);
});

test('latest user message wins for changes, including Codex event format', async t => {
  const f = await fixture(t);
  f.request.decision = 'changes';
  await f.write([meta(), user(), { type: 'event_msg', timestamp: iso(gate + 2),
    payload: { type: 'user_message', message: 'Please fix the error case.' } }]);
  assert.equal((await f.read()).userMessage, 'Please fix the error case.');
  assert.equal((await f.read()).decision, 'changes');
});

test('Claude native identity and text blocks work without Codex metadata', async t => {
  const f = await fixture(t, 'claude');
  await f.write([{ type: 'file-history-snapshot' }, claude('initial request', start), claude('yes', gate + 1)]);
  assert.deepEqual(await f.read(), { ok: true, decision: 'approve', agent: 'claude', sessionId: id,
    userMessage: 'yes', userMessageAt: gate + 1 });
});

test('Claude excludes meta, sidechain and tool-result user records', async t => {
  const f = await fixture(t, 'claude');
  await f.write([claude('initial request', start), claude('system injected', gate + 1, { isMeta: true }),
    claude('subagent', gate + 2, { isSidechain: true }),
    claude('', gate + 3, { message: { role: 'user', content: [{ type: 'tool_result', content: 'yes' }] } })]);
  assert.equal((await f.read()).code, 'user_message_missing');
});

test('Claude refuses a conflicting session identity', async t => {
  const f = await fixture(t, 'claude');
  await f.write([claude('initial request', start), claude('yes', gate + 1, { sessionId: otherId })]);
  assert.equal((await f.read()).code, 'session_unreadable');
});

for (const agent of ['codex', 'claude']) test(`${agent} respects configured home without scanning default home`, async t => {
  const f = await fixture(t, agent);
  const rows = agent === 'codex' ? [meta(), user()] : [claude('initial request', start), claude('yes', gate + 1)];
  await f.write(rows);
  const custom = join(f.home, 'custom');
  f.ports.env[agent === 'codex' ? 'CODEX_HOME' : 'CLAUDE_CONFIG_DIR'] = custom;
  assert.equal((await f.read()).code, 'session_not_found');
  const path = agent === 'codex' ? join(custom, 'sessions', 'rollout-custom.jsonl')
    : join(custom, 'projects', '-tmp-project-work-tree', `${id}.jsonl`);
  await f.write(rows, path);
  assert.equal((await f.read()).ok, true);
});

test('Claude subagent directories and symbolic links are not candidates', async t => {
  const f = await fixture(t, 'claude');
  const nested = join(f.directory, 'subagents', 'agent.jsonl');
  await f.write([claude('request', start), claude('yes', gate + 1)], nested);
  await fs.symlink(nested, f.file);
  assert.equal((await f.read()).code, 'session_not_found');
});

test('incomplete final user record is not evidence; malformed complete records refuse', async t => {
  const f = await fixture(t);
  await f.write([meta()], f.file, JSON.stringify(user()));
  assert.equal((await f.read()).code, 'user_message_missing');
  await f.write([meta(), user()], f.file, '{bad json}\n');
  assert.equal((await f.read()).code, 'session_unreadable');
});

test('unreadable discovery cannot establish a unique session', async t => {
  const f = await fixture(t);
  await f.write([meta(), user()]);
  await f.write([meta({ id: otherId })], join(f.directory, 'rollout-two.jsonl'));
  f.ports.fs = { ...fs, readFile: async (path, ...args) => {
    if (path.endsWith('rollout-two.jsonl')) throw Object.assign(new Error('private diagnostic'), { code: 'EACCES' });
    return fs.readFile(path, ...args);
  } };
  const result = await f.read();
  assert.equal(result.code, 'session_unreadable');
  assert.doesNotMatch(result.message, /private diagnostic/);
});

test('missing or invalid stage/gate/decision refuses before discovery', async () => {
  const stage = { agent: 'codex', root: cwd, startedAt: start, endedAt: gate };
  for (const request of [undefined, {}, { stage, gateAskedAt: NaN, decision: 'approve' },
    { stage, gateAskedAt: start - 1, decision: 'approve' }, { stage, gateAskedAt: now + 1, decision: 'approve' },
    { stage: { ...stage, root: '.' }, gateAskedAt: gate, decision: 'approve' },
    { stage: { ...stage, endedAt: start - 1 }, gateAskedAt: gate, decision: 'approve' },
    { stage, gateAskedAt: gate, decision: 'skip' }]) {
    assert.equal((await readApprovalEvidence(request, { now: () => now })).code, 'invalid_request');
  }
});

// Seen in a real Codex run: each step subagent writes its own rollout with the same worktree cwd.
test('Codex subagent rollouts in the same worktree do not make the main chat ambiguous', async t => {
  const f = await fixture(t);
  const sub = { type: 'session_meta', payload: { id: otherId, cwd, timestamp: iso(start + 10), thread_source: 'subagent',
    parent_thread_id: id, source: { subagent: { thread_spawn: { parent_thread_id: id } } } } };
  await f.write([sub, user('a subagent brief', gate + 2)], join(f.directory, 'rollout-two.jsonl'));
  await f.write([meta({ thread_source: 'user', source: 'cli' }), user('I approve')]);
  const result = await f.read();
  assert.equal(result.ok, true, result.message); assert.equal(result.sessionId, id); assert.equal(result.userMessage, 'I approve');
  assert.deepEqual((await findNativeSessions(f.request.stage, f.ports)).map(match => match.id), [id]);
});

test('a resumed Codex session written to a second file with the same id is still one session', async t => {
  const f = await fixture(t);
  await f.write([meta(), user('first turn', start + 5)]);
  await f.write([meta(), user('I approve after resume')], join(f.directory, 'rollout-resumed.jsonl'));
  const result = await f.read();
  assert.equal(result.ok, true, result.message); assert.equal(result.userMessage, 'I approve after resume');
});
