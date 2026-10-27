import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { matchStageSessionFiles, reopenCommand, runStatusFromState } from '../src/workflow-run-records.mjs';

test('stage session recovery requires the assigned worktree and time window', async () => {
  const home = await mkdtemp(join(tmpdir(), 'pdd-runs-records-'));
  const sessions = join(home, '.codex', 'sessions', '2026', '10', '26');
  await mkdir(sessions, { recursive: true });
  const id = '123e4567-e89b-42d3-a456-426614174000';
  await writeFile(join(sessions, 'rollout-test.jsonl'), JSON.stringify({ type: 'session_meta', id, cwd: '/tmp/worktree', timestamp: 1500 }) + '\n');
  const found = await matchStageSessionFiles({ agent: 'codex', root: '/tmp/worktree', startedAt: 1000, endedAt: 2000 }, { home, codexHome: join(home, '.codex') });
  assert.deepEqual(found.matches, [{ agent: 'codex', id, source: 'session-file' }]);
  assert.equal(reopenCommand('/tmp/worktree', found.matches[0]), `cd '/tmp/worktree' && codex resume ${id}`);
  const outside = await matchStageSessionFiles({ agent: 'codex', root: '/tmp/other', startedAt: 1000, endedAt: 2000 }, { home, codexHome: join(home, '.codex') });
  assert.equal(outside.matches.length, 0);
});

test('run status preserves stage timestamp boundaries for local formatting', async () => {
  const state = { runId: '123e4567-e89b-42d3-a456-426614174001', name: 'small-change', root: '/tmp/worktree', agent: 'codex', startedAt: 1000,
    definitions: [{ id: 'scope', kind: 'agent' }, { id: 'change', kind: 'agent' }], index: 1,
    completed: [{ id: 'scope', kind: 'agent', agent: 'codex', startedAt: 1000, endedAt: 2500 }] };
  const status = await runStatusFromState(state, { now: 3000 }, { home: '/no-such-home', codexHome: '/no-such-codex-home' });
  assert.equal(status.startedAt, 1000);
  assert.deepEqual(status.steps.map(step => [step.id, step.state, step.startedAt, step.endedAt]), [['scope', 'done', 1000, 2500], ['change', 'waiting', null, null]]);
  assert.equal(status.steps[0].session, null);
});

test('finished stage never trusts a saved session without one exact folder/window match', async () => {
  const home = await mkdtemp(join(tmpdir(), 'pdd-runs-unique-'));
  const sessions = join(home, 'sessions'); await mkdir(sessions);
  const state = { runId: '123e4567-e89b-42d3-a456-426614174000', root: '/tmp/worktree', agent: 'codex',
    definitions: [{ id: 'scope', kind: 'agent' }], index: 1,
    completed: [{ id: 'scope', agent: 'codex', startedAt: 1000, endedAt: 2000, backend: { nativeSession: { value: 'saved-but-unproved' } } }] };
  const ports = { home, codexHome: home };
  assert.equal((await runStatusFromState(state, {}, ports)).steps[0].session, null);
  const first = '123e4567-e89b-42d3-a456-426614174001';
  await writeFile(join(sessions, 'rollout-one.jsonl'), JSON.stringify({ type: 'session_meta', payload: { id: first, cwd: state.root, timestamp: 1000 } }));
  assert.equal((await runStatusFromState(state, {}, ports)).steps[0].session.id, first);
  await writeFile(join(sessions, 'rollout-two.jsonl'), JSON.stringify({ type: 'session_meta', payload: { id: '123e4567-e89b-42d3-a456-426614174002', cwd: state.root, timestamp: 2000 } }));
  const ambiguous = (await runStatusFromState(state, {}, ports)).steps[0];
  assert.equal(ambiguous.session, null); assert.equal(ambiguous.reopen, null);
  assert.match(ambiguous.sessionReason, /2 session files/);
});
