import test from 'node:test';
import assert from 'node:assert/strict';
import { runPdd } from '../src/pdd-cli.mjs';

const id = '123e4567-e89b-42d3-a456-426614174000';
const capture = () => ({ text: '', write(value) { this.text += value; } });
const state = { runId: id, name: 'small-change', repo: 'octo/app', issue: { number: 7 }, root: '/tmp/worktree', agent: 'codex', startedAt: 1700000000000,
  definitions: [{ id: 'scope', kind: 'agent' }], index: 1,
  completed: [{ id: 'scope', kind: 'agent', agent: 'codex', startedAt: 1700000000000, endedAt: 1700000005000, backend: { agent: 'codex', nativeSession: { value: '123e4567-e89b-42d3-a456-426614174001' } } }] };
const records = { readRunIndex: async () => ({ entries: [{ runId: id, runDir: `/tmp/runs/${id}`, startedAt: state.startedAt, repo: state.repo, issue: state.issue }], dropped: 0 }),
  readJournalLast: async () => ({ value: { seq: 2, state }, warnings: [] }),
  runStatusFromState: async value => ({ v: 1, runId: value.runId, workflow: value.name, repo: value.repo, issue: value.issue, root: value.root, state: 'completed', steps: [{ id: 'scope', state: 'done', startedAt: 1700000000000, endedAt: 1700000005000, agent: 'codex', session: { agent: 'codex', id: '123e4567-e89b-42d3-a456-426614174001' }, reopen: "cd '/tmp/worktree' && codex resume 123e4567-e89b-42d3-a456-426614174001" }] }) };

test('workflow runs lists and details finished stages without mutating', async () => {
  const list = { stdout: capture(), stderr: capture() };
  assert.equal(await runPdd(['workflow', 'runs'], { ...list, workflowRecords: records }), 0);
  assert.match(list.stdout.text, /octo\/app#7.*small-change.*done/);
  assert.match(list.stdout.text, new RegExp(`pdd workflow runs ${id}`));
  const detail = { stdout: capture(), stderr: capture() };
  assert.equal(await runPdd(['workflow', 'runs', id], { ...detail, workflowRecords: records }), 0);
  assert.match(detail.stdout.text, /start \d{2}:\d{2}:\d{2}.*duration 5s/);
  assert.match(detail.stdout.text, /codex resume 123e4567-e89b-42d3-a456-426614174001/);
  assert.doesNotMatch(detail.stdout.text, /170000000/);
});
