import test from 'node:test';
import assert from 'node:assert/strict';
import { publicStatus } from '../src/workflow-runner.mjs';

const base = (extra = {}) => ({ repo: 'promptdriven/pdd', number: 2571, issue: { number: 2571, title: 'Status', url: 'https://github.com/promptdriven/pdd/issues/2571' }, workflow: 'feature', agent: 'codex', root: '/tmp/worktree', areas: [{ name: 'Story', steps: ['story'] }], area: 0, done: {}, pr: [], ...extra });
const item = { ref: '#2571', number: 2571, group: 'waiting', words: 'Try it: https://runtime.example.test/s/SECRET/ then approve', prs: [], updatedAt: 1, root: '/tmp/worktree', runDir: '/tmp/run', viewCommand: 'pdd workflow view 2571' };

test('versioned status row has stable waits, Herdr session and redacted Try links', () => {
  const row = publicStatus(base({ gate: { id: 'Story:approve', area: 'Story', kind: 'approve', at: 1 } }), item, 'working');
  assert.equal(row.waits_for, 'gate');
  assert.equal(row.gate_id, 'Story:approve');
  assert.equal(row.chat.session, 'pdd');
  assert.equal(row.question, null);
  assert.equal(row.words.includes('SECRET'), false);
});

test('question and stopped reasons are represented', () => {
  const question = publicStatus(base({ question: { text: 'Try https://runtime.example.test/s/SECRET/ ?', at: 2 } }), item, 'blocked');
  assert.equal(question.waits_for, 'question');
  assert.equal(question.question.includes('SECRET'), false);
  const stopped = publicStatus(base({ stopReason: 'usage_limit' }), item, 'stopped');
  assert.equal(stopped.waits_for, 'chat_stopped');
  assert.equal(stopped.stopped_reason, 'usage_limit');
});

test('draft is retained from refreshed GitHub state', () => {
  const row = publicStatus(base({ pr: [{ number: 1, url: 'https://github.com/promptdriven/pdd/pull/1', isDraft: true, ci: 'passing' }] }), item, null);
  assert.equal(row.pull_requests[0].draft, true);
});
