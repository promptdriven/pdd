import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { viewRun } from '../src/workflow-view.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/workflow-view-json-2574.json', import.meta.url)));
function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), 'view-vectors-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  assert.equal(spawnSync('git', ['init', '-q', root]).status, 0);
  const runDir = join(root, '.git/pdd/runs/2574'); mkdirSync(runDir, { recursive: true });
  return { root, runDir, save(run) { writeFileSync(join(runDir, 'status.json'), JSON.stringify({ ...run, root, commonDir: join(root, '.git'), runDir })); } };
}

test('replay each scenario check through viewRun', async t => {
  const f = fixture(t), lookup = scenario.simulation['runs.resolveRun'].cases;
  let index = 0, checks = 0;
  for (const step of scenario.steps) {
    const entry = lookup[index++];
    assert.deepEqual(entry.args, { ref: step.input.ref, cwd: step.input.cwd });
    f.save(JSON.parse(entry.result.json).run);
    // Map the scenario project to the isolated native Git root.
    const result = await viewRun({ ...step.input, cwd: f.root });
    for (const check of step.checks) {
      assert.equal(check.target, 'result'); assert.equal(check.path, '/message'); assert.equal(check.op, 'equals');
      assert.equal(result.message, check.value, `${step.step_id} ${check.criterion_id}`); checks++;
    }
  }
  assert.equal(index, lookup.length); assert.equal(checks, 4);
});

test('bounded saved-gate, approval and privacy rules', async t => {
  const f = fixture(t);
  let cases = 0;
  for (const state of ['waiting', 'completed', 'cancelled']) for (const kind of ['approve', 'ask-code'])
    for (const gatePresent of [false, true]) for (const privateActor of [false, true]) {
      const actor = privateActor ? 'https://runtime.example/s/secret' : 'person-1';
      const run = { v: 1, runId: 'bounded', repo: 'example/project', number: 2574, state, area: 0,
        areas: [{ name: 'story', steps: [] }], chats: [], pr: [{ url: 'https://github.com/example/project/pull/12' }],
        decisions: [{ decision: 'approve', evidence: { actor: { kind: 'person', id: actor }, at: 1000 } }],
        gate: gatePresent ? { id: 'saved-gate', area: 'story', at: 2000, kind } : null };
      f.save(run);
      const result = await viewRun({ ref: '2574', cwd: f.root, json: true });
      assert.equal(result.exitCode, 0);
      const data = JSON.parse(result.message);
      const active = gatePresent && (state === 'waiting' || state === 'completed' && kind === 'ask-code');
      assert.deepEqual(data.gate, active ? { id: 'saved-gate', message: null } : null);
      assert.deepEqual(data.approvals, [{ actor: { kind: 'person', id: privateActor ? '[private link removed]' : actor }, at: 1000 }]);
      assert.deepEqual(data.links.prs, ['https://github.com/example/project/pull/12']);
      assert.ok(!result.message.includes('/s/secret')); cases++;
    }
  assert.equal(cases, 24);
});

test('native transcript identity, gate time and link privacy', async t => {
  const f = fixture(t), home = join(f.root, 'codex'), id = '12345678-1234-1234-1234-123456789abc';
  const dir = join(home, 'sessions', '2025', '01', '01'); mkdirSync(dir, { recursive: true });
  const row = value => JSON.stringify(value) + '\n', time = ms => new Date(ms).toISOString();
  writeFileSync(join(dir, `rollout-${id}.jsonl`),
    row({ type: 'session_meta', timestamp: time(1000), payload: { id, cwd: f.root, timestamp: time(1000) } }) +
    row({ type: 'response_item', timestamp: time(1500), payload: { type: 'message', role: 'assistant', phase: 'final_answer', content: [{ type: 'output_text', text: 'stale' }] } }) +
    row({ type: 'response_item', timestamp: time(2200), payload: { type: 'message', role: 'assistant', phase: 'final_answer', content: [{ type: 'output_text', text: 'Review https://runtime.example/s/secret' }] } }));
  const run = { v: 1, runId: 'transcript', repo: 'example/project', number: 2574, state: 'waiting', area: 0,
    areas: [{ name: 'story', steps: [] }], gate: { id: 'gate', area: 'story', at: 2000 },
    chats: [{ area: 'story', startedAt: 1000, configDir: home, session: { agent: 'codex', id } }],
    pr: [{ url: 'https://runtime.example/s/private' }], decisions: [] };
  const read = async () => { f.save(run); return JSON.parse((await viewRun({ ref: '2574', cwd: f.root, json: true })).message); };
  let data = await read();
  assert.equal(data.gate.message, 'Review [private link removed]');
  assert.deepEqual(data.links.prs, ['[private link removed]']);
  run.gate.at = 2300; data = await read(); assert.equal(data.gate.message, null);
  run.gate.at = 2000; run.chats[0].session.id = '87654321-1234-1234-1234-123456789abc';
  data = await read(); assert.equal(data.gate.message, null);
});
