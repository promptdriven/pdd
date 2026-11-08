// Native vectors through existing workflow record boundaries. These also run on the base.
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { updateRun } from '../src/workflow-runs.mjs';
import { fixture } from './helpers/workflow-runner-fixture.mjs';

const ids = { codex: '11111111-1111-4111-8111-111111111111', claude: '22222222-2222-4222-8222-222222222222' };
for (const agent of ['codex', 'claude']) test(`cost AC1/AC5: ${agent} account totals survive repeated captures without messages`, async t => {
  const f = await fixture(t, { agent }); assert.equal((await f.run()).exitCode, 0);
  let run = f.record();
  const config = join(f.base, `${agent}-account`);
  const file = agent === 'codex' ? join(config, 'sessions/2026/10/27', `rollout-synthetic-${ids[agent]}.jsonl`)
    : join(config, 'projects', run.root.replace(/[^a-zA-Z0-9]/g, '-'), `${ids[agent]}.jsonl`);
  mkdirSync(join(file, '..'), { recursive: true });
  writeFileSync(file, readFileSync(new URL(`./fixtures/cost-ledger/${agent}.jsonl`, import.meta.url)));
  run = updateRun(run.runDir, latest => { latest.chats = [0, 1].map(() => ({ ...latest.chats[0], agent, configDir: config, session: { id: ids[agent] } })); return latest; }, f.ports);
  const expected = agent === 'codex' ? { input: 300, cachedInput: 60, output: 80, reasoningOutput: 30, total: 380 }
    : { input: 65, cachedInput: 30, output: 25, reasoningOutput: 0, total: 90 };
  assert.equal(run.cost?.tokens?.length, 1, 'cost ledger must expose one account for deduplicated native sessions');
  for (const [key, value] of Object.entries(expected)) assert.equal(run.cost.tokens[0][key], value, key);
  const repeated = updateRun(run.runDir, latest => latest, f.ports);
  assert.deepEqual(repeated.cost.tokens, run.cost.tokens);
  assert.equal(repeated.cost.events.filter(e => e.metric === 'total').reduce((sum, e) => sum + e.value, 0), expected.total);
  const text = JSON.stringify(run.cost);
  for (const secret of ['PRIVATE_SYNTHETIC_TEXT', config, ids[agent]]) assert.ok(!text.includes(secret), 'cost data must exclude text, paths and raw session ids');
});

test('cost AC3: saved questions, answers and person approvals retain elapsed waits', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode, 0);
  const dir = f.record().runDir, at = f.clock;
  updateRun(dir, run => { run.question = { at, area: 'plan', text: 'PRIVATE_QUESTION' }; return run; }, f.ports);
  f.tick(120000);
  let run = updateRun(dir, run => { run.changes.push({ stage: 'plan', at: f.clock, answer: true, text: 'PRIVATE_ANSWER' }); run.question = null; return run; }, f.ports);
  assert.equal(run.cost?.person?.questions, 1, 'cost ledger must retain question interactions');
  assert.equal(run.cost.person.answers, 1); assert.equal(run.cost.person.waitingMinutes, 2);
  updateRun(dir, run => { run.gate = { id: 'gate-1', area: 'plan', at: f.clock, kind: 'approve' }; return run; }, f.ports);
  f.tick(60000);
  run = updateRun(dir, run => { run.decisions.push({ gateId: 'gate-1', decision: 'approve', at: f.clock, evidence: { actor: { kind: 'terminal' } } }); run.gate = null; return run; }, f.ports);
  assert.equal(run.cost.person.approvals, 1); assert.equal(run.cost.person.waitingMinutes, 3);
  assert.equal(run.cost.person.activeMinutes, null); assert.equal(run.cost.suiteMinutes, null);
  assert.ok(!JSON.stringify(run.cost).includes('PRIVATE_'));
});

test('cost AC2: merged, closed, stuck and parked outcomes follow saved workflow facts', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode, 0);
  const dir = f.record().runDir;
  for (const [state, outcome] of [['stuck', 'stuck'], ['paused', 'parked'], ['cancelled', 'closed']]) {
    const run = updateRun(dir, run => { run.state = state; return run; }, f.ports);
    assert.equal(run.cost?.outcome, outcome, 'cost ledger must expose the actual issue outcome');
  }
  const run = updateRun(dir, run => { run.state = 'completed'; run.pr = [{ number: 23, stage: run.areas.at(-1).name, state: 'merged' }]; return run; }, f.ports);
  assert.equal(run.cost.outcome, 'merged');
});
