import test from 'node:test';
import assert from 'node:assert/strict';
import { sendToChat } from '../src/workflow-chat.mjs';

const missing = () => { throw Object.assign(Error('absent'), { code: 'agent_not_found' }); };
const live = { result: { agent: { agent_status: 'working' } } };
for (const age of [0, 29_750, 30_000, 60_000]) test(`2677 readiness bounds at age ${age}`, async () => {
  let clock = 60_000, inspections = 0, submissions = 0; const waits = [];
  const result = await sendToChat({ paneId: 'original', startedAt: clock - age }, 'exact request', {
    now: () => clock, sleep: async ms => { waits.push(ms); clock += ms; },
    herdr: async args => { assert.equal(args[2], 'original'); if (args[1] === 'get') { inspections++; return missing(); } submissions++; return {}; }
  });
  assert.equal(submissions, 0, 'confirmed absence never submits');
  assert.equal(result.code, age < 30_000 ? 'chat_still_starting' : 'agent_not_found');
  assert.equal(clock, age < 30_000 ? 90_000 - age : 60_000);
  assert.equal(inspections, age < 30_000 ? Math.ceil((30_000 - age) / 250) : 1);
  assert.ok(waits.every(ms => ms > 0 && ms <= 250));
});
test('2677 latest resume gives readiness time and working submits exact text once', async () => {
  let clock = 100_000, inspections = 0; const calls = [], text = '  x "quote"\n  tail  ';
  const result = await sendToChat({ paneId: 'original', startedAt: 0, resumedAt: clock }, text, {
    now: () => clock, sleep: async ms => { clock += ms; }, herdr: async args => {
      calls.push(args); if (args[1] === 'get') { if (++inspections < 3) return missing(); return live; } return {};
    }
  });
  assert.equal(inspections, 3); assert.equal(clock, 100_500); assert.deepEqual(result, { ok: true });
  assert.deepEqual(calls.at(-1), ['agent', 'prompt', 'original', text]); assert.equal(calls.filter(a => a[1] === 'prompt').length, 1);
});
test('2677 missing submission retries readiness within the original deadline', async t => {
  let clock = 0, inspections = 0, submits = 0;
  const result = await sendToChat({ paneId: 'original', startedAt: 0 }, 'retry', {
    now: () => clock, sleep: async ms => { clock += ms; }, herdr: async args => {
      if (args[1] === 'get') { inspections++; return live; } if (++submits === 1) return missing(); return {};
    }
  });
  assert.deepEqual(result, { ok: true }); assert.equal(submits, 2); assert.equal(inspections, 2); assert.equal(clock, 250);
  const f = await started(t), healthy = f.ports.herdr; let attempts = 0;
  f.ports.herdr = async args => { if (args[1] === 'prompt' && ++attempts === 1) return missing(); return healthy(args); };
  f.ports.sleep = async ms => {
    assert.equal(f.journal()[0].state, 'pending');
    assert.ok(!f.journal()[0].inFlight, 'confirmed rejection restores durable pending before another wait or crash');
    f.tick(ms);
  };
  assert.equal((await changeRun({ ref:'17', text:'Retry a rejected submission', cwd:f.source }, f.ports)).exitCode, 0);
  assert.equal(attempts, 2); assert.equal(f.journal()[0].state, 'delivered');
});
test('2677 ambiguous submission returns uncertainty and never retries', async () => {
  let submits = 0, inspections = 0;
  const result = await sendToChat({ paneId: 'original', startedAt: 0 }, 'kept', { now: () => 0,
    sleep: async () => assert.fail('ambiguous submit must not wait'), herdr: async args => {
      if (args[1] === 'get') { inspections++; return live; } submits++; throw Object.assign(Error('lost reply'), { code: 'herdr_failed' });
    }
  });
  assert.deepEqual(result, { ok: false, code: 'herdr_failed', uncertain: true }); assert.equal(submits, 1); assert.equal(inspections, 1);
});
test('2677 first inspection permits an old live pane but refuses inspection failure before send', async () => {
  const calls = [];
  const result = await sendToChat({ paneId: 'old', startedAt: 0 }, 'kept', { now: () => 60_000,
    herdr: async args => { calls.push(args); if (args[1] === 'get') throw Object.assign(Error('unavailable'), { code: 'server_unavailable' }); return {}; }
  });
  assert.deepEqual(result, { ok: false, code: 'server_unavailable' }); assert.deepEqual(calls, [['agent', 'get', 'old']]);
  const liveCalls = [];
  assert.deepEqual(await sendToChat({ paneId: 'old', startedAt: 0 }, 'same', { now: () => 60_000, herdr: async args => { liveCalls.push(args); return live; } }), { ok: true });
  assert.deepEqual(liveCalls, [['agent', 'get', 'old'], ['agent', 'prompt', 'old', 'same']]);
});

// These lifecycle cases complement the immutable vectors at the same public runner boundary.
import { fixture } from './helpers/workflow-delivery-fixture.mjs';
import { changeRun } from '../src/workflow-runner.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
import { chmodSync } from 'node:fs';
async function started(t) { const f = await fixture(t, { agent: 'codex' }); assert.equal((await f.run()).exitCode, 0); return f; }
test('2677 pending request stays on its pane while an independent target accepts new work', async t => {
  const f = await started(t), healthy = f.ports.herdr, first = f.record().chats.at(-1).paneId;
  f.ports.sleep = async ms => f.tick(ms);
  f.ports.herdr = async args => { if (args[0] === 'agent') return missing(); return healthy(args); };
  await changeRun({ ref: '17', text: 'First request', cwd: f.source }, f.ports);
  const latest = f.record(); latest.chats.at(-1).paneId = 'independent'; writeRun(latest, f.ports);
  const prompts = [];
  f.ports.herdr = async args => { if (args[1] === 'get') return live; if (args[1] === 'prompt') { prompts.push(args); return {}; } return healthy(args); };
  assert.equal((await changeRun({ ref: '17', text: 'Independent request', cwd: f.source }, f.ports)).exitCode, 0);
  assert.equal(f.journal().filter(r => r.paneId === first && r.state === 'pending').length, 1);
  assert.equal(prompts.length, 1); assert.equal(prompts[0][2], 'independent'); assert.ok(prompts[0][3].includes('Independent request'));
});
test('2677 identical text as change then answer retains kind and FIFO identity', async t => {
  const f = await started(t), healthy = f.ports.herdr;
  f.ports.sleep = async ms => f.tick(ms);
  f.ports.herdr = async args => { if (args[0] === 'agent') return missing(); return healthy(args); };
  await changeRun({ ref: '17', text: 'Use blue', cwd: f.source }, f.ports);
  const latest = f.record(); latest.question = { text: 'Which colour?', at: f.clock, area: latest.areas[latest.area].name }; writeRun(latest, f.ports);
  f.ports.herdr = healthy;
  assert.equal((await changeRun({ ref: '17', text: 'Use blue', cwd: f.source }, f.ports)).exitCode, 0);
  assert.deepEqual(f.record().changes.map(r => [r.text, Boolean(r.answer)]), [['Use blue', false], ['Use blue', true]]);
  assert.equal(f.record().question, null);
});
test('2677 failed acknowledgement save cannot cause automatic duplicate submission', { skip: process.geteuid?.() === 0 ? 'chmod cannot deny writes to root' : false }, async t => {
  const f = await started(t), healthy = f.ports.herdr, runDir = f.record().runDir; let submits = 0;
  f.ports.herdr = async args => { const result = await healthy(args); if (args[1] === 'prompt') { submits++; chmodSync(runDir, 0o500); } return result; };
  let first;
  try { first = await changeRun({ ref: '17', text: 'Keep this exact request', cwd: f.source }, f.ports); }
  catch (error) { first = { exitCode: 1, message: String(error) }; }
  finally { chmodSync(runDir, 0o700); }
  f.ports.herdr = async args => { if (args[1] === 'prompt') submits++; return healthy(args); };
  const second = await changeRun({ ref: '17', text: 'Keep this exact request', cwd: f.source }, f.ports);
  assert.equal(submits, 1, 'unknown result must block duplicate transport'); assert.notEqual(first.exitCode, 0); assert.notEqual(second.exitCode, 0); assert.match(second.message, /uncertain|inspect/i);
});
test('2677 overlapping changes keep later text without duplicate dispatch', async t => {
  const f = await started(t), healthy = f.ports.herdr; let release, ready = false, entered;
  const waiting = new Promise(resolve => { entered = resolve; });
  const prompts = [];
  f.ports.sleep = async ms => { entered('waiting'); await new Promise(resolve => { release = resolve; }); f.tick(ms); };
  f.ports.herdr = async args => {
    if (args[0] === 'agent' && !ready) return missing();
    if (args[1] === 'prompt') prompts.push(args[3]); return healthy(args);
  };
  const first = changeRun({ ref: '17', text: 'First request', cwd: f.source }, f.ports);
  assert.equal(await Promise.race([waiting, first.then(() => 'completed before readiness')]), 'waiting');
  let second;
  try { second = await changeRun({ ref: '17', text: 'Second request', cwd: f.source }, f.ports); }
  finally { ready = true; release(); }
  assert.notEqual(second.exitCode, 0); assert.match(second.message, /progress|retry/i);
  assert.equal((await first).exitCode, 0);
  assert.equal((await changeRun({ ref: '17', text: 'Second request', cwd: f.source }, f.ports)).exitCode, 0);
  assert.equal(prompts.length, 2); assert.ok(prompts[0].includes('First request')); assert.ok(prompts[1].includes('Second request'));
  assert.deepEqual(f.record().changes.map(r => r.text), ['First request', 'Second request']);
});

test('2677 injected custody failure never submits, including privileged callers', async t => {
  const f = await started(t); let submits = 0;
  const healthy = f.ports.herdr;
  f.ports.deliveryFiles = { ...await import('node:fs'), writeFileSync: () => { throw Object.assign(Error('denied'), { code: 'EACCES' }); } };
  f.ports.herdr = async args => { if (args[1] === 'prompt') submits++; return healthy(args); };
  const result = await changeRun({ ref: '17', text: 'Must retain before send', cwd: f.source }, f.ports);
  assert.equal(submits, 0, 'failure to save custody must prevent transport');
  assert.notEqual(result.exitCode, 0); assert.match(result.message, /save.*not sent/is);
  delete f.ports.deliveryFiles;
  const { writeFileSync } = await import('node:fs');
  writeFileSync(f.record().runDir + '/delivery-journal.json', JSON.stringify({requests:[{id:'malformed',text:'retained',state:'pending'}]}));
  const malformed = await changeRun({ ref:'17', text:'Do not replace malformed custody', cwd:f.source }, f.ports);
  assert.notEqual(malformed.exitCode,0); assert.equal(submits,0,'malformed journal must not be reset and permit submission');
});

test('2677 injected acknowledgement save failure retains in-flight uncertainty', async t => {
  const f = await started(t), fs = await import('node:fs'), healthy = f.ports.herdr; let submits = 0, deny = false;
  f.ports.deliveryFiles = { ...fs, writeFileSync: (...args) => {
    if (deny && String(args[0]).includes('delivery-journal.json')) throw Object.assign(Error('denied'), { code: 'EACCES' });
    return fs.writeFileSync(...args);
  } };
  f.ports.herdr = async args => { const result = await healthy(args); if (args[1] === 'prompt') { submits++; deny = true; } return result; };
  const first = await changeRun({ ref: '17', text: 'Possibly delivered', cwd: f.source }, f.ports);
  assert.notEqual(first.exitCode, 0, 'an unsaved acknowledgement must not claim durable delivery');
  deny = false;
  const second = await changeRun({ ref: '17', text: 'Possibly delivered', cwd: f.source }, f.ports);
  assert.notEqual(second.exitCode, 0); assert.equal(submits, 1, 'persisted submission intent must prevent duplicate transport');
  assert.match(second.message, /uncertain|check/i);
});
