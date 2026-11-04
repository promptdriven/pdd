// #2939: pdd never delivers text into an open agent dialog. Text and its Enter would answer the dialog, for example
// Codex's near-limit offer to switch to a cheaper model, and the run would change model without the person.
import test from 'node:test';
import assert from 'node:assert/strict';
import { sendToChat } from '../src/workflow-chat.mjs';
import { changeRun, runStatus } from '../src/workflow-runner.mjs';
import { fixture } from './helpers/workflow-delivery-fixture.mjs';

// A synthetic Codex screen built from the Codex CLI 0.166.0 texts of its rate-limit switch prompt.
const CODEX_OFFER = [
  '› Fix the retry example',
  '',
  '• Which retry count should the example use: 3 or 5?',
  '',
  '',
  '  Approaching rate limits',
  '  Switch to gpt-6-luna for lower credit usage?',
  '',
  '› 1. Switch to gpt-6-luna      Uses fewer credits for upcoming turns',
  '  2. Keep current model',
  '  3. Keep current model (never show again)  Hide future rate limit reminders about switching models',
  '',
  '  Press enter to confirm or esc to go back',
  ''].join('\n');
// An idle Codex chat that asks an ordinary question in chat text: the person answers it with pdd workflow changes.
const CODEX_IDLE = [
  '• Use 3 retries in the example? [y/n]',
  '',
  '› Ask Codex to do anything',
  '',
  '  gpt-6.1-sol high · 92% context left · weekly limit: 6% left',
  ''].join('\n');
const GEMINI_WORKING = '✦ I update the example.\n\n⠋ Updating the example (esc to cancel, 5s)\n\n> Type your message\n';

const prompts = f => f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'prompt');
async function idleChat(t, screen) {
  const f = await fixture(t, { agent: 'codex' });
  assert.equal((await f.run()).exitCode, 0);
  const pane = f.herdr.paneOf(f.record().chats.at(-1));
  pane.agent.agent_status = 'idle'; pane.screen = screen;
  return { f, pane, change: text => changeRun({ ref: '17', text, cwd: f.source }, f.ports),
    status: async json => (await runStatus({ ref: '17', cwd: f.source, ...(json ? { json: true } : {}) }, f.ports)).message };
}

test('2939 the Codex cheaper-model offer holds the request with its reason; status shows it; a later delivery sends it', async t => {
  const { f, pane, change, status } = await idleChat(t, CODEX_OFFER);
  const before = prompts(f).length;
  const held = await change('Use 3 retries');
  assert.notEqual(held.exitCode, 0, held.message);
  assert.equal(prompts(f).length, before, 'no text and no Enter reach the dialog');
  assert.match(held.message, /dialog: Approaching rate limits/);
  assert.match(held.message, /did not answer/);
  assert.match(held.message, /workflow changes 17 'Use 3 retries'/);
  const [entry] = f.journal();
  assert.equal(entry.state, 'pending'); assert.ok(!entry.inFlight, 'a held request records no submission intent');
  assert.match(entry.reason, /dialog: Approaching rate limits/);
  assert.match(await status(), /Use 3 retries.*Not sent.*dialog: Approaching rate limits/);
  assert.equal(JSON.parse(await status(true)).runs[0].pendingRequests[0].reason, entry.reason);
  pane.screen = CODEX_IDLE;
  const sent = await change('Use 3 retries');
  assert.equal(sent.exitCode, 0, sent.message);
  assert.equal(prompts(f).length, before + 1); assert.match(prompts(f).at(-1)[3], /Use 3 retries/);
  assert.equal(f.journal()[0].state, 'delivered'); assert.equal(f.journal()[0].reason, undefined);
  assert.doesNotMatch(await status(), /Not sent/);
});

test('2939 a normal idle pane is delivered as today, also when the chat text asks a [y/n] question', async t => {
  const { f, change } = await idleChat(t, CODEX_IDLE);
  const before = prompts(f).length;
  const sent = await change('Yes, use 3 retries');
  assert.equal(sent.exitCode, 0, sent.message);
  assert.equal(prompts(f).length, before + 1);
  assert.equal(f.journal()[0].state, 'delivered');
});

test('2939 a screen read that fails sends nothing, says so and keeps the request', async t => {
  const { f, change, status } = await idleChat(t, '');
  const healthy = f.ports.herdr;
  f.ports.herdr = async args => {
    if (args[0] === 'pane' && args[1] === 'read') throw Object.assign(Error('read failed'), { code: 'herdr_failed' });
    return healthy(args);
  };
  const before = prompts(f).length;
  const held = await change('Use 3 retries');
  assert.notEqual(held.exitCode, 0, held.message);
  assert.equal(prompts(f).length, before, 'an unread screen is never proof that no dialog shows');
  assert.match(held.message, /could not read the chat screen/);
  assert.equal(f.journal()[0].state, 'pending');
  assert.match(await status(), /Use 3 retries.*Not sent.*could not read the chat screen/);
});

test('2939 sendToChat reads the screen before custody and transport', async () => {
  const send = async (screen, status = 'idle') => {
    const calls = []; let custody = 0;
    const result = await sendToChat({ paneId: 'p1', startedAt: 0 }, 'text', { now: () => 60_000, beforeSubmit: async () => { custody++; return true; },
      herdr: async args => {
        calls.push(args);
        if (args[1] === 'get') return { result: { agent: { agent_status: status } } };
        if (args[1] === 'read') { if (screen instanceof Error) throw screen; return screen; }
        return {};
      } });
    return { result, custody, prompted: calls.filter(args => args[1] === 'prompt').length, read: calls.some(args => args[0] === 'pane' && args[1] === 'read') };
  };
  const offer = await send(CODEX_OFFER);
  assert.equal(offer.result.code, 'agent_dialog'); assert.match(offer.result.reason, /Approaching rate limits/);
  assert.equal(offer.prompted, 0); assert.equal(offer.custody, 0);
  for (const unread of [Object.assign(Error('gone'), { code: 'pane_not_found' }), { result: {} }]) {
    const failed = await send(unread);
    assert.equal(failed.result.code, 'pane_unreadable'); assert.equal(failed.prompted, 0); assert.equal(failed.custody, 0);
  }
  const working = await send(GEMINI_WORKING, 'working');
  assert.deepEqual(working.result, { ok: true }); assert.equal(working.prompted, 1); assert.ok(working.read);
  const claude = '────────────\n Bash command\n\n   rm -rf build\n\n Do you want to proceed?\n ❯ 1. Yes\n   2. No\n\n Esc to cancel · Tab to amend\n';
  const blocked = await send(claude, 'blocked');
  assert.equal(blocked.result.code, 'agent_blocked'); assert.match(blocked.result.reason, /dialog: Bash command/); assert.equal(blocked.prompted, 0);
});
