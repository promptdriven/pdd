import test from 'node:test';
import assert from 'node:assert/strict';
import { sendToChat } from '../src/workflow-chat.mjs';

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
// Idle Codex chats whose last agent text quotes or explains a dialog hint: the input line below shows no dialog is open.
const quotedIdle = text => [text, '', '› Ask Codex to do anything', '', '  gpt-6.1-sol high · 92% context left · weekly limit: 6% left', ''].join('\n');
const CODEX_QUOTED = quotedIdle('• To stop the sync, press "esc to cancel" in its dialog.');
const CODEX_QUOTED_FOOTER = quotedIdle('  Enter to confirm · Esc to cancel');
const GEMINI_WORKING = '✦ I update the example.\n\n⠋ Updating the example (esc to cancel, 5s)\n\n> Type your message\n';

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

