import test from 'node:test';
import assert from 'node:assert/strict';
import { runStatus } from '../src/workflow-runner.mjs';
import { fixture } from './helpers/workflow-runner-fixture.mjs';

test('bounded Gemini menu recognition and read-only status', async t => {
  const f = await fixture(t, { agent: 'gemini' });
  assert.equal((await f.run()).exitCode, 0);
  const pane = f.herdr.paneOf(f.record().chats.at(-1));
  pane.agent.agent_status = 'blocked';
  const reads = new Set(['agent get', 'pane read', 'pane list', 'workspace list']);
  for (const selected of [1, 2]) for (const footer of ['', '(Use Enter to select)\n']) {
    const menu = 'CRITICAL SECURITY WARNING: Untrusted Command Flags Detected\nAllow execution of [Shell]?\n'
      + `${selected === 1 ? '●' : ' '} 1. Allow once\n${selected === 2 ? '●' : ' '} 2. No, suggest changes (esc)\n` + footer;
    for (const [suffix, live] of [['', true], ['> \n', false], ['Another question?\n● 1. Yes\n  2. No\n', false]]) {
      pane.screen = menu + suffix;
      const before = f.herdr.calls.length;
      const detail = await runStatus({ ref: '17', cwd: f.source }, f.ports);
      const list = await runStatus({ all: true, cwd: f.source }, f.ports);
      const json = await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports);
      const words = [detail.message, list.message, JSON.parse(json.message).runs[0].words];
      for (const value of words) assert.match(value, live ? /Gemini shell-safety dialog.*pdd workflow open 17/ : /the chat asks a question/,
        `selected=${selected}, footer=${Boolean(footer)}, suffix=${JSON.stringify(suffix)}`);
      const calls = f.herdr.calls.slice(before).map(([group, verb]) => `${group} ${verb}`);
      assert.ok(calls.includes('pane read'));
      assert.deepEqual(calls.filter(call => !reads.has(call)), []);
    }
  }
  const original = f.ports.herdr;
  f.ports.herdr = async args => { if (args[0] === 'pane' && args[1] === 'read') throw Error('unavailable'); return original(args); };
  const status = await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports);
  assert.match(JSON.parse(status.message).runs[0].words, /the chat asks a question/);
});
