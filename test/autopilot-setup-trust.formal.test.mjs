import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { EventEmitter } from 'node:events';
import { runAutopilot } from '../src/autopilot.mjs';

// Story oracle: either lookup can stall; only an owner confirmed before the
// stall may be shown, and no unfinished lookup can confirm a writer.
test('bounded setup trust: each stalled GitHub lookup ends and keeps only confirmed people', async () => {
  await Promise.all(['owner', 'writers'].map(async stalled => {
    const signals = [], child = new EventEmitter();
    child.kill = signal => { signals.push(signal); return true; };
    const pending = new Promise(() => {});
    pending.child = child;
    let shown;
    const ports = {
      config: { read: async () => ({ raw: '{"mode":"auto","trust":[]}' }) },
      terminal: { names: async info => { shown = info; return { names: [] }; } },
      execFile: (file, args) => {
        assert.equal(file, 'gh');
        if (args[0] === 'repo' && stalled === 'writers') return Promise.resolve({ stdout: '{"nameWithOwner":"Org/repo","owner":{"login":"Ada"}}' });
        return pending;
      },
    };
    let timer;
    const result = await Promise.race([
      runAutopilot({ action: 'setup', interactive: true, inRepo: true }, ports),
      new Promise(resolve => { timer = setTimeout(() => resolve(null), 5800); }),
    ]);
    clearTimeout(timer);
    assert.ok(result, 'lookup must finish within the five-second budget and termination grace');
    assert.equal(result.exitCode, 0);
    assert.match(result.message, /incomplete/i);
    assert.deepEqual(shown, { owner: stalled === 'writers' ? 'Ada' : '', writers: [], complete: false });
    await new Promise(resolve => setTimeout(resolve, 300));
    assert.deepEqual(signals, ['SIGTERM', 'SIGKILL']);
  }));
});
