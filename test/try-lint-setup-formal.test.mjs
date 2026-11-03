import test from 'node:test';
import assert from 'node:assert/strict';
import { runTry } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

const defect = 'Defect: Try lint in an agent shell stops waiting after 90 seconds instead of sharing the five-minute setup allowance.';
const start = Date.parse('2026-10-27T16:27:47Z');
// Exhaust the stated finite domain; each case uses the real public boundary and a fresh Git/state world.
for (const interactive of [false, true]) for (const pass of [false, true])
for (const interrupted of [false, true]) for (const at of [90000, 122000, 299000, 300000]) {
  test(`bounded Try dispatch: terminal=${interactive} pass=${pass} interrupt=${interrupted} at=${at}`, async t => {
    const h = harbor(t);
    let clock;
    const fake = await fakeRuntime(t, (entry, f) => {
      if (entry.method === 'POST') return entry.command === 'lint'
        ? { status: 202, json: f.job(entry.request.requestId, 'lint', 'queued') }
        : { status: 200, json: f.tryJob(entry.request.requestId) };
      const id = entry.url.split('/').at(-1);
      return { status: 200, json: pass && clock.now - start >= at ? f.lint(id) : f.job(id, 'lint', 'running') };
    });
    const p = portsFor({ HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: fake.origin }, { interactive, pollMs: 1000 });
    clock = p.clock;
    p.ports.sleep = async ms => { clock.now += ms; if (interrupted && clock.now - start >= at) clock.interrupt(); await new Promise(resolve => setImmediate(resolve)); };
    await runTry({ cwd: h.repo, words: ['place-order'], options: { '--no-open': true, '--no-wait': true } }, p.ports);
    const expected = pass && !interrupted && at < 300000 ? 1 : 0;
    assert.equal(fake.posts.filter(post => post.command === 'try').length, expected, defect);
    if (expected) assert.equal(clock.now - start, at, defect);
  });
}
