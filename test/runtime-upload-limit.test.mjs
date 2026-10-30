import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

const gate = () => { let release; const promise = new Promise(done => { release = done; }); return { promise, release }; };
const watchdog = promise => Promise.race([promise, new Promise((_, reject) => {
  const timer = setTimeout(() => reject(new Error('boundary gate not reached')), 10000); timer.unref();
})]);

for (const [raw, limit, warnings] of [[undefined, 8, 0], ['2', 2, 0], ['0', 8, 1]]) {
  test(`2704 uploads: 20 checks, ${raw ?? 'default'}, POST reply frees a place before job completion`, { timeout: 20000 }, async t => {
    const setup = harbor(t, repo => {
      const bytes = readFileSync(join(repo, 'tests/place-order.json'));
      rmSync(join(repo, 'tests/unknown-item.json'));
      for (let i = 1; i < 20; i++) writeFileSync(join(repo, `tests/order-${i}.json`), bytes);
    });
    const firstWindow = gate(), nextPost = gate(), terminal = gate(), releaseAll = gate();
    const replies = [], requests = []; let open = 0, peak = 0, reads = 0, firstReads = 0;
    const fake = await fakeRuntime(t, (entry, f) => {
      if (entry.command === 'check') return { status: 202, json: f.check(entry.request.requestId, 'queued') };
      if (entry.method === 'GET') return { status: 200, json: f.check(entry.url.split('/').at(-1)) };
      return f.normal(entry);
    });
    const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };
    if (raw !== undefined) env.PDD_MAX_UPLOADS = raw;
    const { ports } = portsFor(env, { now: Date.now, sleep: ms => new Promise(done => setTimeout(done, Math.min(ms, 10))), pollMs: 10,
      fetch: async (url, init) => {
        if (init.method === 'POST' && new URL(url).pathname === '/v1/check') {
          const request = JSON.parse(await init.body.get('request').text());
          requests.push(request); open++; peak = Math.max(peak, open);
          const reply = gate(); replies.push(reply);
          if (requests.length === limit) firstWindow.release();
          if (requests.length === limit + 1) nextPost.release();
          await Promise.race([reply.promise, releaseAll.promise]);
          open--; return globalThis.fetch(url, init);
        }
        if (new URL(url).pathname.startsWith('/v1/runs/')) {
          reads++; if (requests.length <= limit) firstReads++;
          await terminal.promise;
        }
        return globalThis.fetch(url, init);
      }
    });
    const running = runCheck({ cwd: setup.repo, words: [], options: { '--json': true } }, ports);
    let heldCount, afterReply, result;
    try {
      await watchdog(firstWindow.promise);
      // Drain already runnable dispatch work; no elapsed-time assumption about completion.
      for (let i = 0; i < 50; i++) await new Promise(done => setImmediate(done));
      heldCount = requests.length;
      replies[0].release();
      await watchdog(nextPost.promise);
      afterReply = { count: requests.length, reads, firstReads };
    } finally {
      releaseAll.release(); terminal.release(); result = await running;
    }
    assert.equal(heldCount, limit, 'unanswered POSTs alone fill the upload window');
    assert.equal(afterReply.count, limit + 1, 'one answered POST permits the next upload while jobs have no terminal reply');
    assert.equal(result, 0, ports.stderr.text + ports.stdout.text);
    assert.equal(peak, limit); assert.equal(requests.length, 20);
    assert.equal(new Set(requests.map(row => row.scenario)).size, 20);
    assert.equal(new Set(requests.map(row => row.requestId)).size, 20);
    assert.equal(ports.stderr.text.split('\n').filter(line => /Warning:.*PDD_MAX_UPLOADS/.test(line)).length, warnings);
  });
}

for (const raw of ['', '-1', '+2', '1.5', ' 2', 'garbage', '9007199254740992', '02']) {
  test(`2704 uploads: setting ${JSON.stringify(raw)} has one consistent warning`, async t => {
    const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin, PDD_MAX_UPLOADS: raw });
    assert.equal(await runCheck({ cwd: setup.repo, words: [], options: { '--json': true } }, ports), 0);
    const warnings = ports.stderr.text.split('\n').filter(line => /Warning:.*PDD_MAX_UPLOADS/.test(line));
    assert.equal(warnings.length, raw === '02' ? 0 : 1);
    if (warnings.length) assert.match(warnings[0], /8/);
  });
}
