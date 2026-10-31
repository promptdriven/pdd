import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor, PLACE } from './runtime-fake.mjs';

// Bounded native check of the approved runtime-lint-continuation Story's Rules
// to check and AC3–6. Oracle is the conjunction of supplied Story facts below,
// not a private helper or an observed implementation result. Exhaust all 216
// Cartesian inputs. Each starts one selected held row, performs two recoveries
// in the chosen schedule, then one final read. Concurrent means the two actual
// invocations overlap via Promise.all; this does not enumerate OS interleavings,
// crashes, power loss, arbitrary histories, multiple rows or all valid caps.
// The original empty Runtime vector anchor remains NOT REPLAYED (#2548).
const domain = {
  mode: ['read', 'retry'], intent: ['check', 'legacy-check', 'lint'],
  source: ['same', 'changed'], lint: ['passed', 'running', 'refused'],
  cap: [1, 6, 1000], schedule: ['sequential', 'concurrent'],
};
let count = 0;
for (const mode of domain.mode) for (const intent of domain.intent)
for (const source of domain.source) for (const lint of domain.lint)
for (const cap of domain.cap) for (const schedule of domain.schedule) {
  count++;
  test(`FORMAL bounded ${mode}/${intent}/${source}/${lint}/cap${cap}/${schedule}`, async t => {
    const authorized = intent !== 'lint' && source === 'same' && lint === 'passed';
    const h = harbor(t);
    let currentLint = 'running';
    const f = await fakeRuntime(t, (e, f) => {
      if (e.method === 'POST') return { status: 200, json: e.command === 'lint'
        ? f.job(e.request.requestId, 'lint', 'running') : f.check(e.request.requestId) };
      const id = e.url.split('/').at(-1);
      const post = f.posts.find(p => p.request.requestId === id);
      if (post?.command === 'check') return { status: 200, json: f.check(id) };
      if (currentLint === 'passed') return { status: 200, json: f.lint(id) };
      if (currentLint === 'refused') {
        const receipt = f.lint(id);
        receipt.result.refusals = [{ code: 'global-refusal', message: 'Lint refused' }];
        return { status: 200, json: receipt };
      }
      return { status: 200, json: f.job(id, 'lint', 'running') };
    });
    const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin };
    const initial = portsFor(env);
    assert.equal(await runCheck({ cwd: h.repo, words: ['place-order'], options: {
      '--json': true, ...(intent === 'lint' ? { '--lint': true } : { '--max-calls': cap }),
    } }, initial.ports), 3, 'initial lint is held');
    const batch = readdirSync(join(h.state, 'batches'), { withFileTypes: true }).find(e => e.isDirectory()).name;
    const path = join(h.state, 'batches', batch, 'batch.json');
    const saved = () => JSON.parse(readFileSync(path, 'utf8'));
    if (intent === 'legacy-check') {
      const doc = saved(); delete doc.intent; delete doc.rows[0].calls;
      writeFileSync(path, JSON.stringify(doc));
    }
    const before = saved();
    if (source === 'changed') writeFileSync(join(h.repo, PLACE), readFileSync(join(h.repo, PLACE), 'utf8') + '\nChanged source.\n');
    currentLint = lint;
    // Changed current configuration must not redirect saved recovery.
    env.PDD_RUNTIME_URL = 'https://changed.example';
    async function recover(which = mode) {
      const p = portsFor(env);
      const code = await runCheck({ cwd: h.repo, words: which === 'read' ? [batch] : [],
        options: { [which === 'read' ? '--read' : '--retry']: which === 'read' ? true : batch, '--json': true } }, p.ports);
      return { ...p, code };
    }
    const firstTwo = schedule === 'concurrent' ? await Promise.all([recover(), recover()]) : [await recover(), await recover()];
    const last = await recover('read');
    const posts = f.posts.filter(e => e.command === 'check');
    assert.equal(posts.length, authorized ? 1 : 0, 'Story requires exactly one authorized continuation, zero unauthorized dispatches');
    assert.equal(f.posts.filter(e => e.command === 'lint').length, 1, 'no repeated lint/upload');
    const after = saved();
    assert.equal(after.batch, batch);
    assert.equal(after.root, before.root);
    assert.equal(after.source_sha256, before.source_sha256);
    assert.deepEqual(after.rows.map(row => [row.test, row.max_calls]), before.rows.map(row => [row.test, row.max_calls]));
    assert.equal(last.clock.uuids, 0, 'final read never allocates another identity');
    if (authorized) {
      assert.equal(last.code, 0, 'authorized continuation must finish, not merely avoid duplicates');
      assert.equal(posts[0].request.max_calls, cap, 'original ceiling survives');
      assert.equal(posts[0].request.scenario, 'tests/place-order.json', 'original selection survives');
      assert.ok(posts[0].tar.length > 0, 'check retains required source multipart');
      const id = posts[0].request.requestId;
      assert.deepEqual(after.rows[0].request_ids, [...before.rows[0].request_ids, id], 'exactly one original check identity');
      assert.deepEqual(firstTwo.map(result => result.code).sort(), schedule === 'concurrent' ? [0, 3] : [0, 0],
        'an overlapping command refuses the live owner; later commands read its result');
      for (const result of firstTwo) {
        if (result.code === 3) {
          assert.equal(result.ports.stdout.text, '', 'live-owner refusal has no JSON stdout');
          assert.match(result.ports.stderr.text, /pdd test --read/);
          assert.equal(result.clock.uuids, 0, 'live-owner refusal precedes identity allocation');
          assert.equal(result.clock.gh.length, 0, 'live-owner refusal precedes authentication');
        } else {
          const json = JSON.parse(result.ports.stdout.text);
          assert.equal(json.rows[0].request_id, id, 'the successful owner retains winner identity');
        }
      }
    } else {
      assert.deepEqual(after.rows.map(row => row.request_ids), before.rows.map(row => row.request_ids));
      for (const result of firstTwo) assert.equal(result.clock.uuids, 0, 'refusal precedes identity allocation');
    }
  });
}
assert.equal(count, 216, 'the entire stated Cartesian domain is enumerated');
