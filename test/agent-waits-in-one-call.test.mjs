import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-seam.mjs';
import { captureSource } from '../src/runtime-seam.mjs';
import { PUBLIC_COMMAND_MANIFEST } from '../src/command-catalog.mjs';
import { harbor, portsFor, PLACE, ordinaryCapabilities } from './runtime-fake.mjs';

// Offline public-boundary replay: every service reply and clock tick is injected.
// No HTTP listener, native network, model call or renderer substitute.
function fixture(t, { multiple = false, failed = false, completeAt = 150000 } = {}) {
  const h = harbor(t, repo => {
    if (!multiple) return;
    const original = join(repo, 'user_stories/place-order.md');
    writeFileSync(join(repo, 'user_stories/second-order.md'), readFileSync(original, 'utf8').replace('# Place a coffee order', '# Place another coffee order'));
    const doc = JSON.parse(readFileSync(join(repo, 'tests/place-order.json')));
    doc.story_path = 'user_stories/second-order.md';
    writeFileSync(join(repo, 'tests/second-order.json'), JSON.stringify(doc));
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: 'https://offline.invalid' };
  const posts = [], gets = [], ids = new Map();
  let current, start, capture, interruptAt = Infinity;
  const job = (id, command, state, result = null) => ({ id, requestId: id, command, state, result,
    usage: { calls: command === 'check' ? 1 : 0 }, engine_sha: 'eae2202a68d00ab762fcbbf1eba0d8607a132a15',
    report_url: `https://offline.invalid/r/${id}` });
  const fetch = async (url, init) => {
    const path = new URL(url).pathname;
    if (path === '/v1/capacity') return Response.json({}, { status: 404 });
    if (init.method === 'POST') {
      const request = JSON.parse(await init.body.get('request').text()), command = path.split('/').at(-1);
      posts.push({ command, request });
      assert.equal(request.source_sha256, capture.sha256);
      assert.deepEqual(Buffer.from(await init.body.get('source').arrayBuffer()), capture.tar);
      // Explicit synthetic ordinary support, bound to the actual immutable upload.
      // This is supplied fixture input; the timing assertions establish no parser support.
      if (command === 'lint') return Response.json(job(request.requestId, command, 'passed', {
        exitCode: 0, refusals: [], report: { verdict: 'passed',
          lint: { complete: true, tests: ['tests/place-order.json', ...(multiple ? ['tests/second-order.json'] : [])]
            .map(path => ({ path, verdict: 'passed', capabilities: ordinaryCapabilities(capture.sources, path) })) },
          program: { prompts: [{ path: PLACE, admission_state: 'draft', interface: { calls: [] } }], refused_prompts: [] } }
      }));
      const recovery = /pdd test --read (\S+)/.exec(current.ports.stderr.text);
      assert.ok(recovery, 'recovery command is visible before first check POST');
      assert.ok(existsSync(join(h.state, 'batches', recovery[1], 'batch.json')), 'batch exists before dispatch');
      ids.set(request.requestId, request.scenario);
      return Response.json(job(request.requestId, command, 'queued'), { status: 202 });
    }
    const id = path.split('/').at(-1); gets.push(id);
    const done = current.clock.now - start >= (multiple && ids.get(id) === 'tests/place-order.json' ? 70000 : completeAt);
    const checks = [{ criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'equals', expected: 900,
      actual: failed ? 901 : 900, passed: !failed }];
    return Response.json(job(id, 'check', done ? failed ? 'failed' : 'passed' : 'running', done ? {
      outcome: failed ? 'Fail' : 'Pass', report: { samples: [{ steps: [{ checks }] }] }
    } : null));
  };
  async function run(options = {}, { interactive = false, batch, interrupt = Infinity } = {}) {
    current = portsFor(env, { fetch, interactive,
      captureSource: (...args) => (capture = captureSource(...args)) }); start = current.clock.now; interruptAt = interrupt;
    const sleep = current.ports.sleep;
    current.ports.sleep = async ms => {
      await sleep(ms);
      // Safety interrupt means a broken loop fails an assertion instead of hanging.
      if (current.clock.now - start >= Math.min(interruptAt, 600000)) current.clock.interrupt();
    };
    const code = await runCheck({ cwd: h.repo, words: batch ? [batch] : multiple ? ['place-order', 'second-order'] : ['place-order'], options }, current.ports);
    const out = current.ports.stdout.text, err = current.ports.stderr.text;
    const name = batch ?? /pdd test --read (\S+)/.exec(err)?.[1];
    return { ...current, code, out, err, batch: name, elapsed: current.clock.now - start,
      saved: JSON.parse(readFileSync(join(h.state, 'batches', name, 'batch.json'))) };
  }
  return { h, run, posts, gets, ids };
}
const progress = r => r.err.split('\n').filter(line => line.startsWith('Still running:'));
for (const interactive of [false, true]) test(`ONE-CALL start waits through 90s (${interactive ? 'person' : 'agent'})`, async t => {
  const f = fixture(t, { multiple: true }); const r = await f.run({}, { interactive });
  assert.equal(r.code, 0, 'no default caller deadline'); assert.ok(r.elapsed >= 150000 && r.elapsed <= 152000, 'terminal result observed within one 2s receipt interval');
  assert.equal(r.saved.timeout_min, null); assert.ok(r.saved.rows.every(row => row.state === 'passed'));
  assert.equal(f.posts.filter(p => p.command === 'lint').length, 1); assert.equal(f.posts.filter(p => p.command === 'check').length, 2);
  assert.deepEqual(r.saved.rows.flatMap(row => row.request_ids).sort(), [...f.ids.keys()].sort());
  assert.deepEqual(progress(r), [
    'Still running: 0 of 2 Stories done · 2 AI calls so far · 30 s',
    'Still running: 0 of 2 Stories done · 2 AI calls so far · 1 min',
    'Still running: 1 of 2 Stories done · 2 AI calls so far · 1 min',
    'Still running: 1 of 2 Stories done · 2 AI calls so far · 2 min',
  ]);
  assert.doesNotMatch(r.out, /Still running:|STILL RUNNING|expected 900/);
  assert.equal(r.out.split('\n').filter(line => /^Prompt tests \((?!DRAFT\))/.test(line)).length, 2);
  assert.match(r.out, /Story\s+Test\s+Result\s+Checks\s+Time/); assert.match(r.out, /Reports \(/);
});
for (const interactive of [false, true]) test(`ONE-CALL saved read waits on original IDs (${interactive ? 'person' : 'agent'})`, async t => {
  const f = fixture(t); const seed = await f.run({ '--timeout': '1', '--json': true });
  const before = f.posts.length, ids = seed.saved.rows[0].request_ids, source = seed.saved.source_sha256;
  const r = await f.run({ '--read': true, '--json': true }, { batch: seed.batch, interactive });
  assert.equal(r.code, 0, 'read must wait, not return a pending snapshot'); assert.equal(r.elapsed, 150000);
  assert.equal(r.clock.uuids, 0); assert.equal(f.posts.length, before); assert.equal(r.saved.timeout_min, null);
  assert.deepEqual(r.saved.rows[0].request_ids, ids); assert.equal(r.saved.source_sha256, source);
  assert.equal(r.saved.login, seed.saved.login); assert.ok(f.gets.every(id => ids.includes(id)));
  assert.equal(progress(r).length, 4); assert.doesNotMatch(r.out, /Still running:/);
  const json = JSON.parse(r.out); assert.equal(json.exit_code, 0); assert.equal(json.rows[0].state, 'passed');
});
for (const read of [false, true]) test(`ONE-CALL explicit 60s timeout on ${read ? 'read' : 'start'}`, async t => {
  const f = fixture(t); const seed = read ? await f.run({ '--timeout': '1' }) : null;
  const before = f.posts.length;
  const r = await f.run({ '--timeout': '1', ...(read ? { '--read': true } : {}) }, { batch: seed?.batch });
  assert.equal(r.code, 3); assert.equal(r.elapsed, 60000); assert.equal(r.saved.timeout_min, 1);
  assert.match(r.err, /pdd test --read/); assert.equal(progress(r).length, 1);
  assert.equal(r.saved.rows[0].state, 'sent');
  if (read) { assert.equal(f.posts.length, before); assert.equal(r.clock.uuids, 0); assert.deepEqual(r.saved.rows[0].request_ids, seed.saved.rows[0].request_ids); }
});
test('ONE-CALL interruption resumes once without another check', async t => {
  const f = fixture(t); const interrupted = await f.run({}, { interrupt: 40000 });
  assert.equal(interrupted.code, 3); assert.equal(interrupted.elapsed, 40000); assert.match(interrupted.err, /pdd test --read/);
  const before = f.posts.length;
  const resumed = await f.run({ '--read': true }, { batch: interrupted.batch });
  assert.equal(resumed.code, 0); assert.equal(resumed.elapsed, 150000); assert.equal(f.posts.length, before);
  assert.equal(resumed.clock.uuids, 0); assert.deepEqual(resumed.saved.rows[0].request_ids, interrupted.saved.rows[0].request_ids);
});
test('ONE-CALL delayed failure retains compact diagnostics and JSON', async t => {
  const f = fixture(t, { failed: true }); const r = await f.run();
  assert.equal(r.code, 1); assert.equal(r.elapsed, 150000);
  assert.equal(r.out.split('\n').filter(line => /^FAILED /.test(line)).length, 1);
  assert.equal(r.out.split('\n').filter(line => /expected 900, got 901/.test(line)).length, 1);
  assert.equal(r.out.split('\n').filter(line => /^Prompt tests \((?!DRAFT\))/.test(line)).length, 1);
  assert.doesNotMatch(r.out, /Still running:/); assert.match(r.out, /Reports \(/);
  const json = await f.run({ '--read': true, '--json': true }, { batch: r.batch });
  assert.equal(JSON.parse(json.out).exit_code, 1); assert.equal(json.clock.uuids, 0);
});

// Bounded timing/outcome domain from the Story: both shells, before/at/after
// the former cutoff. Deadline oracle is terminal completion, never shell type.
for (const interactive of [false, true]) for (const completeAt of [88000, 90000, 92000, 150000]) for (const failed of [false, true]) {
  test(`ONE-CALL bounded ${interactive ? 'person' : 'agent'} ${completeAt}ms ${failed ? 'failed' : 'passed'}`, async t => {
    const f = fixture(t, { completeAt, failed }); const r = await f.run({ '--json': true }, { interactive });
    assert.equal(r.code, failed ? 1 : 0);
    assert.equal(r.elapsed, completeAt);
    assert.equal(JSON.parse(r.out).rows[0].state, failed ? 'failed' : 'passed');
    assert.equal(f.posts.filter(p => p.command === 'check').length, 1);
  });
}

// The catalog owns the text rendered by public Check help.
test('ONE-CALL public help describes the unlimited caller wait in every shell', () => {
  const help = PUBLIC_COMMAND_MANIFEST.find(row => row.form.startsWith('pdd test [PATH|STORY...]')).description;
  assert.match(help, /no default limit in any shell; --timeout MIN sets the limit/);
  assert.match(help, /progress line every 30 s/);
  assert.doesNotMatch(help, /at most 90 s for an agent/);
});
