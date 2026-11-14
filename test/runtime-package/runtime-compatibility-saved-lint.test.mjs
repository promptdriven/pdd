import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { client } from './runtime-compatibility/replay.mjs';
import { TOKEN } from './runtime-fake.mjs';

// Combined approved contracts: standalone reads retain their lint result and
// selected compatibility, with the same safe view in stdout and saved summary.
// Fake transport and temporary native Git/state only; no live Runtime proof.
for (const pending of [false, true]) for (const [variant, state, exit] of [
  ['supported', 'passed', 0], ['unsupported', 'refused', 4], ['unknown', 'not_run', 5],
]) test(`COMPAT saved standalone lint ${pending ? 'pending-first' : 'finished'}/${variant}`, async t => {
  const c = await client(t, { pending, variant, lintEdit(answer) {
    answer.result.capabilities_complete = { token: TOKEN, path: '/srv/private/source', body: 'PRIVATE_FIXTURE_BODY' };
  } });
  const initial = await c.run('lint', { '--timeout': 0.01 });
  assert.equal(initial.code, pending ? 3 : exit);
  c.state.pending = false;
  const posts = c.f.posts.length;
  let compatibility, advice;
  for (const json of [true, false, true]) {
    // Latest-batch lookup must keep the same standalone intent as an explicit ID.
    const r = await c.run('check', { '--read': json ? initial.json.batch : true, '--json': json }, []);
    assert.equal(r.code, exit, r.err);
    const summary = JSON.parse(readFileSync(join(c.h.state, 'batches', initial.json.batch, 'summary.json')));
    assert.equal(summary.lint_state, state === 'not_run' ? 'not run' : state);
    assert.equal(summary.rows[0].state, state === 'not_run' ? 'not run' : state);
    assert.equal(summary.capabilities_complete, null);
    assert.equal(summary.rows[0].compatibility.association, 'matched');
    assert.equal(summary.rows[0].compatibility.state, variant === 'unsupported' ? 'unsupported-capability' : variant);
    assert.equal(summary.summary_line, `Lint: ${state === 'passed' ? 1 : 0} of 1 tests pass. 0 AI calls. No checks were sent.`);
    compatibility ??= summary.rows[0].compatibility;
    advice ??= summary.rows[0].client_advice;
    assert.deepEqual(summary.rows[0].compatibility, compatibility);
    assert.deepEqual(summary.rows[0].client_advice, advice);
    if (json) assert.deepEqual(r.json, summary, 'stdout and saved summary expose the same lint result');
    else {
      const nonSupported = variant === 'unsupported' ? '; non-supported: retained-mutation-unsupported'
        : variant === 'unknown' ? '; non-supported: requirement-uninspectable' : '';
      assert.ok(r.out.includes(`Compatibility (place-order / tests/place-order.json): ${compatibility.state} (association matched); 1 step (1 operation, 0 edges); execution ordinary; resources simulated; complete true; engine eae2202a68d0${nonSupported}.`));
      assert.ok(r.out.includes(`  Client advice (${advice.owner}): ${advice.next_step}`));
      assert.ok(!r.out.includes('Compatibility (place-order / tests/place-order.json): {'));
      assert.ok(r.out.split('\n').includes(summary.summary_line));
    }
    for (const secret of [TOKEN, '/srv/private/source', 'PRIVATE_FIXTURE_BODY']) assert.ok(!(r.out + r.err).includes(secret));
    assert.doesNotMatch(r.out + r.err, /Run a fresh pdd test command to start checks\./);
    assert.equal(c.f.posts.length, posts, 'saved lint reads create no new dispatch');
    assert.deepEqual(c.saved(initial).batch.rows[0].request_ids, []);
  }
  c.unchanged(); c.archive();
});
