import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { runCheck } from '../src/runtime-client.mjs';
import { renderJson, renderText, summaryLine, exitCodeFor } from '../src/runtime-output.mjs';
import { harbor, fakeRuntime, portsFor, TOKEN } from './runtime-fake.mjs';
const row = (state, story = 'one', extra = {}) => ({ state, story, title: story, test: `${story}.json`, refusals: [], ...extra });

test('NO-VERDICT replay: unchanged Story scenario, every step and criterion', () => {
  const scenario = JSON.parse(readFileSync(new URL('./runtime/check-no-verdict.json', import.meta.url)));
  const seen = new Set();
  assert.equal(scenario.steps.length, 18);
  for (const step of scenario.steps) {
    assert.equal(step.operation, 'renderJson');
    const result = renderJson(step.input);
    for (const check of step.checks) {
      seen.add(check.criterion_id);
      const actual = check.path.split('/').slice(1).reduce((value, key) => value[key], result);
      assert.deepEqual(actual, check.value, `${step.step_id} ${check.path}`);
    }
  }
  assert.deepEqual([...seen].sort(), scenario.criteria.map(c => c.id).sort());
});

test('NO-VERDICT notices count Stories and preserve failure/open/busy precedence and exits', () => {
  for (const state of ['refused', 'not_run', 'unknown', 'queued', 'running']) {
    const rows = [row('failed'), row(state, 'two'), row(state, 'two')];
    const code = exitCodeFor(rows);
    assert.match(renderText({ rows, exitCode: code }), new RegExp(`1 Story failed its checks\\. Another Story has no verdict, so the exit code is ${code}\\.`));
    assert.match(summaryLine(rows), /: ✗ /);
    assert.match(renderText({ rows: [row('failed'), row(state)], exitCode: code }), /That Story also has checks with no verdict/);
  }
  assert.match(summaryLine([row('passed'), row('not_run', 'two', { busy: true })]), /: no verdict · /);
  assert.match(summaryLine([row('not_run', 'one', { busy: true })]), /: busy · /);
  assert.match(summaryLine([row('queued'), row('refused')]), /: running · /);
  assert.equal(exitCodeFor([row('unknown'), row('not_run'), row('refused'), row('failed')]), 3);
  assert.equal(exitCodeFor([row('not_run'), row('refused'), row('failed')]), 5);
  assert.equal(exitCodeFor([row('refused'), row('failed')]), 4);
  assert.equal(exitCodeFor([row('failed')]), 1);
  assert.equal(exitCodeFor([row('passed')]), 0);
  const plural = [row('failed', 'one'), row('failed', 'two'), row('unknown', 'one'), row('unknown', 'one')];
  assert.match(renderText({ rows: plural, exitCode: 3 }), /2 Stories failed their checks\. 1 of those Stories also has checks with no verdict/);
  assert.match(renderText({ rows: [...plural, row('refused', 'three'), row('refused', 'four'), row('refused', 'four')], exitCode: 3 }), /2 other Stories have no verdict/);
  assert.doesNotMatch(renderText({ rows: [row('refused')], exitCode: 4 }), /so the exit code/);
  for (const state of ['refused', 'unknown']) assert.match(summaryLine([row(state, 'one', { busy: true })]), /: no verdict · /);
  for (const state of ['passed', 'failed']) {
    const output = renderJson({ rows: [row(state, 'one', { note: { message: 'stale' }, provider: { code: 'stale' }, time_limit: { code: 'stale' } })] });
    assert.equal(output.rows[0].reason, null);
  }

});

test('NO-VERDICT server advice independently overrides fallbacks, including provider and time limit', () => {
  const refusal = { code: 'service', reason: 'Declined', cause: 'ai-service', fix: 'CLIENT FIX', hint: 'CLIENT HINT' };
  for (const state of ['refused', 'not_run', 'unknown']) {
    for (const fields of [{ why: 'SERVER WHY' }, { next_step: 'SERVER NEXT' }, { why: 'SERVER WHY', next_step: 'SERVER NEXT' }]) {
      const r = row(state, 'one', { phase: 'server', note: { message: 'Run it again' }, refusals: [refusal], ...fields });
      const text = renderText({ rows: [r], exitCode: exitCodeFor([r]) });
      if (fields.why) assert.match(text, /Why: SERVER WHY/);
      if (state === 'not_run' && !fields.next_step) assert.match(text, /Run it again/);
      if (fields.next_step) {
        assert.match(text, /Next: SERVER NEXT/);
        assert.doesNotMatch(text, /Run it again|CLIENT FIX|CLIENT HINT/);
      } else if (state === 'refused') assert.match(text, /Your test is fine\. Run it again\./);
    }
  }
  const local = ['one', 'two'].map(story => row('refused', story, { refusals: [{ code: 'lint', message: 'Bad file' }], why: `Reason ${story} ${TOKEN}`, next_step: `Next ${story}` }));
  const localText = renderText({ rows: local, exitCode: 4, secrets: [TOKEN] });
  assert.match(localText, /one\.json[\s\S]*Why: Reason one \[secret\][\s\S]*Next: Next one\n  two\.json/);
  assert.doesNotMatch(localText, new RegExp(TOKEN));
  for (const extra of [{ provider: { code: 'graph-provider-failure' } }, { time_limit: { message: 'Stopped', fix: 'CLIENT FIX' } }]) {
    const r = row('unknown', 'one', { ...extra, why: 'SERVER WHY', next_step: 'SERVER NEXT' });
    const text = renderText({ rows: [r], exitCode: 3 });
    assert.match(text, /Why: SERVER WHY/); assert.match(text, /Next: SERVER NEXT/);
    assert.doesNotMatch(text, /CLIENT FIX|To try again/);
  }
});

test('NO-VERDICT real check projection retains sanitized advice and refusal cause', async t => {
  for (const state of ['refused', 'unknown']) {
    const setup = harbor(t);
    const fake = await fakeRuntime(t, (entry, f) => {
      if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
      const answer = f.check(entry.request?.requestId ?? entry.url.split('/').at(-1), state, [], [{ code: 'service', cause: 'ai-service', reason: 'Declined', fix: 'BAD FIX' }]);
      Object.assign(answer.result, { why: `No verdict. ${TOKEN} /srv/private/file`, next_step: 'Tell the person. Never resend.' });
      return { status: 200, json: answer };
    });
    const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
    await runCheck({ words: [], options: { '--json': true }, cwd: setup.repo }, ports);
    const output = JSON.parse(ports.stdout.text);
    for (const r of output.rows) {
      assert.equal(r.why, 'No verdict. [secret] <server path>');
      assert.equal(r.next_step, 'Tell the person. Never resend.');
      assert.equal(r.refusals[0].cause, 'ai-service');
      assert.equal(r.who, null);
    }
    assert.doesNotMatch(ports.stdout.text, new RegExp(TOKEN));
  }
});

test('NO-VERDICT lint advice survives initial refusal and unknown mapping and saved reads', async t => {
  for (const state of ['refused', 'unknown']) {
    const setup = harbor(t);
    let pending = true;
    const fake = await fakeRuntime(t, (entry, f) => {
      const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
      const answer = f.job(id, 'lint', pending ? 'running' : state, pending ? null : {
        why: `No verdict. ${TOKEN} /srv/private`, next_step: 'Tell the person. Never resend.',
        refusals: [{ code: 'service', cause: 'ai-service', reason: 'Declined' }]
      });
      return { status: 200, json: answer };
    });
    const makePorts = () => portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }).ports;
    const first = makePorts();
    await runCheck({ words: [], options: { '--json': true, '--timeout': '1' }, cwd: setup.repo }, first);
    const batch = JSON.parse(first.stdout.text).batch;
    pending = false;
    const saved = makePorts();
    await runCheck({ words: [], options: { '--json': true, '--read': batch }, cwd: setup.repo }, saved);
    const savedAgain = makePorts();
    await runCheck({ words: [], options: { '--json': true, '--read': batch }, cwd: setup.repo }, savedAgain);
    const initial = makePorts();
    await runCheck({ words: [], options: { '--json': true }, cwd: setup.repo }, initial);
    const initialRead = makePorts();
    await runCheck({ words: [], options: { '--json': true, '--read': JSON.parse(initial.stdout.text).batch }, cwd: setup.repo }, initialRead);
    for (const output of [saved, savedAgain, initial, initialRead]) for (const r of JSON.parse(output.stdout.text).rows) {
      assert.equal(r.why, 'No verdict. [secret] <server path>');
      assert.equal(r.next_step, 'Tell the person. Never resend.');
      assert.equal(r.state, state === 'unknown' ? 'not_run' : 'refused');
    }
    // Older batches did not persist next_step; they still read with the existing fallback.
    const oldPath = `${setup.state}/batches/${JSON.parse(initial.stdout.text).batch}/batch.json`;
    const oldBatch = JSON.parse(readFileSync(oldPath, 'utf8'));
    for (const r of oldBatch.rows) delete r.next_step;
    writeFileSync(oldPath, JSON.stringify(oldBatch));
    const older = makePorts();
    await runCheck({ words: [], options: { '--json': true, '--read': oldBatch.batch }, cwd: setup.repo }, older);
    for (const r of JSON.parse(older.stdout.text).rows) {
      assert.equal(r.state, state === 'unknown' ? 'not_run' : 'refused');
      assert.equal(r.why, 'No verdict. [secret] <server path>');
      if (state === 'refused') assert.equal(r.next_step, null);
    }
    assert.equal(fake.posts.filter(p => p.command === 'check').length, 0);
  }
});
