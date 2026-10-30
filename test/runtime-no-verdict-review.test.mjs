import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, rmSync } from 'node:fs';
import { runCheck } from '../src/runtime-client.mjs';
import { renderText, summaryLine, exitCodeFor } from '../src/runtime-output.mjs';
import { harbor, fakeRuntime, portsFor, PLACE, TOKEN } from './runtime-fake.mjs';
const row = (state, extra = {}) => ({ state, story: 'one', title: 'One', test: 'one.json', refusals: [], ...extra });
async function run(setup, fake, options = { '--json': true }, words = ['place-order']) {
  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  const code = await runCheck({ words: options['--read'] ? [] : words, options, cwd: setup.repo }, ports);
  return { code, text: ports.stdout.text, json: options['--json'] ? JSON.parse(ports.stdout.text) : null };
}
const capacity = (f, id) => f.job(id, 'check', 'refused', { outcome: 'Inconclusive', why: 'No verdict. Queue full.', next_step: 'STALE RETRY',
  refusals: [{ code: 'check-queue-timeout', details: { retryable: true, retry_after: 1 } }],
  report: { dispatch: 'not_started', provider_calls: 0, samples: [] } }, 0);

test('REVIEW marks keep passed plus actual busy busy and preserve precedence controls', () => {
  assert.match(summaryLine([row('passed'), row('not_run', { busy: true })]), /: busy ·/);
  for (const state of ['refused', 'unknown']) assert.match(summaryLine([row(state, { busy: true })]), /: no verdict ·/);
  assert.match(summaryLine([row('running'), row('refused')]), /: running ·/);
  assert.match(summaryLine([row('failed'), row('running'), row('not_run', { busy: true })]), /: ✗/);
});
test('REVIEW final rows with exit-three flags never claim checks have no verdict', () => {
  for (const rows of [[row('failed')], [row('failed'), row('failed', { story: 'two' })], [row('failed'), row('passed')]]) {
    for (const flag of [{ interrupted: true }, { lintUnknown: true }]) {
      const code = exitCodeFor(rows, flag); assert.equal(code, 3);
      assert.doesNotMatch(renderText({ rows, exitCode: code }), /so the exit code|checks with no verdict/);
    }
  }
  assert.match(renderText({ rows: [row('failed'), row('unknown')], exitCode: 3 }), /That Story also has checks with no verdict/);
});
test('REVIEW NOT RUN advice keeps sent busy explanation and has no dangling colon', () => {
  const base = row('not_run', { busy: true, request_ids: ['a', 'b', 'c'], note: { code: 'check-busy', message: 'The runtime is busy. No checks ran for this attempt. Retry this batch later.' }, next_step: 'Tell the person.' });
  const text = renderText({ rows: [base], exitCode: 5 });
  assert.match(text, /The runtime is busy\. No checks ran for this attempt\./);
  assert.doesNotMatch(text, /pdd did not send|Retry this batch/);
  const both = renderText({ rows: [{ ...base, why: 'No verdict. Queue full.' }], exitCode: 5 });
  assert.doesNotMatch(both, /:\s*(?:\(check-busy\))?\n/);
  assert.match(both, /Why: No verdict/);
  const lint = renderText({ rows: [row('not_run', { note: { message: 'The saved lint finished. No checks were sent. Run a fresh pdd check command to start checks.' }, next_step: 'Tell the person.' })], exitCode: 5 });
  assert.match(lint, /The saved lint finished\. No checks were sent\./); assert.doesNotMatch(lint, /Run a fresh pdd check/);
});
test('REVIEW server why accepts only no-verdict advice and drops legacy generic even with inconsistent outcome', async t => {
  for (const [why, outcome, expected] of [['Checks failed.', 'Fail', null], ['Checks failed.', 'Inconclusive', null], ['Old failure', 'Fail', null], ['nO VeRdIcT: service unavailable', 'Fail', 'nO VeRdIcT: service unavailable'], ['No verdictish failure', 'Fail', null], ['Service unavailable', 'Inconclusive', 'Service unavailable']]) {
    const setup = harbor(t);
    const fake = await fakeRuntime(t, (e, f) => {
      if (e.command !== 'check') return f.normal(e);
      const answer = f.check(e.request.requestId, 'refused', [], [{ code: 'service', reason: 'Unavailable' }]);
      Object.assign(answer.result, { why, outcome, next_step: 'Tell the person.' });
      return { status: 200, json: answer };
    });
    const result = await run(setup, fake);
    assert.equal(result.json.rows[0].why, expected, `${outcome}: ${why}`);
    assert.equal(result.json.rows[0].next_step, 'Tell the person.');
  }
  for (const legacyWhy of ['Checks failed.', 'The answer to the request was lost.']) {
    const setup = harbor(t);
    const fake = await fakeRuntime(t, (e, f) => {
      if (e.command === 'lint') return f.normal(e);
      const answer = f.check(e.request?.requestId ?? e.url.split('/').at(-1), 'unknown', [], []);
      Object.assign(answer.result, { why: 'Checks failed.', outcome: 'Fail' });
      return { status: 200, json: answer };
    });
    const first = await run(setup, fake), folder = `${setup.state}/batches/${first.json.batch}`;
    const path = `${folder}/batch.json`, saved = JSON.parse(readFileSync(path));
    saved.rows[0].why = legacyWhy; saved.rows[0].lost = true;
    writeFileSync(path, JSON.stringify(saved)); rmSync(`${folder}/${saved.rows[0].request_ids.at(-1)}.json`);
    const read = await run(setup, fake, { '--json': true, '--read': first.json.batch });
    assert.equal(read.json.rows[0].why, legacyWhy === 'Checks failed.' ? null : legacyWhy);
  }
});
test('REVIEW busy retry to lost response or fresh refusal never inherits retry advice', async t => {
  for (const mode of ['busy', 'lost', 'refused']) {
    const setup = harbor(t); let posts = 0;
    const fake = await fakeRuntime(t, (e, f) => {
      if (e.command === 'check') {
        if (++posts === 1 || mode === 'busy') return { status: 200, json: capacity(f, e.request.requestId) };
        return mode === 'lost' ? { destroy: true } : { status: 422, json: { error: { code: 'source-too-large', message: 'Source too large.', reason: `Source too large. ${TOKEN} /srv/private/reason`, fix: `NEW FIX ${TOKEN} /srv/private/fix`, hint: `NEW HINT ${TOKEN} /srv/private/hint`, cause: 'test' } } };
      }
      if (e.method === 'GET') return { status: 410, json: { error: { code: 'expired' } } };
      return f.normal(e);
    });
    const result = await run(setup, fake);
    assert.equal(posts, mode === 'busy' ? 3 : 2); assert.equal(result.json.rows[0].next_step, null);
    const text = await run(setup, fake, { '--read': result.json.batch });
    assert.doesNotMatch(text.text, /STALE RETRY/);
    if (mode === 'busy') { assert.equal(result.code, 5); assert.match(text.text, /The runtime is busy\. No checks ran for this attempt\./); }
    else if (mode === 'lost') { assert.equal(result.code, 3); assert.match(text.text, /The result expired\./); assert.doesNotMatch(text.text, /Why: The result expired/); }
    else { assert.equal(result.code, 4); assert.match(text.text, /Fix: NEW FIX/); assert.match(text.text, /NEW HINT/);
      assert.deepEqual(Object.fromEntries(['reason', 'fix', 'hint', 'cause'].map(key => [key, result.json.rows[0].refusals[0][key]])), { reason: 'Source too large. [secret] <server path>', fix: 'NEW FIX [secret] <server path>', hint: 'NEW HINT [secret] <server path>', cause: 'test' });
      assert.doesNotMatch(text.text, /gho_TESTTOKEN|\/srv\/private/); }
  }
});
test('REVIEW changed saved refusal cannot reuse stale why; client lost reason remains visible', async t => {
  const setup = harbor(t); let valid = true;
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'lint') return f.normal(e);
    const answer = f.check(e.request?.requestId ?? e.url.split('/').at(-1), 'refused', [], [{ code: 'service', reason: 'Unavailable' }]);
    if (answer.result) Object.assign(answer.result, { why: valid ? 'No verdict. Waiting for service.' : 'Checks failed.', outcome: valid ? 'Inconclusive' : 'Fail' });
    return { status: 200, json: answer };
  });
  const first = await run(setup, fake);
  assert.equal(first.json.rows[0].why, 'No verdict. Waiting for service.');
  const path = `${setup.state}/batches/${first.json.batch}/batch.json`, saved = JSON.parse(readFileSync(path));
  saved.rows[0].why = 'No verdict. STALE WHY'; saved.rows[0].state = 'unknown'; writeFileSync(path, JSON.stringify(saved));
  rmSync(`${setup.state}/batches/${first.json.batch}/${saved.rows[0].request_ids.at(-1)}.json`); valid = false;
  const result = await run(setup, fake, { '--json': true, '--read': first.json.batch });
  assert.equal(result.json.rows[0].why, null);
});
test('REVIEW partial lint refusal keeps independent server advice after per-test judgment', async t => {
  for (const why of ['Checks failed.', 'No verdict. Fix the named prompt rule.']) {
    const other = 'prompts/other.prompt.md';
    const setup = harbor(t, repo => {
      writeFileSync(`${repo}/${other}`, readFileSync(`${repo}/${PLACE}`));
      const path = `${repo}/tests/unknown-item.json`, scenario = JSON.parse(readFileSync(path));
      scenario.steps[0].entry_path = other; writeFileSync(path, JSON.stringify(scenario));
    });
    const fake = await fakeRuntime(t, (e, f) => {
      if (e.command !== 'lint') return f.normal(e);
      const answer = f.lint(e.request.requestId, [{ path: PLACE, state: 'refused', admission_state: 'refused', interface: { calls: [] } },
        { path: other, state: 'approved', admission_state: 'approved', interface: { calls: [] } }], [{ path: PLACE, code: 'bad-prompt', message: 'Bad prompt.' }]);
      Object.assign(answer.result, { outcome: 'Fail', why, next_step: 'SERVER LINT NEXT' });
      return { status: 200, json: answer };
    });
    const result = await run(setup, fake, { '--json': true }, []);
    assert.equal(result.code, 4);
    const refused = result.json.rows.find(r => r.state === 'refused');
    assert.equal(refused.why, why === 'Checks failed.' ? null : why); assert.equal(refused.next_step, 'SERVER LINT NEXT');
    assert.equal(result.json.rows.filter(r => r.state === 'passed').length, 1);
    assert.equal(fake.posts.filter(e => e.command === 'check').length, 1);
    const read = await run(setup, fake, { '--read': result.json.batch }); assert.match(read.text, /Next: SERVER LINT NEXT/);
  }
});
test('REVIEW local and lost advice suppress only conflicting hint and keep lost Next', () => {
  const local = row('refused', { refusals: [{ code: 'local', message: 'Invalid.', hint: 'CONFLICTING LOCAL HINT' }], next_step: 'SERVER NEXT' });
  const text = renderText({ rows: [local], exitCode: 4 }); assert.match(text, /Next: SERVER NEXT/); assert.doesNotMatch(text, /CONFLICTING LOCAL HINT/);
  const lost = row('unknown', { lost: true, why: 'Reply lost.', next_step: 'Read only.' });
  assert.match(renderText({ rows: [lost], exitCode: 3 }), /Reply lost\.\n  Next: Read only\./);
});
