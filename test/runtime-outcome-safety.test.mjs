import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor, TOKEN } from './runtime-fake.mjs';

function client(h, f) {
  return async (words, options) => {
    const p = portsFor({ HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin });
    const code = await runCheck({ cwd: h.repo, words, options }, p.ports);
    return { code, out: p.ports.stdout.text, err: p.ports.stderr.text, json: options['--json'] && p.ports.stdout.text ? JSON.parse(p.ports.stdout.text) : null };
  };
}
test('OUTCOME safety: unknown is not counted done alongside a running Story', async t => {
  const h = harbor(t);
  const f = await fakeRuntime(t, (e, f) => {
    if (e.command === 'lint') return { status: 200, json: f.lint(e.request.requestId) };
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    const post = f.posts.find(p => p.request.requestId === id);
    return { status: 200, json: f.check(id, post?.request.scenario === 'tests/place-order.json' ? 'unknown' : 'running') };
  });
  const result = await client(h, f)(['place-order', 'unknown-item'], { '--json': true, '--timeout': 1.5 });
  assert.equal(result.code, 3);
  assert.match(result.err, /0 of 2 Stories done/);
  assert.doesNotMatch(result.err, /1 of 2 Stories done/);
});
for (const json of [false, true]) test(`OUTCOME safety: refused lint text is cleaned in ${json ? 'JSON' : 'text'}`, async t => {
  const h = harbor(t);
  const f = await fakeRuntime(t, (e, f) => {
    const answer = f.lint(e.request.requestId);
    answer.state = 'refused'; answer.result.report.lint = { complete: false, tests: [] };
    answer.result.report.refusal = { code: 'admission-stopped', message: `Secret ${TOKEN} at /srv/private/test\u001b[31m`, field: '/input' };
    return { status: 200, json: answer };
  });
  const result = await client(h, f)(['place-order'], { '--lint': true, ...(json ? { '--json': true } : {}) });
  assert.equal(result.code, 4);
  assert.doesNotMatch(result.out + result.err, new RegExp(TOKEN + '|/srv/private|\\\\u001b'));
  assert.match(result.out, /admission-stopped/);
});
test('OUTCOME safety: saved restart cannot bypass missing selected lint evidence', async t => {
  const h = harbor(t); let restarted = false;
  const f = await fakeRuntime(t, (e, f) => {
    if (e.command === 'lint') return { status: 200, json: f.lint(e.request.requestId) };
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    return { status: 200, json: restarted ? f.job(id, 'check', 'unknown', { refusals: [{ code: 'service-restarted' }] }, 'unknown') : f.check(id, 'running') };
  });
  const run = client(h, f), first = await run(['place-order'], { '--json': true, '--timeout': 1.5 });
  const folder = join(h.state, 'batches', first.json.batch), saved = JSON.parse(readFileSync(join(folder, 'batch.json')));
  const lintPath = join(folder, `${saved.lint.request_ids.at(-1)}.json`), answer = JSON.parse(readFileSync(lintPath));
  delete answer.result.report.lint;
  writeFileSync(lintPath, JSON.stringify(answer)); restarted = true;
  const result = await run([], { '--read': first.json.batch, '--json': true });
  assert.equal(result.code, 3);
  assert.equal(f.posts.filter(p => p.command === 'check').length, 1, 'only the original paid request exists');
  assert.match(result.err, /The interpreter restarted a check, but the saved lint gives no pass of its own to that test, so pdd did not send it again\./);
  assert.equal(result.json.rows[0].request_id, first.json.rows[0].request_id);
});
test('OUTCOME safety: each selected test passes its own lint gate', async t => {
  const h = harbor(t);
  const f = await fakeRuntime(t, (e, f) => {
    if (e.command !== 'lint') return f.normal(e);
    const answer = f.lint(e.request.requestId);
    answer.result.report.lint = { complete: true, tests: [{ path: 'tests/place-order.json', verdict: 'passed' }, { path: 'tests/unknown-item.json', verdict: 'refused' }] };
    return { status: 200, json: answer };
  });
  const result = await client(h, f)(['place-order', 'unknown-item'], { '--json': true });
  assert.deepEqual(f.posts.filter(p => p.command === 'check').map(p => p.request.scenario), ['tests/place-order.json'], 'only the passing test is sent');
  assert.deepEqual(result.json.rows.map(row => [row.test, row.state]), [['tests/place-order.json', 'passed'], ['tests/unknown-item.json', 'refused']]);
  assert.equal(result.json.rows[1].calls, 0);
  assert.equal(result.code, 4);
  assert.match(result.err, /Lint refused 1 of 2 tests\. Sent 1 check/);
});
