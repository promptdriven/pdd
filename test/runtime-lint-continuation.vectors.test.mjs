import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync, copyFileSync, mkdirSync, unlinkSync } from 'node:fs';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { harbor, fakeRuntime, portsFor, PLACE } from './runtime-fake.mjs';

// Native replay of the approved Story's case table. There are no executable Runtime
// vectors for this native boundary (#2548); this suite does not claim a Runtime pass.
const START = Date.parse('2026-10-27T16:27:47Z');
async function setup(t, { mode = 'check', interactive = false, timeout, multiple = false } = {}) {
  const h = harbor(t, repo => {
    if (multiple === 'mixed') { const doc = JSON.parse(readFileSync(join(repo, 'tests/place-order.json'))); doc.steps = []; writeFileSync(join(repo, 'tests/second-1.json'), JSON.stringify(doc)); }
    for (let i = 1; multiple !== 'mixed' && i < (multiple === true || multiple === 'mixed' ? 2 : multiple || 1); i++) copyFileSync(join(repo, 'tests/place-order.json'), join(repo, `tests/second-${i}.json`));
  });
  const state = { lint: 'running', checks: 'passed', lost: false, clock: null, readyAt: Infinity };
  const f = await fakeRuntime(t, async (e, f) => {
    if (e.method === 'POST') {
      if (e.command === 'lint') return { status: 202, json: f.job(e.request.requestId, 'lint', 'queued') };
      if (state.checkDelay) await new Promise(resolve => setTimeout(resolve, state.checkDelay));
      assert.ok(e.tar.length > 0, 'every check keeps the source multipart');
      if (state.lost) return { destroy: true };
      if (e.command === 'try') return { status: 200, json: f.tryJob(e.request.requestId) };
      return { status: 200, json: f.check(e.request.requestId, state.checks) };
    }
    const id = e.url.split('/').at(-1);
    const post = f.posts.find(p => p.request.requestId === id);
    if (post?.command === 'check') {
      if (state.lost) return { status: 404, json: {} };
      return { status: 200, json: f.check(id, state.checks) };
    }
    if (!post) return { status: 404, json: {} };
    if (state.clock.now >= state.readyAt) state.lint = 'passed';
    if (state.lint === 'wrong-id') return { status: 200, json: f.lint('00000000-0000-4000-8000-000000000000') };
    if (state.lint === 'wrong-command') return { status: 200, json: f.check(id) };
    if (state.lint === 'missing') return { status: 404, json: {} };
    if (state.lint === 'reached') return { status: 200, json: f.lint(id, [{ path: PLACE, admission_state: 'missing' }]) };
    if (state.lint === 'global') {
      const answer = f.lint(id); answer.result.refusals = [{ code: 'global-refusal', message: 'Global refusal' }];
      return { status: 200, json: answer };
    }
    return { status: 200, json: state.lint === 'passed' ? f.lint(id) : f.job(id, 'lint', state.lint) };
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin };
  const p = portsFor(env, { interactive }); state.clock = p.clock;
  const options = mode === 'try' ? { '--no-open': true, '--no-wait': true } : { '--json': true, ...(mode === 'lint' ? { '--lint': true } : { '--max-calls': 6 }), ...(timeout ? { '--timeout': timeout } : {}) };
  return { h, state, f, env, p, options, mode,
    async first() {
      const code = await (mode === 'try' ? runTry : runCheck)({ cwd: h.repo, words: multiple ? ['tests/place-order.json', ...Array.from({ length: (multiple === true || multiple === 'mixed' ? 2 : multiple) - 1 }, (_, i) => `tests/second-${i + 1}.json`)] : ['place-order'], options }, p.ports);
      const batch = mode === 'try' ? null : readdirSync(join(h.state, 'batches'), { withFileTypes: true }).find(e => e.isDirectory())?.name;
      return { code, batch };
    } };
}
function saved(r, batch) {
  const path = join(r.h.state, 'batches', batch, 'batch.json');
  return { path, doc: JSON.parse(readFileSync(path)) };
}
async function recovery(r, batch, retry = false, extra = {}, extraOptions = {}) {
  const p = portsFor(r.env, extra); r.state.clock = p.clock;
  const code = await runCheck({ cwd: r.h.repo, words: retry ? [] : [batch], options: { [retry ? '--retry' : '--read']: retry ? batch : true, '--json': true, ...extraOptions } }, p.ports);
  return { ...p, code, json: p.ports.stdout.text ? JSON.parse(p.ports.stdout.text) : null };
}
const paid = r => r.f.posts.filter(e => e.command === 'check');

for (const [name, config, expect, elapsed] of [
  ['explicit wait', { timeout: 4 }, 0, 150000],
  ['agent default', {}, 3, 90000],
  ['interactive', { interactive: true }, 0, 150000],
  ['lint-only wait', { mode: 'lint', timeout: 4 }, 0, 150000],
  ['Try interactive', { mode: 'try', interactive: true }, 0, 150000],
  ['Try agent', { mode: 'try' }, 3, 90000],
]) test(`CONTINUATION native table: ${name}`, async t => {
  const r = await setup(t, config); r.state.readyAt = START + 150000;
  const { code } = await r.first(); assert.equal(code, expect, r.p.ports.stderr.text);
  assert.equal(r.p.clock.now - START, elapsed);
  assert.equal(r.f.posts.filter(e => e.command === 'lint').length, 1);
  assert.equal(paid(r).length, code === 0 && r.mode === 'check' ? 1 : 0);
  if (paid(r).length) assert.equal(paid(r)[0].request.max_calls, 6);
});
for (const retry of [false, true]) test(`CONTINUATION native table: ${retry ? 'retry' : 'read'} and repeat`, async t => {
  const r = await setup(t); const { batch } = await r.first(); r.state.lint = 'passed';
  const next = await recovery(r, batch, retry); assert.equal(next.code, 0, next.ports.stderr.text);
  assert.equal(paid(r).length, 1); assert.equal(paid(r)[0].request.max_calls, 6);
  assert.equal(r.f.posts.filter(e => e.command === 'lint').length, 1);
  const again = await recovery(r, batch, retry); assert.equal(again.code, 0);
  assert.equal(again.clock.uuids, 0); assert.equal(paid(r).length, 1);
  assert.equal(again.json.rows[0].request_id, next.json.rows[0].request_id);
});
for (const retry of [false, true]) test(`CONTINUATION native table: concurrent read/${retry ? 'retry' : 'read'}`, async t => {
  const r = await setup(t, { multiple: true }); const { batch } = await r.first(); r.state.lint = 'passed';
  const replies = await Promise.all([recovery(r, batch), recovery(r, batch, retry)]);
  assert.equal(paid(r).length, 2, 'one POST per original held row');
  assert.equal(new Set(paid(r).map(e => e.request.scenario)).size, 2);
  const final = await recovery(r, batch);
  assert.equal(final.code, 0); assert.equal(final.clock.uuids, 0);
  for (const reply of replies) assert.deepEqual(reply.json.rows.map(row => row.request_id).sort(), final.json.rows.map(row => row.request_id).sort());
});

test('CONTINUATION native table: lost POST and repeated recovery preserve ID and unknown usage', async t => {
  const r = await setup(t); const { batch } = await r.first(); r.state.lint = 'passed'; r.state.lost = true;
  const next = await recovery(r, batch); assert.equal(next.code, 3);
  const id = paid(r)[0].request.requestId;
  for (let i = 0; i < 2; i++) {
    const again = await recovery(r, batch); assert.equal(again.code, 3); assert.equal(again.clock.uuids, 0);
    assert.equal(again.json.rows[0].request_id, id); assert.equal(again.json.rows[0].calls, 'unknown');
  }
  assert.equal(paid(r).length, 1);
});
for (const change of ['owner', 'repo', 'source']) test(`CONTINUATION native table: changed ${change} refuses before UUID`, async t => {
  const r = await setup(t); const { batch } = await r.first(); r.state.lint = 'passed';
  if (change === 'repo') { const s = saved(r, batch); s.doc.root += '-elsewhere'; writeFileSync(s.path, JSON.stringify(s.doc)); }
  if (change === 'source') writeFileSync(join(r.h.repo, PLACE), readFileSync(join(r.h.repo, PLACE), 'utf8') + '\nChanged.\n');
  const extra = change === 'owner' ? { gh: args => ({ status: 0, stdout: args[0] === 'auth' ? 'token' : 'other 123' }) } : {};
  const next = await recovery(r, batch, false, extra);
  if (change === 'source') { assert.equal(next.code, 5); assert.equal(next.json.rows.length, 1); assert.match(next.ports.stderr.text, /No checks were sent.*source changed/); } else assert.ok([2, 5].includes(next.code)); assert.equal(next.clock.uuids, 0); assert.equal(paid(r).length, 0);
});
for (const lint of ['running', 'wrong-id', 'wrong-command', 'unknown', 'missing', 'reached', 'global']) test(`CONTINUATION native table: ${lint} lint never authorizes checks`, async t => {
  const r = await setup(t); const { batch } = await r.first(); r.state.lint = lint;
  const next = await recovery(r, batch); assert.notEqual(next.code, 0); assert.equal(next.clock.uuids, 0); assert.equal(paid(r).length, 0);
});
for (const legacy of [false, true]) test(`CONTINUATION native table: standalone ${legacy ? 'legacy' : 'new'} never dispatches`, async t => {
  const r = await setup(t, { mode: 'lint' }); const { batch } = await r.first(); r.state.lint = 'passed';
  if (legacy) { const s = saved(r, batch); delete s.doc.intent; writeFileSync(s.path, JSON.stringify(s.doc)); }
  for (const retry of [false, true]) { const next = await recovery(r, batch, retry); assert.equal(next.clock.uuids, 0); }
  assert.equal(paid(r).length, 0);
});
for (const form of ['pending', 'already-read', 'prior-unknown']) test(`CONTINUATION native table: legacy ${form} omitted calls`, async t => {
  const r = await setup(t); const { batch } = await r.first(); r.state.lint = 'passed';
  const s = saved(r, batch); delete s.doc.intent; delete s.doc.rows[0].calls;
  if (form === 'already-read') {
    s.doc.lint = { ...s.doc.lint, state: 'passed', unknown: false, pending: false };
    s.doc.rows[0].note = { code: 'lint-finished', message: 'The saved lint finished. No checks were sent.' };
  }
  if (form === 'prior-unknown') s.doc.rows[0].note = { code: null, message: 'The lint result is unknown, so pdd sent no checks.' };
  writeFileSync(s.path, JSON.stringify(s.doc));
  const next = await recovery(r, batch); assert.equal(next.code, 0, next.ports.stderr.text); assert.equal(paid(r).length, 1);
});
for (const bad of ['positive', 'unknown', 'null', 'cap', 'criteria', 'steps', 'intent', 'version', 'incomplete']) test(`CONTINUATION native table: ambiguous legacy ${bad} fails closed`, async t => {
  const r = await setup(t); const { batch } = await r.first(); r.state.lint = 'passed'; const s = saved(r, batch); delete s.doc.intent;
  if (bad === 'positive') s.doc.rows[0].calls = 1;
  if (bad === 'unknown') s.doc.rows[0].calls = 'unknown';
  if (bad === 'null') s.doc.rows[0].calls = null;
  if (bad === 'cap') delete s.doc.rows[0].max_calls;
  if (bad === 'criteria') s.doc.rows[0].criteria_total++;
  if (bad === 'steps') s.doc.rows[0].steps = [];
  if (bad === 'intent') s.doc.intent = 'other';
  if (bad === 'version') s.doc.version = 2;
  if (bad === 'incomplete') s.doc.rows[0].calls = {};
  writeFileSync(s.path, JSON.stringify(s.doc)); const next = await recovery(r, batch);
  assert.equal(next.code, 5); assert.equal(next.json.rows.length, 1); assert.equal(next.clock.uuids, 0); assert.equal(paid(r).length, 0); assert.match(next.ports.stderr.text, /intent|proof/i);
});
test('CONTINUATION native table: saved origin and selected source only', async t => {
  const r = await setup(t); const { batch } = await r.first(); r.state.lint = 'passed';
  r.env.PDD_RUNTIME_URL = 'https://changed.example';
  // New unrelated untracked files do not enter the saved selected capture.
  writeFileSync(join(r.h.repo, 'user_stories/unrelated.md'), '# Unrelated\n');
  const next = await recovery(r, batch); assert.equal(next.code, 0); assert.equal(paid(r).length, 1);
  assert.equal(paid(r)[0].request.scenario, 'tests/place-order.json');
});
for (const timeout of [undefined, 4]) test(`CONTINUATION native table: fresh deadline ${timeout ?? 'default'}`, async t => {
  const r = await setup(t); const { batch } = await r.first(); r.state.lint = 'passed'; r.state.checks = 'running';
  const next = await recovery(r, batch, false, {}, timeout ? { '--timeout': timeout } : {});
  assert.equal(next.code, 3); assert.equal(next.clock.now - START, (timeout ?? 1.5) * 60000); assert.equal(paid(r).length, 1);
});
for (const when of ['before-claim', 'after-claim', 'incomplete-claim']) test(`CONTINUATION native table: interruption ${when}`, async t => {
  const r = await setup(t); const { batch } = await r.first(); r.state.lint = 'passed';
  let interrupt;
  const extra = { onInterrupt: handler => { interrupt = handler; if (when === 'before-claim') handler(); return () => {}; } };
  if (when === 'after-claim') extra.randomUUID = () => { interrupt(); return '11111111-1111-4111-8111-111111111111'; };
  if (when === 'incomplete-claim') {
    const key = createHash('sha256').update('tests/place-order.json').digest('hex');
    writeFileSync(join(r.h.state, 'batches', batch, `${key}.0.dispatch.json`), '');
  }
  await recovery(r, batch, false, extra); assert.equal(paid(r).length, 0);
  const again = await recovery(r, batch);
  assert.equal(paid(r).length, when === 'before-claim' ? 1 : 0);
  if (when !== 'before-claim') { assert.equal(again.clock.uuids, 0); assert.notEqual(again.code, 0); }
});
test('CONTINUATION native table: parser accepts timeout on remote lint and saved read', () => {
  for (const mode of ['--lint', '--read']) {
    const parsed = parseArgv(['check', mode, '--timeout', '4']);
    assert.equal(parsed.options['--timeout'], '4');
  }
});

test('CONTINUATION native table: posted completed/running/lost/unknown IDs remain read-only beside a held row', async t => {
  const r = await setup(t, { multiple: 5 }); const { batch } = await r.first(); r.state.lint = 'passed';
  const s = saved(r, batch);
  const states = ['passed', 'running', 'unknown', 'sending'];
  const ids = states.map((_, i) => `22222222-2222-4222-8222-22222222222${i}`);
  for (let i = 0; i < states.length; i++) Object.assign(s.doc.rows[i + 1], { state: states[i], phase: 'server', request_ids: [ids[i]], note: null });
  writeFileSync(s.path, JSON.stringify(s.doc));
  writeFileSync(join(r.h.state, 'batches', batch, ids[0] + '.json'), JSON.stringify(r.f.check(ids[0])));
  const next = await recovery(r, batch);
  assert.equal(paid(r).length, 1, 'only the original lint-held row is eligible');
  assert.deepEqual(saved(r, batch).doc.rows.slice(1).map(row => row.request_ids), ids.map(id => [id]));
  assert.equal(next.json.rows[1].state, 'passed');
  assert.ok(next.json.rows.slice(2).every(row => row.calls === 'unknown'));
});

for (const broken of [null, {}, { criterion_id: '' }]) test(`CONTINUATION native table: malformed legacy authored check ${JSON.stringify(broken)}`, async t => {
  const r = await setup(t); const { batch } = await r.first(); r.state.lint = 'passed';
  const s = saved(r, batch); delete s.doc.intent; s.doc.rows[0].steps[0].checks = [broken]; writeFileSync(s.path, JSON.stringify(s.doc));
  const next = await recovery(r, batch); assert.equal(next.code, 5); assert.equal(next.json.rows.length, 1); assert.equal(paid(r).length, 0); assert.equal(next.clock.uuids, 0);
});

test('CONTINUATION native table: parsed remote lint timeout and parsed recovery timeout reach public boundary', async t => {
  const lint = await setup(t, { mode: 'lint' }); lint.state.readyAt = START + 150000;
  const plan = parseArgv(['check', '--lint', 'place-order', '--timeout', '4', '--json']);
  assert.equal(await runCheck({ cwd: lint.h.repo, words: plan.operands, options: plan.options }, lint.p.ports), 0);
  assert.equal(lint.p.clock.now - START, 150000); assert.equal(paid(lint).length, 0);
  const r = await setup(t); const { batch } = await r.first(); r.state.lint = 'passed'; r.state.checks = 'running';
  const readPlan = parseArgv(['check', '--read', batch, '--timeout', '4', '--json']);
  const p = portsFor(r.env); r.state.clock = p.clock;
  assert.equal(await runCheck({ cwd: r.h.repo, words: readPlan.operands, options: readPlan.options }, p.ports), 3);
  assert.equal(p.clock.now - START, 240000);
});

test('CONTINUATION preservation: concurrent legacy capacity retries adopt claims after historical IDs', async t => {
  const r = await setup(t); const { batch } = await r.first();
  const s = saved(r, batch), oldId = '33333333-3333-4333-8333-333333333333';
  const folder = join(r.h.state, 'batches', batch), lintId = s.doc.lint.request_ids.at(-1);
  Object.assign(s.doc.lint, { state: 'passed', pending: false, unknown: false });
  Object.assign(s.doc.rows[0], { request_ids: [oldId], state: 'not_run', phase: 'server', busy: true, can_retry: true, eligible: true, note: { code: 'check-busy' } });
  writeFileSync(s.path, JSON.stringify(s.doc));
  writeFileSync(join(folder, lintId + '.json'), JSON.stringify(r.f.lint(lintId)));
  writeFileSync(join(folder, oldId + '.admission.json'), JSON.stringify({ dispatch: 'not_started', error: { code: 'check-queue-full', details: { retryable: true, retry_after: 1 } } }));
  const replies = await Promise.all([recovery(r, batch, true), recovery(r, batch, true)]);
  assert.equal(paid(r).length, 1); assert.ok(replies.every(reply => reply.code === 0));
  const final = saved(r, batch).doc.rows[0];
  assert.deepEqual(final.request_ids, [oldId, paid(r)[0].request.requestId]);
});

for (const legacy of [false, true]) test(`CONTINUATION: ${legacy ? 'legacy' : 'current'} batch local refusal does not block valid held row`, async t => {
  const r = await setup(t, { multiple: 'mixed' }); const { batch } = await r.first(); r.state.lint = 'passed';
  assert.equal(saved(r, batch).doc.rows.find(row => row.test === 'tests/second-1.json').state, 'refused');
  if (legacy) { const s = saved(r, batch); delete s.doc.intent; writeFileSync(s.path, JSON.stringify(s.doc)); }
  const next = await recovery(r, batch);
  assert.equal(next.code, 4); assert.equal(next.json.rows.length, 2);
  assert.equal(paid(r).length, 1); assert.equal(paid(r)[0].request.scenario, 'tests/place-order.json');
  assert.equal(next.json.rows.find(row => row.test === 'tests/second-1.json').state, 'refused');
});

test('CONTINUATION: two real CLI read processes send the original held check exactly once', { timeout: 30000 }, async t => {
  const r = await setup(t); const { batch } = await r.first(); r.state.lint = 'passed';
  r.state.checkDelay = 250; // Keep the winning POST in flight while the other process adopts its claim.
  const bin = join(r.h.sandbox, 'bin'); mkdirSync(bin);
  writeFileSync(join(bin, 'gh'), '#!/bin/sh\nif [ "$1" = auth ]; then echo local-fake-token; else echo "octo 4242"; fi\n', { mode: 0o755 });
  const cli = fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url));
  const child = () => new Promise((resolve, reject) => {
    const proc = spawn(process.execPath, [cli, 'check', '--read', batch, '--json'], { cwd: r.h.repo, env: { ...process.env, ...r.env, PATH: bin + ':' + process.env.PATH } });
    t.after(() => { if (proc.exitCode === null) proc.kill(); });
    let stdout = '', stderr = ''; proc.stdout.on('data', chunk => stdout += chunk); proc.stderr.on('data', chunk => stderr += chunk);
    proc.on('error', reject); proc.on('close', code => resolve({ code, stdout, stderr }));
  });
  const replies = await Promise.all([child(), child()]);
  assert.equal(paid(r).length, 1);
  const id = paid(r)[0].request.requestId;
  for (const reply of replies) { assert.equal(reply.code, 0, reply.stderr); assert.equal(JSON.parse(reply.stdout).rows[0].request_id, id); }
  assert.deepEqual(saved(r, batch).doc.rows[0].request_ids, [id]);
  const repeat = await recovery(r, batch); assert.equal(repeat.code, 0); assert.equal(repeat.clock.uuids, 0);
  assert.equal(repeat.json.rows[0].request_id, id); assert.equal(paid(r).length, 1);
});

test('CONTINUATION: deleting a selected test preserves saved rows and refuses before UUID', async t => {
  const r = await setup(t); const { batch } = await r.first(); r.state.lint = 'passed';
  unlinkSync(join(r.h.repo, 'tests/place-order.json'));
  for (let i = 0; i < 2; i++) {
    const next = await recovery(r, batch);
    assert.equal(next.code, 5); assert.equal(next.json.rows.length, 1); assert.equal(next.json.rows[0].state, 'not_run');
    assert.equal(next.clock.uuids, 0); assert.equal(paid(r).length, 0);
    assert.match(next.ports.stderr.text, /No checks were sent.*saved source cannot be verified/);
  }
});
