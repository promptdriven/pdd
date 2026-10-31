import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, cpSync, mkdirSync, readFileSync, writeFileSync, unlinkSync, symlinkSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { resolve, join } from 'node:path';
import { pathToFileURL, fileURLToPath } from 'node:url';

// Native bounded oracle from review M1/M2 and the Story's Rules to check.
// Foreign/tracked evidence never skips; only a confirmed pass clears a failure;
// a late older attempt never replaces the newer attempt's verdict.
const root = resolve(process.env.FORMAL_CODE_ROOT || fileURLToPath(new URL('..', import.meta.url)));
const { runCheck } = await import(pathToFileURL(join(root, 'src/runtime-client.mjs')));
const { harbor, fakeRuntime, portsFor } = await import(pathToFileURL(join(root, 'test/runtime-fake.mjs')));
function git(repo, ...args) {
  const result = spawnSync('git', args, { cwd: repo, encoding: 'utf8' });
  assert.equal(result.status, 0, result.stderr);
}
async function fixture(t) {
  const env = harbor(t);
  let mode = 'passed', incomplete = false, delay = null;
  const fake = await fakeRuntime(t, async entry => {
    if (entry.command === 'lint') return { status: 200, json: fake.lint(entry.request.requestId) };
    const state = mode, missingAccounting = incomplete;
    if (delay && entry.method === 'POST') { const gate = delay; delay = null; await gate; }
    const answer = fake.check(entry.request?.requestId ?? entry.url.split('/').at(-1), state);
    if (missingAccounting) answer.usage.accounting_complete = false;
    return { status: 200, json: answer };
  });
  const invoke = async ({ options = {}, words = ['place-order'], repo = env.repo, state = env.state, trouble } = {}) => {
    const { ports, clock } = portsFor({ HOME: env.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: state });
    if (trouble === 'auth') ports.gh = () => ({ status: 1, stdout: '', stderr: 'not logged in' });
    if (trouble === 'interrupt') ports.sleep = async ms => { clock.now += ms; clock.interrupt(); };
    if (trouble === 'timeout') ports.sleep = async ms => { clock.now += 120000; };
    const before = fake.posts.filter(row => row.command === 'check').length;
    const code = await runCheck({ cwd: repo, words, options: { '--json': true, ...options }, cache: true }, ports);
    return { code, json: ports.stdout.text ? JSON.parse(ports.stdout.text) : null, sent: fake.posts.filter(row => row.command === 'check').length - before };
  };
  return { ...env, fake, invoke, mode: value => { mode = value; }, incomplete: value => { incomplete = value; }, delay: value => { delay = value; } };
}
function change(ctx) {
  const path = join(ctx.repo, 'tests/place-order.json'), original = readFileSync(path, 'utf8'), doc = JSON.parse(original);
  doc.initial_world.formal_changed = true; writeFileSync(path, JSON.stringify(doc));
}
for (const foreign of ['tracked-story', 'tracked-nested', 'copied-state', 'copied-checkout']) for (const clear of [false, true]) {
  test(`bounded foreign=${foreign} clear=${clear}`, async t => {
    const ctx = await fixture(t);
    assert.equal((await ctx.invoke()).sent, 1);
    assert.equal((await ctx.invoke()).sent, 0, 'own complete pass is reusable');
    let repo = ctx.repo, state = ctx.state;
    if (foreign.startsWith('tracked')) {
      const file = foreign === 'tracked-story' ? '.pdd/cache/test/stories.json' : '.pdd/cache/test/nested/foreign.txt';
      if (foreign === 'tracked-nested') { mkdirSync(join(repo, '.pdd/cache/test/nested'), { recursive: true }); writeFileSync(join(repo, file), 'tracked sentinel'); }
      git(repo, 'add', '-f', file);
      git(repo, '-c', 'user.name=Serhan Asad', '-c', 'user.email=95069916+Serhan-Asad@users.noreply.github.com', 'commit', '-qm', 'foreign cache');
    } else {
      state = join(ctx.sandbox, 'foreign-state');
      if (foreign === 'copied-checkout') { repo = join(ctx.sandbox, 'foreign-repo'); cpSync(ctx.repo, repo, { recursive: true }); }
    }
    ctx.mode('failed');
    const result = await ctx.invoke({ repo, state, options: { '--cache-clear': clear } });
    assert.equal(result.sent, 1, 'foreign/tracked cache cannot authorize skipped checks');
    assert.equal(result.code, 1, 'actual failing checks cannot become a false green');
    assert.ok(result.json.rows.every(row => !row.cached));
    if (foreign.startsWith('tracked')) assert.equal(result.json.warnings.filter(w => /cache/i.test(String(w))).length, 1);
  });
}
for (const noVerdict of ['auth', 'unknown', 'refused', 'incomplete', 'interrupt', 'timeout']) {
  test(`bounded failure survives ${noVerdict} until pass`, async t => {
    const ctx = await fixture(t); ctx.mode('failed');
    assert.equal((await ctx.invoke()).code, 1);
    ctx.mode(['interrupt', 'timeout'].includes(noVerdict) ? 'running' : noVerdict === 'refused' ? 'refused' : noVerdict === 'unknown' ? 'unknown' : 'passed');
    ctx.incomplete(noVerdict === 'incomplete');
    const attempt = await ctx.invoke({ options: { '--lf': true }, trouble: noVerdict });
    assert.equal(attempt.sent, noVerdict === 'auth' ? 0 : 1, 'exercise declared no-verdict attempt');
    if (noVerdict === 'auth') assert.equal(attempt.code, 5);
    if (['interrupt', 'timeout'].includes(noVerdict)) assert.equal(attempt.code, 3);
    if (['unknown', 'refused'].includes(noVerdict)) assert.equal(attempt.json.rows[0].state, noVerdict);
    if (noVerdict === 'incomplete') assert.equal(attempt.json.rows[0].calls, 'unknown');
    ctx.incomplete(false); ctx.mode('failed');
    const remains = await ctx.invoke({ options: { '--lf': true } });
    assert.equal(remains.sent, 1, 'no verdict must retain known failure'); assert.equal(remains.code, 1);
    ctx.mode('passed'); assert.equal((await ctx.invoke({ options: { '--lf': true } })).sent, 1, 'confirmed pass executes');
    const cleared = await ctx.invoke({ options: { '--lf': true } });
    assert.equal(cleared.sent, 0, 'confirmed pass clears last failure'); assert.equal(cleared.code, 0);
  });
}
for (const older of ['passed', 'failed']) for (const newer of ['passed', 'failed']) for (const clear of [false, true]) {
  test(`bounded generation older=${older} newer=${newer} clear=${clear}`, async t => {
    const ctx = await fixture(t); await ctx.invoke(); change(ctx);
    let release; const gate = new Promise(done => { release = done; });
    ctx.mode(older); ctx.delay(gate);
    const before = ctx.fake.posts.filter(row => row.command === 'check').length;
    const earlier = ctx.invoke();
    const deadline = Date.now() + 15000;
    while (ctx.fake.posts.filter(row => row.command === 'check').length === before) {
      assert.ok(Date.now() < deadline, 'older attempt dispatches'); await new Promise(done => setTimeout(done, 5));
    }
    try {
      ctx.mode(newer);
      const latest = await ctx.invoke({ options: { '--cache-clear': clear } });
      assert.equal(latest.code, newer === 'passed' ? 0 : 1);
      ctx.mode('failed');
      const independent = await ctx.invoke({ words: ['unknown-item'] });
      assert.equal(independent.code, 1, JSON.stringify(independent));
    } finally { release(); }
    assert.equal((await earlier).code, older === 'passed' ? 0 : 1);
    assert.ok(existsSync(join(ctx.repo, '.pdd/cache/test/lastfailed.json')), 'completed attempt persists last-known failure metadata');
    const persisted = JSON.parse(readFileSync(join(ctx.repo, '.pdd/cache/test/lastfailed.json'), 'utf8'));
    assert.equal(Boolean(persisted.stories['user_stories/unknown-item.md']), true, 'late completion retains independent failure');
    assert.equal(Boolean(persisted.stories['user_stories/place-order.md']), newer === 'failed', 'late completion preserves newer confirmed failure');
    ctx.mode('passed');
    const selected = await ctx.invoke({ options: { '--lf': true } });
    assert.equal(selected.sent, Number(newer === 'failed'), 'latest generation alone determines failure selection');
  });
}

// Exhaustive 4 outcomes × 2 source identities × 2 filters × 2 clears.
// With no known failures --lf falls back to normal selection, so it does
// not change this one-Story scope's dispatch/reuse oracle.
for (const prior of ['passed', 'failed', 'refused', 'unknown']) for (const changed of [false, true]) for (const lf of [false, true]) for (const clear of [false, true]) {
  test(`bounded state prior=${prior} changed=${changed} lf=${lf} clear=${clear}`, async t => {
    const ctx = await fixture(t); await ctx.invoke();
    const path = join(ctx.repo, 'tests/place-order.json'), original = readFileSync(path, 'utf8');
    change(ctx); ctx.mode(prior);
    const established = await ctx.invoke();
    assert.equal(established.sent, 1); assert.equal(established.json.rows[0].state, prior);
    if (changed) writeFileSync(path, original);
    ctx.mode('passed');
    const got = await ctx.invoke({ options: { '--lf': lf, '--cache-clear': clear } });
    const sends = Number(clear || prior !== 'passed' || changed);
    assert.equal(got.sent, sends, 'only unchanged complete pass permits reuse');
    assert.equal(got.code, 0); assert.equal(got.json.rows.length, 1, 'clear retains named selection');
    assert.equal(got.json.rows.filter(row => row.cached).length, 1 - sends);
    if (!sends) { assert.equal(got.json.rows[0].calls, 0); assert.equal(got.json.rows[0].request_id, null); assert.equal(got.json.rows[0].report_url, null); }
  });
}
for (const damage of ['malformed', 'symlink']) for (const clear of [false, true]) {
  test(`bounded damage=${damage} clear=${clear}`, async t => {
    const ctx = await fixture(t); await ctx.invoke();
    const path = join(ctx.repo, '.pdd/cache/test/stories.json'), outside = join(ctx.sandbox, 'outside');
    assert.ok(existsSync(path), 'completed attempt persists cache before damage');
    writeFileSync(outside, 'outside sentinel');
    if (damage === 'symlink') { unlinkSync(path); symlinkSync(outside, path); } else writeFileSync(path, '{broken');
    const got = await ctx.invoke({ options: { '--cache-clear': clear } });
    assert.equal(got.sent, 1); assert.equal(got.code, 0); assert.ok(got.json.rows.every(row => !row.cached));
    assert.equal(got.json.warnings.filter(w => /cache/i.test(String(w))).length, 1);
    assert.ok(got.json.warnings.some(w => String(w).includes('pdd test --cache-clear')));
    assert.equal(readFileSync(outside, 'utf8'), 'outside sentinel');
    if (damage === 'malformed') assert.equal((await ctx.invoke()).sent, 0, 'regular cache heals');
  });
}
for (const selected of ['place-order.json', 'place-order-extra.json']) {
  test(`bounded incomplete sibling=${selected}`, async t => {
    const ctx = await fixture(t);
    writeFileSync(join(ctx.repo, 'tests/place-order-extra.json'), readFileSync(join(ctx.repo, 'tests/place-order.json')));
    assert.equal((await ctx.invoke({ words: [`tests/${selected}`] })).sent, 1);
    const complete = await ctx.invoke();
    assert.equal(complete.sent, 2, 'partial sibling evidence never authorizes whole Story pass');
    assert.ok(complete.json.rows.every(row => !row.cached));
    assert.equal((await ctx.invoke()).sent, 0);
  });
}
