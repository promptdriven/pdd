import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, unlinkSync, existsSync } from 'node:fs';
import { resolve, join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

// Independent bounded oracle: LEAD.md 20:05, approved TEST-CACHE rules.
// Failure selection is local to the named scope. No in-scope failure means
// normal selection, including reuse. Clear retains scope and overrides --lf.
const root = resolve(process.env.FORMAL_CODE_ROOT || fileURLToPath(new URL('..', import.meta.url)));
const { runCheck } = await import(pathToFileURL(join(root, 'src/runtime-client.mjs')));
const { harbor, fakeRuntime, portsFor } = await import(pathToFileURL(join(root, 'test/runtime-fake.mjs')));
const read = path => JSON.parse(readFileSync(path, 'utf8'));
const write = (path, doc) => writeFileSync(path, JSON.stringify(doc));
async function fixture(t) {
  const ctx = harbor(t, repo => {
    writeFileSync(join(repo, 'user_stories/independent.md'), readFileSync(join(repo, 'user_stories/place-order.md')));
    writeFileSync(join(repo, 'prompts/independent.prompt.md'), readFileSync(join(repo, 'prompts/place_order.prompt.md')));
    const doc = read(join(repo, 'tests/place-order.json'));
    doc.story_path = 'user_stories/independent.md';
    for (const step of doc.steps) step.entry_path = 'prompts/independent.prompt.md';
    write(join(repo, 'tests/independent.json'), doc);
  });
  let mode = 'passed';
  const fake = await fakeRuntime(t, entry => ({ status: 200, json: entry.command === 'lint' ? fake.lint(entry.request.requestId, ['prompts/place_order.prompt.md', 'prompts/independent.prompt.md'].map(path => ({ path, state: 'approved', admission_state: 'approved', interface: { calls: [] } }))) : fake.check(entry.request?.requestId ?? entry.url.split('/').at(-1), mode) }));
  const invoke = async (words, options = {}) => {
    const { ports } = portsFor({ HOME: ctx.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: ctx.state });
    const before = fake.posts.filter(row => row.command === 'check').length;
    const code = await runCheck({ cwd: ctx.repo, words, options: { '--json': true, ...options }, cache: true }, ports);
    return { code, json: ports.stdout.text ? JSON.parse(ports.stdout.text) : null, err: ports.stderr.text, sent: fake.posts.filter(row => row.command === 'check').length - before };
  };
  return { ...ctx, invoke, mode: value => { mode = value; }, failed: join(ctx.repo, '.pdd/cache/test/lastfailed.json') };
}
for (const selected of ['place-order', 'independent']) for (const history of ['none', 'inside', 'outside', 'deleted']) for (const clear of [false, true]) {
  test(`bounded scope=${selected} failure=${history} clear=${clear}`, async t => {
    const ctx = await fixture(t);
    assert.equal((await ctx.invoke([selected])).sent, 1, 'seed selected saved pass');
    if (history !== 'none') {
      const failing = history === 'inside' ? selected : selected === 'place-order' ? 'independent' : 'place-order';
      ctx.mode('failed');
      assert.equal((await ctx.invoke([failing], { '--cache-clear': true })).code, 1, 'seed known failure');
      // Clearing for the seed also invalidated the selected pass. Restore that
      // pass when the failure is elsewhere, preserving the unrelated failure.
      if (history !== 'inside') { ctx.mode('passed'); await ctx.invoke([selected]); }
      if (history === 'deleted') {
        unlinkSync(join(ctx.repo, `tests/${failing}.json`));
        unlinkSync(join(ctx.repo, `user_stories/${failing}.md`));
      }
    }
    ctx.mode('passed');
    const result = await ctx.invoke([selected], { '--lf': true, '--cache-clear': clear });
    assert.equal(result.code, 0);
    assert.equal(result.json.rows.length, 1, 'normal named scope must never become an empty green');
    assert.equal(result.json.rows[0].test, `tests/${selected}.json`, 'scope remains named');
    assert.equal(result.sent, clear || history === 'inside' ? 1 : 0, 'only in-scope failure or clear requires dispatch');
    if (clear) assert.match(result.err, /saved answers|saved results/i, 'clear honestly discloses interpreter reuse');
    if (history === 'deleted') assert.deepEqual(Object.keys(read(ctx.failed).stories), [], 'deleted failure forgotten');
  });
}
for (const damage of ['missing', 'malformed', 'epoch', 'generation', 'exact-set']) for (const lf of [false, true]) {
  test(`bounded lastfailed damage=${damage} lf=${lf}`, async t => {
    const ctx = await fixture(t);
    await ctx.invoke(['independent']);
    assert.ok(existsSync(ctx.failed), 'completed Story pass persists required last-failed metadata');
    const doc = read(ctx.failed);
    if (damage === 'epoch') doc.epoch = '00000000-0000-4000-8000-000000000000';
    if (damage === 'generation') doc.generation += 1;
    if (damage === 'exact-set') doc.stories = { 'user_stories/independent.md': true };
    if (damage === 'missing') unlinkSync(ctx.failed);
    else writeFileSync(ctx.failed, damage === 'malformed' ? '{bad' : JSON.stringify(doc));
    const result = await ctx.invoke(['independent'], { '--lf': lf });
    assert.equal(result.code, 0);
    assert.equal(result.sent, 1, 'invalid failure index cannot authorize reuse');
    assert.equal(result.json.warnings.filter(w => /cache/i.test(String(w))).length, 1, 'one cache warning');
    const healed = await ctx.invoke(['independent'], { '--lf': lf });
    assert.equal(healed.sent, 0, 'completed safe run heals metadata');
    assert.equal(healed.json.warnings.filter(w => /cache/i.test(String(w))).length, 0);
  });
}
