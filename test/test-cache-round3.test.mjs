import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync, writeFileSync, readdirSync, statSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';
import { interfaceBlocks, proseSha256 } from '../src/runtime-preflight.mjs';

const read = path => { assert.ok(existsSync(path), 'required fixture or cache metadata exists'); return JSON.parse(readFileSync(path, 'utf8')); };
const write = (path, value) => writeFileSync(path, JSON.stringify(value, null, 2) + '\n');
const min = 60000;
const A = { engine_sha: 'a'.repeat(40), requested_model: 'synthetic-model-A' };
const B = { engine_sha: 'b'.repeat(40), requested_model: 'synthetic-model-A' };

async function setup(t, edit) {
  const fixture = harbor(t, repo => {
    writeFileSync(join(repo, 'user_stories/independent.md'), readFileSync(join(repo, 'user_stories/place-order.md')));
    writeFileSync(join(repo, 'prompts/independent.prompt.md'), readFileSync(join(repo, 'prompts/place_order.prompt.md')));
    const doc = read(join(repo, 'tests/place-order.json')); doc.story_path = 'user_stories/independent.md';
    for (const step of doc.steps) step.entry_path = 'prompts/independent.prompt.md';
    write(join(repo, 'tests/independent.json'), doc); edit?.(repo);
  });
  const state = { identity: { ...A }, running: false, reply: null, pick: null, onCheckPost: null };
  const fake = await fakeRuntime(t, entry => {
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    if (entry.command === 'lint') return { status: 200, json: fake.lint(id, ['prompts/place_order.prompt.md', 'prompts/independent.prompt.md'].map(path => ({ path, state: 'approved', admission_state: 'approved', interface: { calls: [] } }))) };
    if (entry.method === 'POST' && entry.command === 'check') state.onCheckPost?.(entry);
    const custom = state.reply?.(id, entry, fake); if (custom) return custom;
    const identity = state.pick?.(id) ?? state.identity;
    if (state.running) {
      const job = fake.check(id, 'running'); job.engine_sha = identity.engine_sha; job.usage.requested_model = identity.requested_model;
      return { status: entry.method === 'POST' ? 202 : 200, json: job };
    }
    const job = fake.check(id); job.engine_sha = identity.engine_sha;
    job.usage.requested_model = identity.requested_model;
    job.result.report.evaluation.requested_model = identity.requested_model;
    return { status: 200, json: job };
  });
  const env = { HOME: fixture.home, PDD_RUNTIME_URL: fake.origin, PDD_INTERPRETER_CONCURRENCY: '8', PDD_STATE_DIR: fixture.state };
  const { ports, clock } = portsFor(env);
  const invokeWith = async (p, words = [], options = {}, cache = true) => {
    p.stdout.text = ''; p.stderr.text = '';
    const before = fake.posts.filter(x => x.command === 'check').length;
    const code = await runCheck({ words, options: { '--json': true, ...options }, cwd: fixture.repo, cache }, p);
    if (p === ports) clock.now += 1;
    return { code, sent: fake.posts.filter(x => x.command === 'check').length - before, json: options['--json'] === false ? null : JSON.parse(p.stdout.text), stderr: p.stderr.text };
  };
  const invoke = (words, options) => invokeWith(ports, words, options);
  const readBatch = async (name, p = ports, options = {}) => { p.stdout.text = ''; p.stderr.text = ''; return runCheck({ words: [name], options: { '--read': true, '--json': true, ...options }, cwd: fixture.repo, cache: true }, p); };
  return { ...fixture, fake, ports, clock, env, invoke, invokeWith, readBatch, state };
}
// Cache actors share cache files, while each actor owns its admission queue.
// Busy adaptation in one actor must not turn this cache barrier into a queue test.
function actorPorts(ctx, extra = {}) {
  ctx.actors = (ctx.actors ?? 0) + 1;
  return portsFor({...ctx.env, PDD_INTERPRETER_QUEUE: join(ctx.env.PDD_STATE_DIR, `interpreter-actor-${ctx.actors}`)}, extra);
}
function bump(ctx, file) { const path = join(ctx.repo, file), doc = read(path); doc.initial_world.changed = (doc.initial_world.changed ?? 0) + 1; write(path, doc); }
function findBatch(dir, name) {
  for (const entry of readdirSync(dir)) {
    const path = join(dir, entry);
    if (entry === name && existsSync(join(path, 'batch.json'))) return join(path, 'batch.json');
    if (statSync(path).isDirectory()) { const found = findBatch(path, name); if (found) return found; }
  }
  return null;
}

const interleavings = [
  { name: 'overlap and older writer', run: async ctx => {
  assert.equal((await ctx.invoke()).sent, 3);
  bump(ctx, 'tests/independent.json'); bump(ctx, 'tests/place-order.json');
  const p = actorPorts(ctx); p.ports.interactive = true; p.clock.now = ctx.clock.now + 1000;
  const q = actorPorts(ctx); q.clock.now = ctx.clock.now + 60000;
  let released = false; const held = new Set(); let phase = 'p';
  ctx.state.reply = (id, entry, fake) => {
    if (entry.method === 'POST') { if (phase === 'p') held.add(id); }
    const hold = held.has(id);
    if (hold && !released) { const job = fake.check(id, 'running'); job.engine_sha = A.engine_sha; job.usage.requested_model = A.requested_model; return { status: entry.method === 'POST' ? 202 : 200, json: job }; }
    const identity = hold ? A : B;
    const job = fake.check(id); job.engine_sha = identity.engine_sha; job.usage.requested_model = identity.requested_model; job.result.report.evaluation.requested_model = identity.requested_model;
    return { status: 200, json: job };
  };
  const pRun = ctx.invokeWith(p.ports, ['independent']);
  while (!held.size) await new Promise(done => setTimeout(done, 5));
  phase = 'q';
  const qRes = await ctx.invokeWith(q.ports, ['place-order']);
  released = true;
  const pRes = await pRun;
  ctx.state.reply = null; ctx.state.identity = { ...B }; ctx.clock.now = q.clock.now + 60000;
  const u = await ctx.invoke(['unknown-item']);
  assert.equal(u.sent, 1, 'pdd saw build b in Q; the old build-a pass must not be reused');
  } },
  { name: 'read that resends', run: async ctx => {
  assert.equal((await ctx.invoke()).sent, 3);
  bump(ctx, 'tests/independent.json'); bump(ctx, 'tests/place-order.json');
  ctx.state.running = true;
  const x = await ctx.invoke(['independent', 'place-order'], { '--timeout': 1 });
  assert.equal(x.code, 3); assert.equal(x.sent, 2);
  ctx.state.running = false;
  const saved = read(findBatch(ctx.env.PDD_STATE_DIR, x.json.batch) ?? findBatch(ctx.home, x.json.batch));
  const ids = Object.fromEntries(saved.rows.map(r => [r.test, r.request_ids.at(-1)]));
  ctx.clock.now += 10 * min; ctx.state.identity = { ...B }; bump(ctx, 'tests/unknown-item.json');
  const y = await ctx.invoke(['unknown-item']);
  ctx.clock.now += 10 * min;
  ctx.state.reply = (id, entry, fake) => {
    if (id === ids['tests/independent.json']) { const job = fake.check(id); job.engine_sha = A.engine_sha; job.usage.requested_model = A.requested_model; job.result.report.evaluation.requested_model = A.requested_model; return { status: 200, json: job }; }
    if (id === ids['tests/place-order.json']) { const job = fake.job(id, 'check', 'unknown', { exitCode: 1, refusals: [{ code: 'service-restarted', message: 'restarted' }], report: { refusal: { code: 'service-restarted' } } }); job.engine_sha = A.engine_sha; job.usage.requested_model = A.requested_model; return { status: 200, json: job }; }
    const job = fake.check(id, 'queued'); delete job.engine_sha; delete job.usage.requested_model; return { status: entry.method === 'POST' ? 202 : 200, json: job };
  };
  const before = ctx.fake.posts.filter(p => p.command === 'check').length;
  const code = await ctx.readBatch(x.json.batch, ctx.ports, { '--timeout': 1 });
  ctx.state.reply = null;
  const named = await ctx.invoke(['independent']);
  assert.equal(named.sent, 1, 'Y saw build b after X started; X\'s build-a pass must not be reused');
  } },
  { name: 'clean repeat', run: async ctx => {
    assert.equal((await ctx.invoke()).sent, 3);
    assert.equal((await ctx.invoke(['unknown-item'])).sent, 0);
  } },
  { name: 'late read', run: async ctx => {
    ctx.state.running = true; const first = await ctx.invoke(['independent'], { '--timeout': 1 }); assert.equal(first.code, 3);
    ctx.state.running = false; ctx.clock.now += 10 * min;
    assert.equal((await ctx.invoke(['place-order', 'unknown-item'])).sent, 2);
    ctx.state.identity = { ...B }; ctx.clock.now += 10 * min;
    assert.equal(await ctx.readBatch(first.json.batch), 0);
    assert.equal((await ctx.invoke(['place-order'])).sent, 1, 'never skip after a read wrote the record');
  } },
  { name: 'mixed builds', run: async ctx => {
    assert.equal((await ctx.invoke()).sent, 3); bump(ctx, 'tests/independent.json'); bump(ctx, 'tests/place-order.json');
    const ids = []; ctx.state.pick = id => { if (!ids.includes(id)) ids.push(id); return ids.indexOf(id) === 0 ? B : A; };
    assert.equal((await ctx.invoke(['independent', 'place-order'])).sent, 2); ctx.state.pick = null;
    assert.equal((await ctx.invoke(['unknown-item'])).sent, 1, 'never skip after mixed observations');
  } },
  { name: 'partial identity', run: async ctx => {
    assert.equal((await ctx.invoke()).sent, 3); bump(ctx, 'tests/independent.json');
    ctx.state.reply = (id, entry, fake) => { const job = fake.check(id); delete job.engine_sha; return { status: 200, json: job }; };
    assert.equal((await ctx.invoke(['independent'])).sent, 1); ctx.state.reply = null;
    assert.equal((await ctx.invoke(['unknown-item'])).sent, 1, 'never skip after a partial identity');
  } },
  { name: 'old writer record', run: async ctx => {
    assert.equal((await ctx.invoke()).sent, 3);
    const file = join(ctx.repo, '.pdd/cache/test/stories.json'), doc = read(file);
    doc.latest_identity.clean = false; write(file, doc);
    assert.equal((await ctx.invoke(['unknown-item'])).sent, 1, 'never skip when the writer was not clean');
  } },
  { name: 'unknown writer', run: async ctx => {
    assert.equal((await ctx.invoke()).sent, 3);
    const file = join(ctx.repo, '.pdd/cache/test/stories.json'), doc = read(file);
    delete doc.latest_identity.clean; delete doc.latest_identity.written_at; write(file, doc);
    assert.equal((await ctx.invoke(['unknown-item'])).sent, 1, 'legacy or unknown writers cannot authorize reuse');
  } },
];
test('TEST-CACHE-R3 interleaving table: never skip on doubt', async t => {
  const failures = [];
  for (const row of interleavings) {
    try { await row.run(await setup(t)); }
    catch (error) { failures.push({ case: row.name, code: error.code, message: error.message }); }
  }
  assert.deepEqual(failures, [], 'every interleaving must obey never-skip-on-doubt');
});
function editClock(repo) {
  const file = join(repo, 'prompts/place_order.prompt.md'); let text = readFileSync(file, 'utf8');
  const block = interfaceBlocks(text)[0], doc = JSON.parse(block[1]); doc.status = 'draft';
  const schema = { type: 'object', properties: {}, required: [], additionalProperties: false };
  doc.resources = [{ name: 'clock', kind: 'port', access: 'read', operations: [{ name: 'now', access: 'read', arguments_schema: schema, result_schema: schema }] }];
  text = text.slice(0, block.indices[1][0]) + JSON.stringify(doc) + text.slice(block.indices[1][1]);
  text = text.replace(/"prose_sha256"\s*:\s*"[^"]*"/, '"prose_sha256":"' + proseSha256(text) + '"'); writeFileSync(file, text);
}
test('TEST-CACHE-R3 only ISO date-time strings fix the clock', async t => {
  const ctx = await setup(t, editClock), selected = ['tests/place-order.json'];
  for (const value of ['real 2026', 'now 1', '1', '2026-10-31', '2026-10-31T12:00:00Z', '2026-10-31T12:00:00+01:00']) {
    const file = join(ctx.repo, 'tests/place-order.json'), doc = read(file); doc.initial_world.clock = { now: value }; write(file, doc);
    assert.equal((await ctx.invoke(selected)).sent, 1);
    const repeat = await ctx.invoke(selected), iso = value.includes('T');
    assert.equal(repeat.sent, iso ? 0 : 1);
    if (!iso) assert.equal(repeat.json.rows[0].cache_reason, 'runs every time: uses the real clock');
  }
});
for (const part of ['engine', 'model']) test(`TEST-CACHE-R3 multiple stored ${part} values remain doubt with a false flag`, async t => {
  const ctx = await setup(t); assert.equal((await ctx.invoke()).sent, 3);
  const file = join(ctx.repo, '.pdd/cache/test/stories.json'), doc = read(file);
  if (part === 'engine') Object.assign(doc.latest_identity, { engine_sha: null, engine_shas: [A.engine_sha, B.engine_sha], conflict: false });
  else Object.assign(doc.latest_identity, { models: [A.requested_model, 'synthetic-model-B'], conflict: false });
  write(file, doc);
  assert.equal((await ctx.invoke()).sent, 3, 'stored multiple values can never authorize a skip');
});


test('TEST-CACHE-V1 short run inside a longer run cannot reuse a pass', async t => {
  const ctx = await setup(t); assert.equal((await ctx.invoke()).sent, 3);
  bump(ctx, 'tests/independent.json'); bump(ctx, 'tests/place-order.json');
  const p = actorPorts(ctx); p.ports.interactive = true; p.clock.now = ctx.clock.now + 1000;
  const q = actorPorts(ctx); q.clock.now = ctx.clock.now + 30000;
  const r = actorPorts(ctx); r.clock.now = ctx.clock.now + 60000;
  let released = false, phase = 'p'; const held = new Set();
  ctx.state.reply = (id, entry, fake) => {
    if (entry.method === 'POST' && phase === 'p') held.add(id);
    const identity = held.has(id) ? B : A;
    const job = fake.check(id, held.has(id) && !released ? 'running' : 'passed');
    job.engine_sha = identity.engine_sha; job.usage.requested_model = identity.requested_model;
    if (job.result?.report?.evaluation) job.result.report.evaluation.requested_model = identity.requested_model;
    return { status: job.state === 'running' && entry.method === 'POST' ? 202 : 200, json: job };
  };
  const pRun = ctx.invokeWith(p.ports, ['independent']);
  try {
    while (!held.size) await new Promise(done => setTimeout(done, 5));
    phase = 'q'; await ctx.invokeWith(q.ports, ['place-order']);
    const short = await ctx.invokeWith(r.ports, ['unknown-item']);
    assert.equal(short.sent, 1, 'the longer run has already seen build b; never reuse build a while it is active');
  } finally { released = true; await pRun; ctx.state.reply = null; }
  ctx.clock.now = r.clock.now + 5 * min;
  assert.equal((await ctx.invoke(['unknown-item'])).sent, 1, 'overlap leaves doubt');
  assert.equal((await ctx.invoke(['unknown-item'])).sent, 0, 'a later clean run restores reuse');
});

test('TEST-CACHE-V2 crash before finish leaves a mark that forces a run', async t => {
  const ctx = await setup(t); assert.equal((await ctx.invoke()).sent, 3);
  bump(ctx, 'tests/independent.json'); bump(ctx, 'tests/place-order.json');
  const deadPid = 987654321, c = actorPorts(ctx, { pid: deadPid, isAlive: () => true }); c.clock.now = ctx.clock.now + 1000;
  let first = true;
  ctx.state.reply = (id, entry, fake) => {
    const job = fake.check(id, first && entry.method === 'POST' ? 'passed' : 'running'); first = false;
    job.engine_sha = B.engine_sha; job.usage.requested_model = B.requested_model;
    if (job.result?.report?.evaluation) job.result.report.evaluation.requested_model = B.requested_model;
    return { status: job.state === 'running' && entry.method === 'POST' ? 202 : 200, json: job };
  };
  c.ports.sleep = async () => { throw new Error('simulated crash before finish'); };
  await assert.rejects(ctx.invokeWith(c.ports, ['independent', 'place-order']), /simulated crash before finish/);
  ctx.state.reply = null; ctx.clock.now += 5 * min; ctx.state.identity = { ...B };
  ctx.ports.isAlive = pid => pid !== deadPid;
  assert.equal((await ctx.invoke(['unknown-item'])).sent, 1, 'a crash after observing build b must not leave build-a reuse');
  assert.equal((await ctx.invoke(['unknown-item'])).sent, 0, 'one clean recovery run restores reuse');
});

// Round 4: a failed sign-in, an in-flight read and a clear must retain doubt.
const DEAD = 987654321;
const wait = () => new Promise(done => setTimeout(done, 5));
function round4Other(ctx, offset, extra = {}) {
  const other = actorPorts(ctx, { isAlive: pid => pid !== DEAD, ...extra });
  other.clock.now = ctx.clock.now + offset; return other;
}
const job = (fake, id, identity, state = 'passed') => {
  const value = fake.check(id, state); value.engine_sha = identity.engine_sha; value.usage.requested_model = identity.requested_model;
  if (value.result?.report?.evaluation) value.result.report.evaluation.requested_model = identity.requested_model;
  return value;
};
// A crash run with pid DEAD: its first answer reports build b, then the process dies before finish.
async function crashOnB(ctx, words) {
  const c = round4Other(ctx, 1000, { pid: DEAD, isAlive: () => true });
  let first = true;
  ctx.state.reply = (id, entry, fake) => {
    if (entry.method === 'POST' && first) { first = false; return { status: 200, json: job(fake, id, B) }; }
    return { status: entry.method === 'POST' ? 202 : 200, json: job(fake, id, B, 'running') };
  };
  c.ports.sleep = async () => { throw new Error('simulated crash'); };
  let error; try { await ctx.invokeWith(c.ports, words); } catch (e) { error = e; }
  ctx.state.reply = null;
  return error;
}

// K1: a crash leaves a dead mark; the next run retires it at begin and then fails sign-in.
test('TEST-CACHE-K1: sign-in failure after retiring a dead mark', async t => {
  const ctx = await setup(t);
  assert.equal((await ctx.invoke()).sent, 3);
  bump(ctx, 'tests/independent.json'); bump(ctx, 'tests/place-order.json');
  const crash = await crashOnB(ctx, ['independent', 'place-order']);
  assert.match(crash.message, /simulated crash/);
  ctx.state.identity = { ...B };
  const s = round4Other(ctx, 2 * min, { gh: () => ({ status: 1, stdout: '', stderr: 'You are not logged into any GitHub hosts.' }) });
  const signin = await ctx.invokeWith(s.ports, ['independent'], { '--json': false });
  assert.equal(signin.code, 5); assert.equal(signin.sent, 0);
  ctx.clock.now += 5 * min;
  const next = await ctx.invoke(['unknown-item']);
  assert.equal(next.sent, 1, 'the crashed run saw build b; nothing has run since; never reuse build a');
});

// K2: a read that sends a restarted check again is in flight (new job on build b) while another run starts.
test('TEST-CACHE-K2: read that resends, in flight', async t => {
  const ctx = await setup(t);
  assert.equal((await ctx.invoke()).sent, 3);
  bump(ctx, 'tests/place-order.json');
  ctx.state.running = true; const x = await ctx.invoke(['place-order'], { '--timeout': 1 }); ctx.state.running = false;
  const xId = ctx.fake.posts.filter(e => e.command === 'check').at(-1).request.requestId;
  const resent = new Set(); let released = false;
  ctx.state.reply = (id, entry, fake) => {
    if (id === xId) { const j = fake.job(id, 'check', 'unknown', { exitCode: 1, refusals: [{ code: 'service-restarted', message: 'restarted' }], report: { refusal: { code: 'service-restarted' } } }); j.engine_sha = A.engine_sha; j.usage.requested_model = A.requested_model; return { status: 200, json: j }; }
    if (entry.method === 'POST') resent.add(id);
    if (resent.has(id)) return { status: entry.method === 'POST' && !released ? 202 : 200, json: job(fake, id, B, released ? 'passed' : 'running') };
    return null;
  };
  const ro = round4Other(ctx, 5 * min);
  ro.ports.stdout.text = ''; ro.ports.stderr.text = '';
  const readRun = runCheck({ words: [x.json.batch], options: { '--read': true, '--json': true, '--timeout': '60' }, cwd: ctx.repo, cache: true }, ro.ports);
  for (let i = 0; !resent.size && i < 2000; i++) await wait();
  let r;
  try {
    assert.equal(resent.size, 1, 'read resends the restarted job before the concurrent check');
    r = await ctx.invokeWith(round4Other(ctx, 6 * min).ports, ['unknown-item'], { '--timeout': 1 });
  } finally { released = true; assert.equal(await readRun, 0); ctx.state.reply = null; }
  assert.equal(r.sent, 1, 'the read is sending checks and has seen build b; never reuse build a');
});

// K3: --cache-clear while another run is in flight removes that run's live mark.
test('TEST-CACHE-K3: --cache-clear during a run', async t => {
  const ctx = await setup(t);
  assert.equal((await ctx.invoke()).sent, 3);
  bump(ctx, 'tests/independent.json');
  const p = round4Other(ctx, 1000); p.ports.interactive = true;
  const held = new Set(); let phase = 'p', released = false;
  ctx.state.reply = (id, entry, fake) => {
    if (entry.method === 'POST' && phase === 'p') held.add(id);
    if (held.has(id)) return released ? { status: 200, json: job(fake, id, B) } : { status: entry.method === 'POST' ? 202 : 200, json: job(fake, id, B, 'running') };
    return { status: 200, json: job(fake, id, A) };
  };
  const pRun = ctx.invokeWith(p.ports, ['independent']);
  for (let i = 0; !held.size && i < 2000; i++) await wait();
  let r;
  try {
    assert.equal(held.size, 1, 'the other run is still in progress');
    phase = 'q';
    const q = await ctx.invokeWith(round4Other(ctx, 30000).ports, ['place-order'], { '--cache-clear': true });
    assert.equal(q.code, 0); assert.equal(q.sent, 1);
    r = await ctx.invokeWith(round4Other(ctx, 60000).ports, ['place-order']);
  } finally { released = true; await pRun; ctx.state.reply = null; }
  assert.equal(r.sent, 1, 'P is in flight and has seen build b');
});

// Class invariant: inspect the actual cache at every fake-runtime check POST.
function watchSendOwnership(ctx) {
  const violations = [], tokens = new Map(); let expectedPid = null, count = 0;
  ctx.state.onCheckPost = () => {
    count++;
    let marks = [];
    try { marks = JSON.parse(readFileSync(join(ctx.repo, '.pdd/cache/test/stories.json'), 'utf8')).latest_identity?.in_progress ?? []; } catch {}
    const own = marks.find(mark => mark.pid === expectedPid);
    if (!own || !own.token || !Number.isFinite(own.started_at)) violations.push({ post: count, expectedPid, marks });
    else if (tokens.has(expectedPid) && tokens.get(expectedPid) !== own.token) violations.push({ post: count, expectedPid, changedToken: true });
    else tokens.set(expectedPid, own.token);
  };
  let sequence = 0;
  const actor = offset => {
    const pid = 40000 + ++sequence, item = actorPorts(ctx, { pid, isAlive: () => true });
    item.clock.now = ctx.clock.now + offset;
    return { ...item, pid, use: () => { expectedPid = pid; } };
  };
  return { actor, assert: () => { assert.ok(count > 0, 'the scenario actually sent checks'); assert.deepEqual(violations, [], 'every check POST holds the sending run own mark, unchanged until finish'); } };
}
const queueRefusal = (fake, id) => {
  const answer = fake.job(id, 'check', 'refused', { outcome: 'Inconclusive', why: 'No verdict. Queue full.', next_step: 'RETRY LATER',
    refusals: [{ code: 'check-queue-timeout', details: { retryable: true, retry_after: 1 } }],
    report: { dispatch: 'not_started', provider_calls: 0, accounting_complete: true, samples: [] } }, 0);
  answer.accounting_complete = true;
  Object.assign(answer.usage, { known_calls: 0, unknown_calls: 0, accounting_complete: true });
  return answer;
};

for (const path of ['normal', 'read-resend', 'retry', 'recovery', 'reuse-disabled']) test(`TEST-CACHE-R5 every POST owns a mark: ${path}`, async t => {
  const ctx = await setup(t), watched = watchSendOwnership(ctx), a = watched.actor(1000);
  a.use();
  if (path === 'normal' || path === 'reuse-disabled') {
    assert.equal((await ctx.invokeWith(a.ports, [], {}, path !== 'reuse-disabled')).sent, 3);
  } else if (path === 'retry') {
    ctx.state.reply = (id, entry, fake) => entry.method === 'POST' ? { status: 200, json: queueRefusal(fake, id) } : null;
    const first = await ctx.invokeWith(a.ports, ['place-order'], { '--timeout': 1 });
    ctx.state.reply = null;
    const b = watched.actor(5 * min); b.use();
    assert.equal((await ctx.invokeWith(b.ports, [], { '--retry': first.json.batch }, false)).sent, 1);
  } else {
    const original = new Set(); let recover = false;
    ctx.state.reply = (id, entry, fake) => {
      if (entry.method === 'POST' && !original.size) { original.add(id); return { status: 202, json: job(fake, id, A, 'running') }; }
      if (original.has(id)) return { status: 200, json: recover ? fake.job(id, 'check', 'unknown', { exitCode: 1, refusals: [{ code: 'service-restarted', message: 'restarted' }], report: { refusal: { code: 'service-restarted' } } }) : job(fake, id, A, 'running') };
      return { status: 200, json: job(fake, id, B) };
    };
    if (path === 'read-resend') {
      const first = await ctx.invokeWith(a.ports, ['place-order'], { '--timeout': 1 }); assert.equal(first.code, 3);
      recover = true; const b = watched.actor(5 * min); b.use();
      assert.equal((await ctx.invokeWith(b.ports, [first.json.batch], { '--read': true })).code, 0);
    } else {
      recover = true; assert.equal((await ctx.invokeWith(a.ports, ['place-order'])).sent, 2);
    }
  }
  watched.assert();
  const doc = read(join(ctx.repo, '.pdd/cache/test/stories.json'));
  assert.deepEqual(doc.latest_identity.in_progress, [], 'finished sends remove only their own marks');
});

test('TEST-CACHE-L1 retry cannot hide build b during or after its sends', async t => {
  const ctx = await setup(t); assert.equal((await ctx.invoke()).sent, 3); bump(ctx, 'tests/place-order.json');
  ctx.state.reply = (id, entry, fake) => entry.method === 'POST' ? { status: 200, json: queueRefusal(fake, id) } : null;
  const busy = await ctx.invoke(['place-order'], { '--timeout': 1 }); assert.equal(busy.json.rows[0].can_retry, true, 'capacity refusal permits retry');
  const retried = new Set(); let release, released = false; const gate = new Promise(done => { release = () => { released = true; done(); }; });
  ctx.state.reply = (id, entry, fake) => {
    if (entry.method === 'POST' && !retried.size) retried.add(id);
    return { status: entry.method === 'POST' && !released ? 202 : 200, json: job(fake, id, retried.has(id) ? B : A, retried.has(id) && !released ? 'running' : 'passed') };
  };
  const retry = round4Other(ctx, 10 * min); retry.ports.sleep = async ms => { retry.clock.now += ms; await gate; };
  const pending = runCheck({ cwd: ctx.repo, words: [], options: { '--retry': busy.json.batch, '--json': true }, cache: true }, retry.ports);
  let during;
  try {
    for (let i = 0; !retried.size && i < 2000; i++) await wait();
    assert.equal(retried.size, 1, 'the retry is in flight');
    bump(ctx, 'tests/independent.json');
    assert.equal((await ctx.invokeWith(round4Other(ctx, 11 * min).ports, ['independent'])).sent, 1);
    during = await ctx.invokeWith(round4Other(ctx, 12 * min).ports, ['unknown-item']);
  } finally { release(); assert.equal(await pending, 0); ctx.state.reply = null; }
  const after = await ctx.invokeWith(round4Other(ctx, 20 * min).ports, ['unknown-item']);
  assert.deepEqual([during.sent, after.sent], [1, 1], 'never reuse build a while or after retry observes build b');
});
