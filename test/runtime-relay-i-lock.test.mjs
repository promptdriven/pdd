import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, portsFor, fakeRuntime } from './runtime-fake.mjs';

const read = path => JSON.parse(readFileSync(path, 'utf8'));
const deferred = () => { let resolve; const promise = new Promise(done => { resolve = done; }); return { promise, resolve }; };
async function bounded(promise, label) {
  let timer;
  try { return await Promise.race([promise, new Promise((_, reject) => { timer = setTimeout(() => reject(new Error(`Timed out: ${label}`)), 5000); })]); }
  finally { clearTimeout(timer); }
}
const CLAIMED = '99999999-9999-4999-8999-999999999999';

async function heldBatch(t) {
  const h = harbor(t), entered = deferred(), resume = deferred();
  t.after(() => resume.resolve());
  const state = { passed: false, hold: false };
  const fake = await fakeRuntime(t, async (entry, f) => {
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    if (entry.command === 'lint') return { status: 202, json: f.job(id, 'lint', 'running') };
    const lint = f.posts.find(post => post.command === 'lint')?.request.requestId;
    if (id === lint) {
      if (state.hold) { state.hold = false; entered.resolve(); await bounded(resume.promise, 'release lint refresh'); }
      return { status: 200, json: state.passed ? f.lint(id) : f.job(id, 'lint', 'running') };
    }
    if (id === CLAIMED) return { status: 404, json: {} };
    const answer = f.check(id); answer.usage.calls = 4;
    return { status: 200, json: answer };
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: fake.origin };
  const first = portsFor(env);
  assert.equal(await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--json': true, '--timeout': '0.01', '--max-calls': 6 } }, first.ports), 3);
  assert.equal(fake.posts.filter(post => post.command === 'check').length, 0);
  const batches = readdirSync(join(h.state, 'batches'), { withFileTypes: true }).filter(entry => entry.isDirectory());
  assert.equal(batches.length, 1);
  const batch = batches[0].name, folder = join(h.state, 'batches', batch), file = join(folder, 'batch.json');
  const saved = read(file);
  assert.equal(saved.intent, 'check'); assert.equal(saved.rows[0].phase, 'lint');
  assert.deepEqual(saved.rows[0].request_ids, []); assert.equal(saved.rows[0].calls, 0);
  state.passed = true; state.hold = true;
  return { h, fake, env, state, batch, folder, file, entered, resume };
}

function worker(t, r, retry) {
  const source = `import {runCheck} from ${JSON.stringify(new URL('../src/runtime-client.mjs', import.meta.url).href)};
    import {portsFor} from ${JSON.stringify(new URL('./runtime-fake.mjs', import.meta.url).href)};
    const {ports}=portsFor(${JSON.stringify(r.env)});
    const code=await runCheck(${JSON.stringify({ cwd: r.h.repo, words: retry ? [] : [r.batch], options: { '--json': true, [retry ? '--retry' : '--read']: retry ? r.batch : true } })},ports);
    process.stdout.write(ports.stdout.text); process.stderr.write(ports.stderr.text); process.exitCode=code;`;
  const child = spawn(process.execPath, ['--input-type=module', '-e', source], { stdio: ['ignore', 'pipe', 'pipe'] });
  t.after(() => { if (child.exitCode === null) child.kill('SIGKILL'); });
  let out = '', err = '';
  child.stdout.on('data', chunk => { out += chunk; }); child.stderr.on('data', chunk => { err += chunk; });
  const done = new Promise((resolve, reject) => {
    child.on('error', reject);
    child.on('close', code => { try { resolve({ code, out, err, json: out ? JSON.parse(out) : null }); } catch (error) { reject(error); } });
  });
  return { child, done };
}

async function refuseCompetitor(t, r, retry) {
  const bytes = readFileSync(r.file), summaryPath = join(r.folder, 'summary.json');
  const summary = existsSync(summaryPath) ? readFileSync(summaryPath) : null;
  const posts = r.fake.posts.length, gets = r.fake.gets.length;
  const second = await bounded(worker(t, r, retry).done, 'competing process');
  assert.equal(second.code, 3, second.err); assert.equal(second.out, '');
  assert.match(second.err, /pdd check --read/);
  assert.equal(r.fake.posts.length, posts); assert.equal(r.fake.gets.length, gets);
  assert.deepEqual(readFileSync(r.file), bytes);
  assert.deepEqual(existsSync(summaryPath) ? readFileSync(summaryPath) : null, summary);
}

test('RELAY-I b: a held-for-lint retry owns the batch before refresh and refuses a second process', { timeout: 15000 }, async t => {
  const r = await heldBatch(t), owner = worker(t, r, true); let result;
  try {
    await bounded(r.entered.promise, 'owner lint refresh');
    const lock = join(r.folder, 'batch.lock');
    assert.ok(existsSync(lock), 'saved-lint continuation must run inside native batch ownership');
    assert.equal(read(lock).pid, owner.child.pid);
    await refuseCompetitor(t, r, true);
  } finally { r.resume.resolve(); result = await bounded(owner.done, 'owner continuation'); }
  assert.equal(result.code, 0, result.err);
  const posts = r.fake.posts.filter(post => post.command === 'check');
  assert.equal(posts.length, 1); assert.equal(posts[0].request.max_calls, 6);
  const saved = read(r.file);
  assert.deepEqual(saved.rows[0].request_ids, [posts[0].request.requestId]);
  assert.equal(result.json.rows[0].state, 'passed'); assert.equal(result.json.rows[0].calls, 4);
  assert.equal(saved.source_sha256, posts[0].request.source_sha256);
  assert.equal(r.fake.posts.filter(post => post.command === 'lint').length, 1);
  assert.equal(existsSync(join(r.folder, 'batch.lock')), false);
});

test('RELAY-I c: the lock owner adopts a claim, clears busy retry advice and refuses another reader', { timeout: 15000 }, async t => {
  const r = await heldBatch(t), saved = read(r.file), row = saved.rows[0];
  Object.assign(row, { busy: true, can_retry: true, why: 'This check was never sent.', next_step: 'Retry now.' });
  writeFileSync(r.file, JSON.stringify(saved));
  const key = createHash('sha256').update(row.test).digest('hex');
  writeFileSync(join(r.folder, `${key}.0.dispatch.json`), JSON.stringify({ id: CLAIMED }));
  const owner = worker(t, r, true); let result;
  try {
    await bounded(r.entered.promise, 'owner claim recovery');
    assert.equal(read(join(r.folder, 'batch.lock')).pid, owner.child.pid);
    await refuseCompetitor(t, r, false);
  } finally { r.resume.resolve(); result = await bounded(owner.done, 'owner claim result'); }
  assert.equal(result.code, 3, result.err);
  const out = result.json.rows[0];
  assert.equal(out.request_id, CLAIMED); assert.equal(out.state, 'unknown'); assert.equal(out.calls, 'unknown');
  assert.equal(out.busy, false); assert.equal(out.can_retry, false); assert.equal(out.next_step, null);
  assert.notEqual(out.why, 'This check was never sent.');
  assert.equal(r.fake.posts.filter(post => post.command === 'check').length, 0, 'an uncertain claimed check must never be replayed');
  assert.ok(r.fake.gets.some(get => get.url.endsWith(CLAIMED)));
  const kept = read(r.file).rows[0];
  assert.deepEqual(kept.request_ids, [CLAIMED]); assert.equal(kept.busy, false); assert.equal(kept.can_retry, false);
  assert.equal(readdirSync(r.folder).filter(name => name.endsWith('.dispatch.json')).length, 1);
  assert.equal(existsSync(join(r.folder, 'batch.lock')), false);
});
