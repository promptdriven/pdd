import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { existsSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { exitCodeFor } from '../src/runtime-output.mjs';
import { PLACE, TOKEN, fakeRuntime, filesUnder, harbor, portsFor, sha } from './runtime-fake.mjs';

async function check(setup, fake, words = [], options = {}, extra = {}) {
  const { ports, clock } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }, extra);
  const code = await runCheck({ words, options, cwd: setup.repo }, ports);
  return { code, clock, out: ports.stdout.text, err: ports.stderr.text, json: options['--json'] ? JSON.parse(ports.stdout.text) : null,
    batch: /pdd check --read (\d{8}-\d{6}-[a-z0-9]{4})/.exec(ports.stderr.text)?.[1] };
}
const batchFile = (setup, batch) => JSON.parse(readFileSync(join(setup.state, 'batches', batch, 'batch.json'), 'utf8'));

// Wrong: checks go one by one, before lint, or with different sources (RESULT.md issue 13, spec 7.3-7.4).
test('RUNTIME-SERVER1: one lint, then every check is sent before the first answer, with one source_sha256', async t => {
  const setup = harbor(t);
  let release, held = 0;
  const allSent = new Promise(done => { release = done; });
  const fake = await fakeRuntime(t, async (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'check') {
      held += 1;
      if (held === 2) release();
      await Promise.race([allSent, new Promise(done => setTimeout(done, 5000))]);
    }
    return f.normal(entry);
  });
  const result = await check(setup, fake);
  assert.equal(result.code, 0, result.err + result.out);
  assert.deepEqual(fake.posts.map(post => post.command), ['lint', 'check', 'check']);
  assert.equal(held, 2);
  const [lint, ...checks] = fake.posts;
  assert.deepEqual(Object.keys(lint.request).sort(), ['requestId', 'source_sha256']);
  assert.deepEqual(checks.map(post => post.request.scenario).sort(), ['tests/place-order.json', 'tests/unknown-item.json']);
  for (const post of fake.posts) { assert.equal(post.request.source_sha256, sha(post.tar)); assert.ok(post.tar.equals(lint.tar)); }
  assert.deepEqual(checks.map(post => post.request.max_calls), [4, 4]);
  assert.equal(new Set(fake.posts.map(post => post.request.requestId)).size, 3);
  assert.deepEqual([...fake.authorization], [`Bearer ${TOKEN}`]);
  assert.match(result.err, /Lint passed\. Sent 2 checks \(6 files, \d+ KB\) at \d\d:\d\d:\d\d\./);
  assert.match(result.out, /^Place a coffee order +tests\/place-order\.json +passed +1\/1 +2\.0 s$/m);
  assert.match(result.out, /^Runtime check: 2 of 2 stories passed\. AI calls: 2\. Model asked for: gpt-6\.1-sol\.$/m);
  assert.match(result.out, /^Reports \(anyone with a link can open it\):\n {2}place-order +http:\/\/127\.0\.0\.1:\d+\/r\/[0-9a-f]+$/m);
  assert.doesNotMatch(result.out + result.err, new RegExp(checks[0].request.requestId));
});

// Wrong: a lost answer is resent (a second run with AI calls) instead of read with the same ID.
test('RUNTIME-SERVER2: a lost connection after a POST is read with the same ID and never posted again', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'check' ? { destroy: true } : f.normal(entry));
  const result = await check(setup, fake, ['place-order']);
  assert.equal(result.code, 0, result.err + result.out);
  assert.equal(fake.posts.filter(post => post.command === 'check').length, 1);
  assert.deepEqual(fake.gets.map(get => get.url), [`/v1/runs/${fake.posts[1].request.requestId}`]);
  const missing = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'check' ? { destroy: true }
    : entry.method === 'GET' ? { status: 404, json: { error: { code: 'not-found', message: 'The requested run or session was not found.' } } } : f.normal(entry));
  const lost = await check(setup, missing, ['place-order'], {}, {});
  assert.equal(lost.code, 3);
  assert.equal(missing.posts.filter(post => post.command === 'check').length, 1);
  assert.ok(missing.gets.length > 100 && missing.gets.every(get => get.url === `/v1/runs/${missing.posts[1].request.requestId}`));
  assert.equal(lost.out.split('\n')[0], `pdd check --read ${lost.batch}`);
  assert.match(lost.out, /UNKNOWN {2}Place a coffee order: the run may have executed\. Its result is unknown\./);
});

// Wrong: a busy server makes pdd give up, resend the same ID, or forget the first ID (spec 7, OPEN 2).
test('RUNTIME-SERVER3: 429 server-full gives a new ID after Retry-After and keeps the old one', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'check' && f.posts.filter(p => p.command === 'check').length === 1
    ? { status: 429, headers: { 'retry-after': '3' }, json: { requestId: entry.request.requestId, command: 'check', state: 'refused', job_created: true,
      dispatch: 'not_started', error: { code: 'server-full', message: 'The runtime is busy. Try again later.' } } } : f.normal(entry));
  const result = await check(setup, fake, ['place-order']);
  assert.equal(result.code, 0, result.err + result.out);
  const checks = fake.posts.filter(post => post.command === 'check');
  assert.equal(checks.length, 2); assert.notEqual(checks[0].request.requestId, checks[1].request.requestId);
  assert.match(result.err, /Server busy: 0 checks running, 1 waiting for a free slot\./);
  const saved = batchFile(setup, result.batch);
  assert.deepEqual(saved.rows[0].request_ids, checks.map(post => post.request.requestId));
  for (const post of checks) assert.ok(existsSync(join(setup.state, 'batches', result.batch, `${post.request.requestId}.posted`)));
});

// Wrong: no AI room, the gate or a bad token is retried or looks like a failed check.
test('RUNTIME-SERVER4: 503 pool-low-room, the gate and 401 are not run (exit 5) with no new attempt', async t => {
  const setup = harbor(t);
  const cases = [
    [{ status: 503, json: { requestId: null, command: 'check', state: 'refused', job_created: true, dispatch: 'not_started',
      error: { code: 'pool-low-room', message: 'The runtime model account has too little room for this job. Try again later.' } } },
    /NOT RUN {2}Place a coffee order \(tests\/place-order\.json\): The runtime model account has too little room for this job\. Try again later\. \(pool-low-room\)/],
    [{ status: 503, text: 'The runtime opens soon.' }, /The runtime opens soon\./],
    [{ status: 401, json: { error: { code: 'auth-invalid', message: 'Your GitHub token is invalid. Sign in again.' } } }, /Run gh auth login/],
  ];
  for (const [reply, pattern] of cases) {
    const fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'check' ? reply : f.normal(entry));
    const result = await check(setup, fake, ['place-order']);
    assert.equal(result.code, 5, result.err + result.out);
    assert.equal(fake.posts.filter(post => post.command === 'check').length, 1); assert.equal(fake.gets.length, 0);
    assert.match(result.out + result.err, pattern);
  }
});

// Wrong: --read sends work or makes new IDs; Ctrl-C loses the batch or exits as if it passed (spec 7, A5).
test('RUNTIME-SERVER5: Ctrl-C prints the read line and exits 3; --read then GETs only and makes no ID', async t => {
  const setup = harbor(t);
  let finished = false, interrupt;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'GET') {
      if (!finished) { interrupt(); return { status: 200, json: f.check(entry.url.split('/').at(-1), 'running') }; }
      return { status: 200, json: f.check(entry.url.split('/').at(-1), 'failed', [{ criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'equals', expected: 899, actual: 900, passed: false }]) };
    }
    return f.normal(entry);
  });
  const { ports, clock } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  interrupt = () => clock.interrupt?.();
  const code = await runCheck({ words: ['place-order'], options: {}, cwd: setup.repo }, ports);
  assert.equal(code, 3);
  const batch = /pdd check --read (\S+)/.exec(ports.stderr.text)[1];
  assert.equal(ports.stdout.text.split('\n')[0], `pdd check --read ${batch}`);
  assert.match(ports.stdout.text, /STILL RUNNING after 10 min: Place a coffee order\. Do not send it again\./);
  finished = true;
  const posts = fake.posts.length;
  const read = await check(setup, fake, [batch], { '--read': true });
  assert.equal(read.code, 1, read.err + read.out); assert.equal(fake.posts.length, posts); assert.equal(read.clock.uuids, 0);
  assert.match(read.out, /FAILED {2}Place a coffee order \(tests\/place-order\.json\)\n {2}AC1 {2}result \/totalCents {2}expected 899, got 900/);
  const last = await check(setup, fake, [], { '--read': true, '--json': true });
  assert.equal(last.code, 1); assert.equal(last.json.batch, batch); assert.equal(fake.posts.length, posts); assert.equal(last.clock.uuids, 0);
  assert.equal(last.json.rows[0].request_id, fake.posts[1].request.requestId);
  const other = await check(setup, fake, [batch], { '--read': true }, { gh: args => args[0] === 'auth' ? { status: 0, stdout: TOKEN } : { status: 0, stdout: 'someone 7\n' } });
  assert.equal(other.code, 5); assert.match(other.err, /These runs belong to octo\. Run: gh auth switch -u octo/);
});

// Wrong: precedence lets a failure hide an unknown run, or a mismatched answer counts as a result.
test('RUNTIME-SERVER6: exit precedence 3 > 5 > 4 > 1 > 0, and a wrong ID or command is unknown (3)', async t => {
  const rows = states => states.map(state => ({ state }));
  assert.equal(exitCodeFor(rows(['passed', 'failed', 'refused', 'not_run', 'running'])), 3);
  assert.equal(exitCodeFor(rows(['passed', 'failed', 'refused', 'not_run'])), 5);
  assert.equal(exitCodeFor(rows(['passed', 'failed', 'refused'])), 4);
  assert.equal(exitCodeFor(rows(['passed', 'failed'])), 1);
  assert.equal(exitCodeFor(rows(['passed'])), 0);
  assert.equal(exitCodeFor(rows(['passed']), { interrupted: true }), 3);
  const setup = harbor(t);
  for (const wrong of [json => ({ ...json, requestId: randomUUID(), id: randomUUID() }), json => ({ ...json, command: 'try' })]) {
    const fake = await fakeRuntime(t, (entry, f) => {
      const reply = f.normal(entry);
      return entry.method === 'POST' && entry.command === 'check' ? { ...reply, json: wrong(reply.json) } : entry.method === 'GET' ? { status: 200, json: wrong(f.check(entry.url.split('/').at(-1))) } : reply;
    });
    const result = await check(setup, fake, ['place-order']);
    assert.equal(result.code, 3, result.out); assert.equal(fake.posts.filter(post => post.command === 'check').length, 1);
  }
});

// Wrong: the token reaches a file or the terminal, or state is readable by others or kept in the repo.
test('RUNTIME-SERVER7: the token is in no state file and no output; folders are 0700 and files 0600 outside the repo', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET'
    ? { status: 200, json: { ...f.check(entry.url.split('/').at(-1), 'refused', [], [{ code: 'invalid-input', section: 'steps[0].input.items[0].quantity',
      message: 'The runtime refused this job. See the reported reason.', engine_message: `invalid-input at /srv/runtime/jobs/x token ${TOKEN}` }]) } } : f.normal(entry));
  const text = await check(setup, fake, ['place-order']);
  const json = await check(setup, fake, ['place-order'], { '--json': true });
  assert.equal(text.code, 4); assert.equal(json.code, 4);
  assert.match(text.out, /REFUSED {2}Place a coffee order \(tests\/place-order\.json\)\n {2}invalid-input {2}steps\[0\]\.input\.items\[0\]\.quantity {2}The runtime refused this job\. See the reported reason\.\n {2}engine: invalid-input at <server path> token \[secret\]/);
  for (const output of [text.out, text.err, json.out, json.err]) assert.equal(output.includes(TOKEN), false);
  assert.equal(json.json.rows[0].refusals[0].code, 'invalid-input');
  for (const path of [setup.state, ...filesUnder(setup.state)]) {
    const stat = statSync(path);
    assert.equal(stat.mode & 0o777, stat.isDirectory() ? 0o700 : 0o600, path);
    if (stat.isFile()) assert.equal(readFileSync(path, 'utf8').includes(TOKEN), false, path);
  }
  assert.ok(filesUnder(setup.state).some(path => path.endsWith('summary.json')));
  assert.equal(spawnSync('git', ['status', '--porcelain'], { cwd: setup.repo, encoding: 'utf8' }).stdout, '');
  assert.ok(text.clock.gh.every(args => !args.join(' ').includes(TOKEN)));
});

// Wrong: a test that reaches a draft or refused prompt is sent anyway, or lint unknown still sends checks.
test('RUNTIME-SERVER8: lint refuses tests that reach a bad prompt; unknown lint sends no checks', async t => {
  const setup = harbor(t);
  const draft = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'lint'
    ? { status: 200, json: f.lint(entry.request.requestId, [{ path: PLACE, state: 'approved', admission_state: 'approved', interface: { calls: [{ target: 'prompts/menu.prompt.md' }] } },
      { path: 'prompts/menu.prompt.md', state: 'draft', admission_state: 'draft', interface: { calls: [] } }]) } : f.normal(entry));
  const refused = await check(setup, draft, [], { '--json': true });
  assert.equal(refused.code, 4); assert.deepEqual(draft.posts.map(post => post.command), ['lint']);
  assert.deepEqual(refused.json.rows.map(row => row.refusals[0].code), ['interface-unapproved', 'interface-unapproved']);
  assert.equal(refused.json.rows[0].refusals[0].hint, 'pdd: prompts/menu.prompt.md is "draft". The person must approve it first.');
  const lost = await fakeRuntime(t, entry => entry.method === 'POST' ? { destroy: true } : { status: 404, json: { error: { code: 'not-found' } } });
  const unknown = await check(setup, lost, []);
  assert.equal(unknown.code, 3); assert.deepEqual(lost.posts.map(post => post.command), ['lint']);
  assert.match(unknown.out, /^pdd check --read /);
});

// Wrong: a failed check is shown as raw JSON, or without the criterion, expected and got values (issue 10).
test('RUNTIME-SERVER9: a failed check shows one line per failed check, the warning, the report and the next step', async t => {
  const setup = harbor(t, repo => {
    const file = join(repo, 'tests/place-order.json'), doc = JSON.parse(readFileSync(file, 'utf8'));
    doc.steps[0].checks[0].value = 899; writeFileSync(file, JSON.stringify(doc));
  });
  const failed = [{ criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'equals', expected: 899, actual: 900, passed: false },
    { criterion_id: 'AC2', target: 'result', path: '/customerName', op: 'equals', expected: 'Sam', actual: 'Sam', passed: true }];
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET' ? { status: 200, json: f.check(entry.url.split('/').at(-1), 'failed', failed) } : f.normal(entry));
  const result = await check(setup, fake, ['place-order'], { '--details': true });
  assert.equal(result.code, 1, result.err);
  const lines = result.out.split('\n');
  const at = lines.indexOf('FAILED  Place a coffee order (tests/place-order.json)');
  assert.deepEqual(lines.slice(at + 1, at + 3), ['  AC1  result /totalCents  expected 899, got 900', '  Warning: the AC1 check expects 899, but the AC1 text says 900.']);
  assert.match(lines[at + 3], /^ {2}Report: http:\/\/127\.0\.0\.1:\d+\/r\/\w+ {3}Next: show the person this check\. Do not change the expected value yourself\.$/);
  assert.deepEqual(lines.slice(lines.indexOf('Checks for Place a coffee order (tests/place-order.json):') + 1).slice(0, 2),
    ['  failed  AC1  result /totalCents  expected 899, got 900', '  passed  AC2  result /customerName  expected "Sam", got "Sam"']);
});
