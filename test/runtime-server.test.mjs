import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { existsSync, readFileSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { exitCodeFor } from '../src/runtime-output.mjs';
import { PLACE, TOKEN, fakeRuntime, filesUnder, harbor, portsFor, root, sha } from './runtime-fake.mjs';

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
  assert.deepEqual(checks.map(post => post.request.max_calls), [6, 6]);
  assert.equal(new Set(fake.posts.map(post => post.request.requestId)).size, 3);
  assert.deepEqual([...fake.authorization], [`Bearer ${TOKEN}`]);
  assert.match(result.err, /Lint passed\. Sent 2 checks \(6 files, \d+ KB\) at \d\d:\d\d:\d\d\./);
  assert.match(result.err, /^Warning: 1 of the 6 files sent are not prompt, story or test files\. Run pdd check --files to see them\.$/m);
  assert.match(result.out, /^Place a coffee order +tests\/place-order\.json +passed +1\/1 +2\.0 s$/m);
  assert.equal(result.out.split('\n')[3], 'Runtime check: ✓ 2 of 2 criteria · 2/2 checks · 2 AI calls');
  assert.match(result.out, /^2 of 2 stories passed\. Model asked for: gpt-6\.1-sol\.$/m);
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
  assert.match(ports.stdout.text, /STILL RUNNING when pdd stopped reading: Place a coffee order\. Do not send it again\./);
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
      { path: 'prompts/menu.prompt.md', state: 'stale', admission_state: 'stale', interface: { calls: [] } }]) } : f.normal(entry));
  const refused = await check(setup, draft, [], { '--json': true });
  assert.equal(refused.code, 4); assert.deepEqual(draft.posts.map(post => post.command), ['lint']);
  assert.deepEqual(refused.json.rows.map(row => row.refusals[0].code), ['interface-stale', 'interface-stale']);
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

// Wrong: pdd waits forever, or calls a still-running check failed or done at the timeout.
test('RUNTIME-SERVER10: at --timeout an open check is still running (exit 3) and was read every 2 s', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET' ? { status: 200, json: f.check(entry.url.split('/').at(-1), 'running') } : f.normal(entry));
  const result = await check(setup, fake, ['place-order'], { '--timeout': '1' });
  assert.equal(result.code, 3);
  assert.match(result.out, /^Place a coffee order +tests\/place-order\.json +running +- +-$/m);
  assert.match(result.out, /STILL RUNNING after 1 min: Place a coffee order\. Do not send it again\./);
  assert.match(result.out, /^Runtime check: ✗ 0 of 3 criteria · 0\/0 checks · 1 running · 0 AI calls \+ 1 unknown$/m);
  assert.ok(fake.gets.length >= 28 && fake.gets.length <= 31, String(fake.gets.length));
  assert.equal(fake.posts.length, 2);
});

// Wrong: a 429 with no Retry-After header is retried at once, again and again (it must wait 5 s).
test('RUNTIME-SERVER11: 429 with no Retry-After waits 5 s before the new request ID', async t => {
  const setup = harbor(t), times = [];
  let clock;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'check') {
      times.push(clock.now);
      if (times.length === 1) return { status: 429, json: { dispatch: 'not_started', error: { code: 'server-full', message: 'The runtime is busy. Try again later.' } } };
    }
    return f.normal(entry);
  });
  const made = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  clock = made.clock;
  assert.equal(await runCheck({ words: ['place-order'], options: {}, cwd: setup.repo }, made.ports), 0, made.ports.stderr.text);
  assert.equal(times.length, 2); assert.ok(times[1] - times[0] >= 5000, String(times[1] - times[0]));
});

// Wrong: a pdd that was killed mid-send leaves rows that --read shows as passed (exit 0) or never reads.
test('RUNTIME-SERVER12: --read reads a posted row with no saved answer, and a row never sent is not run', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const first = await check(setup, fake, ['place-order']);
  assert.equal(first.code, 0);
  const folder = join(setup.state, 'batches', first.batch), saved = JSON.parse(readFileSync(join(folder, 'batch.json'), 'utf8'));
  const id = saved.rows[0].request_ids[0], gets = fake.gets.length;
  rmSync(join(folder, `${id}.json`));
  saved.rows[0].state = 'sending';
  writeFileSync(join(folder, 'batch.json'), JSON.stringify(saved));
  const read = await check(setup, fake, [], { '--read': true });
  assert.equal(read.code, 0, read.out); assert.equal(fake.gets.length, gets + 1); assert.equal(fake.gets.at(-1).url, `/v1/runs/${id}`);
  saved.rows[0] = { ...saved.rows[0], state: 'ready', request_ids: [] };
  writeFileSync(join(folder, 'batch.json'), JSON.stringify(saved));
  const never = await check(setup, fake, [], { '--read': true });
  assert.equal(never.code, 5); assert.match(never.out, /NOT RUN {2}Place a coffee order \(tests\/place-order\.json\): pdd stopped before sending this check\./);
  assert.equal(exitCodeFor([{ state: 'ready' }]), 3); assert.equal(exitCodeFor([{ state: 'sending' }, { state: 'failed' }]), 3);
});

// Wrong: after Ctrl-C pdd still posts the waiting check with a new ID.
test('RUNTIME-SERVER13: no POST starts after Ctrl-C, even for a check that waits after a 429', async t => {
  const setup = harbor(t);
  let interrupt;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.request.scenario === 'tests/place-order.json') {
      return { status: 429, headers: { 'retry-after': '1' }, json: { dispatch: 'not_started', error: { code: 'server-full', message: 'busy' } } };
    }
    if (entry.method === 'GET') { interrupt(); return { status: 200, json: f.check(entry.url.split('/').at(-1), 'running') }; }
    return f.normal(entry);
  });
  const { ports, clock } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  interrupt = () => clock.interrupt?.();
  assert.equal(await runCheck({ words: [], options: {}, cwd: setup.repo }, ports), 3);
  assert.equal(fake.posts.filter(post => post.command === 'check').length, 2);
  assert.match(ports.stdout.text, /NOT RUN {2}Place a coffee order \(tests\/place-order\.json\)/);
});

// Wrong: the token reaches --json through an expected or actual value that a server echoed.
test('RUNTIME-SERVER14: --json output and saved answers never hold the token, even inside check values', async t => {
  const setup = harbor(t);
  const echo = [{ criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'equals', expected: 900, actual: { note: `token ${TOKEN}` }, passed: false }];
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET' ? { status: 200, json: f.check(entry.url.split('/').at(-1), 'failed', echo) } : f.normal(entry));
  const result = await check(setup, fake, ['place-order'], { '--json': true });
  assert.equal(result.code, 1);
  assert.equal(result.out.includes(TOKEN), false);
  assert.deepEqual(result.json.rows[0].failed_checks[0].actual, { note: 'token [secret]' });
  for (const path of filesUnder(setup.state)) if (statSync(path).isFile()) assert.equal(readFileSync(path, 'utf8').includes(TOKEN), false, path);
});

// Wrong: the runtime runs a newer engine and nobody notices that pdd's local rules may now differ (OPEN 9).
test('RUNTIME-SERVER15: an answer from another engine build gives a warning', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET' ? { status: 200, json: { ...f.check(entry.url.split('/').at(-1)), engine_sha: 'eae2202a0123456789' } } : f.normal(entry));
  const result = await check(setup, fake, ['place-order']);
  assert.equal(result.code, 0);
  assert.match(result.out, /Warning: the runtime engine is eae2202a0123, but pdd's local checks copy engine 7b03d3ea\. The engine stays the judge\./);
  const same = await check(setup, await fakeRuntime(t, (entry, f) => f.normal(entry)), ['place-order']);
  assert.doesNotMatch(same.out, /runtime engine is/);
});

// Wrong: the PR line hides a failure, or --json lacks the line an agent pastes (Serhan, Oct 27).
test('RUNTIME-SERVER16: one pasteable summary line with ✓ or ✗, also as summary_line in --json', async t => {
  const setup = harbor(t);
  const failed = [{ criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'equals', expected: 899, actual: 900, passed: false },
    { criterion_id: 'AC2', target: 'result', path: '/customerName', op: 'equals', expected: 'Sam', actual: 'Sam', passed: true }];
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method !== 'GET') return f.normal(entry);
    const id = entry.url.split('/').at(-1), place = f.posts.find(post => post.request.requestId === id).request.scenario === 'tests/place-order.json';
    return { status: 200, json: place ? f.check(id, 'failed', failed) : f.check(id) };
  });
  const text = await check(setup, fake, []);
  assert.equal(text.code, 1);
  assert.equal(text.out.split('\n')[3], 'Runtime check: ✗ 2 of 3 criteria · 2/3 checks · 2 AI calls');
  const json = await check(setup, fake, [], { '--json': true });
  assert.equal(json.json.summary_line, 'Runtime check: ✗ 2 of 3 criteria · 2/3 checks · 2 AI calls');
  const refused = harbor(t, repo => {
    const file = join(repo, 'tests/place-order.json'), doc = JSON.parse(readFileSync(file, 'utf8'));
    doc.steps[0].input.items[0].quantity = 0; writeFileSync(file, JSON.stringify(doc));
  });
  const mixed = await check(refused, await fakeRuntime(t, (entry, f) => f.normal(entry)), [], { '--json': true });
  assert.equal(mixed.code, 4); assert.equal(mixed.json.summary_line, 'Runtime check: ✗ 1 of 4 criteria · 1/1 checks · 1 refused · 1 AI call');
});

// Wrong: the runtime address is written in more than one place, so a move needs many edits (Serhan, Oct 27).
test('RUNTIME-ADDRESS1: the runtime address is in one place only, and PDD_RUNTIME_URL overrides it', async () => {
  const { DEFAULT_RUNTIME_URL, runtimeOrigin } = await import('../src/runtime-client.mjs');
  const host = new URL(DEFAULT_RUNTIME_URL).host;
  // This test names the hosts on purpose; every other tracked file must not.
  const others = ['--', '.', ':!test/runtime-server.test.mjs'];
  const hits = spawnSync('git', ['grep', '-n', '-F', host, ...others], { cwd: root, encoding: 'utf8' }).stdout.trim().split('\n').filter(Boolean);
  assert.deepEqual(hits.map(hit => hit.split(':')[0]), ['src/runtime-client.mjs']);
  assert.equal(DEFAULT_RUNTIME_URL, 'https://runtime.promptdriven.ai');
  assert.equal(spawnSync('git', ['grep', '-n', '-e', 'sslip', '-e', '34-72-131-98', ...others], { cwd: root, encoding: 'utf8' }).stdout, '');
  assert.equal(runtimeOrigin({}), DEFAULT_RUNTIME_URL);
  assert.equal(runtimeOrigin({ PDD_RUNTIME_URL: 'https://runtime.example' }), 'https://runtime.example');
  for (const bad of ['http://runtime.example', 'https://u:p@runtime.example', 'https://runtime.example/v1', 'ftp://x']) assert.throws(() => runtimeOrigin({ PDD_RUNTIME_URL: bad }), bad);
});

// Wrong: --read of a running row claims it ran for the full timeout.
test('RUNTIME-SERVER17: --read of a still-running row names no wait time', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET' ? { status: 200, json: f.check(entry.url.split('/').at(-1), 'running') } : f.normal(entry));
  const first = await check(setup, fake, ['place-order'], { '--timeout': '1' });
  assert.equal(first.code, 3);
  const read = await check(setup, fake, [], { '--read': true });
  assert.equal(read.code, 3); assert.match(read.out, /^STILL RUNNING: Place a coffee order\. Do not send it again\.$/m);
});

const NOT_STARTED = { requestId: null, command: 'check', state: 'refused', job_created: false, dispatch: 'not_started', error: { code: 'not-found', message: 'The requested run or session was not found.' } };

// Wrong: under load the POST times out and the job appears minutes later; pdd stops reading too soon or calls the 404 a refusal.
test('RUNTIME-SERVER18: after a POST timeout pdd reads the same ID for at least 5 min, and a 404 "refused" body is not a refusal', async t => {
  const setup = harbor(t);
  let clock, lostAt = null;
  const slow = (appearAfter) => async (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'check') { await new Promise(done => setTimeout(done, 600)); return f.normal(entry); }
    if (entry.method === 'GET') {
      lostAt ??= clock.now;
      if (appearAfter === null || clock.now - lostAt < appearAfter) return { status: 404, json: NOT_STARTED };
      return { status: 200, json: f.check(entry.url.split('/').at(-1)) };
    }
    return f.normal(entry);
  };
  const run = async (fake, options) => {
    const made = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }, { postMs: 150 });
    clock = made.clock; lostAt = null;
    const code = await runCheck({ words: ['place-order'], options, cwd: setup.repo }, made.ports);
    return { code, out: made.ports.stdout.text };
  };
  const late = await fakeRuntime(t, slow(220_000));
  const appeared = await run(late, { '--timeout': '1' });
  assert.equal(appeared.code, 0, appeared.out);
  assert.equal(late.posts.filter(post => post.command === 'check').length, 1);
  assert.ok(late.gets.every(get => get.url === `/v1/runs/${late.posts[1].request.requestId}`));
  const never = await fakeRuntime(t, slow(null));
  const lost = await run(never, { '--timeout': '1' });
  assert.equal(lost.code, 3);
  assert.ok(never.gets.length >= 149, String(never.gets.length));
  assert.match(lost.out, /^Place a coffee order +tests\/place-order\.json +unknown/m);
  assert.doesNotMatch(lost.out, /refused/);
});

// Wrong: an AI provider failure looks like a failed check, or pdd resends it by itself.
test('RUNTIME-SERVER19: a provider failure gets its own UNKNOWN block, exit 3 and no new POST', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method !== 'GET') return f.normal(entry);
    const id = entry.url.split('/').at(-1);
    return { status: 200, json: { ...f.job(id, 'check', 'unknown', { outcome: 'Inconclusive', exitCode: 3, why: 'The run may have executed. Its result is unknown. Read this request; do not resubmit.',
      refusals: [{ code: 'graph-provider-failure', message: 'The runtime refused this job. See the reported reason.', engine_message: 'step execution refused', section: 'samples[0].steps[0]' }],
      report: { samples: [{ sample: 1, refusal: { code: 'graph-provider-failure', failure_cause: { kind: 'transport_unknown', detail: 'internal-retry' } } }] } }, 3) } };
  });
  const result = await check(setup, fake, ['place-order']);
  assert.equal(result.code, 3);
  assert.match(result.out, /^UNKNOWN {2}Place a coffee order: the AI provider failed during the run\. It is not a failed check\. Do not send it again yet\.$/m);
  assert.doesNotMatch(result.out, /FAILED|REFUSED/);
  assert.match(result.out, /graph-provider-failure \(transport_unknown, internal-retry\)[^\n]*\n {2}To try again, run `pdd check` again \(a new request\)\.$/m);
  assert.equal(fake.posts.filter(post => post.command === 'check').length, 1);
  const json = await check(setup, fake, ['place-order'], { '--json': true });
  assert.equal(json.json.rows[0].reason.code, 'graph-provider-failure');
});

// Wrong: a mismatch in whitespace looks like no mismatch ("A\n" and "A" print the same).
test('RUNTIME-SERVER20: expected and got strings print JSON-escaped', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET' ? { status: 200, json: f.check(entry.url.split('/').at(-1), 'failed',
    [{ criterion_id: 'AC2', target: 'result', path: '/customerName', op: 'equals', expected: 'Sam\n', actual: 'Sam', passed: false }]) } : f.normal(entry));
  const result = await check(setup, fake, ['place-order']);
  assert.equal(result.code, 1);
  assert.match(result.out, /^ {2}AC2 {2}result \/customerName {2}expected "Sam\\n", got "Sam"$/m);
});

// Wrong: the engine warning repeats on every run (Serhan: at most once a day for each engine build).
test('RUNTIME-SERVER21: the engine-build warning prints once a day for each engine sha', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET' ? { status: 200, json: { ...f.check(entry.url.split('/').at(-1)), engine_sha: 'eae2202a68d00ab7' } } : f.normal(entry));
  const warned = /runtime engine is eae2202a68d0/;
  assert.match((await check(setup, fake, ['place-order'])).out, warned);
  assert.doesNotMatch((await check(setup, fake, ['place-order'])).out, warned);
  const json = await check(setup, fake, ['place-order'], { '--json': true });
  assert.equal(json.json.warnings.some(text => warned.test(text)), false);
  const tomorrow = await check(setup, fake, ['place-order'], {}, { now: () => Date.parse('2026-10-28T16:27:47Z') });
  assert.match(tomorrow.out, warned);
});

const DRAFT_TEXT = 'The server does not run draft prompts yet. Approve the prompt first, or wait for the server update.';
const draftRepo = t => harbor(t, repo => {
  const file = join(repo, PLACE); writeFileSync(file, readFileSync(file, 'utf8').replace('"approved"', '"draft"'));
});
const draftLint = (entry, f) => entry.method === 'POST' && entry.command === 'lint'
  ? { status: 200, json: f.lint(entry.request.requestId, [{ path: PLACE, state: 'draft', admission_state: 'draft', interface: { calls: [] } }]) } : null;

// Wrong: a draft run looks like an approved one in the table, the links, the PR line or --json (Serhan, Oct 27).
test('RUNTIME-DRAFT2: a draft prompt is checked, and every row, link, summary line and --json says DRAFT', async t => {
  const setup = draftRepo(t), fake = await fakeRuntime(t, (entry, f) => draftLint(entry, f) ?? f.normal(entry));
  const result = await check(setup, fake, ['place-order']);
  assert.equal(result.code, 0, result.err + result.out);
  assert.match(result.out, /^Place a coffee order +tests\/place-order\.json +passed \(DRAFT\) +1\/1/m);
  assert.match(result.out, /^Runtime check \(DRAFT\): ✓ 1 of 1 criterion · 1\/1 checks · 1 AI call$/m);
  assert.match(result.out, /^ {2}place-order +http:\/\/127\.0\.0\.1:\d+\/r\/\w+ {2}\(DRAFT\)$/m);
  const json = await check(setup, fake, ['place-order'], { '--json': true });
  assert.equal(json.json.draft, true); assert.equal(json.json.rows[0].draft, true);
  assert.match(json.json.summary_line, /^Runtime check \(DRAFT\): ✓/);
  const approved = await check(harbor(t), await fakeRuntime(t, (entry, f) => f.normal(entry)), ['place-order'], { '--json': true });
  assert.equal(approved.json.draft, false); assert.doesNotMatch(approved.json.summary_line, /DRAFT/);
});

// Wrong: until the server takes drafts, its refusal reads like a broken prompt instead of a plain reason.
test('RUNTIME-DRAFT3: the server refusal of a draft prompt says plainly that drafts do not run yet (exit 4)', async t => {
  const setup = draftRepo(t);
  const fake = await fakeRuntime(t, (entry, f) => draftLint(entry, f) ?? (entry.method === 'GET'
    ? { status: 200, json: f.check(entry.url.split('/').at(-1), 'refused', [], [{ code: 'interface-unapproved', section: 'steps[0]',
      message: 'The runtime refused this job. See the reported reason.', engine_message: 'interface-unapproved' }]) } : f.normal(entry)));
  const result = await check(setup, fake, ['place-order']);
  assert.equal(result.code, 4);
  assert.match(result.out, /REFUSED {2}Place a coffee order \(tests\/place-order\.json\)\n {2}interface-unapproved {2}steps\[0\] {2}The server does not run draft prompts yet\./);
  assert.ok(result.out.includes(DRAFT_TEXT));
});

// Wrong: pdd guesses DRAFT locally even when the server says which prompts were drafts (prompt-runtime #365).
test('RUNTIME-DRAFT4: the draft_prompts list of the server decides DRAFT; without the field the local guess stays', async t => {
  const setup = draftRepo(t);
  const said = list => async (entry, f) => draftLint(entry, f) ?? (entry.method === 'GET' ? { status: 200, json: { ...f.check(entry.url.split('/').at(-1)), draft_prompts: list } } : f.normal(entry));
  const server = await check(setup, await fakeRuntime(t, await said([PLACE])), ['place-order'], { '--json': true });
  assert.equal(server.json.rows[0].draft, true);
  const cleared = await check(setup, await fakeRuntime(t, await said([])), ['place-order'], { '--json': true });
  assert.equal(cleared.json.rows[0].draft, false); assert.doesNotMatch(cleared.json.summary_line, /DRAFT/);
  const plain = harbor(t);
  const flagged = await check(plain, await fakeRuntime(t, await said([PLACE])), ['place-order'], { '--json': true });
  assert.equal(flagged.json.rows[0].draft, true); assert.match(flagged.json.summary_line, /^Runtime check \(DRAFT\)/);
});
