import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { cpSync, existsSync, readFileSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { exitCodeFor, validLink } from '../src/runtime-output.mjs';
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
  const setup = harbor(t, repo => writeFileSync(join(repo, 'pdd-source.json'), JSON.stringify({ include: ['README.md'] })));
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
  assert.deepEqual(checks.map(post => post.request.max_calls), [18, 18]);
  assert.equal(new Set(fake.posts.map(post => post.request.requestId)).size, 3);
  assert.deepEqual([...fake.authorization], [`Bearer ${TOKEN}`]);
  assert.match(result.err, /^Lint passed\. Sent 2 checks at \d\d:\d\d:\d\d: 6 files, \d+ KB \(1 is not prompt, story or test files; run `pdd check --files` to see them\)\.$/m);
  assert.equal((result.out + result.err).split('not prompt, story or test files').length, 2);
  const json = await check(harbor(t), await fakeRuntime(t, (entry, f) => f.normal(entry)), [], { '--json': true });
  assert.deepEqual(json.json.warnings, []);
  assert.match(result.out, /^Place a coffee order +tests\/place-order\.json +passed +1\/1 +2\.0 s$/m);
  assert.deepEqual(result.out.split('\n').slice(3, 6), ['Runtime check (place-order): ✓ 1 of 1 criterion · 1/1 checks · 1 AI call',
    'Runtime check (unknown-item): ✓ 1 of 1 criterion · 1/1 checks · 1 AI call', 'Runtime check: ✓ 2 of 2 criteria · 2/2 checks · 2 AI calls']);
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
  const lost = await check(setup, missing, ['place-order'], {}, { interactive: true });
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
  assert.deepEqual(lines.slice(at + 1, at + 3), ['  AC1  result /totalCents  expected 899, got 900', '  Warning: possible numeric mismatch at tests/place-order.json steps[0].checks[0] (result /totalCents): expected 899; user_stories/place-order.md AC1 contains 900. These may be different quantities. Confirm against the Story and prompt; retain a correct expected value. Record a scoped rationale in pdd-numeric-reviews.json if needed (RUNBOOK §4).']);
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
  assert.match(result.out, /^Runtime check \(place-order\): running · 0 of 3 criteria · 0\/0 checks · 1 running · 0 AI calls \+ 1 unknown$/m);
  assert.doesNotMatch(result.out, /✗|failed/);
  assert.ok(fake.gets.length >= 28 && fake.gets.length <= 31, String(fake.gets.length));
  assert.equal(fake.posts.length, 2);
});

// Wrong: pdd gives up on a slow check after 10 min, or waits in silence.
test('RUNTIME-WAIT1: in a terminal with no --timeout pdd waits until every row ends and prints one progress line every 30 s', async t => {
  const setup = harbor(t), sent = new Map();
  const endsAfter = { 'tests/place-order.json': 60_000, 'tests/unknown-item.json': 25 * 60_000 };
  let clock;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'check') sent.set(entry.request.requestId, { at: clock.now, test: entry.request.scenario });
    if (entry.method !== 'GET') return f.normal(entry);
    const id = entry.url.split('/').at(-1), { at, test } = sent.get(id);
    return { status: 200, json: f.check(id, clock.now - at < endsAfter[test] ? 'running' : 'passed') };
  });
  const made = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }, { interactive: true });
  clock = made.clock;
  const code = await runCheck({ words: [], options: {}, cwd: setup.repo }, made.ports);
  const err = made.ports.stderr.text, out = made.ports.stdout.text;
  assert.equal(code, 0, err + out);
  const progress = err.split('\n').filter(text => text.startsWith('Still running'));
  assert.equal(progress.length, 49, progress.join('\n'));
  assert.equal(progress[0], 'Still running: 0 of 2 Stories done · 2 AI calls so far · 30 s');
  assert.equal(progress[7], 'Still running: 1 of 2 Stories done · 2 AI calls so far · 4 min');
  assert.equal(progress.at(-1), 'Still running: 1 of 2 Stories done · 2 AI calls so far · 24 min');
  // Polite: one GET for each open row every 2 s, the same as with a limit.
  assert.equal(fake.gets.length, 30 + 750);
  assert.equal(fake.posts.length, 3);
  assert.doesNotMatch(out, /STILL RUNNING/);
  assert.match(out, /^2 of 2 stories passed\./m);
  const one = await check(harbor(t), await fakeRuntime(t, (entry, f) => entry.method === 'GET' ? { status: 200, json: f.check(entry.url.split('/').at(-1), 'running') } : f.normal(entry)),
    ['place-order'], { '--timeout': '1' }, { interactive: true });
  assert.equal(one.code, 3);
  assert.deepEqual(one.err.split('\n').filter(text => text.startsWith('Still running')), ['Still running: 0 of 1 Story done · 1 AI call so far · 30 s',
    `Still running. Read the results later with: pdd check --read ${one.batch}`]);
});

// Wrong: with no time limit Ctrl-C loses the batch, or a waiting check is said to have hit a timeout.
test('RUNTIME-WAIT3: Ctrl-C after 12 min prints the read line and exits 3; --read then shows the result', async t => {
  const setup = harbor(t);
  let clock, done = false;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.request.scenario === 'tests/unknown-item.json')
      return { status: 429, json: { dispatch: 'not_started', error: { code: 'server-full', message: 'The runtime is busy. Try again later.' } } };
    if (entry.method !== 'GET') return f.normal(entry);
    if (clock.now >= Date.parse('2026-10-27T16:39:47Z')) clock.interrupt?.();
    return { status: 200, json: f.check(entry.url.split('/').at(-1), done ? 'passed' : 'running') };
  });
  const made = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }, { interactive: true });
  clock = made.clock;
  const code = await runCheck({ words: [], options: {}, cwd: setup.repo }, made.ports);
  const out = made.ports.stdout.text, batch = /pdd check --read (\S+)/.exec(made.ports.stderr.text)[1];
  assert.equal(code, 3, out);
  assert.equal(out.split('\n')[0], `pdd check --read ${batch}`);
  assert.match(out, /^STILL RUNNING when pdd stopped reading: Place a coffee order\. Do not send it again\.$/m);
  assert.match(out, /^NOT RUN {2}Refuse an item[^:]*: The runtime stayed busy\. No checks ran for this attempt\. Retry this batch later\. \(check-busy\)$/m);
  assert.equal(made.ports.stderr.text.split('\n').filter(text => text.startsWith('Still running')).length, 23);
  assert.equal(JSON.parse(readFileSync(join(setup.state, 'batches', batch, 'batch.json'), 'utf8')).timeout_min, null);
  done = true;
  const read = await check(setup, fake, [batch], { '--read': true });
  assert.match(read.out, /^Place a coffee order +tests\/place-order\.json +passed/m);
});

// Wrong: an agent's shell tool (Claude Code: 2 min) cuts pdd off before pdd prints anything (owner, Oct 27).
test('RUNTIME-WAIT4: with no terminal pdd waits at most 90 s, prints the table and the read line, and exits 3; --timeout overrides', async t => {
  const setup = harbor(t);
  let clock;
  const sent = new Map(), fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'check') sent.set(entry.request.requestId, clock.now);
    if (entry.method !== 'GET') return f.normal(entry);
    const id = entry.url.split('/').at(-1);
    return { status: 200, json: f.check(id, clock.now - sent.get(id) < 12 * 60_000 ? 'running' : 'passed') };
  });
  const run = async (options, extra) => {
    const made = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }, extra);
    clock = made.clock;
    const code = await runCheck({ words: ['place-order'], options, cwd: setup.repo }, made.ports);
    return { code, out: made.ports.stdout.text, err: made.ports.stderr.text, batch: /pdd check --read (\S+)/.exec(made.ports.stderr.text)?.[1] };
  };
  const agent = await run({}, { interactive: false });
  assert.equal(agent.code, 3, agent.err + agent.out);
  assert.match(agent.out, /^Place a coffee order +tests\/place-order\.json +running +- +-$/m);
  assert.match(agent.out, /^STILL RUNNING after 90 s: Place a coffee order\. Do not send it again\.$/m);
  const err = agent.err.trimEnd().split('\n');
  assert.deepEqual(err.filter(text => text.startsWith('Still running:')), ['Still running: 0 of 1 Story done · 1 AI call so far · 30 s',
    'Still running: 0 of 1 Story done · 1 AI call so far · 1 min']);
  assert.equal(err.at(-1), `Still running. Read the results later with: pdd check --read ${agent.batch}`);
  assert.equal(err.filter(text => text.startsWith('If pdd stops')).length, 1);
  assert.equal(JSON.parse(readFileSync(join(setup.state, 'batches', agent.batch, 'batch.json'), 'utf8')).timeout_min, 1.5);
  const longer = await run({ '--timeout': '20' }, { interactive: false });
  assert.equal(longer.code, 0, longer.err + longer.out);
  assert.doesNotMatch(longer.err, /Read the results later/);
  const person = await run({}, { interactive: true });
  assert.equal(person.code, 0, person.err + person.out);
  const short = await run({ '--timeout': '1' }, { interactive: true });
  assert.equal(short.code, 3);
  assert.match(short.out, /^STILL RUNNING after 1 min: /m);
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
  const engine = sha => fakeRuntime(t, (entry, f) => entry.method === 'GET' ? { status: 200, json: { ...f.check(entry.url.split('/').at(-1)), engine_sha: sha } } : f.normal(entry));
  const result = await check(setup, await engine('eae2202a0123456789'), ['place-order']);
  assert.equal(result.code, 0);
  assert.match(result.out, /Warning: the runtime engine is eae2202a0123, but pdd's local checks copy engine eae2202a68d0\. The engine stays the judge\./);
  const old = await check(setup, await engine('7b03d3ea8cc047ed0c58905075321e59e62b02f1'), ['place-order']);
  assert.match(old.out, /Warning: the runtime engine is 7b03d3ea8cc0, but pdd's local checks copy engine eae2202a68d0\./);
  // The local rules were checked to match engine eae2202a (Oct 27): its full or short sha gives no warning.
  for (const sha of [null, 'eae2202a68d00ab762fcbbf1eba0d8607a132a15', 'eae2202a68d0']) {
    const same = await check(setup, sha ? await engine(sha) : await fakeRuntime(t, (entry, f) => f.normal(entry)), ['place-order']);
    assert.doesNotMatch(same.out, /runtime engine is/, String(sha));
  }
});

// Wrong: the PR line hides a failure, or --json lacks the line an agent pastes.
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
  assert.deepEqual(text.out.split('\n').slice(3, 6), ['Runtime check (place-order): ✗ 1 of 2 criteria · 1/2 checks · 1 AI call',
    'Runtime check (unknown-item): ✓ 1 of 1 criterion · 1/1 checks · 1 AI call', 'Runtime check: ✗ 2 of 3 criteria · 2/3 checks · 2 AI calls']);
  const json = await check(setup, fake, [], { '--json': true });
  assert.equal(json.json.summary_line, 'Runtime check: ✗ 2 of 3 criteria · 2/3 checks · 2 AI calls');
  const refused = harbor(t, repo => {
    const file = join(repo, 'tests/place-order.json'), doc = JSON.parse(readFileSync(file, 'utf8'));
    doc.steps[0].input.items[0].quantity = 0; writeFileSync(file, JSON.stringify(doc));
  });
  const mixed = await check(refused, await fakeRuntime(t, (entry, f) => f.normal(entry)), [], { '--json': true });
  assert.equal(mixed.code, 4); assert.equal(mixed.json.summary_line, 'Runtime check: ✗ 1 of 4 criteria · 1/1 checks · 1 refused · 1 AI call');
});

// Wrong: the runtime address is written in more than one place, so a move needs many edits.
test('RUNTIME-ADDRESS1: the runtime address is in one place only, and PDD_RUNTIME_URL overrides it', async () => {
  const { DEFAULT_RUNTIME_URL, runtimeOrigin } = await import('../src/runtime-client.mjs');
  const host = new URL(DEFAULT_RUNTIME_URL).host;
  // This test names the hosts on purpose; every other tracked file must not.
  const others = ['--', '.', ':!test/runtime-server.test.mjs'];
  const hits = spawnSync('git', ['grep', '-n', '-F', host, ...others], { cwd: root, encoding: 'utf8' }).stdout.trim().split('\n').filter(Boolean);
  // Fixed report evidence in the two runbooks is not a runtime configuration value.
  const evidenceOnly = hit => {
    const match = /^(RUNBOOK\.md|skills\/pdd-prompting\/RUNBOOK\.md):[0-9]+:(.*)$/.exec(hit);
    if (!match) return false;
    const report = new RegExp(`\\[[^\\]\\n]+\\]\\(https://${host.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}/r/[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\\)`, 'g');
    return !match[2].replace(report, '').includes(host);
  };
  assert.equal(evidenceOnly(`RUNBOOK.md:1:[proof](${DEFAULT_RUNTIME_URL}/r/13e8c6dc-532a-4f0c-bb0b-1d1b3671d2a8)`), true);
  for (const bad of [`RUNBOOK.md:1:PDD_RUNTIME_URL=${DEFAULT_RUNTIME_URL}`, `docs/cli.md:1:[proof](${DEFAULT_RUNTIME_URL}/r/13e8c6dc-532a-4f0c-bb0b-1d1b3671d2a8)`, `RUNBOOK.md:1:[proof](${DEFAULT_RUNTIME_URL}/r/latest)`]) assert.equal(evidenceOnly(bad), false);
  assert.deepEqual(hits.filter(hit => !evidenceOnly(hit)).map(hit => hit.split(':')[0]), ['src/runtime-client.mjs']);
  assert.equal(DEFAULT_RUNTIME_URL, 'https://runtime.promptdriven.ai');
  assert.equal(spawnSync('git', ['grep', '-n', '-e', 'sslip', '-e', '34-72-131-98', '-e', '34\\.72\\.131\\.98', ...others], { cwd: root, encoding: 'utf8' }).stdout, '');
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

// Wrong: with no time limit, a check whose job never shows up on the server is read forever.
test('RUNTIME-WAIT2: in a terminal with no --timeout a lost POST answer is read for 5 min, then the row is unknown', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'check' ? { destroy: true }
    : entry.method === 'GET' ? { status: 404, json: NOT_STARTED } : f.normal(entry));
  const result = await check(setup, fake, ['place-order'], {}, { interactive: true });
  assert.equal(result.code, 3);
  assert.ok(fake.gets.length >= 149 && fake.gets.length <= 150, String(fake.gets.length));
  assert.match(result.out, /^UNKNOWN {2}Place a coffee order: the run may have executed\. Its result is unknown\.\n {2}The answer to the request was lost\.$/m);
});

// Wrong: a lost POST answer keeps an agent's pdd reading for 5 min, past its shell tool's limit.
test('RUNTIME-WAIT5: with no terminal a lost POST answer is read until 90 s, then exit 3 with the read line and no new POST', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'check' ? { destroy: true }
    : entry.method === 'GET' ? { status: 404, json: NOT_STARTED } : f.normal(entry));
  const result = await check(setup, fake, ['place-order']);
  assert.equal(result.code, 3);
  assert.ok(fake.gets.length >= 44 && fake.gets.length <= 45, String(fake.gets.length));
  assert.equal(fake.posts.filter(post => post.command === 'check').length, 1);
  assert.equal(result.err.trimEnd().split('\n').at(-1), `Still running. Read the results later with: pdd check --read ${result.batch}`);
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

// Wrong: a failed CLI output loses its line breaks and is cut near the difference (round-2 tester, Oct 27).
test('RUNTIME-FAILTEXT1: a failed multi-line string keeps its line breaks, is never cut inside a line, and names the lines left out', async t => {
  const setup = harbor(t);
  const bill = cents => `Bill:  $100.00\nTip:   $0.00 (0%)\nTotal: $100.00\nPerson 1: $${cents}\nPerson 2: $33.33\nPerson 3: $33.33\n`;
  const long = mark => Array.from({ length: 60 }, (_, index) => index === 24 ? `line 25 ${mark}` : `line ${index + 1}`).join('\n');
  const checks = [{ criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', expected: bill('33.34'), actual: bill('33.33'), passed: false },
    { criterion_id: 'AC2', target: 'result', path: '/log', op: 'equals', expected: long('want'), actual: long('got'), passed: false }];
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET' ? { status: 200, json: f.check(entry.url.split('/').at(-1), 'failed', checks) } : f.normal(entry));
  const result = await check(setup, fake, ['place-order']);
  assert.equal(result.code, 1, result.err);
  const lines = result.out.split('\n'), first = lines.indexOf('  AC1  result /stdout');
  const shown = cents => ['      Bill:  $100.00', '      Tip:   $0.00 (0%)', '      Total: $100.00', `      Person 1: $${cents}`, '      Person 2: $33.33', '      Person 3: $33.33',
    '      (ends with a line break)'];
  assert.deepEqual(lines.slice(first, first + 17), ['  AC1  result /stdout', '    expected:', ...shown('33.34'), '    got:', ...shown('33.33')]);
  const window = mark => ['      … 22 lines before', ...Array.from({ length: 20 }, (_, index) => `      line ${index + 23}${index === 2 ? ` ${mark}` : ''}`),
    '      … 18 more lines in the report'];
  const second = lines.indexOf('  AC2  result /log');
  assert.deepEqual(lines.slice(second, second + 47), ['  AC2  result /log', '    expected:', ...window('want'), '    got:', ...window('got')]);
  assert.match(lines[second + 47], /^ {2}Report: http/);
});

// Refusal items as prompt-runtime #379 sends them (not live yet): plain reason, fix, file, at, where, cause, and message = reason + fix.
const PLAIN_REFUSALS = [
  { code: 'unknown-criterion', reason: 'The test names a criterion that the Story does not have.', fix: 'Use AC1, AC2 or AC3, as the Story lists them.',
    file: 'tests/place-order.json', at: 'steps[0].checks[1]', where: 'tests/place-order.json steps[0].checks[1]', cause: 'test',
    message: 'The test names a criterion that the Story does not have. Use AC1, AC2 or AC3, as the Story lists them.' },
  { code: 'graph-uncertain-child-dispatch', reason: 'The AI service did not answer one call.', fix: 'Run the check again.', file: null, at: null, where: null,
    cause: 'ai-service', message: 'The AI service did not answer one call. Run the check again.' }];

// Wrong: a refused check shows only a code, or calls an AI service failure a problem in the test (round-2 report text, Oct 27).
test('RUNTIME-REFUSAL1: a refusal with #379 fields shows the reason, where and fix; ai-service says the test is fine; old answers keep their text', async t => {
  const setup = harbor(t);
  const refusing = refusals => fakeRuntime(t, (entry, f) => entry.method === 'GET' ? { status: 200, json: f.check(entry.url.split('/').at(-1), 'refused', [], refusals) } : f.normal(entry));
  const plain = await check(setup, await refusing(PLAIN_REFUSALS), ['place-order']);
  assert.equal(plain.code, 4, plain.err + plain.out);
  const lines = plain.out.split('\n'), at = lines.indexOf('REFUSED  Place a coffee order (tests/place-order.json)');
  assert.deepEqual(lines.slice(at + 1, at + 6), ['  unknown-criterion: The test names a criterion that the Story does not have.',
    '  Where: tests/place-order.json steps[0].checks[1]', '  Fix: Use AC1, AC2 or AC3, as the Story lists them.',
    '  graph-uncertain-child-dispatch: The AI service did not answer one call.', '  Your test is fine. Run it again.']);
  const json = await check(setup, await refusing(PLAIN_REFUSALS), ['place-order'], { '--json': true });
  assert.deepEqual(json.json.rows[0].refusals.map(item => [item.code, item.reason, item.where, item.fix, item.cause]), [
    ['unknown-criterion', PLAIN_REFUSALS[0].reason, PLAIN_REFUSALS[0].where, PLAIN_REFUSALS[0].fix, 'test'],
    ['graph-uncertain-child-dispatch', PLAIN_REFUSALS[1].reason, null, PLAIN_REFUSALS[1].fix, 'ai-service']]);
  const { where, ...noWhere } = PLAIN_REFUSALS[0];
  const placed = await check(setup, await refusing([noWhere]), ['place-order']);
  assert.match(placed.out, /^ {2}Where: tests\/place-order\.json steps\[0\]\.checks\[1\]$/m);
  const old = await check(setup, await refusing([{ code: 'unknown-criterion', section: 'steps[0].checks[1]', message: 'unknown-criterion', engine_message: 'criterion AC9 is not in the story' }]), ['place-order']);
  const before = old.out.split('\n'), from = before.indexOf('REFUSED  Place a coffee order (tests/place-order.json)');
  assert.deepEqual(before.slice(from + 1, from + 3), ['  unknown-criterion  steps[0].checks[1]  unknown-criterion', '  engine: criterion AC9 is not in the story']);
  assert.doesNotMatch(old.out, /Where:|Fix:|Your test is fine/);
});

// Wrong: the engine warning repeats on every run.
test('RUNTIME-SERVER21: the engine-build warning prints once a day for each engine sha', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET' ? { status: 200, json: { ...f.check(entry.url.split('/').at(-1)), engine_sha: '7b03d3ea8cc047ed' } } : f.normal(entry));
  const warned = /runtime engine is 7b03d3ea8cc0/;
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

// Wrong: a draft run looks like an approved one in the table, the links, the PR line or --json.
test('RUNTIME-DRAFT2: a draft prompt is checked, and every row, link, summary line and --json says DRAFT', async t => {
  const setup = draftRepo(t), fake = await fakeRuntime(t, (entry, f) => draftLint(entry, f) ?? f.normal(entry));
  const result = await check(setup, fake, ['place-order']);
  assert.equal(result.code, 0, result.err + result.out);
  assert.match(result.out, /^Place a coffee order +tests\/place-order\.json +passed \(DRAFT\) +1\/1/m);
  assert.match(result.out, /^Runtime check \(place-order\) \(DRAFT\): ✓ 1 of 1 criterion · 1\/1 checks · 1 AI call$/m);
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

// Wrong: the runtime runs on a bare IP, and pdd refuses its own links or accepts a link to another host.
test('RUNTIME-ADDRESS2: Try and report links on the runtime domain pass; links on the old IP or any other host, port or scheme fail', async () => {
  const { runtimeOrigin } = await import('../src/runtime-client.mjs');
  const origin = runtimeOrigin({}), host = 'https://runtime.promptdriven.ai';
  assert.equal(origin, host);
  const token = 'GzKhkowPRTBHXC8Px6XKK8bjrEpWNWk7E-igsV6aA-s';
  assert.equal(validLink(`${host}/s/${token}/`, origin, 'try'), `${host}/s/${token}/`);
  assert.equal(validLink(`${host}/r/b3fbedfb-03de-4b15-ae23-ee6c35a2029f`, origin, 'report'), `${host}/r/b3fbedfb-03de-4b15-ae23-ee6c35a2029f`);
  for (const bad of [`https://34.72.131.98/s/${token}/`, `https://promptdriven.ai/s/${token}/`, `https://runtime.promptdriven.ai.evil.example/s/${token}/`,
    `http://runtime.promptdriven.ai/s/${token}/`, `https://runtime.promptdriven.ai:8443/s/${token}/`, `https://u:p@runtime.promptdriven.ai/s/${token}/`, `${host}/s/${token}`]) {
    assert.equal(validLink(bad, origin, 'try'), null, bad);
  }
  for (const bad of ['https://34.72.131.98/r/abc', 'https://evil.example/r/abc', 'http://runtime.promptdriven.ai/r/abc', `${host}/s/abc/`]) {
    assert.equal(validLink(bad, origin, 'report'), null, bad);
  }
});

// Wrong: a check of every story starts with no word on what it costs (cli 12b).
test('RUNTIME-COST1: a check of all stories says about how many AI calls it uses; a check of one story does not', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const all = await check(setup, fake, []);
  assert.equal(all.code, 0);
  const lines = all.err.split('\n');
  assert.ok(lines.indexOf('Checking all 2 stories: about 2 AI calls (at most 36).') >= 0, all.err);
  assert.ok(lines.indexOf('Checking all 2 stories: about 2 AI calls (at most 36).') < lines.findIndex(text => text.startsWith('Lint passed')));
  const one = await check(setup, fake, ['place-order']);
  assert.doesNotMatch(one.err, /Checking all/);
});

// Wrong: a check that is still running looks like a failure in the PR line (cli 12b).
test('RUNTIME-COST2: the summary line shows running or unknown, never a cross, until a row really fails', async () => {
  const { summaryLine } = await import('../src/runtime-output.mjs');
  const row = (state, extra = {}) => ({ state, phase: 'server', criteria_total: 1, calls: 1, ...extra });
  assert.match(summaryLine([row('passed'), row('running')]), /^Runtime check: running · /);
  assert.match(summaryLine([row('passed'), row('unknown')]), /^Runtime check: unknown · /);
  assert.match(summaryLine([row('failed'), row('running')]), /^Runtime check: ✗ /);
  assert.match(summaryLine([row('passed')]), /^Runtime check: ✓ /);
});

const NOT_INVITED = { status: 403, json: { code: 'not-invited', login: 'octo', message: 'This GitHub login is not on the invite list.' } };
const INVITE_LINE = 'Your GitHub login octo is not on the PDD runtime invite list yet. Ask the PDD team to add you.';

// Wrong: a person who is not invited sees a table of failures or a retry hint instead of one plain line (invite list, Oct 27).
test('RUNTIME-INVITE1: 403 not-invited is one plain line, exit 5, and no check is sent', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST' ? NOT_INVITED : f.normal(entry));
  for (const options of [{}, { '--json': false }]) {
    const result = await check(setup, fake, [], options);
    assert.equal(result.code, 5); assert.equal(result.out, '');
    assert.ok(result.err.trimEnd().split('\n').includes(INVITE_LINE), result.err);
    assert.doesNotMatch(result.err, /Lint passed|Sent \d|If pdd stops/);
  }
  assert.deepEqual(fake.posts.map(post => post.command), ['lint', 'lint']);
  const later = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'check' ? { ...NOT_INVITED, json: { error: { code: 'not-invited', message: 'not invited' }, login: 'octo' } } : f.normal(entry));
  const viaCheck = await check(setup, later, ['place-order']);
  assert.equal(viaCheck.code, 5); assert.ok(viaCheck.err.includes(INVITE_LINE), viaCheck.err);
  const gate = await fakeRuntime(t, (entry, f) => entry.method === 'POST' ? { status: 503, text: 'The runtime opens soon.' } : f.normal(entry));
  const opens = await check(setup, gate, ['place-order']);
  assert.equal(opens.code, 5); assert.match(opens.out + opens.err, /The runtime opens soon\./);
});

// Wrong: the read line shows before lint, when there is nothing to read yet (lead, Oct 27).
test('RUNTIME-READLINE1: "If pdd stops" prints after lint passes and before the checks are sent', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const result = await check(setup, fake, ['place-order']);
  const lines = result.err.split('\n'), read = lines.findIndex(text => text.startsWith('If pdd stops, read the results with: pdd check --read '));
  assert.ok(read > lines.findIndex(text => text.startsWith('Lint passed.')), result.err);
  assert.equal(lines.filter(text => text.startsWith('If pdd stops')).length, 1);
  const refused = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'lint'
    ? { status: 200, json: f.lint(entry.request.requestId, [{ path: PLACE, state: 'stale', admission_state: 'stale', interface: { calls: [] } }]) } : f.normal(entry));
  const none = await check(setup, refused, ['place-order']);
  assert.equal(none.code, 4); assert.doesNotMatch(none.err, /If pdd stops/);
});

// Wrong: many Stories in one run give one blended line, so the gate and PR 1 cannot say which Story failed (0.1.6).
test('RUNTIME-STORYLINE1: one paste line per Story after the table, the overall line last, and summary_line on each --json row', async t => {
  const setup = harbor(t, repo => cpSync(join(repo, 'tests/place-order.json'), join(repo, 'tests/place-order-2.json')));
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const result = await check(setup, fake, []);
  assert.equal(result.code, 0, result.err);
  const lines = result.out.split('\n'), table = lines.findIndex(text => text.startsWith('Story '));
  assert.deepEqual(lines.slice(table + 4, table + 7), ['Runtime check (place-order): ✓ 2 of 2 criteria · 2/2 checks · 2 AI calls',
    'Runtime check (unknown-item): ✓ 1 of 1 criterion · 1/1 checks · 1 AI call', 'Runtime check: ✓ 3 of 3 criteria · 3/3 checks · 3 AI calls']);
  const json = await check(setup, fake, [], { '--json': true });
  assert.deepEqual(json.json.rows.map(row => [row.test, row.summary_line]), [
    ['tests/place-order-2.json', 'Runtime check (place-order): ✓ 2 of 2 criteria · 2/2 checks · 2 AI calls'],
    ['tests/place-order.json', 'Runtime check (place-order): ✓ 2 of 2 criteria · 2/2 checks · 2 AI calls'],
    ['tests/unknown-item.json', 'Runtime check (unknown-item): ✓ 1 of 1 criterion · 1/1 checks · 1 AI call']]);
  assert.equal(json.json.summary_line, 'Runtime check: ✓ 3 of 3 criteria · 3/3 checks · 3 AI calls');
  const draft = await check(draftRepo(t), await fakeRuntime(t, (entry, f) => draftLint(entry, f) ?? f.normal(entry)), ['place-order']);
  assert.ok(draft.out.split('\n').includes('Runtime check (place-order) (DRAFT): ✓ 1 of 1 criterion · 1/1 checks · 1 AI call'), draft.out);
});

// Wrong: one Story prints its line twice, once with its name and once as the overall line (round-2 tester, Oct 27).
test('RUNTIME-STORYLINE2: one Story prints only its own Runtime check line; two Stories add the overall line', async t => {
  const fake = await fakeRuntime(t, (entry, f) => draftLint(entry, f) ?? f.normal(entry));
  const one = await check(draftRepo(t), fake, ['place-order']);
  assert.deepEqual(one.out.split('\n').filter(text => text.startsWith('Runtime check')),
    ['Runtime check (place-order) (DRAFT): ✓ 1 of 1 criterion · 1/1 checks · 1 AI call']);
  const two = await check(harbor(t), await fakeRuntime(t, (entry, f) => f.normal(entry)), []);
  assert.deepEqual(two.out.split('\n').filter(text => text.startsWith('Runtime check')), ['Runtime check (place-order): ✓ 1 of 1 criterion · 1/1 checks · 1 AI call',
    'Runtime check (unknown-item): ✓ 1 of 1 criterion · 1/1 checks · 1 AI call', 'Runtime check: ✓ 2 of 2 criteria · 2/2 checks · 2 AI calls']);
});

// Wrong: when the server retires an address it answers "update required", and an old pdd shows a failure table or retries (0.1.6).
test('RUNTIME-UPDATE1: code update-required (any status, top level or error.code) is one plain line, exit 5, and no check is sent', async t => {
  const setup = harbor(t);
  const said = { status: 426, json: { code: 'update-required', message: 'This pdd is too old for the PDD runtime. Run: npm install -g github:promptdriven/pdd#alpha' } };
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST' ? said : f.normal(entry));
  const result = await check(setup, fake, []);
  assert.equal(result.code, 5); assert.equal(result.out, '');
  assert.deepEqual(result.err.trimEnd().split('\n').slice(-1), [said.json.message]);
  assert.doesNotMatch(result.err, /Lint passed|If pdd stops/);
  assert.deepEqual(fake.posts.map(post => post.command), ['lint']);
  const bare = await fakeRuntime(t, (entry, f) => entry.method === 'POST' ? { status: 400, json: { error: { code: 'update-required' } } } : f.normal(entry));
  const fallback = await check(setup, bare, ['place-order']);
  assert.equal(fallback.code, 5); assert.ok(fallback.err.includes('Please update pdd: npm install -g github:promptdriven/pdd#alpha'), fallback.err);
  const onRead = await fakeRuntime(t, (entry, f) => entry.method === 'GET' ? said : f.normal(entry));
  const reading = await check(setup, onRead, ['place-order']);
  assert.ok(reading.err.includes(said.json.message), reading.err);
});

// Wrong: agents import pdd's source for a lint, or a lint runs pdd's local copy of the engine rules.
test('RUNTIME-LINT1: pdd check --lint sends one lint and no checks, prints every server problem, and skips the local rules', async t => {
  const setup = harbor(t, repo => {
    const file = join(repo, 'tests/place-order.json'), doc = JSON.parse(readFileSync(file, 'utf8'));
    doc.steps[0].input.items[0].quantity = 0; writeFileSync(file, JSON.stringify(doc));
  });
  const ok = await check(setup, await fakeRuntime(t, (entry, f) => f.normal(entry)), [], { '--lint': true });
  assert.equal(ok.code, 0, ok.err + ok.out);
  assert.match(ok.out, /^Lint: 2 of 2 tests pass\. 0 AI calls\. No checks were sent\.$/m);
  assert.doesNotMatch(ok.out + ok.err, /invalid-input|Runtime check|If pdd stops/);
  const refusing = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'lint'
    ? { status: 200, json: f.lint(entry.request.requestId, [{ path: PLACE, state: 'refused', admission_state: 'refused', interface: null }],
      [{ code: 'graph-schema-type-list', path: PLACE, section: 'Runtime interface.entries[0].input_schema', message: 'graph executable schema is invalid: type list' },
        { code: 'invalid-interface', path: 'prompts/other.prompt.md', section: 'Runtime interface', message: 'invalid-interface' }]) } : f.normal(entry));
  const bad = await check(setup, refusing, [], { '--lint': true });
  assert.equal(bad.code, 4);
  assert.match(bad.out, /^ {2}graph-schema-type-list {2}prompts\/place_order\.prompt\.md {2}Runtime interface\.entries\[0\]\.input_schema {2}graph executable schema is invalid: type list$/m);
  assert.match(bad.out, /^ {2}invalid-interface {2}prompts\/other\.prompt\.md /m);
  assert.match(bad.out, /^Lint: 0 of 2 tests pass\. 0 AI calls\. No checks were sent\.$/m);
  const json = await check(setup, refusing, ['place-order'], { '--lint': true, '--json': true });
  assert.equal(json.code, 4); assert.equal(json.json.problems.length, 2); assert.equal(json.json.rows[0].state, 'refused');
  assert.deepEqual(refusing.posts.map(post => post.command), ['lint', 'lint']);
});

// Wrong: --lint hides not-invited, update-required or no room behind a problem list, or sends files with secrets.
test('RUNTIME-LINT2: --lint keeps the capture checks, exit 5 answers and option rules', async t => {
  const setup = harbor(t, repo => {
    writeFileSync(join(repo, 'deploy.pem'), 'x');
    writeFileSync(join(repo, 'pdd-source.json'), JSON.stringify({ include: ['deploy.pem'] }));
  });
  const quiet = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const secret = await check(setup, quiet, [], { '--lint': true });
  assert.equal(secret.code, 4); assert.match(secret.err, /deploy\.pem: the name looks like a secret/); assert.equal(quiet.posts.length, 0);
  const clean = harbor(t);
  for (const [reply, said] of [[{ status: 403, json: { code: 'not-invited', login: 'octo' } }, /octo is not on the PDD runtime invite list/],
    [{ status: 426, json: { code: 'update-required', message: 'Please update pdd.' } }, /Please update pdd\./],
    [{ status: 503, json: { error: { code: 'pool-low-room', message: 'The runtime model account has too little room for this job. Try again later.' } } }, /too little room/]]) {
    const fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST' ? reply : f.normal(entry));
    const result = await check(clean, fake, [], { '--lint': true });
    assert.equal(result.code, 5, String(said)); assert.match(result.err, said); assert.deepEqual(fake.posts.map(post => post.command), ['lint']);
  }
  for (const options of [{ '--lint': true, '--read': true }, { '--lint': true, '--max-calls': '5' }, { '--lint': true, '--local': true, '--details': true }, { '--local': true }]) {
    assert.equal((await check(clean, quiet, [], options)).code, 2, JSON.stringify(options));
  }
});

// Wrong: a global refused job label overrides passing selected rows in lint JSON (night issue 10).
test('RUNTIME-LINT3: selected lint JSON reports passed when its admitted rows pass despite an overall refused job', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (request, f) => {
    assert.equal(request.command, 'lint');
    const answer = f.lint(request.request.requestId); answer.state = 'refused'; answer.result.exitCode = 4;
    return { status: 200, json: answer };
  });
  const result = await check(setup, fake, ['place-order'], { '--lint': true, '--json': true });
  assert.equal(result.code, 0); assert.equal(result.json.exit_code, 0);
  assert.equal(result.json.lint_state, 'passed');
  assert.deepEqual(result.json.rows.map(row => row.state), ['passed']); assert.deepEqual(result.json.problems, []);
  assert.deepEqual(fake.posts.map(post => post.command), ['lint']);
});

// Wrong: an overall passed job label conceals a selected prompt refusal in lint JSON.
test('RUNTIME-LINT4: selected lint JSON reports refused when its selected prompt is refused despite an overall passed job', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (request, f) => ({ status: 200, json: f.lint(request.request.requestId,
    [{ path: PLACE, state: 'refused', admission_state: 'refused', interface: null }],
    [{ path: PLACE, code: 'graph-schema-type-list', section: 'Runtime interface', message: 'type list' }]) }));
  const result = await check(setup, fake, ['place-order'], { '--lint': true, '--json': true });
  assert.equal(result.code, 4); assert.equal(result.json.exit_code, 4);
  assert.equal(result.json.lint_state, 'refused');
  assert.deepEqual(result.json.rows.map(row => row.state), ['refused']);
  assert.ok(result.json.problems.some(row => row.path === PLACE && row.code === 'graph-schema-type-list'));
  assert.deepEqual(fake.posts.map(post => post.command), ['lint']);
});

// Wrong: correcting the selected summary hides unselected diagnostics, or lets them refuse selected rows.
test('RUNTIME-LINT5: passing selected lint JSON preserves unrelated refusal diagnostics without changing the selected verdict', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (request, f) => {
    const answer = f.lint(request.request.requestId, [{ path: PLACE, state: 'approved', admission_state: 'approved', interface: { calls: [] } }],
      [{ path: 'prompts/legacy.prompt.md', code: 'duplicate-interface', section: 'pdd-interface', message: 'duplicate-interface' }]);
    answer.state = 'refused';
    return { status: 200, json: answer };
  });
  const result = await check(setup, fake, ['place-order'], { '--lint': true, '--json': true });
  assert.equal(result.code, 0); assert.equal(result.json.exit_code, 0); assert.equal(result.json.lint_state, 'passed');
  assert.deepEqual(result.json.rows.map(row => row.state), ['passed']);
  assert.deepEqual(result.json.problems.map(row => [row.path, row.code]), [['prompts/legacy.prompt.md', 'duplicate-interface']]);
  assert.deepEqual(fake.posts.map(post => post.command), ['lint']);
});


test('T3-5: explicit lint requests complete diagnostics while preliminary check lint stays unchanged', async t => {
  const setup = harbor(t);
  const faults = [{ code:'invalid-schema',path:PLACE,section:'Runtime interface.entries[0].input_schema.properties.argv.items.type',message:'Use one schema type.' },
    { code:'invalid-schema',path:PLACE,section:'Runtime interface.resources[0].result_schema.properties.value.items',message:'Array items are required.' }];
  const fake = await fakeRuntime(t, (entry,f) => entry.command === 'lint'
    ? { status:200, json:f.lint(entry.request.requestId,[{path:PLACE,state:'refused',admission_state:'refused'}],entry.request.complete === true ? faults : faults.slice(0,1)) }
    : f.normal(entry));
  const result = await check(setup,fake,['place-order'],{'--lint':true,'--json':true});
  assert.equal(result.code,4);
  assert.equal(result.json.problems.length,2,'complete mode must retain both independent faults');
  assert.deepEqual(fake.posts.map(p=>p.command),['lint']);
  assert.deepEqual(Object.keys(fake.posts[0].request).sort(),['complete','requestId','source_sha256']);
  assert.equal(fake.posts[0].request.complete,true);
  const ordinary=await fakeRuntime(t,(entry,f)=>f.normal(entry));
  assert.equal((await check(setup,ordinary,['place-order'])).code,0);
  assert.equal(Object.hasOwn(ordinary.posts[0].request,'complete'),false);
});


test('T3-5 complete lint retains canonical schema pointers and selected test refusals outside prompt admission', async t => {
  const setup=harbor(t);
  const canonical=[{code:'graph-schema-type-list',file:PLACE,at:'Runtime interface.entries[0].input_schema.properties.argv.items',pointer:'/entries/0/input_schema/properties/argv/items',severity:'error',source:'server',reason:'Use one schema type.',fix:'Use oneOf.'},
    {code:'graph-schema-invalid',file:PLACE,at:'Runtime interface.resources[0].operations[1].arguments_schema.properties.value',pointer:'/resources/0/operations/1/arguments_schema/properties/value',severity:'error',source:'server',reason:'Array items are required.',fix:'Add items.'}];
  const schema=await fakeRuntime(t,(entry,f)=>{const job=f.lint(entry.request.requestId,[{path:PLACE,state:'refused',admission_state:'refused'}],[{code:canonical[0].code,path:PLACE,section:canonical[0].at,message:canonical[0].reason}]);
    return {status:200,json:{...job,result:{...job.result,problems:canonical,problems_complete:true,tests:[{path:'tests/place-order.json',verdict:'refused'}]}}};});
  const faults=await check(setup,schema,['place-order'],{'--lint':true,'--json':true});
  assert.equal(faults.code,4);assert.equal(faults.json.problems.length,2);
  assert.deepEqual(faults.json.problems.map(p=>p.pointer),canonical.map(p=>p.pointer));
  const mismatch={code:'story-criterion-mismatch',file:'tests/place-order.json',at:'criteria[0].text',pointer:'/criteria/0/text',severity:'error',reason:'Copy the exact Story criterion.',fix:'Keep the expected criterion unchanged.'};
  const fake=await fakeRuntime(t,(entry,f)=>{const job=f.lint(entry.request.requestId);return {status:200,json:{...job,result:{...job.result,problems:[mismatch],problems_complete:true,tests:[{path:'tests/place-order.json',verdict:'refused'},{path:'tests/unknown-item.json',verdict:'passed'}]}}};});
  const bad=await check(setup,fake,['place-order'],{'--lint':true,'--json':true});
  assert.equal(bad.code,4);assert.equal(bad.json.lint_state,'refused');assert.equal(bad.json.rows[0].state,'refused');
  assert.equal(bad.json.rows[0].refusals[0].code,'story-criterion-mismatch');
  const unrelated=await check(setup,fake,['unknown-item'],{'--lint':true,'--json':true});
  assert.equal(unrelated.code,0);assert.equal(unrelated.json.lint_state,'passed');assert.equal(unrelated.json.problems.length,1);
});

test('hcli-2: saved-data and nested prompt calls contribute to the estimate without changing caps', async t => {
  const setup = harbor(t, repo => {
    rmSync(join(repo, 'tests/unknown-item.json'));
    const file = join(repo, PLACE), text = readFileSync(file, 'utf8'), iface = JSON.parse(text.match(/```json\s*([\s\S]*?)```/)[1]);
    const schema = { type: 'object', properties: {}, required: [], additionalProperties: false };
    iface.status = 'draft'; iface.resources = [{ name: 'store', kind: 'key-value', access: 'write', operations: ['load','save'].map(name => ({ name, access: name === 'load' ? 'read' : 'write', arguments_schema: schema, result_schema: schema })) }];
    const shared = { ...iface, resources: [ { ...iface.resources[0], operations: [iface.resources[0].operations[0]] } ], calls: [] };
    iface.calls = [{ operation: 'lookup', target: 'prompts/shared.prompt.md', target_operation: 'place_order', max_calls: 2 }];
    const prompt = value => text.replace(/```json\s*[\s\S]*?```/, '```json\n' + JSON.stringify(value) + '\n```');
    writeFileSync(file, prompt(iface)); writeFileSync(join(repo, 'prompts/shared.prompt.md'), prompt(shared));
  });
  const fill = spawnSync(process.execPath, [join(root, 'bin/pdd.mjs'), 'check', '--fill-hash'], { cwd: setup.repo, encoding: 'utf8' }); assert.equal(fill.status, 0, fill.stderr);
  const fake = await fakeRuntime(t, (e, f) => f.normal(e));
  const result = await check(setup, fake, [], { '--max-calls': '32' });
  assert.equal(result.code, 0, result.out + result.err);
  // Entry1 + store(load,save)2 + target(1+load1)*max_calls2 =7.
  assert.match(result.err, /about 7 AI calls \(at most 32\)/);
  assert.equal(fake.posts.find(p => p.command === 'check').request.max_calls, 32);
});
