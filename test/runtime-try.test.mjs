import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runTry } from '../src/runtime-client.mjs';
import { findTests, preflight } from '../src/runtime-preflight.mjs';
import { PLACE, fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

async function tryStory(setup, fake, words, options = {}, extra = {}) {
  const opened = [];
  const { ports, clock } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state },
    { openUrl: async url => { opened.push(url); return true; }, ...extra });
  const code = await runTry({ words, options, cwd: setup.repo }, ports);
  return { code, opened, clock, out: ports.stdout.text, err: ports.stderr.text };
}

// The fake Try server: lint passes, a Try is queued, then running with `link(id)`; DELETE stops it.
function trying(link) {
  return (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.method === 'POST') return { status: 202, json: f.job(entry.request.requestId, 'try', 'queued') };
    if (entry.method === 'DELETE') return { status: 202, json: { ...f.job(entry.headers['x-request-id'], 'stop', 'running'), session_id: entry.url.split('/').at(-1) } };
    if (entry.url.endsWith('/tests')) return { status: 404, json: { error: { code: 'not-found', message: 'The requested run or session was not found.' } } };
    const id = entry.url.split('/').at(-1), stop = f.deletes.find(item => item.headers['x-request-id'] === id);
    if (stop) return { status: 200, json: f.stopJob(id, stop.url.split('/').at(-1)) };
    const stopped = f.deletes.some(item => item.url.endsWith(`/${id}`));
    return { status: 200, json: f.tryJob(id, link?.(f, id) ?? undefined, stopped ? 'stopped' : 'running') };
  };
}

// Wrong: the Try seed, tab or call cap differs from the spec, or a running Try is made again (spec 11, A7).
test('RUNTIME-TRY1: pdd try lints, posts one Try with the test as seed, opens the link, then reuses it', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, trying());
  const first = await tryStory(setup, fake, ['place-order']);
  assert.equal(first.code, 0, first.err + first.out);
  assert.deepEqual(fake.posts.map(post => post.command), ['lint', 'try']);
  const request = fake.posts[1].request;
  assert.deepEqual(Object.keys(request).sort(), ['requestId', 'seed', 'source_sha256', 'tab']);
  assert.equal(request.seed, 'tests/place-order.json'); assert.equal(request.tab, 'call');
  assert.deepEqual(first.opened, [`${fake.origin}/s/${'t'.repeat(43)}/`]);
  assert.equal(first.out, 'Try link for "Place a coffee order" is open in your browser. It ends in 24 hours, or with: pdd try --stop place-order\n');
  const again = await tryStory(setup, fake, ['place-order'], { '--no-open': true });
  assert.equal(again.code, 0, again.err);
  assert.equal(fake.posts.length, 2); assert.deepEqual(again.opened, []);
  assert.match(again.out, new RegExp(`Try link for "Place a coffee order": ${fake.origin}/s/t{43}/`));
  const screen = await tryStory(setup, fake, ['place-order'], { '--new': true, '--tab': 'screen' });
  assert.equal(screen.code, 0, screen.err);
  assert.equal(fake.deletes.length, 1); assert.match(fake.deletes[0].headers['x-request-id'], /^[0-9a-f-]{36}$/);
  assert.equal(fake.deletes[0].url, `/v1/try/${request.requestId}`);
  assert.deepEqual(fake.posts.map(post => post.command), ['lint', 'try', 'lint', 'try']);
  assert.equal(fake.posts[3].request.tab, 'screen');
});

// Wrong: --stop sends no request ID, or forgets the Try before the stop is confirmed.
test('RUNTIME-TRY2: --stop sends DELETE with X-Request-Id, reads the stop job and forgets the Try', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, trying());
  assert.equal((await tryStory(setup, fake, ['place-order'])).code, 0);
  const stopped = await tryStory(setup, fake, ['place-order'], { '--stop': true });
  assert.equal(stopped.code, 0, stopped.err);
  assert.equal(fake.deletes.length, 1);
  const id = fake.deletes[0].headers['x-request-id'];
  assert.match(id, /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/);
  assert.ok(fake.gets.some(get => get.url === `/v1/runs/${id}`));
  assert.equal(stopped.out, 'The Try link for "Place a coffee order" is stopped.\n');
  const none = await tryStory(setup, fake, ['place-order'], { '--stop': true });
  assert.equal(none.code, 2); assert.equal(fake.deletes.length, 1);
});

// Wrong: pdd opens a link that points to another host, plain HTTP or a wrong path (spec 11 link checks).
test('RUNTIME-TRY3: a Try link with another host, scheme, path or a user is not opened; pdd says why in one line, with no table', async t => {
  for (const bad of [
    f => `https://${new URL(f.origin).host}/s/abc/`, f => `${f.origin.replace('127.0.0.1', 'localhost')}/s/abc/`,
    f => `${f.origin}/r/abc`, f => `${f.origin}/s/abc`, f => f.origin.replace('http://', 'http://user:pw@') + '/s/abc/']) {
    const setup = harbor(t), fake = await fakeRuntime(t, trying(f => bad(f)));
    const elsewhere = new URL(bad(fake)).origin !== fake.origin;
    const refused = elsewhere ? `Try link refused: it points at ${new URL(bad(fake)).origin}, not ${fake.origin}. The server's address setting may be wrong; tell the PDD team.`
      : 'Try link refused: it is not a valid Try link. Tell the PDD team.';
    for (const result of [await tryStory(setup, fake, ['place-order']), await tryStory(setup, fake, ['place-order'])]) {
      assert.equal(result.code, 3, `${bad(fake)}: ${result.out}${result.err}`); assert.deepEqual(result.opened, []);
      assert.equal((result.out + result.err).includes(bad(fake)), false);
      assert.equal(result.out, ''); assert.equal(result.err.trimEnd().split('\n').at(-1), refused);
      assert.doesNotMatch(result.err, /Runtime check|Story +Test/);
    }
    assert.equal(fake.posts.filter(post => post.command === 'try').length, 1);
    assert.equal((await tryStory(setup, fake, ['place-order'], { '--stop': true })).code, 0);
  }
});

// Wrong: too many Try links are retried, or pdd picks a test when several exist.
test('RUNTIME-TRY4: 429 is exit 5 with the stop hint; no STORY with many tests lists them (exit 2)', async t => {
  const setup = harbor(t);
  const busy = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'try'
    ? { status: 429, headers: { 'retry-after': '5' }, json: { error: { code: 'server-full', message: 'The runtime is busy. Try again later.' }, dispatch: 'not_started' } } : trying()(entry, f));
  const full = await tryStory(setup, busy, ['place-order']);
  assert.equal(full.code, 5); assert.match(full.err, /Too many Try links are open\. Stop one with pdd try --stop/);
  assert.equal(busy.posts.filter(post => post.command === 'try').length, 1);
  const many = await tryStory(setup, busy, []);
  assert.equal(many.code, 2); assert.match(many.err, /place-order/); assert.match(many.err, /unknown-item/);
  const one = harbor(t, repo => rmSync(join(repo, 'tests/unknown-item.json')));
  const lone = await fakeRuntime(t, trying());
  const used = await tryStory(one, lone, []);
  assert.equal(used.code, 0, used.err); assert.equal(lone.posts[1].request.seed, 'tests/place-order.json');
  const bad = harbor(t, repo => {
    const file = join(repo, 'tests/place-order.json'), doc = JSON.parse(readFileSync(file, 'utf8'));
    doc.steps[0].input.items[0].quantity = 0; writeFileSync(file, JSON.stringify(doc));
  });
  const quiet = await fakeRuntime(t, trying());
  const refused = await tryStory(bad, quiet, ['place-order']);
  assert.equal(refused.code, 4); assert.equal(quiet.posts.length, 0);
  assert.match(refused.out, /steps\[0\] input \/items\/0\/quantity is 0\. The prompt allows 1 to 20\./);
});

// Wrong: a Try that is still starting is made a second time, so the first one runs with no way to stop it.
test('RUNTIME-TRY5: a recorded Try that is not ready gives exit 3 and no new Try; --new stops it first', async t => {
  const setup = harbor(t);
  let ready = false;
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET' && !ready && !f.deletes.length
    ? { status: 200, json: f.job(entry.url.split('/').at(-1), 'try', 'running') } : trying()(entry, f));
  const slow = await tryStory(setup, fake, ['place-order'], {}, {});
  assert.equal(slow.code, 3); assert.equal(fake.posts.filter(post => post.command === 'try').length, 1);
  const again = await tryStory(setup, fake, ['place-order']);
  assert.equal(again.code, 3); assert.match(again.err, /pdd try place-order --new/);
  assert.equal(fake.posts.filter(post => post.command === 'try').length, 1);
  const fresh = await tryStory(setup, fake, ['place-order'], { '--new': true });
  assert.equal(fresh.code, 0, fresh.err);
  assert.equal(fake.deletes.length, 1); assert.equal(fake.posts.filter(post => post.command === 'try').length, 2);
  ready = true;
});

// Wrong: the Try page gets no app map, so the Screen tab is empty (runtime session, Oct 27).
test('RUNTIME-TRY6: pdd try sends the app map it finds, opens on the screen tab, and --app-map and --tab win', async t => {
  const withMap = harbor(t, repo => { mkdirSync(join(repo, 'app')); writeFileSync(join(repo, 'app/app-map.json'), '{"screens": []}\n'); });
  const fake = await fakeRuntime(t, trying());
  assert.equal((await tryStory(withMap, fake, ['place-order'], { '--no-open': true })).code, 0);
  const sent = fake.posts.filter(post => post.command === 'try');
  assert.equal(sent[0].request.app_map, 'app/app-map.json'); assert.equal(sent[0].request.tab, 'screen');
  const rooted = harbor(t, repo => { mkdirSync(join(repo, 'app')); writeFileSync(join(repo, 'app/app-map.json'), '{}\n'); writeFileSync(join(repo, 'app-map.json'), '{}\n');
    writeFileSync(join(repo, 'other-map.json'), '{}\n'); });
  const second = await fakeRuntime(t, trying());
  assert.equal((await tryStory(rooted, second, ['place-order'], { '--tab': 'call' })).code, 0);
  assert.equal(second.posts[1].request.app_map, 'app-map.json'); assert.equal(second.posts[1].request.tab, 'call');
  const third = await fakeRuntime(t, trying());
  assert.equal((await tryStory(rooted, third, ['place-order'], { '--app-map': 'other-map.json', '--new': true })).code, 0);
  assert.equal(third.posts[1].request.app_map, 'other-map.json');
  const missing = await tryStory(rooted, third, ['place-order'], { '--app-map': 'nope.json', '--new': true });
  assert.equal(missing.code, 2); assert.match(missing.err, /nope\.json/); assert.equal(third.posts.length, 2);
});

const AC1 = 'An order of 2 Espresso S and 1 Blueberry Muffin L has a total of 900 cents ($9.00).';
// One case saved on the Try page, as GET /v1/try/<id>/tests returns it (try-page DESIGN.md).
const savedCase = (id, { story = 'user_stories/place-order.md', criterion = { id: 'AC1', text: AC1 }, name = `Case ${id}` } = {}) => ({
  id, path: `tests/${id}.json`, name, created: '2026-10-27T18:02:11Z', story_path: story,
  test: { schema_version: 'prompt-runtime.program-scenario.v1', story_path: story, criteria: [criterion], initial_world: {}, simulation: {}, context: [],
    steps: [{ step_id: `saved-${id}`, entry_path: PLACE, operation: 'place_order',
      input: { customerName: 'Ana', pickupAt: '07:45', items: [{ itemId: 'latte', size: 'M', quantity: 1 }] },
      checks: [{ criterion_id: criterion.id, target: 'result', path: '/totalCents', op: 'equals', value: 445 }] }] } });

// Wrong: a case saved on the Try page is lost, makes a second test file, or is added twice (Serhan, Oct 27: save as test).
test('RUNTIME-TRY7: pdd try stays open and appends each saved case as a new step of the story\'s test file', async t => {
  const setup = harbor(t, repo => writeFileSync(join(repo, 'user_stories/refund.md'), '# Refund an order\n\n## Acceptance criteria\n\n1. A refund returns the total.\n'));
  const original = readFileSync(join(setup.repo, 'tests/place-order.json'), 'utf8');
  let polls = 0, reopened = false;
  const lists = [[], [savedCase('a')], [savedCase('a'), savedCase('b', { criterion: { id: 'ac-1', text: AC1 } }),
    savedCase('c', { criterion: { id: 'ac-9', text: 'Something the story does not say.' } }),
    savedCase('d', { story: 'user_stories/refund.md', criterion: { id: 'AC1', text: 'A refund returns the total.' } })]];
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'GET' && entry.url.endsWith('/tests')) { polls += 1; return { status: 200, json: { tests: lists[Math.min(polls - 1, 2)] } }; }
    if (entry.method === 'GET' && polls >= 5 && !reopened) return { status: 200, json: f.tryJob(entry.url.split('/').at(-1), undefined, 'stopped') };
    return trying()(entry, f);
  });
  const result = await tryStory(setup, fake, ['place-order'], { '--no-open': true }, { interactive: true });
  assert.equal(result.code, 0, result.err);
  assert.equal(result.out.split('\n').filter(text => text.startsWith('added to')).join('\n'), ['added to tests/place-order.json as step saved-a',
    'added to tests/place-order.json as step saved-b', 'added to tests/refund.json as step saved-d'].join('\n'));
  assert.match(result.out, /not added: "Case c" checks a criterion that tests\/place-order\.json does not have/);
  const text = readFileSync(join(setup.repo, 'tests/place-order.json'), 'utf8'), doc = JSON.parse(text);
  assert.ok(text.startsWith(original.slice(0, original.lastIndexOf('}', original.lastIndexOf(']')) + 1)));
  assert.deepEqual(doc.steps.map(step => step.step_id), ['sam-orders-espressos-and-a-muffin', 'saved-a', 'saved-b']);
  assert.deepEqual(doc.steps.slice(1).map(step => step.checks[0].criterion_id), ['AC1', 'AC1']);
  assert.equal(JSON.parse(readFileSync(join(setup.repo, 'tests/refund.json'), 'utf8')).steps[0].step_id, 'saved-d');
  const found = findTests({ root: setup.repo }), checked = preflight({ root: setup.repo, found, selected: found.tests });
  assert.deepEqual(checked.rows.map(row => [row.test, row.refusals.map(item => item.code)]),
    [['tests/place-order.json', []], ['tests/refund.json', []], ['tests/unknown-item.json', []]]);
  reopened = true;
  const again = await tryStory(setup, fake, ['place-order'], { '--no-open': true });
  assert.equal(again.code, 0); assert.doesNotMatch(again.out, /added to/);
  assert.equal(JSON.parse(readFileSync(join(setup.repo, 'tests/place-order.json'), 'utf8')).steps.length, 3);
});

// Wrong: an agent's pdd try blocks forever, or a missing saved-tests endpoint looks like an error.
test('RUNTIME-TRY8: --no-wait returns at once; a runtime with no saved-tests endpoint is said plainly', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, trying());
  const quick = await tryStory(setup, fake, ['place-order'], { '--no-open': true, '--no-wait': true }, { interactive: true });
  assert.equal(quick.code, 0); assert.doesNotMatch(quick.out, /Waiting/);
  const waiting = await tryStory(setup, fake, ['place-order'], { '--no-open': true }, { interactive: true });
  assert.equal(waiting.code, 0); assert.match(waiting.out, /The runtime does not keep saved tests yet/);
});

// Wrong: the live server pauses an idle Try, and pdd then thinks the Try is gone or unknown (seen on the live server, Oct 27).
test('RUNTIME-TRY9: a paused Try is reused like a running one', async t => {
  const setup = harbor(t);
  let made = false;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'GET' && made && !entry.url.endsWith('/tests')) return { status: 200, json: f.tryJob(entry.url.split('/').at(-1), undefined, 'paused') };
    return trying()(entry, f);
  });
  assert.equal((await tryStory(setup, fake, ['place-order'], { '--no-open': true })).code, 0);
  made = true;
  const again = await tryStory(setup, fake, ['place-order'], { '--no-open': true });
  assert.equal(again.code, 0, again.err); assert.equal(fake.posts.filter(post => post.command === 'try').length, 1);
});

// Wrong: a Try that the server no longer knows (404) or that expired (410) blocks pdd try until the person edits the state file (review R8).
test('RUNTIME-TRY10: GET 404/410 counts as ended and DELETE 404/410 as stopped; the record goes and the next pdd try makes a new one', async t => {
  for (const status of [404, 410]) {
    const setup = harbor(t);
    const gone = new Set(), lastTry = f => f.posts.filter(post => post.command === 'try').at(-1).request.requestId;
    const fake = await fakeRuntime(t, (entry, f) => {
      const id = entry.url.split('/').at(-1);
      if ((entry.method === 'DELETE' || entry.method === 'GET') && gone.has(id)) {
        return { status, json: { error: { code: status === 404 ? 'not-found' : 'result-expired', message: 'gone' } } };
      }
      return trying()(entry, f);
    });
    assert.equal((await tryStory(setup, fake, ['place-order'], { '--no-open': true })).code, 0);
    gone.add(lastTry(fake));
    const stopped = await tryStory(setup, fake, ['place-order'], { '--stop': true });
    assert.equal(stopped.code, 0, `${status}: ${stopped.err}`); assert.match(stopped.out, /is stopped/);
    assert.equal((await tryStory(setup, fake, ['place-order'], { '--stop': true })).code, 2);
    assert.equal((await tryStory(setup, fake, ['place-order'], { '--no-open': true })).code, 0);
    gone.add(lastTry(fake));
    const again = await tryStory(setup, fake, ['place-order'], { '--no-open': true });
    assert.equal(again.code, 0, `${status}: ${again.err}`);
    assert.equal(fake.posts.filter(post => post.command === 'try').length, 3, String(status));
  }
});

// Wrong: the note about other files reads like an alarm, or prints twice (runtime session, real check of b61547c).
test('RUNTIME-TRY11: pdd try says once, in calm words, how many sent files are not prompt, story or test files', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, trying());
  const result = await tryStory(setup, fake, ['place-order'], { '--no-open': true });
  assert.equal(result.code, 0);
  const said = (result.out + result.err).split('\n').filter(text => text.includes('not prompt, story or test files'));
  assert.deepEqual(said, ['Sent 6 files (1 is not prompt, story or test files; run `pdd check --files` to see them).']);
});
