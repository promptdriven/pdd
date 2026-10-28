import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, readFileSync, readdirSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runTry } from '../src/runtime-client.mjs';
import { findTests, preflight, proseSha256 } from '../src/runtime-preflight.mjs';
import { Readable } from 'node:stream';
import { PLACE, fakeRuntime, harbor, portsFor, temp } from './runtime-fake.mjs';

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
  assert.deepEqual(Object.keys(request).sort(), ['max_calls', 'requestId', 'seed', 'source_sha256', 'tab']);
  assert.equal(request.max_calls, 160); assert.equal(request.seed, 'tests/place-order.json'); assert.equal(request.tab, 'call');
  assert.deepEqual(first.opened, [`${fake.origin}/s/${'t'.repeat(43)}/`]);
  assert.equal(first.out, 'Try budget 160 calls; 160 remaining. You are charged only for calls that run.\nTry link for "Place a coffee order" is open in your browser. It ends in 24 hours, or with: pdd try --stop place-order\n');
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
  const withMap = harbor(t, repo => { mkdirSync(join(repo, 'app')); writeFileSync(join(repo, 'app/app-map.json'), `${APP_MAP}\n`); });
  const fake = await fakeRuntime(t, trying());
  assert.equal((await tryStory(withMap, fake, ['place-order'], { '--no-open': true })).code, 0);
  const sent = fake.posts.filter(post => post.command === 'try');
  assert.equal(sent[0].request.app_map, 'app/app-map.json'); assert.equal(sent[0].request.tab, 'screen');
  const rooted = harbor(t, repo => { mkdirSync(join(repo, 'app')); writeFileSync(join(repo, 'app/app-map.json'), `${APP_MAP}\n`); writeFileSync(join(repo, 'app-map.json'), `${APP_MAP}\n`);
    writeFileSync(join(repo, 'other-map.json'), `${APP_MAP}\n`); });
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

// T3-11: only an explicit owner reopen makes a paused Try usable; its ID, seed and cap stay the same.
test('RUNTIME-TRY9: a paused Try is explicitly reopened before its link is reused', async t => {
  const setup = harbor(t); let paused = false, reopened = false, polls = 0;
  const fake = await fakeRuntime(t, (entry, f) => {
    const id=f.posts.find(p=>p.command==='try')?.request.requestId;
    if(entry.method==='POST' && entry.url===`/v1/try/${id}/reopen`){ reopened=true;return {status:200,json:f.job(id,'try','queued')}; }
    if(entry.method==='GET' && paused && entry.url===`/v1/runs/${id}`){
      if(!reopened)return {status:200,json:f.tryJob(id,undefined,'paused')};
      return ++polls===1 ? {status:200,json:f.job(id,'try','running')} : {status:200,json:f.tryJob(id)};
    }
    return trying()(entry,f);
  });
  assert.equal((await tryStory(setup,fake,['place-order'],{'--no-open':true})).code,0); paused=true;
  const again=await tryStory(setup,fake,['place-order'],{'--no-open':true});
  assert.equal(again.code,0,again.err);assert.equal(reopened,true);assert.equal(polls,2);
  assert.match(again.out,/keeps its original 24-hour expiry/);
  assert.equal(fake.jsonPosts.length,1);assert.deepEqual(fake.jsonPosts[0].json,{});
  assert.equal(fake.posts.filter(p=>p.command==='try').length,1);assert.equal(fake.deletes.length,0);
  assert.equal(again.clock.uuids,0,'same Try, no new request IDs');
});

test('a lost reopen reply is read once by ID, while a rejected reopen keeps the record and prints no link',async t=>{
  for(const outcome of ['lost','refused']){
    const setup=harbor(t);let paused=false,reopened=false;
    const fake=await fakeRuntime(t,(entry,f)=>{
      const id=f.posts.find(p=>p.command==='try')?.request.requestId;
      if(entry.method==='POST'&&entry.url===`/v1/try/${id}/reopen`){reopened=true;return outcome==='lost'?{destroy:true}:{status:409,json:{dispatch:'not_started',error:{code:'session-stopped',message:'This Try cannot reopen.'}}};}
      if(entry.method==='GET'&&paused&&entry.url===`/v1/runs/${id}`)return {status:200,json:f.tryJob(id,undefined,reopened&&outcome==='lost'?'running':'paused')};
      return trying()(entry,f);
    });
    assert.equal((await tryStory(setup,fake,['place-order'],{'--no-open':true})).code,0);paused=true;
    const again=await tryStory(setup,fake,['place-order'],{'--no-open':true});
    assert.equal(again.code,outcome==='lost'?0:3,again.err);assert.equal(fake.jsonPosts.length,1);
    assert.equal(fake.posts.filter(p=>p.command==='try').length,1);
    if(outcome==='refused'){assert.doesNotMatch(again.out,/Try link/);assert.match(again.err,/cannot reopen/);assert.match(again.err,/pdd try tests\/place-order\.json/);}
  }
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
  const setup = harbor(t, repo => writeFileSync(join(repo, 'pdd-source.json'), JSON.stringify({ include: ['README.md'] }))), fake = await fakeRuntime(t, trying());
  const result = await tryStory(setup, fake, ['place-order'], { '--no-open': true });
  assert.equal(result.code, 0);
  const said = (result.out + result.err).split('\n').filter(text => text.includes('not prompt, story or test files'));
  assert.deepEqual(said, ['Sent 4 files (1 is not prompt, story or test files; run `pdd check --files` to see them).']);
});

const APP_MAP = JSON.stringify({ schema_version: 'prompt-runtime.app-map.v1', name: 'Harbor', initial_screen: 'menu' });

// Wrong: --app-map with an HTML page is sent (or silently ignored) and the Try breaks later (real-user web test, issue 4).
test('RUNTIME-TRY12: --app-map must be a Git-visible app-map JSON; an open Try needs --new for a new app map or tab', async t => {
  const setup = harbor(t, repo => { mkdirSync(join(repo, 'public')); writeFileSync(join(repo, 'public/index.html'), '<html></html>\n');
    writeFileSync(join(repo, 'public/map.json'), '{"screens": []}\n'); writeFileSync(join(repo, 'app.json'), `${APP_MAP}\n`); });
  const fake = await fakeRuntime(t, trying());
  for (const [path, said] of [['public/index.html', /--app-map public\/index\.html is not an app map: it is not JSON\. .*See RUNBOOK\.md §13\./],
    ['public/map.json', /--app-map public\/map\.json is not an app map: its schema_version is not "prompt-runtime\.app-map\.v1"\./],
    ['nope.json', /--app-map nope\.json is not a Git-visible file in this repository\./]]) {
    const result = await tryStory(setup, fake, ['place-order'], { '--app-map': path, '--no-open': true });
    assert.equal(result.code, 2, path); assert.match(result.err, said, path); assert.equal(fake.posts.length, 0, path);
  }
  assert.equal((await tryStory(setup, fake, ['place-order'], { '--no-open': true })).code, 0);
  for (const options of [{ '--app-map': 'app.json' }, { '--tab': 'screen' }]) {
    const open = await tryStory(setup, fake, ['place-order'], { ...options, '--no-open': true });
    assert.equal(open.code, 2, JSON.stringify(options));
    assert.match(open.err, /A Try for "Place a coffee order" is already open\. --app-map and --tab apply only to a new Try: run pdd try place-order --new/);
  }
  const fresh = await tryStory(setup, fake, ['place-order'], { '--app-map': 'app.json', '--new': true, '--no-open': true });
  assert.equal(fresh.code, 0, fresh.err);
  assert.equal(fake.posts.filter(post => post.command === 'try').at(-1).request.app_map, 'app.json');
});

// Wrong: after a Try setup that the server lost (state unknown, for example after a restart), pdd try stays stuck until --new (issue 4).
test('RUNTIME-TRY13: a Try setup that ends unknown is forgotten, and the next pdd try makes a new Try', async t => {
  const setup = harbor(t), lost = new Set();
  const fake = await fakeRuntime(t, (entry, f) => {
    const id = entry.url.split('/').at(-1);
    if (entry.method === 'GET' && lost.has(id)) return { status: 200, json: f.job(id, 'try', 'unknown', { exitCode: 3, refusals: [{ code: 'service-restarted', message: 'The run may have executed.' }] }) };
    if (entry.method === 'POST' && entry.command === 'try' && f.posts.filter(post => post.command === 'try').length === 2) lost.add(entry.request.requestId);
    return trying()(entry, f);
  });
  assert.equal((await tryStory(setup, fake, ['place-order'], { '--no-open': true })).code, 0);
  const restarted = await tryStory(setup, fake, ['place-order'], { '--new': true, '--no-open': true });
  assert.equal(restarted.code, 3);
  assert.match(restarted.err, /The Try setup did not finish on the server \(its state is unknown; the server may have restarted\)\. It used no AI calls\. Run pdd try place-order to make a new Try\./);
  const next = await tryStory(setup, fake, ['place-order'], { '--no-open': true });
  assert.equal(next.code, 0, next.err);
  assert.equal(fake.posts.filter(post => post.command === 'try').length, 3);
  lost.add(fake.posts.filter(post => post.command === 'try').at(-1).request.requestId);
  const after = await tryStory(setup, fake, ['place-order'], { '--no-open': true });
  assert.equal(after.code, 0, after.err); assert.equal(fake.posts.filter(post => post.command === 'try').length, 4);
});

// Wrong: adding a saved case to a compact test file rewrites the whole file (issue 16).
test('RUNTIME-TRY14: a saved case is added to a one-line test file without rewriting the rest', async t => {
  const setup = harbor(t, repo => {
    const file = join(repo, 'tests/place-order.json'); writeFileSync(file, `${JSON.stringify(JSON.parse(readFileSync(file, 'utf8')))}\n`);
  });
  const original = readFileSync(join(setup.repo, 'tests/place-order.json'), 'utf8');
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET' && entry.url.endsWith('/tests') ? { status: 200, json: { tests: [savedCase('a')] } } : trying()(entry, f));
  assert.equal((await tryStory(setup, fake, ['place-order'], { '--no-open': true })).code, 0);
  const text = readFileSync(join(setup.repo, 'tests/place-order.json'), 'utf8'), close = original.lastIndexOf(']');
  assert.ok(text.startsWith(original.slice(0, close)), text.slice(0, 200));
  assert.equal(JSON.parse(text).steps.length, 2);
});

// Wrong: on a branch without the story, pdd try --stop says "No tests found" and the open link cannot be stopped (issue 14).
test('RUNTIME-TRY15: pdd try --stop finds the Try by story name in the state, without the story on this branch', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, trying());
  assert.equal((await tryStory(setup, fake, ['place-order'], { '--no-open': true })).code, 0);
  rmSync(join(setup.repo, 'tests'), { recursive: true }); rmSync(join(setup.repo, 'user_stories'), { recursive: true });
  const unknown = await tryStory(setup, fake, ['refund'], { '--stop': true });
  assert.equal(unknown.code, 2); assert.match(unknown.err, /No open Try for "refund"\. Open Try links: place-order/);
  const stopped = await tryStory(setup, fake, ['place-order'], { '--stop': true });
  assert.equal(stopped.code, 0, stopped.err); assert.equal(fake.deletes.length, 1);
  assert.equal(stopped.out, 'The Try link for "Place a coffee order" is stopped.\n');
  assert.equal((await tryStory(setup, fake, [], { '--stop': true })).code, 2);
});

// Wrong: a saved case from anyone with the Try link writes outside the repo, follows a symlink, or edits a non-test file (runtime review).
test('RUNTIME-TRY16: hostile saved cases write nothing outside tests/ or into non-test files', async t => {
  const outside = temp(t);
  const run = async (setup, saved) => {
    const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET' && entry.url.endsWith('/tests') ? { status: 200, json: { tests: [saved] } } : trying()(entry, f));
    return tryStory(setup, fake, ['place-order'], { '--no-open': true });
  };
  const story = harbor(t), parent = readdirSync(join(story.repo, '..')).sort();
  const escape = await run(story, savedCase('a', { story: '../../package' }));
  assert.equal(escape.code, 0); assert.match(escape.out, /^not added: its story "\.\.\/\.\.\/package" is not a story file in this repository\.$/m);
  assert.deepEqual(readdirSync(join(story.repo, '..')).filter(name => name !== 'state').sort(), parent); assert.equal(existsSync(join(story.repo, 'tests/package.json')), false);
  const refund = { story: 'user_stories/refund.md', criterion: { id: 'AC1', text: 'A refund returns the total.' } };
  const addRefund = repo => writeFileSync(join(repo, 'user_stories/refund.md'), '# Refund an order\n\n## Acceptance criteria\n\n1. A refund returns the total.\n');
  const named = harbor(t, addRefund);
  assert.equal((await run(named, { ...savedCase('b', refund), path: '../x.json' })).code, 0);
  assert.equal(existsSync(join(named.repo, '../x.json')), false); assert.equal(existsSync(join(named.repo, 'x.json')), false);
  assert.ok(existsSync(join(named.repo, 'tests/refund.json')));
  const linked = harbor(t, repo => {
    addRefund(repo); mkdirSync(join(repo, 'scenarios'));
    for (const name of ['place-order.json', 'unknown-item.json']) writeFileSync(join(repo, 'scenarios', name), readFileSync(join(repo, 'tests', name)));
    rmSync(join(repo, 'tests'), { recursive: true }); symlinkSync(outside, join(repo, 'tests')); writeFileSync(join(repo, '.gitignore'), 'tests\n');
  });
  const viaLink = await run(linked, savedCase('c', refund));
  assert.match(viaLink.out, /^not added: tests\/ is a symbolic link\. pdd writes test files only inside the repository\.$/m);
  assert.deepEqual(readdirSync(outside), []);
  const pkg = harbor(t, repo => {
    const doc = JSON.parse(readFileSync(join(repo, 'tests/place-order.json'), 'utf8'));
    writeFileSync(join(repo, 'package.json'), JSON.stringify(doc)); rmSync(join(repo, 'tests/place-order.json'));
  });
  const before = readFileSync(join(pkg.repo, 'package.json'), 'utf8');
  const intoPackage = await run(pkg, savedCase('d'));
  assert.match(intoPackage.out, /^not added: package\.json is not a file pdd adds steps to\. Move the test to tests\/\.$/m);
  assert.equal(readFileSync(join(pkg.repo, 'package.json'), 'utf8'), before);
});

// The Try page's approval requests, as GET /v1/try/<id>/approvals returns them (agreed fields, PLAN-0.1.4).
const approval = (id, prose_sha256, prompt_path = PLACE) => ({ id, prompt_path, prose_sha256, requested_at: '2026-10-27T21:00:00Z', state: 'pending' });
const draftPlace = repo => { const file = join(repo, PLACE); writeFileSync(file, readFileSync(file, 'utf8').replace('"status": "approved"', '"status": "draft"')); };

// Wrong: a click on the Try page approves a prompt without the person's y in the terminal, or approves a text that changed (#9).
test('RUNTIME-TRY17: pdd try asks y/n for each approval request from the Try page and answers the page', async t => {
  const setup = harbor(t, draftPlace), hash = proseSha256(readFileSync(join(setup.repo, PLACE), 'utf8'));
  let polls = 0;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'GET' && entry.url.endsWith('/approvals')) {
      polls += 1;
      const answered = new Set(f.jsonPosts.map(post => post.url.split('/').at(-1)));
      const all = polls === 1 ? [] : [approval('a1', '0'.repeat(64)), approval('a2', hash), approval('a3', hash), approval('a4', hash, '../outside.prompt.md')];
      return { status: 200, json: { approvals: all.filter(item => !answered.has(item.id)) } };
    }
    if (entry.method === 'POST' && entry.json) return { status: 200, json: { id: entry.url.split('/').at(-1), state: entry.json.state } };
    if (entry.method === 'GET' && polls >= 4 && !entry.url.endsWith('/tests')) return { status: 200, json: f.tryJob(entry.url.split('/').at(-1), undefined, 'stopped') };
    return trying()(entry, f);
  });
  const result = await tryStory(setup, fake, ['place-order'], { '--no-open': true }, { interactive: true, stdin: Readable.from(['y\nn\n']) });
  assert.equal(result.code, 0, result.err);
  assert.ok(fake.jsonPosts.every(post => post.url.startsWith(`/v1/try/${fake.posts.find(item => item.command === 'try').request.requestId}/approvals/`)));
  const states = Object.fromEntries(fake.jsonPosts.map(post => [post.url.split('/').at(-1), post.json.state]));
  assert.deepEqual(states, { a1: 'declined', a2: 'done', a3: 'done', a4: 'declined' });
  assert.match(result.out, /prompts\/place_order\.prompt\.md: the prompt changed since you clicked Approve\. Not approved/);
  assert.match(result.out, /Approve prompts\/place_order\.prompt\.md\? y\/n /);
  assert.match(result.out, /Approved prompts\/place_order\.prompt\.md\./);
  assert.match(result.out, /prompts\/place_order\.prompt\.md is already approved and current\./);
  assert.match(result.out, /not approved: \.\.\/outside\.prompt\.md is not a Git-visible \*\.prompt\.md file in this repository\./);
  assert.match(readFileSync(join(setup.repo, PLACE), 'utf8'), /"status": "approved"/);
  assert.equal(result.out.split('Approve prompts/place_order.prompt.md? y/n').length, 2);
});

// Wrong: an agent's pdd try (no terminal) answers an approval request, or blocks on it.
test('RUNTIME-TRY18: without a terminal pdd try only names the approval request; it asks nothing and answers nothing', async t => {
  const setup = harbor(t, draftPlace), hash = proseSha256(readFileSync(join(setup.repo, PLACE), 'utf8'));
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'GET' && entry.url.endsWith('/approvals')
    ? { status: 200, json: { approvals: [approval('b1', hash)] } } : trying()(entry, f));
  const result = await tryStory(setup, fake, ['place-order'], { '--no-open': true });
  assert.equal(result.code, 0);
  assert.match(result.out, /The Try page asks to approve prompts\/place_order\.prompt\.md\. A person answers it in a terminal: pdd try place-order/);
  assert.equal(fake.jsonPosts.length, 0); assert.match(readFileSync(join(setup.repo, PLACE), 'utf8'), /"status": "draft"/);
});

// Wrong: pdd try hides a not-invited answer behind a Try or link message (invite list, Oct 27).
test('RUNTIME-TRY19: pdd try says once that the login is not invited, exit 5, and makes no Try', async t => {
  const line = 'Your GitHub login octo is not on the PDD runtime invite list yet. Ask the PDD team to add you.';
  const denied = { status: 403, json: { code: 'not-invited', login: 'octo', message: 'not invited' } };
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST' ? denied : trying()(entry, f));
  const result = await tryStory(setup, fake, ['place-order'], { '--no-open': true });
  assert.equal(result.code, 5); assert.equal(result.out, ''); assert.ok(result.err.includes(line), result.err);
  assert.deepEqual(fake.posts.map(post => post.command), ['lint']);
  const open = harbor(t), first = await fakeRuntime(t, trying());
  assert.equal((await tryStory(open, first, ['place-order'], { '--no-open': true })).code, 0);
  const now = await fakeRuntime(t, (entry, f) => entry.method === 'GET' ? denied : trying()(entry, f));
  const reuse = await tryStory(open, now, ['place-order'], { '--no-open': true });
  assert.equal(reuse.code, 5); assert.ok(reuse.err.includes(line), reuse.err); assert.equal(now.posts.length, 0);
});

// Wrong: pdd try hides "update required" behind a Try message (0.1.6).
test('RUNTIME-TRY20: pdd try prints the update-required message as one line, exit 5, and makes no Try', async t => {
  const said = { status: 426, json: { code: 'update-required', message: 'Please update pdd.' } };
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST' ? said : trying()(entry, f));
  const result = await tryStory(setup, fake, ['place-order'], { '--no-open': true });
  assert.equal(result.code, 5); assert.equal(result.out, ''); assert.equal(result.err.trimEnd().split('\n').at(-1), 'Please update pdd.');
  assert.deepEqual(fake.posts.map(post => post.command), ['lint']);
});

// Wrong: a refused Try setup prints a check table and "pdd check" advice, and hides what was refused (runtime team live proof, Oct 27).
test('RUNTIME-TRY21: a refused Try setup says what was refused, why and the fix, in two plain lines, exit 4', async t => {
  const withMap = harbor(t, repo => writeFileSync(join(repo, 'app-map.json'), `${APP_MAP}\n`));
  const generic = 'The runtime refused this job. See the reported reason.';
  const refusing = refusals => async (entry, f) => {
    if (entry.method === 'GET' && !entry.url.endsWith('/tests')) {
      const id = entry.url.split('/').at(-1);
      return { status: 200, json: f.job(id, 'try', 'refused', { exitCode: 1, refusals, report: { verdict: 'refused', refusal: { code: refusals[0].code } }, session: { id, state: 'stopped' } }) };
    }
    return trying()(entry, f);
  };
  const map = await tryStory(withMap, await fakeRuntime(t, refusing([{ code: 'ambiguous-handler', message: generic, engine_message: null, section: null }])), ['place-order']);
  assert.equal(map.code, 4, map.err + map.out);
  assert.deepEqual(map.out.trimEnd().split('\n'), ['The Try could not start: the app map was refused (ambiguous-handler: on one screen, all taps of one kind must match by the same key).',
    'Fix app-map.json (RUNBOOK §13), then run pdd try place-order --new.']);
  assert.doesNotMatch(map.out + map.err, /Runtime check|pdd check(?! --files)|Story +Test|REFUSED/);
  const told = await tryStory(withMap, await fakeRuntime(t, refusing([{ code: 'template-reference-schema', message: generic,
    reason: 'the field id gets /event/target but has a minLength', fix: 'Make id a plain {"type": "string"} in prompts/place_order.prompt.md.' }])), ['place-order']);
  assert.deepEqual(told.out.trimEnd().split('\n'), ['The Try could not start: the app map was refused (template-reference-schema: the field id gets /event/target but has a minLength).',
    'Make id a plain {"type": "string"} in prompts/place_order.prompt.md. Then run pdd try place-order --new.']);
  const placed = await tryStory(withMap, await fakeRuntime(t, refusing([{ code: 'ambiguous-handler', reason: 'two button handlers on the screen list match by value and by name',
    fix: 'Match all buttons of the screen list by name.', file: 'app-map.json', at: '/screens/0/handlers/1', where: 'app-map.json /screens/0/handlers/1', cause: 'prompt',
    message: 'two button handlers on the screen list match by value and by name. Match all buttons of the screen list by name.' }])), ['place-order']);
  assert.deepEqual(placed.out.trimEnd().split('\n'), ['The Try could not start: the app map was refused (ambiguous-handler: two button handlers on the screen list match by value and by name; at app-map.json /screens/0/handlers/1).',
    'Match all buttons of the screen list by name. Then run pdd try place-order --new.']);
  const plain = harbor(t), posted = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'try'
    ? { status: 422, json: { error: { code: 'invalid-seed', message: 'The seed is not a test file.' } } } : trying()(entry, f));
  const seed = await tryStory(plain, posted, ['place-order']);
  assert.equal(seed.code, 4);
  assert.deepEqual(seed.out.trimEnd().split('\n'), ['The Try could not start: the server refused it (invalid-seed: The seed is not a test file.).',
    'Fix what it names, then run pdd try place-order --new.']);
});
