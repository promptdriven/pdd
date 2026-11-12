import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, readFileSync, renameSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { runTry } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, PLACE, portsFor, temp } from './runtime-fake.mjs';

// Local native replay only: Git and saved state are real; authentication and service replies are injected.
const inventory = JSON.parse(readFileSync(new URL('./runtime/stop-simulation-by-story-path-cases.json', import.meta.url), 'utf8'),
  (key, value, context) => typeof value === 'number' && /^-?(?:0|[1-9][0-9]*)$/.test(context.source)
    && !Number.isSafeInteger(value) ? BigInt(context.source) : value);
const origin = 'https://runtime.example.test';
const stopId = '22222222-2222-4222-8222-222222222222';
const secondId = '33333333-3333-4333-8333-333333333333';
const uuid = /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/;

function fixture(t, vector, { absent = false } = {}) {
  const sandbox = temp(t), repo = join(sandbox, 'repo'), state = join(sandbox, 'state'), home = join(sandbox, 'home');
  mkdirSync(repo); mkdirSync(home);
  const git = spawnSync('git', ['init', '-q'], { cwd: repo, encoding: 'utf8' });
  assert.equal(git.status, 0, git.stderr);
  const selected = { ...inventory.setup.selected_record, origin, login: 'octo',
    seed_scenario: { retained: ['seed'] }, prompt_hashes: { 'prompts/app.prompt.md': 'a'.repeat(64) },
    ...vector.record_override };
  const key = inventory.setup.selected_record_key;
  if (!absent) for (const path of [selected.storyPath, key]) {
    mkdirSync(dirname(join(repo, path)), { recursive: true }); writeFileSync(join(repo, path), 'synthetic local fixture\n');
  }
  const tries = { [key]: selected };
  if (vector.other_saved_record || vector.id === 'ambiguous-short-name') {
    tries[vector.other_saved_record ?? 'tests/other/control-panel.json'] = {
      id: secondId, story: vector.id === 'ambiguous-short-name' ? selected.story : 'other',
      storyPath: 'user_stories/other.md', title: 'Other Try', origin, retained: { untouched: true },
    };
  }
  const saved = { root: repo, last_batch: 'retained-batch', retained: { unrelated: [1, 2] }, tries };
  const repoKey = createHash('sha256').update(repo).digest('hex').slice(0, 16);
  const file = join(state, 'repos', `${repoKey}.json`);
  mkdirSync(dirname(file), { recursive: true });
  const before = JSON.stringify(saved, null, 2) + '\n'; writeFileSync(file, before);
  return { repo, state, home, file, before, saved, key, selected };
}

async function replay(t, vector, words, status = 202) {
  const f = fixture(t, vector, { absent: vector.id === 'story-absent-on-current-branch' });
  if (vector.id === 'story-absent-on-current-branch') {
    assert.equal(existsSync(join(f.repo, f.selected.storyPath)), false);
    assert.equal(existsSync(join(f.repo, f.key)), false);
  }
  const requests = [];
  let issued = 0;
  const job = state => ({ requestId: stopId, id: stopId, command: 'stop', state,
    result: state === 'running' ? null : { exitCode: state === 'passed' ? 0 : 1, refusals: [],
      session: { id: f.selected.id, state: state === 'passed' ? 'stopped' : 'unknown' } } });
  const { ports, clock } = portsFor({ HOME: f.home, PDD_STATE_DIR: f.state, PDD_RUNTIME_URL: origin }, {
    randomUUID: () => { issued += 1; assert.equal(issued, 1); return stopId; },
    fetch: async (url, init) => {
      // A selected record must survive both dispatch and the confirming status read.
      assert.equal(readFileSync(f.file, 'utf8'), f.before, 'state changed before stop confirmation');
      const request = { method: init.method, path: new URL(url).pathname, id: init.headers['X-Request-Id'] };
      requests.push(request);
      if (request.method === 'DELETE') {
        assert.equal(request.path, `/v1/try/${f.selected.id}`);
        assert.match(request.id, uuid);
        return Response.json(status === 202 ? job('running') : { error: { code: 'not-found' } }, { status });
      }
      assert.equal(request.method, 'GET'); assert.equal(request.path, `/v1/runs/${stopId}`);
      return Response.json(job(vector.id === 'unconfirmed-stop' ? 'failed' : 'passed'));
    },
  });
  const code = await runTry({ cwd: f.repo, words, options: vector.options }, ports);
  const afterBytes = readFileSync(f.file, 'utf8'), after = JSON.parse(afterBytes);
  const deletes = requests.filter(request => request.method === 'DELETE' && request.path === `/v1/try/${f.selected.id}`);
  const expected = vector.expected ?? vector.expected_each;
  for (const [name, value] of Object.entries(expected)) {
    switch (name) {
      case 'exit_code': assert.equal(code, value, `STOP-STORY-PATH ${vector.id}: ${ports.stderr.text}`); break;
      case 'exit_code_nonzero': assert.equal(code !== 0, value); break;
      case 'selected_deletes': assert.equal(deletes.length, value); break;
      case 'stop_job_read': assert.equal(requests.some(request => request.method === 'GET' && request.path === `/v1/runs/${stopId}`), value); break;
      case 'uuid_request_header': assert.equal(deletes.every(request => uuid.test(request.id)), value); break;
      case 'selected_record_removed': assert.equal(!Object.hasOwn(after.tries, f.key), value); break;
      case 'other_record_unchanged': assert.equal(JSON.stringify(after.tries[vector.other_saved_record]) === JSON.stringify(f.saved.tries[vector.other_saved_record]), value); break;
      case 'stdout_from_setup': assert.equal(ports.stdout.text, value ? inventory.setup.expected_stdout : ''); break;
      case 'selected_record_unchanged': assert.equal(JSON.stringify(after.tries[f.key]) === JSON.stringify(f.selected), value); break;
      case 'success_confirmation_absent': assert.equal(!ports.stdout.text.includes(inventory.setup.expected_stdout.trim()), value); break;
      case 'runtime_requests': assert.equal(requests.length, value); break;
      case 'authentication_calls': assert.equal(clock.gh.length, value); break;
      case 'all_saved_records_unchanged': assert.equal(afterBytes === f.before, value); break;
      default: assert.fail(`Not replayed: ${vector.id} expectation ${name}`);
    }
  }
  // Compare the entire surviving state, including fields unrelated to selection.
  const surviving = structuredClone(f.saved);
  if (code === 0) delete surviving.tries[f.key];
  assert.deepEqual(after, surviving);
  if (code !== 0) assert.equal(afterBytes, f.before);
}

for (const vector of inventory.cases) test(`STOP-STORY-PATH ${vector.id} (${vector.criterion_ids.join(', ')})`, async t => {
  if (vector.repeat_with_fresh_state) {
    for (const words of vector.repeat_with_fresh_state) await t.test(JSON.stringify(words), t => replay(t, vector, words));
  } else if (vector.repeat_with_fresh_state_delete_status) {
    for (const status of vector.repeat_with_fresh_state_delete_status) await t.test(`DELETE ${status}`, t => replay(t, vector, vector.words, status));
  } else await replay(t, vector, vector.words);
});

test('STOP-STORY-PATH preserves leading ./ selectors', async t => {
  const vector = inventory.cases.find(vector => vector.id === 'saved-story-path');
  for (const selector of [inventory.setup.selected_record.storyPath, inventory.setup.selected_record.story, inventory.setup.selected_record_key]) {
    await t.test(selector, t => replay(t, vector, [`./${selector}`]));
  }
});

test('STOP-STORY-PATH starts from an authored Story path, then stops the saved Try by that path (AC1)', async t => {
  const storyPath = inventory.setup.selected_record.storyPath, testPath = inventory.setup.selected_record_key;
  const f = harbor(t, repo => {
    mkdirSync(dirname(join(repo, storyPath)), { recursive: true });
    mkdirSync(dirname(join(repo, testPath)), { recursive: true });
    const originalStory = join(repo, 'user_stories/place-order.md');
    writeFileSync(originalStory, readFileSync(originalStory, 'utf8').replace('# Place a coffee order', `# ${inventory.setup.selected_record.title}`));
    renameSync(originalStory, join(repo, storyPath));
    const originalTest = join(repo, 'tests/place-order.json'), doc = JSON.parse(readFileSync(originalTest, 'utf8'));
    doc.story_path = storyPath; writeFileSync(originalTest, JSON.stringify(doc));
    renameSync(originalTest, join(repo, testPath));
  });
  const fake = await fakeRuntime(t, (entry, service) => {
    if (entry.command === 'lint') return { status: 200, json: service.lint(entry.request.requestId,
      [{ path: PLACE, state: 'approved', admission_state: 'approved', interface: { calls: [] } }]) };
    if (entry.command === 'try') return { status: 200, json: service.tryJob(entry.request.requestId) };
    if (entry.method === 'DELETE') return { status: 202, json: service.job(entry.headers['x-request-id'], 'stop', 'running') };
    if (entry.url.endsWith('/tests')) return { status: 404, json: { error: { code: 'not-found' } } };
    return { status: 200, json: service.stopJob(entry.url.split('/').at(-1), fake.posts.find(entry => entry.command === 'try').request.requestId) };
  });
  let issued = 0;
  const { ports } = portsFor({ HOME: f.home, PDD_STATE_DIR: f.state, PDD_RUNTIME_URL: fake.origin }, {
    randomUUID: () => `44444444-4444-4444-8444-${String(++issued).padStart(12, '0')}`,
  });
  const started = await runTry({ cwd: f.repo, words: [storyPath], options: { '--no-open': true, '--no-wait': true } }, ports);
  assert.equal(started, 0, ports.stderr.text);
  const file = join(f.state, 'repos', `${createHash('sha256').update(f.repo).digest('hex').slice(0, 16)}.json`);
  const saved = JSON.parse(readFileSync(file, 'utf8'));
  assert.equal(saved.tries[testPath].storyPath, storyPath);
  assert.equal(fake.posts.find(entry => entry.command === 'try').request.seed, testPath);
  ports.stdout.text = ''; ports.stderr.text = '';
  const stopped = await runTry({ cwd: f.repo, words: [storyPath], options: { '--stop': true } }, ports);
  assert.equal(stopped, 0, `STOP-STORY-PATH start then stop: ${ports.stderr.text}`);
  assert.equal(ports.stdout.text, inventory.setup.expected_stdout);
  assert.deepEqual(fake.deletes.map(entry => entry.url), [`/v1/try/${saved.tries[testPath].id}`]);
  assert.deepEqual(JSON.parse(readFileSync(file, 'utf8')).tries, {});
});
