import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { runTry } from '../src/runtime-client.mjs';

// Oracle authority: user_stories/stop-simulation-by-story-path.md, Rules to check
// and AC3/AC4. This is a native bounded check, not an interpreted prompt verdict.
// Bounds: all 16 subsets of four records x 13 authored selector rows x two file
// worlds x seven reply traces = 2,912 public runTry executions. A row declares
// its eligible record labels independently of the production selection code.
// No absolute paths, normalization variants, malformed/legacy records, concurrent
// writers, live authentication/service, or start/reopen/recovery behavior is proved.
const origin = 'https://runtime.example.test';
const records = [
  { label: 'A', key: 'tests/rehearsal/control-panel.json', story: 'control-panel',
    storyPath: 'user_stories/rehearsal/control-panel.md', title: 'Control panel rehearsal' },
  { label: 'B', key: 'tests/auxiliary.json', story: 'auxiliary',
    storyPath: 'user_stories/rehearsal/control-panel.md', title: 'Auxiliary rehearsal' },
  { label: 'C', key: 'tests/third.json', story: 'control-panel',
    storyPath: 'user_stories/third.md', title: 'Third rehearsal' },
  { label: 'D', key: 'tests/else/control-panel.json', story: 'different-story',
    storyPath: 'user_stories/different-story.md', title: 'Different rehearsal' },
].map((record, i) => ({ ...record, value: {
  story: record.story, storyPath: record.storyPath, title: record.title,
  id: `${String(i + 1).repeat(8)}-1111-4111-8111-111111111111`, origin, login: 'synthetic-user',
  retained: { seed: [i, { unchanged: true }], prompt_hashes: { example: 'a'.repeat(64) } },
} }));

// Labels express the approved relation. In particular, repeated aliases within
// B identify one record; a Story-name/basename collision across A/C/D is ambiguous.
const selectors = [
  { words: [], eligible: ['A', 'B', 'C', 'D'] },
  { words: ['user_stories/rehearsal/control-panel.md'], eligible: ['A', 'B'] },
  { words: ['control-panel'], eligible: ['A', 'C', 'D'] },
  { words: ['tests/rehearsal/control-panel.json'], eligible: ['A'] },
  { words: ['auxiliary'], eligible: ['B'] },
  { words: ['tests/auxiliary.json'], eligible: ['B'] },
  { words: ['user_stories/third.md'], eligible: ['C'] },
  { words: ['tests/third.json'], eligible: ['C'] },
  { words: ['third'], eligible: ['C'] },
  { words: ['user_stories/different-story.md'], eligible: ['D'] },
  { words: ['tests/else/control-panel.json'], eligible: ['D'] },
  { words: ['different-story'], eligible: ['D'] },
  { words: ['missing-story'], eligible: [] },
];
const replies = [
  { name: 'pending then passed', status: 202, terminal: 'passed', confirmed: true, reads: 2 },
  { name: 'immediate passed', status: 200, terminal: 'passed', confirmed: true, reads: 0 },
  { name: 'already absent', status: 404, confirmed: true, reads: 0 },
  { name: 'expired', status: 410, confirmed: true, reads: 0 },
  { name: 'pending then failed', status: 202, terminal: 'failed', confirmed: false, reads: 2 },
  { name: 'pending then unknown', status: 202, terminal: 'unknown', confirmed: false, reads: 2 },
  { name: 'unconfirmed HTTP reply', status: 503, confirmed: false, reads: 0 },
];

test('STOP-STORY-PATH formal: exhaustive bounded saved-selection and removal rules', async t => {
  const sandbox = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-stop-formal-')));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));
  const repo = join(sandbox, 'repo'), state = join(sandbox, 'private-state'), home = join(sandbox, 'home');
  mkdirSync(repo); mkdirSync(home);
  const initialized = spawnSync('git', ['init', '-q'], { cwd: repo, encoding: 'utf8' });
  assert.equal(initialized.status, 0, initialized.stderr);
  const file = join(state, 'repos', `${createHash('sha256').update(repo).digest('hex').slice(0, 16)}.json`);
  mkdirSync(dirname(file), { recursive: true });
  let executions = 0, uniqueSelections = 0, rejectedSelections = 0, confirmedRemovals = 0, retainedStops = 0;
  let requestSequence = 0;
  for (const present of [false, true]) {
    if (present) for (const record of records) for (const path of [record.storyPath, record.key]) {
      mkdirSync(dirname(join(repo, path)), { recursive: true });
      writeFileSync(join(repo, path), 'Synthetic formal fixture; selection must use saved state.\n');
    }
    for (let mask = 0; mask < 16; mask++) {
      const saved = records.filter((_, i) => mask & (1 << i));
      for (const selector of selectors) for (const reply of replies) {
        const eligible = saved.filter(record => selector.eligible.includes(record.label));
        const selected = eligible.length === 1 ? eligible[0] : null;
        const context = `STOP-STORY-PATH formal mask=${mask} files=${present} words=${JSON.stringify(selector.words)} reply=${reply.name}`;
        const before = { root: repo, last_batch: 'preserved-batch', unrelated: { values: [1, 2, 3] },
          tries: Object.fromEntries(saved.map(record => [record.key, record.value])) };
        const beforeBytes = `${JSON.stringify(before, null, 2)}\n`;
        writeFileSync(file, beforeBytes);
        let stdout = '', stderr = '', reads = 0, time = Date.UTC(2026, 0, 1);
        const requests = [], auth = [], snapshots = [];
        const observe = stage => snapshots.push({ stage, bytes: readFileSync(file, 'utf8'), stdout });
        const stopId = `55555555-5555-4555-8555-${String(++requestSequence).padStart(12, '0')}`;
        const job = state => ({ requestId: stopId, id: stopId, command: 'stop', state,
          result: state === 'running' ? null : { exitCode: state === 'passed' ? 0 : 1, refusals: [],
            session: { id: selected?.value.id, state: state === 'passed' ? 'stopped' : 'unknown' } } });
        const code = await runTry({ cwd: repo, words: selector.words, options: { '--stop': true } }, {
          env: { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: origin },
          stdout: { write: text => { stdout += text; } }, stderr: { write: text => { stderr += text; } },
          interactive: false, agentBridge: false, onInterrupt: () => () => {},
          now: () => time, sleep: async ms => { time += ms; }, randomUUID: () => stopId,
          gh: args => {
            observe('authentication'); auth.push(args);
            return { status: 0, stdout: args[0] === 'auth' ? 'synthetic-formal-token\n' : 'synthetic-user 123\n' };
          },
          fetch: async (url, init) => {
            // Observe here; assert after runTry so its transport error handler
            // cannot turn an assertion into an apparent network error.
            observe(init.method);
            requests.push({ method: init.method, path: new URL(url).pathname, requestId: init.headers['X-Request-Id'] });
            if (init.method === 'DELETE') return Response.json(reply.status < 300
              ? job(reply.status === 202 ? 'running' : reply.terminal)
              : { error: { code: 'synthetic-stop-reply' } }, { status: reply.status });
            reads++;
            return Response.json(job(reads === 1 ? 'running' : reply.terminal));
          },
        });
        executions++;
        const afterBytes = readFileSync(file, 'utf8');
        for (const snapshot of snapshots) {
          assert.equal(snapshot.bytes, beforeBytes, `${context}: record removed before confirmation at ${snapshot.stage}`);
          assert.equal(snapshot.stdout, '', `${context}: success printed before confirmation`);
        }
        if (!selected) {
          rejectedSelections++;
          assert.equal(code, 2, `${context}: non-unique selection must exit 2; ${stderr}`);
          assert.equal(auth.length, 0, `${context}: authentication before unique selection`);
          assert.deepEqual(requests, [], `${context}: service call before unique selection`);
          assert.equal(stdout, '', `${context}: rejected selection printed success`);
          assert.equal(afterBytes, beforeBytes, `${context}: rejected selection changed state`);
          continue;
        }
        uniqueSelections++;
        if (reply.confirmed) assert.equal(code, 0, `${context}: confirmed unique stop must exit 0; ${stderr}`);
        assert.equal(auth.length, uniqueSelections === 1 ? 2 : 1, `${context}: selected stop must authenticate`);
        assert.deepEqual(auth[0], ['auth', 'token'], `${context}: selected stop must read live gh auth token`);
        assert.deepEqual(requests, [
          { method: 'DELETE', path: `/v1/try/${selected.value.id}`, requestId: stopId },
          ...Array.from({ length: reply.reads }, () => ({ method: 'GET', path: `/v1/runs/${stopId}`, requestId: undefined })),
        ], `${context}: selected stop request/read identity`);
        if (reply.confirmed) {
          confirmedRemovals++;
          assert.equal(stdout, `The Try link for "${selected.title}" is stopped.\n`, `${context}: confirmation text`);
          const expected = structuredClone(before);
          delete expected.tries[selected.key];
          assert.deepEqual(JSON.parse(afterBytes), expected, `${context}: only selected record may be removed`);
        } else {
          retainedStops++;
          assert.notEqual(code, 0, `${context}: unconfirmed stop must fail`);
          assert.equal(stdout, '', `${context}: unconfirmed stop printed success`);
          assert.equal(afterBytes, beforeBytes, `${context}: unconfirmed stop changed state`);
        }
      }
    }
  }
  assert.deepEqual({ executions, uniqueSelections, rejectedSelections, confirmedRemovals, retainedStops },
    { executions: 2912, uniqueSelections: 1260, rejectedSelections: 1652, confirmedRemovals: 720, retainedStops: 540 });
  t.diagnostic(`Proved (bounded): ${executions} public runTry executions; ${uniqueSelections} unique selections; ${rejectedSelections} rejections before auth/service; ${confirmedRemovals} confirmed selected-only removals; ${retainedStops} unconfirmed retained records.`);
});
