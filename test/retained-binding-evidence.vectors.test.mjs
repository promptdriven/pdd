import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {fixture} from './helpers/workflow-runner-fixture.mjs';
import {readRunResults} from '../src/workflow-results.mjs';
import {moveToCore, movedState} from '../src/autopilot-retire.mjs';
import {runStatus} from '../src/workflow-runner.mjs';

// Native local replay. Expectations come from the approved frozen cases, not
// from the reader. GitHub, Herdr and machine health use controlled local ports.
const vectorPath = new URL('./fixtures/retained-binding-evidence-cases.json', import.meta.url);
const vectorBytes = readFileSync(vectorPath);
const vectors = JSON.parse(vectorBytes);
const batch = '20261101-120000-abcd';
const save = run => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));

function writeBatch({home, root, intent, rows, at}) {
  const folder = join(home, '.pdd/runtime/batches', batch);
  mkdirSync(folder, {recursive: true});
  writeFileSync(join(folder, 'batch.json'), JSON.stringify({version: 1, batch,
    root, intent, created_at: new Date(at).toISOString(), rows}));
  // A saved summary must not become the source of detailed row evidence.
  writeFileSync(join(folder, 'summary.json'), JSON.stringify({batch, rows: [], summary_line: 'No admission verdict.'}));
  return folder;
}

function filesUnder(folder) {
  return Object.fromEntries(readdirSync(folder, {withFileTypes: true}).sort((a, b) => a.name.localeCompare(b.name))
    .flatMap(entry => entry.isDirectory()
      ? Object.entries(filesUnder(join(folder, entry.name))).map(([name, bytes]) => [join(entry.name, name), bytes])
      : [[entry.name, readFileSync(join(folder, entry.name))]]));
}

for (const intent of vectors.reader_intents) for (const row of vectors.reader_cases) {
  test(`3135 reader ${intent}: ${row.id} (${row.criteria.join(',')})`, t => {
    const base = mkdtempSync(join(tmpdir(), 'pdd-retained-evidence-'));
    t.after(() => rmSync(base, {recursive: true, force: true}));
    const root = join(base, 'project'), home = join(base, 'home');
    mkdirSync(root); mkdirSync(home);
    writeBatch({root, home, intent, rows: row.rows, at: Date.parse('2026-11-01T12:00:00Z')});
    const before = filesUnder(base);
    const requests = [];
    t.mock.method(globalThis, 'fetch', async (...args) => {
      requests.push(args); assert.fail('Saved-result reader must not request a service');
    });
    const results = readRunResults({root}, {env: {HOME: home},
      capture: () => assert.fail('Legacy evidence must not start source capture'),
      git: () => assert.fail('Saved-result reader must not start Git')});
    assert.equal(results.length, 1);
    assert.equal(results[0].kind, intent === 'check' ? 'pdd test' : 'pdd lint');
    assert.deepEqual(results[0].states, row.expected_states, '3135_READER_EVIDENCE_DROPPED');
    assert.deepEqual(filesUnder(base), before, 'AC4: reader changed saved files');
    assert.deepEqual(requests, [], 'AC4: reader requested a service');
    assert.deepEqual(readFileSync(vectorPath), vectorBytes, 'Frozen cases changed');
  });
}

const reply = (status, value) => ({code: 0, stdout: `HTTP/1.1 ${status} Test\r\n\r\n${value === undefined ? '' : JSON.stringify(value)}`});

async function retirementFixture(t, row) {
  const f = await fixture(t);
  f.ports.skipMetricsDelivery = true;
  assert.equal((await f.run()).exitCode, 0);
  assert.equal((await runStatus({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  const run = f.record();
  run.automaticOrigin = {repository: run.repo, coordinatorId: 'retire-owner', machine: 'retire-machine',
    claim: {commentId: '11', labelEventId: '12'}};
  run.state = 'waiting';
  run.gate = {kind: 'approve-pr', area: run.areas[run.area].name};
  run.done.check = 'Synthetic no-verdict receipt';
  if (row.question) run.question = {at: f.clock, ...row.question};
  if (row.blockedOn) run.blockedOn = row.blockedOn;
  save(run);
  const stateFile = join(f.state, 'launcher.json');
  const state = {enabled: true, engine: 'full', stateFile, cwd: f.source, repo: run.repo,
    coordinatorId: run.automaticOrigin.coordinatorId, machine: run.automaticOrigin.machine,
    agent: {id: 'claude', kind: 'claude', command: 'claude'}, parking: {legacy: true}, recipeDelivered: true};
  const actions = [], saves = [], cancellations = [], releases = [];
  const claim = {repository: state.repo, coordinatorId: state.coordinatorId, machine: state.machine, labelEventId: '12'};
  const gh = async args => {
    const method = args[args.indexOf('--method') + 1], endpoint = args[args.indexOf('--method') + 2];
    actions.push({method, endpoint});
    if (method === 'GET' && endpoint.includes('/issues?')) return reply(200, [{number: run.number}]);
    if (method === 'GET' && endpoint.endsWith(`/issues/${run.number}/comments?per_page=100`)) return reply(200, [{id: 11, body: JSON.stringify(claim)}]);
    if (method === 'GET' && endpoint.endsWith(`/issues/${run.number}/timeline?per_page=100`)) return reply(200, [{id: 12, event: 'labeled', label: {name: 'pdd:working'}}]);
    if (method === 'GET' && endpoint.endsWith(`/issues/${run.number}`)) return reply(200, {labels: [{name: 'pdd:working'}]});
    if (method === 'DELETE' && (endpoint.endsWith('/issues/comments/11') || endpoint.endsWith(`/issues/${run.number}/labels/pdd%3Aworking`))) return reply(204);
    return reply(404, {});
  };
  const ports = {now: () => f.clock, commonDir: f.git(f.source, 'rev-parse', '--path-format=absolute', '--git-common-dir'),
    samePath: (left, right) => left === right, coreJobs: () => new Set(), gh, herdr: f.herdr.herdr,
    save: async journal => { saves.push(structuredClone(journal)); }, listRuns: async () => [f.record()],
    cancelRun: async current => { cancellations.push(current.runId); current.state = 'cancelled'; save(current); return {exitCode: 0}; },
    releaseLocal: async current => { releases.push(current.runId); return {state: 'released'}; }, releaseSlots: async () => true,
    processes: async () => `${process.pid} ${process.ppid} ${process.pid} 1 Mon Nov 11 10:00:00 2026 node test-runner`, signal: () => assert.fail('The fixture has no old worker process.'), sleep: async () => {}};
  f.herdr.calls.length = 0;
  return {f, state, stateFile, ports, actions, saves, cancellations, releases};
}

for (const row of vectors.parking_cases) {
  test(`3135 retirement: ${row.id}`, async t => {
    const {f, state, stateFile, ports, actions, saves, cancellations, releases} = await retirementFixture(t, row);
    const readerCase = vectors.reader_cases.find(candidate => candidate.id === row.reader_case);
    assert.ok(readerCase, `Missing frozen reader case ${row.reader_case}`);
    const held = f.record();
    const folder = writeBatch({root: held.root, home: f.ports.env.HOME,
      intent: 'check', rows: readerCase.rows, at: f.clock});
    const before = filesUnder(folder);
    assert.equal(readRunResults({root: held.root, since: held.startedAt ?? 0}, {env: f.ports.env})[0]?.batch, batch);
    const first = await moveToCore({state, stateFile}, ports);
    assert.equal(first.done, true, first.message);
    const after = f.record();
    assert.equal(after.state, 'cancelled', '3135_RETIRED_RUN_NOT_CANCELLED');
    assert.deepEqual(cancellations, [held.runId]); assert.deepEqual(releases, [held.runId]);
    assert.ok(first.journal.cancelledRuns.includes(held.runId)); assert.ok(saves.length >= 7);
    const moved = movedState(state, first.journal);
    assert.equal(moved.engine, 'core'); assert.equal(moved.parking, undefined); assert.equal(moved.recipeDelivered, undefined);
    assert.deepEqual(filesUnder(folder), before, 'Parking changed the saved receipt');
    assert.deepEqual(f.pushes, []); assert.deepEqual(f.prs, []); assert.deepEqual(f.edits, []);
    assert.equal(f.herdr.calls.some(args => args[0] === 'pane' && args[1] === 'run'), false);
    assert.equal(f.herdr.calls.some(args => args[0] === 'agent' && args[1] === 'prompt'), false);
    const actionCount = actions.length;
    const again = await moveToCore({state: moved, stateFile}, ports);
    assert.equal(again.done, true); assert.equal(again.message, '');
    assert.deepEqual(cancellations, [held.runId], '3135_RETIREMENT_REPEATED_CANCELLATION');
    assert.equal(actions.length, actionCount, '3135_RETIREMENT_REPEATED_CLEANUP');
    assert.deepEqual(readFileSync(vectorPath), vectorBytes, 'Frozen cases changed');
  });
}

test('3135 retirement: a saved evidence move retries before cancelling the old run', async t => {
  const {f, state, stateFile, ports, cancellations} = await retirementFixture(t, vectors.parking_cases[0]);
  const held = f.record(), readerCase = vectors.reader_cases.find(candidate => candidate.id === vectors.parking_cases[0].reader_case);
  const folder = writeBatch({root: held.root, home: f.ports.env.HOME, intent: 'check', rows: readerCase.rows, at: f.clock});
  const before = filesUnder(folder), saveJournal = ports.save; let attempts = 0;
  ports.save = async journal => { attempts++; if (attempts === 2) throw Error('journal unavailable'); await saveJournal(journal); };
  const delayed = await moveToCore({state, stateFile}, ports);
  assert.equal(delayed.done, false); assert.equal(f.record().state, 'waiting'); assert.deepEqual(cancellations, []);
  assert.match(delayed.message, /could not save the move journal/);
  ports.save = saveJournal;
  const resumed = await moveToCore({state: {...state, retiredFull: delayed.journal}, stateFile}, ports);
  assert.equal(resumed.done, true, resumed.message); assert.equal(f.record().state, 'cancelled');
  assert.deepEqual(cancellations, [held.runId]); assert.deepEqual(filesUnder(folder), before);
  assert.deepEqual(readFileSync(vectorPath), vectorBytes, 'Frozen cases changed');
});
