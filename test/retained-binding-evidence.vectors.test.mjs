import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {fixture, packageRoot, matchingClaimPorts} from './helpers/workflow-runner-fixture.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {readRunResults} from '../src/workflow-results.mjs';
import {tickAutopilot} from '../src/autopilot-launcher.mjs';
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

async function parkingFixture(t) {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  assert.equal((await runStatus({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  f.herdr.idle();
  const run = f.record();
  run.automaticOrigin = {repository: run.repo, coordinatorId: 'park-owner', machine: 'park-machine',
    claim: {commentId: '11', labelEventId: '12'}};
  save(run);
  f.ports.owners = matchingClaimPorts(run);
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', trust: []}}));
  const stateFile = join(f.state, 'launcher.json');
  writeFileSync(stateFile, JSON.stringify({enabled: true, defaultBranch: 'main', baseBranch: 'main',
    stateFile, cwd: f.source, repo: run.repo, packageRoot, runs: 1, coordinatorId: 'park-owner',
    machine: 'park-machine', activatedAt: 1, agent: {id: 'claude', kind: 'claude', command: 'claude'},
    environment: f.ports.env, recipeDelivered: true}));
  const warnings = [], requests = [];
  const herdr = async args => {
    if (args[0] === 'pane' && args[1] === 'get') {
      const pane = f.herdr.panes.find(pane => pane.pane_id === args[2]);
      if (!pane) throw Object.assign(Error('pane_not_found'), {code: 'pane_not_found'});
      return {result: {type: 'pane_info', pane: {...pane, foreground_cwd: pane.cwd, ...pane.agent}}};
    }
    return f.herdr.herdr(args);
  };
  const ports = {...healthyMachine, ...f.ports, herdr,
    checkCapacityPorts: isolatedCheckCapacity(f.base),
    run: async (file, args, options) => ({code: 0, ...await f.ports.execFile(file, args, options)}),
    reconcileDependencyIntake: async () => ({eligible: [], claims: [{issue: run.issue.url, active: true,
      owner: 'park-owner', coordinatorId: 'park-owner', machine: 'park-machine', ...run.automaticOrigin.claim}],
      groups: [], queued: [], skipped: []}),
    refreshClaimHeartbeat: async ({at}) => ({state: 'refreshed', lastSeen: at}),
    queryIssues: async () => ({status: 200, issues: []}), comments: async () => [],
    runtimeHealth: async () => ({state: 'healthy', detail: 'controlled local health'}),
    sendDigest: async () => ({exitCode: 0}), sendAlert: async () => ({exitCode: 0}),
    blockerCleared: async () => false, warn: message => warnings.push(message)};
  t.mock.method(globalThis, 'fetch', async (...args) => {
    requests.push(args); assert.fail('Native local replay must not request a service');
  });
  f.herdr.calls.length = 0;
  return {f, stateFile, ports, warnings, requests};
}

for (const row of vectors.parking_cases) {
  test(`3135 parking: ${row.id}`, async t => {
    const {f, stateFile, ports, warnings, requests} = await parkingFixture(t);
    const readerCase = vectors.reader_cases.find(candidate => candidate.id === row.reader_case);
    assert.ok(readerCase, `Missing frozen reader case ${row.reader_case}`);
    const held = f.record();
    held.state = 'waiting';
    held.gate = {kind: 'approve-pr', area: held.areas[held.area].name};
    held.done.check = 'Synthetic no-verdict receipt';
    if (row.question) held.question = {at: f.clock, ...row.question};
    if (row.blockedOn) held.blockedOn = row.blockedOn;
    save(held);
    const folder = writeBatch({root: held.root, home: f.ports.env.HOME,
      intent: 'check', rows: readerCase.rows, at: f.clock});
    const before = filesUnder(folder);
    assert.equal(ports.readRunResults, undefined, 'Replay must use the normal reader');
    assert.equal(readRunResults({root: held.root, since: held.startedAt ?? 0}, {env: f.ports.env})[0]?.batch, batch);
    await tickAutopilot(stateFile, ports);
    const after = f.record();
    assert.equal(after.parking?.blocker?.kind, row.expected_blocker, '3135_BINDING_HOLD_MISCLASSIFIED');
    if (row.preserve) assert.deepEqual(after[row.preserve], held[row.preserve]);
    assert.deepEqual(filesUnder(folder), before, 'Parking changed the saved receipt');
    assert.deepEqual(warnings, []);
    assert.deepEqual(requests, []);
    assert.deepEqual(f.pushes, []); assert.deepEqual(f.prs, []); assert.deepEqual(f.edits, []);
    assert.equal(f.herdr.calls.some(args => args[0] === 'pane' && args[1] === 'run'), false);
    assert.equal(f.herdr.calls.some(args => args[0] === 'agent' && args[1] === 'prompt'), false);
    assert.deepEqual(readFileSync(vectorPath), vectorBytes, 'Frozen cases changed');
  });
}
