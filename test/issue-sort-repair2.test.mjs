import test from 'node:test';
import assert from 'node:assert/strict';
import { readDependencySnapshot, createDependencyReadPorts } from '../src/issue-dependencies-github.mjs';
import { routeSortIssues, syncSortGroups, prepareSortContext } from '../src/issue-sort-github.mjs';
import { sortPlan } from '../src/issue-sort.mjs';
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { readFileSync } from 'node:fs';
import { interfaceBlocks, checkInput } from '../src/runtime/runtime-preflight.mjs';
import { fixture, repository, key } from './helpers/issue-sort-fixture.mjs';
const read = async w => (await readDependencySnapshot({ repository }, w.ports)).snapshot;
const http = (value, status = 200) => ({ code: 0, stdout: `HTTP/2.0 ${status} Reply\r\n\r\n${JSON.stringify(value)}` });

for (const action of ['close', 'assign']) for (const ownership of ['person', 'claim']) test(`late ${ownership} during final source validation prevents native ${action}`, async () => {
  const w = fixture([1], action === 'assign' ? { context: { areas: [{ name: 'cli', owner: 'helper', match: { paths: ['src/**'] } }] } } : {});
  w.save(w.record(1, action === 'close' ? { status: { ...w.record(1).status, state: 'fixed', fix: 'https://github.com/example/project/pull/90' } } : {}));
  const snapshot = await read(w); let reads = 0, patches = 0;
  const native = createDependencyReadPorts({}, { admitMutation: async action => action(), execFile: async (_file, args) => {
    if (args[args.indexOf('--method') + 1] === 'PATCH') { patches++; w.issues[0].state = 'closed'; }
    return http(w.issues[0]);
  } });
  const context = w.ports.context.read;
  w.ports.context.read = args => {
    if (++reads === 3) {
      if (ownership === 'person') w.issues[0].assignees = [{ login: 'person' }];
      else w.claims.push({ issue: key(1), active: true, owner: 'worker' });
    }
    return context(args);
  };
  w.ports.github.sortUpdate = native.github.sortUpdate;
  // Either a returned hold or a rejected guard is safe. Neither may PATCH.
  await routeSortIssues({ repository, snapshot, mode: 'auto' }, w.ports).catch(() => {});
  assert.equal(reads, 3); assert.equal(patches, 0, 'late ownership must prevent native PATCH');
  assert.equal(w.issues[0].state, 'open');
});

// Separate native adapters and local stores share only this controlled GitHub server.
function sharedAdmission() {
  const refs = new Map(), writes = [];
  return { refs, writes, execFile: async (_file, args, options) => {
    const method = args[args.indexOf('--method') + 1], endpoint = args[args.indexOf('--method') + 2];
    if (endpoint.endsWith('/commits/HEAD')) return http({ sha: 'a'.repeat(40) });
    if (method === 'POST' && endpoint.endsWith('/git/refs')) {
      const body = JSON.parse(options.input); writes.push({ method, ref: body.ref });
      if (refs.has(body.ref)) return http({}, 422);
      refs.set(body.ref, body.sha); return http({ ref: body.ref, object: { sha: body.sha } }, 201);
    }
    const ref = 'refs/' + endpoint.split('/git/refs/')[1];
    if (method === 'DELETE' && refs.has(ref)) { refs.delete(ref); writes.push({ method, ref }); return { code: 0, stdout: 'HTTP/2.0 204 No Content\r\n\r\n' }; }
    const observed = 'refs/' + endpoint.split('/git/ref/')[1];
    if (method === 'GET' && refs.has(observed)) return http({ ref: observed, object: { sha: refs.get(observed) } });
    throw Error(`Unexpected controlled request: ${method} ${endpoint}`);
  } };
}
const store = () => { let groups = []; return { read: async () => ({ groups: structuredClone(groups) }), save: async value => { groups = structuredClone(value.groups); return { ok: true }; } }; };

test('independent coordinators admit one global umbrella and recover it from a stale snapshot', async () => {
  const w = fixture([1,2,3]); for (const n of [1,2,3]) { w.save(w.record(n)); w.review(n); }
  const first = await read(w), second = structuredClone(first), server = sharedAdmission();
  const machine = () => ({ ...w.ports, sortGroups: store(), github: { ...w.ports.github,
    withSortGroupAdmission: createDependencyReadPorts({}, { execFile: server.execFile }).github.withSortGroupAdmission } });
  const a = machine(), b = machine();
  await Promise.all([syncSortGroups({ repository, snapshot: first, mode: 'auto' }, a), syncSortGroups({ repository, snapshot: second, mode: 'auto' }, b)]);
  assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 1, 'one cause must create one global umbrella');
  // The losing machine still has its old snapshot. Recovery must use the live index.
  await syncSortGroups({ repository, snapshot: second, mode: 'auto' }, b);
  const ga = (await a.sortGroups.read()).groups[0], gb = (await b.sortGroups.read()).groups[0];
  assert.equal(ga.umbrella, gb.umbrella); assert.ok(ga.umbrella);
  assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 1);
  assert.equal(server.refs.size, 0); assert.deepEqual(w.claims, []);
  const number = Number(ga.umbrella.split('/').pop()); w.save(w.record(number)); w.review(number);
  const fresh = (await readDependencySnapshot({ repository }, a)).snapshot;
  const eligible = projectIssueGraph({ snapshot: fresh }).nodes.filter(x => x.eligible).map(x => x.key);
  assert.deepEqual(eligible, [ga.umbrella]);
});

for (const action of ['close', 'assign']) for (const ownership of ['person', 'claim']) test(`${ownership} arriving inside native admission prevents ${action}`, async () => {
  const w = fixture([1], action === 'assign' ? { context: { areas: [{ name: 'cli', owner: 'helper', match: { paths: ['src/**'] } }] } } : {});
  w.save(w.record(1, action === 'close' ? { status: { ...w.record(1).status, state: 'fixed', fix: 'https://github.com/example/project/pull/90' } } : {}));
  const snapshot = await read(w); let patches = 0, guards = 0;
  const native = createDependencyReadPorts({}, {
    admitMutation: async effect => {
      guards++;
      if (ownership === 'person') w.issues[0].assignees = [{ login: 'person' }];
      else w.claims.push({ issue: key(1), active: true, owner: 'worker' });
      return effect();
    },
    execFile: async (_file, args) => { if (args[args.indexOf('--method') + 1] === 'PATCH') patches++; return http(w.issues[0]); },
  });
  w.ports.github.sortUpdate = native.github.sortUpdate;
  await routeSortIssues({ repository, snapshot, mode: 'auto' }, w.ports).catch(() => {});
  assert.equal(guards, 1); assert.equal(patches, 0, 'ownership at native admission must prevent PATCH');
  assert.equal(w.issues[0].state, 'open');
});

test('native umbrella reservations pace and stop before exhausting the shared write stream', async () => {
  const w = fixture(Array.from({ length: 21 }, (_, i) => i + 1));
  for (let n = 1; n <= 21; n++) { w.save(w.record(n, { rootCause: `cause-${Math.floor((n - 1) / 3)}` })); w.review(n); }
  const server = sharedAdmission();
  w.ports.github.withSortGroupAdmission = createDependencyReadPorts({}, { execFile: server.execFile }).github.withSortGroupAdmission;
  await syncSortGroups({ repository, snapshot: await read(w), mode: 'auto' }, w.ports).catch(() => {});
  const saved = (await w.ports.sortGroups.read()).groups;
  assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 6, 'reservation overhead must respect the shared cap');
  assert.equal(saved.filter(x => x.umbrella).length, 6); assert.equal(server.refs.size, 0);
  await syncSortGroups({ repository, snapshot: await read(w), mode: 'auto' }, w.ports);
  assert.equal(w.writes.filter(x => x.kind === 'umbrella').length, 7);
  assert.equal((await w.ports.sortGroups.read()).groups.filter(x => x.umbrella).length, 7);
  const times = w.writes.filter(x => x.kind === 'umbrella').map(x => x.at);
  assert.ok(times.slice(1).every((at, i) => at - times[i] >= 1000));
});

test('an uncertain native creation retains shared admission and prevents a second POST', async () => {
  const w = fixture([1,2,3]); for (const n of [1,2,3]) { w.save(w.record(n)); w.review(n); }
  const stale = await read(w), server = sharedAdmission(); let posts = 0;
  const native = () => createDependencyReadPorts({}, { execFile: server.execFile }).github.withSortGroupAdmission;
  const a = { ...w.ports, sortGroups: store(), github: { ...w.ports.github, withSortGroupAdmission: native(), createSortUmbrella: async () => { posts++; throw Error('unconfirmed'); } } };
  const b = { ...w.ports, sortGroups: store(), github: { ...w.ports.github, withSortGroupAdmission: native(), createSortUmbrella: async () => { posts++; throw Error('unconfirmed'); } } };
  await syncSortGroups({ repository, snapshot: structuredClone(stale), mode: 'auto' }, a).catch(() => {});
  await syncSortGroups({ repository, snapshot: structuredClone(stale), mode: 'auto' }, b).catch(() => {});
  assert.equal(posts, 1, 'uncertain POST must retain shared admission'); assert.equal(server.refs.size, 1);
});

for (const owner of ['issue-sort', 'issue-sort-github']) test(`${owner} Runtime boundary admits the native snapshot`, async () => {
  const w = fixture([1,2,3]); for (const n of [1,2,3]) { w.save(w.record(n)); w.review(n); }
  const snapshot = await read(w);
  const iface = JSON.parse(interfaceBlocks(readFileSync(`prompts/cli/${owner}.prompt.md`, 'utf8'))[0][1]);
  const entry = iface.entries[0], input = owner === 'issue-sort' ? { snapshot } : snapshot;
  const result = owner === 'issue-sort' ? sortPlan(input) : prepareSortContext(input);
  assert.deepEqual(checkInput(input, entry.input_schema, 0).refusals, [], 'native input must conform to the helper contract');
  assert.deepEqual(checkInput(result, entry.result_schema, 0).refusals, []);
  const minimal = { repository, complete: true, inputs: snapshot.inputs, issues: snapshot.issues.map(({ key, revision, title, authority, state, execution, holds }) => ({ key, revision, title, authority, state, execution, holds })) };
  assert.deepEqual(checkInput(owner === 'issue-sort' ? { snapshot: minimal } : minimal, entry.input_schema, 0).refusals, []);
});
