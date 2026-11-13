import { readFileSync } from 'node:fs';
import { interfaceBlocks, checkInput } from '../src/runtime-seam.mjs';
import { prepareSortContext } from '../src/issue-sort-github.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readDependencySnapshot, createDependencyReadPorts } from '../src/issue-dependencies-github.mjs';
import { reconcileDependencyIntake, prepareDependencyIntake } from '../src/issue-dependencies-intake.mjs';
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { sortPlan, selectedSort, validSort } from '../src/issue-sort.mjs';
import { fixture, repository, key } from './helpers/issue-sort-fixture.mjs';
const read = async w => (await readDependencySnapshot({ repository }, w.ports)).snapshot;
const tick = w => reconcileDependencyIntake({ repository, mode: w.mode ?? 'auto' }, w.ports);
const areas = mixed => [
  { name: 'cli', owner: 'autopilot', match: { paths: ['src/**'] } },
  { name: 'runtime', owner: 'runtime-owner', mixed, match: { keywords: ['hosted interpreter'] } },
];
function mixedFixture(mixed = 'whole', options = {}) {
  const w = fixture([1], { ...options, context: { areas: areas(mixed) } });
  w.mode = options.mode ?? 'auto';
  w.issues[0].body = 'The hosted interpreter error also requires src/cli.mjs to send context.';
  const timeline = [], links = [];
  const page = w.ports.github.page;
  w.ports.github.page = args => {
    if (args.kind === 'splitCandidates') return { json: JSON.stringify({ items: w.issues, next: '' }) };
    if (args.kind === 'timeline' && args.issue === 1) return { json: JSON.stringify({ items: timeline, next: '' }) };
    if (['blockedBy','blocking'].includes(args.kind)) return { json: JSON.stringify({ items: links.filter(x => x.kind === 'blocker' && (args.kind === 'blockedBy' ? x.issue === args.issue : x.childId === String(args.issue))).map(x => w.issues.find(i => args.kind === 'blockedBy' ? String(i.id) === x.childId : i.number === x.issue)), next: '' }) };
    return page(args);
  };
  w.ports.github.createSortPart = async ({ title, body }) => {
    const number = Math.max(...w.issues.map(x => x.number)) + 1;
    const raw = { id: number, number, html_url: key(number), title, body, state: 'open', user: { login: 'owner' }, labels: [], assignees: [] };
    w.issues.push(raw); w.comments.set(number, []);
    w.writes.push({ at: Date.parse((await w.ports.clock.now({})).iso), issue: number, kind: 'part', body });
    return { json: JSON.stringify(raw) };
  };
  w.ports.github.ensureSortLink = async ({ issue, childId, kind, checkOwnership }) => {
    if (links.some(x => x.issue === issue && x.childId === childId && x.kind === kind)) return { ok: true };
    if (!await checkOwnership()) throw Error('owned');
    links.push({ issue, childId, kind });
    w.writes.push({ at: Date.parse((await w.ports.clock.now({})).iso), issue, kind: 'link' });
    return { ok: true };
  };
  w.label = (name, login = 'owner') => { w.issues[0].labels.push(name); timeline.push({ event: 'labeled', label: { name }, actor: { login } }); };
  w.mixedRecord = () => {
    const r = w.record(1, { touchedAreas: [{ area: 'cli', evidence: ['src/cli.mjs:12'] }, { area: 'runtime', evidence: ['hosted interpreter: missing context'] }], splitOrder: { first: options.first ?? 'runtime', evidence: ['The context contract must exist before its caller.'] } });
    // Trusted comments are requirements and have to be included before sorting.
    return r;
  };
  w.seed = async (changes = {}) => {
    const r = { ...w.mixedRecord(), ...changes };
    const prepared = await prepareDependencyIntake({ repository }, w.ports);
    const snapshot = JSON.parse(prepared.request.snapshotJson);
    for (const input of snapshot.inputs.filter(x => x.key.startsWith(`${key(1)}#issuecomment-`))) if (!r.inputs.some(x => x.key === input.key)) r.inputs.push(input);
    const old = w.comments.get(1).filter(x => x.body.includes('pdd-issue-sort:v1'));
    r.base = old.map(x => String(x.id));
    w.save(r); w.review(1);
    return r;
  };
  w.timeline = timeline; w.links = links;
  return w;
}

test('whole assigns one owner, records every part and never starts work', async () => {
  const w = mixedFixture(); const r = await w.seed();
  assert.equal(validSort(r), true, 'mixed evidence must be admitted');
  const snapshot = await read(w);
  assert.deepEqual(selectedSort(snapshot, snapshot.issues[0])?.touchedAreas, r.touchedAreas);
  await tick(w); await tick(w);
  assert.deepEqual(w.issues[0].assignees, [{ login: 'runtime-owner' }]);
  const notes = w.writes.filter(x => x.kind === 'comment');
  assert.equal(notes.length, 1);
  for (const part of r.touchedAreas) { assert.ok(notes[0].body.includes(part.area)); assert.ok(part.evidence.every(x => notes[0].body.includes(x))); }
  assert.equal(w.writes.filter(x => x.kind === 'part').length, 0);
  assert.deepEqual((await tick(w)).eligible, []);
});

for (const first of ['runtime','cli']) test(`split creates independent parts in ${first}-first order and closes parent only after both`, async () => {
  const w = mixedFixture('split', { first }); await w.seed(); await tick(w);
  assert.equal(w.writes.filter(x => x.kind === 'part').length, 2, 'split needs two independently closable parts');
  const cli = w.issues.find(x => x.title === 'cli part of #1'), remote = w.issues.find(x => x.title === 'runtime part of #1');
  assert.ok(cli && remote); assert.deepEqual(remote.assignees, [{ login: 'runtime-owner' }]);
  assert.deepEqual(cli.assignees, []);
  for (const child of [cli,remote]) {
    assert.ok(child.body.includes(key(1)));
    assert.ok(w.links.some(x => x.issue === 1 && x.childId === String(child.id) && x.kind === 'sub'));
    assert.ok(w.links.some(x => x.issue === 1 && x.childId === String(child.id) && x.kind === 'blocker'));
  }
  const earlier = first === 'runtime' ? remote : cli, later = first === 'runtime' ? cli : remote;
  assert.ok(w.links.some(x => x.issue === later.number && x.childId === String(earlier.id) && x.kind === 'blocker'));
  w.save(w.record(cli.number, { touchedAreas: [{ area: 'cli', evidence: ['src/cli.mjs:12'] }], rootCause: '' })); w.review(cli.number);
  const before = await tick(w);
  assert.equal(before.eligible.includes(key(1)), false);
  assert.equal(before.eligible.includes(cli.html_url), first === 'cli');
  earlier.state = 'closed'; earlier.state_reason = 'completed'; await tick(w); assert.equal(w.issues[0].state, 'open');
  later.state = 'closed'; later.state_reason = 'completed'; await tick(w); assert.equal(w.issues[0].state, 'closed');
  assert.equal(w.writes.filter(x => x.kind === 'part').length, 2);
});

for (const [defaultMode, override, expected] of [['whole','split','split'], ['split','whole','assign']]) test(`trusted label ${override} overrides ${defaultMode} and a contrary comment`, async () => {
  const w = mixedFixture(defaultMode); w.append(1, `mixed: ${defaultMode}`); w.label(`pdd:owner-${override}`); await w.seed();
  const route = sortPlan({ snapshot: await read(w) }).routes[0];
  assert.equal(route.action, expected, 'trusted owner label must win');
  await tick(w);
  assert.equal(w.writes.filter(x => x.kind === 'part').length, override === 'split' ? 2 : 0);
  assert.equal(w.issues[0].assignees.length, override === 'whole' ? 1 : 0);
});

for (const directive of ['pdd:owner-split','mixed: split','Split this issue.']) test(`one trusted comment selects split: ${directive}`, async () => {
  const w = mixedFixture(); w.append(1, directive); await w.seed();
  assert.equal(sortPlan({ snapshot: await read(w) }).routes[0].action, 'split');
  await tick(w); assert.equal(w.writes.filter(x => x.kind === 'part').length, 2);
});

for (const problem of ['missing-evidence','missing-area','missing-order','conflicting-labels','outsider-label','missing-label-provenance','unknown-area','missing-policy']) test(`uncertain ${problem} asks one owner question`, async () => {
  const w = mixedFixture(problem === 'missing-policy' ? undefined : 'split');
  if (problem === 'missing-policy') delete w.context.areas[1].mixed;
  if (problem === 'conflicting-labels') { w.label('pdd:owner-whole'); w.label('pdd:owner-split'); }
  if (problem === 'outsider-label') w.label('pdd:owner-whole', 'outsider');
  if (problem === 'missing-label-provenance') w.issues[0].labels.push('pdd:owner-whole');
  const changes = problem === 'missing-evidence' ? { touchedAreas: undefined } : problem === 'missing-area' ? { touchedAreas: [{ area: 'cli', evidence: ['src/cli.mjs'] }] } : problem === 'missing-order' ? { splitOrder: undefined } : problem === 'unknown-area' ? { belongs: { kind: 'unknown', area: '', repository: '' } } : {};
  // Absent fields, rather than explicit undefined, are the legacy JSON shape.
  const r = await w.seed(changes); await tick(w); await tick(w);
  assert.ok(w.issues[0].labels.includes('pdd:needs-owner'), problem);
  assert.equal(w.writes.filter(x => x.kind === 'comment').length, 1);
  assert.equal(w.writes.filter(x => x.kind === 'part' || x.kind === 'assign').length, 0);
  assert.equal(projectIssueGraph({ snapshot: await read(w) }).nodes[0].eligible, false);
});

for (const mode of ['whole','split']) for (const ownership of ['person','claim']) test(`${mode} leaves ${ownership} assigned issue untouched`, async () => {
  const w = mixedFixture(mode); await w.seed();
  assert.equal(sortPlan({ snapshot: await read(w) }).routes[0].action, mode === 'whole' ? 'assign' : 'split');
  if (ownership === 'person') w.issues[0].assignees = [{ login: 'person' }];
  else { w.claims.push({ issue: key(1), active: true, owner: 'worker' }); w.issues[0].labels.push('pdd:working'); }
  await tick(w); assert.equal(w.writes.length, 0);
  assert.deepEqual((await tick(w)).eligible, []);
});

test('split write stream is paced, bounded, resumes and never duplicates parts', async () => {
  const w = mixedFixture('split'); await w.seed();
  const sleep = w.ports.wait.sleep;
  let calls = 0;
  w.ports.wait.sleep = async args => { await sleep(args); if (++calls === 3) throw Error('controlled interruption'); };
  await tick(w);
  assert.equal(w.writes.filter(x => x.kind === 'part').length, 2);
  w.ports.wait.sleep = sleep;
  await tick(w); await tick(w);
  assert.equal(w.writes.filter(x => x.kind === 'part').length, 2);
  assert.equal(w.writes.filter(x => x.kind === 'comment').length, 1);
  assert.ok(w.writes.length <= 20);
  // Separate ticks can start at the same fake clock time. Within one stream all
  // adjacent effects, including the recovered links and assignment, are paced.
  const times = w.writes.slice(3).map(x => x.at);
  assert.ok(times.slice(1).every((at, i) => at - times[i] >= 1000));
});

test('ownership arriving during split pacing prevents every later write', async () => {
  const w = mixedFixture('split'); await w.seed();
  const sleep = w.ports.wait.sleep;
  w.ports.wait.sleep = async args => { await sleep(args); w.issues[0].assignees = [{ login: 'person' }]; };
  await tick(w);
  assert.equal(w.writes.filter(x => x.kind === 'part').length, 1);
  assert.equal(w.writes.filter(x => x.kind !== 'part').length, 0);
});

test('observe proposes split without creating parts or exposing parent work', async () => {
  const w = mixedFixture('split', { mode: 'observe' }); await w.seed();
  const result = await tick(w);
  assert.equal(sortPlan({ snapshot: await read(w) }).routes[0].action, 'split');
  assert.deepEqual(result.eligible, []); assert.equal(w.writes.length, 0);
});

test('stale cross-area group member holds umbrella until a fresh sort recovers it', async () => {
  const w = fixture([1,2], { context: { areas: [{ name: 'cli', owner: 'autopilot', match: { paths: ['src/**'] } }, { name: 'docs', owner: 'autopilot', match: { paths: ['docs/**'] } }] } });
  w.save(w.record(1)); w.review(1);
  w.save(w.record(2, { paths: ['docs/guide.md'], belongs: { kind: 'area', area: 'docs', repository: '' } })); w.review(2);
  await tick(w);
  const group = (await w.ports.sortGroups.read()).groups[0], n = Number(group.umbrella.split('/').pop());
  w.save(w.record(n)); w.review(n);
  const ready = () => read(w).then(snapshot => projectIssueGraph({ snapshot }).nodes.find(x => x.key === group.umbrella));
  assert.equal((await ready()).eligible, true);
  w.files.set(`https://github.com/${repository}/blob/HEAD/docs/guide.md`, 'source-v2');
  const stale = await ready();
  assert.equal(stale.eligible, false, 'stale cross-area member must hold global work');
  assert.equal(stale.sort.ready, false);
  w.save(w.record(2, { base: w.comments.get(2).filter(x => x.body.includes('pdd-issue-sort:v1')).map(x => x.id), paths: ['docs/guide.md'], belongs: { kind: 'area', area: 'docs', repository: '' } }));
  assert.equal((await ready()).eligible, true);
});

test('promptdriven/pdd runtime defaults to whole without changing another repository default', async () => {
  const w = mixedFixture(); delete w.context.areas[1].mixed; await w.seed();
  const snapshot = await read(w);
  assert.equal(sortPlan({ snapshot }).routes[0].action, 'question');
  const pdd = JSON.parse(JSON.stringify(snapshot).replaceAll('example/project','promptdriven/pdd'));
  assert.equal(sortPlan({ snapshot: pdd }).routes[0].action, 'assign');
  assert.equal(sortPlan({ snapshot: pdd }).routes[0].owner, 'runtime-owner');
});

test('outsider and quoted comments cannot override the default whole policy', async () => {
  const w = mixedFixture(); w.append(1, 'mixed: split', 'outsider'); w.append(1, '> mixed: split'); await w.seed();
  assert.equal(sortPlan({ snapshot: await read(w) }).routes[0].action, 'assign');
  await tick(w); assert.deepEqual(w.issues[0].assignees, [{ login: 'runtime-owner' }]);
});

test('a child closed as not planned cannot complete the main issue', async () => {
  const w = mixedFixture('split'); await w.seed(); await tick(w);
  assert.equal(w.issues.length, 3);
  w.issues.slice(1).forEach(x => { x.state = 'closed'; }); w.issues[1].state_reason = 'not_planned';
  await tick(w); assert.equal(w.issues[0].state, 'open');
});

for (const kind of ['part','sub','blocker']) test(`native ${kind} mutation has ownership admission and readback`, async () => {
  const writes = [], relationships = [];
  const raw = { id: 2, number: 2, html_url: key(2), title: 'runtime part of #1', body: 'scoped evidence', assignees: [] };
  let allowed = true;
  const native = createDependencyReadPorts({}, { admitMutation: async action => action(), execFile: async (_file, args, options) => {
    const method = args.includes('--method') ? args[args.indexOf('--method')+1] : 'GET', endpoint = args.find(word=>/^repos\//.test(word));
    if (method !== 'GET') writes.push({ method, endpoint });
    const reply = value => ({ code: 0, stdout: JSON.stringify(value) });
    const subject = new RegExp(`^repos/${repository}/issues/(1|2)$`).exec(endpoint??'');
    if (method === 'GET' && subject) return reply({...raw,number:Number(subject[1]),labels:[],assignees:[]});
    if (kind === 'part') return reply(raw);
    if (method === 'POST') { relationships.push({ id: 2 }); return reply({}); }
    return reply(relationships);
  } });
  const action = () => kind === 'part' ? native.github.createSortPart?.({ repository, title: raw.title, body: raw.body, checkOwnership: async () => allowed }) : native.github.ensureSortLink?.({ repository, issue: 1, childId: '2', kind, checkOwnership: async () => allowed });
  const result = await action();
  assert.ok(result, 'native mixed-area write port must exist');
  assert.equal(writes.length, 1);
  if (kind !== 'part') { await action(); assert.equal(writes.length, 1, 'confirmed existing links must not be posted again'); relationships.length = 0; }
  allowed = false;
  await assert.rejects(action, /sort-owner-changed/);
  assert.equal(writes.length, 1);
});

for (const kind of ['part','sub','blocker']) test(`ownership arriving inside native ${kind} admission prevents POST`, async () => {
  let allowed = true, posts = 0;
  const native = createDependencyReadPorts({}, { admitMutation: async action => { allowed = false; return action(); }, execFile: async (_file, args) => {
    if (args[args.indexOf('--method')+1] === 'POST') posts++;
    const endpoint=args.find(word=>/^repos\//.test(word)),subject=new RegExp(`^repos/${repository}/issues/(1|2)$`).exec(endpoint??'');
    return {code:0,stdout:JSON.stringify(subject ? {number:Number(subject[1]),labels:[],assignees:[]} : [])};
  } });
  const action = () => kind === 'part' ? native.github.createSortPart?.({ repository, title: 'part', body: 'evidence', checkOwnership: async () => allowed }) : native.github.ensureSortLink?.({ repository, issue: 1, childId: '2', kind, checkOwnership: async () => allowed });
  // The explicit result assertion also detects a missing native boundary on base.
  const outcome = await Promise.resolve().then(action).then(() => 'unguarded', e => e.message);
  assert.equal(outcome, 'sort-owner-changed'); assert.equal(posts, 0);
});

for (const ownership of ['person','claim']) for (const target of ['sub','order-first','order-later']) test(`${ownership} on ${target} child prevents relationship mutation`, async () => {
  const w = mixedFixture('split'); await w.seed();
  const link = w.ports.github.ensureSortLink;
  let ownedNumber = 0;
  w.ports.github.ensureSortLink = async args => {
    const isOrder = args.kind === 'blocker' && args.issue !== 1;
    if (!ownedNumber && (target === 'sub' ? args.kind === 'sub' : isOrder)) {
      ownedNumber = target === 'order-later' ? args.issue : Number(args.childId);
      const child = w.issues.find(x => x.number === ownedNumber);
      if (ownership === 'person') child.assignees = [{ login: 'person' }];
      else { w.claims.push({ issue: child.html_url, active: true, owner: 'worker' }); child.labels.push('pdd:working'); }
    }
    return link(args);
  };
  await tick(w);
  assert.equal(w.writes.filter(x => x.kind === 'part').length, 2);
  assert.ok(ownedNumber > 0);
  assert.equal(w.links.filter(x => target === 'sub' ? x.kind === 'sub' && x.childId === String(ownedNumber) : x.kind === 'blocker' && x.issue !== 1).length, 0);
  assert.equal(w.writes.filter(x => x.kind === 'comment' || x.kind === 'assign').length, 0);
});

test('split recovers an already closed part after the final parent note was interrupted', async () => {
  const w = mixedFixture('split'); await w.seed();
  const append = w.ports.github.appendComment; let interrupted = true;
  w.ports.github.appendComment = args => { if (interrupted) throw Error('controlled before parent note'); return append(args); };
  await tick(w);
  assert.equal(w.issues.length, 3);
  const remote = w.issues.find(x => x.title.startsWith('runtime part')), cli = w.issues.find(x => x.title.startsWith('cli part'));
  remote.state = 'closed'; remote.state_reason = 'completed'; interrupted = false;
  await tick(w); await tick(w);
  assert.equal(w.writes.filter(x => x.kind === 'part').length, 2, 'closed part must be recovered rather than recreated');
  assert.equal(w.writes.filter(x => x.kind === 'comment').length, 1);
  assert.equal(w.issues[0].state, 'open');
  cli.state = 'closed'; cli.state_reason = 'completed'; await tick(w); assert.equal(w.issues[0].state, 'closed');
});

function nativeReservation(w) {
  const refs = new Map();
  const native = createDependencyReadPorts({}, { execFile: async (_file, args, options) => {
    const method = args[args.indexOf('--method')+1], endpoint = args[args.indexOf('--method')+2];
    const reply = (value, status = 200) => ({ code: 0, stdout: `HTTP/2.0 ${status} Reply\r\n\r\n${JSON.stringify(value)}` });
    if (endpoint.endsWith('/commits/HEAD')) return reply({ sha: 'a'.repeat(40) });
    if (method === 'POST') {
      const { ref, sha } = JSON.parse(options.input);
      if (refs.has(ref)) return reply({}, 422);
      refs.set(ref, sha); return reply({ ref, object: { sha } }, 201);
    }
    if (method === 'DELETE') { refs.delete(`refs/${endpoint.split('/git/refs/')[1]}`); return reply(null, 204); }
    const ref = `refs/${endpoint.split('/git/ref/')[1]}`;
    if (refs.has(ref)) return reply({ ref, object: { sha: refs.get(ref) } });
    throw Error('unexpected reservation read');
  } });
  w.ports.github.withSortGroupAdmission = native.github.withSortGroupAdmission;
  return refs;
}

test('a parent guard refusal before part creation releases admission and permits retry', async () => {
  const w = mixedFixture('split'); await w.seed(); const refs = nativeReservation(w);
  const sleep = w.ports.wait.sleep; let once = true;
  w.ports.wait.sleep = async args => { await sleep(args); if (once) { once = false; w.issues[0].assignees = [{ login: 'person' }]; } };
  await tick(w);
  assert.equal(w.writes.filter(x => x.kind === 'part').length, 0);
  assert.equal(refs.size, 0, 'proven unsent creation must release its reservation');
  w.issues[0].assignees = [];
  await tick(w);
  assert.equal(w.writes.filter(x => x.kind === 'part').length, 2);
  assert.equal(refs.size, 0);
});

test('native pre-transport rejection is unsent while failed readback remains uncertain', async () => {
  let allow = false, posts = 0;
  const native = createDependencyReadPorts({}, { execFile: async (_file, args) => {
    if (args[args.indexOf('--method')+1] === 'POST') { posts++; return { code: 0, stdout: JSON.stringify({ number: 2, html_url: key(2) }) }; }
    throw Error('controlled readback failure');
  } });
  const action = () => native.github.createSortPart?.({ repository, title: 'part', body: 'evidence', checkOwnership: async () => allow });
  let error = await Promise.resolve().then(action).then(() => null, e => e);
  assert.equal(error?.sortUnsent, true); assert.equal(posts, 0);
  allow = true; error = await Promise.resolve().then(action).then(() => null, e => e);
  assert.equal(error?.sortUnsent, false); assert.equal(posts, 1);
});

for (const reason of [undefined,null,'not_planned','unknown']) test(`unproved child completion reason ${reason} keeps parent open`, async () => {
  const w = mixedFixture('split'); await w.seed(); await tick(w);
  assert.equal(w.issues.length, 3);
  w.issues.slice(1).forEach(x => { x.state = 'closed'; x.state_reason = 'completed'; });
  w.issues[1].state_reason = reason;
  await tick(w); assert.equal(w.issues[0].state, 'open');
  assert.equal(w.writes.filter(x => x.kind === 'close').length, 0);
});

test('child completion must remain proved at native parent-close admission', async () => {
  const w = mixedFixture('split'); await w.seed(); await tick(w);
  assert.equal(w.issues.length, 3);
  w.issues.slice(1).forEach(x => { x.state = 'closed'; x.state_reason = 'completed'; });
  let patches = 0;
  const native = createDependencyReadPorts({}, { admitMutation: async action => { w.issues[1].state_reason = null; return action(); }, execFile: async (_file,args) => {
    if (args[args.indexOf('--method')+1] === 'PATCH') patches++;
    return { code: 0, stdout: JSON.stringify(w.issues[0]) };
  } });
  w.ports.github.sortUpdate = native.github.sortUpdate;
  await tick(w); assert.equal(patches, 0); assert.equal(w.issues[0].state, 'open');
});

test('whole names all three touched areas in its single handoff note', async () => {
  const w = mixedFixture(); w.context.areas.push({ name: 'docs', owner: 'autopilot', match: { keywords: ['context'] } });
  const touchedAreas = [...w.mixedRecord().touchedAreas, { area: 'docs', evidence: ['manual command: context setup'] }];
  await w.seed({ touchedAreas }); await tick(w);
  assert.deepEqual(w.issues[0].assignees, [{ login: 'runtime-owner' }]);
  const notes = w.writes.filter(x => x.kind === 'comment'); assert.equal(notes.length, 1);
  assert.ok(touchedAreas.every(x => notes[0].body.includes(x.area) && notes[0].body.includes(x.evidence[0])));
});

test('multiple mixed parents share a bounded paced stream and later ticks finish the parts', async () => {
  const w = mixedFixture('split');
  for (const number of [2,3]) { w.issues.push({ ...structuredClone(w.issues[0]), id:number,number,html_url:key(number) }); w.comments.set(number, []); }
  for (const n of [1,2,3]) {
    const r = w.record(n, { touchedAreas: w.mixedRecord().touchedAreas, splitOrder: w.mixedRecord().splitOrder });
    w.save(r); w.review(n);
  }
  await tick(w);
  assert.ok(w.writes.length <= 20); assert.ok(w.writes.length > 0);
  assert.ok(w.writes.slice(1).every((x,i) => x.at - w.writes[i].at >= 1000));
  await tick(w); await tick(w);
  assert.equal(w.writes.filter(x => x.kind === 'part').length, 6);
  assert.equal(w.writes.filter(x => x.kind === 'comment').length, 3);
  const parentSnapshot = await read(w);
  assert.ok([1,2,3].every(n => parentSnapshot.issues.find(x => x.key === key(n)).sortSplit?.parts.length === 2));
});


test('Runtime helper schemas admit native mixed metadata and graph projections', async () => {
  const w = mixedFixture('split'); await w.seed();
  const snapshot = await read(w), graph = projectIssueGraph({ snapshot });
  assert.equal(snapshot.issues[0].sorts[0].record?.touchedAreas.length, 2);
  for (const [name,input,result] of [
    ['issue-sort', { snapshot }, sortPlan({ snapshot })],
    ['issue-sort-github', snapshot, prepareSortContext(snapshot)],
    ['issue-dependencies', { snapshot }, graph],
    ['issue-dependency-graph-view', { graph, query: '', filter: 'all', selected: '', sync: 'current', lastSync: '' }, undefined],
  ]) {
    const entry = JSON.parse(interfaceBlocks(readFileSync(`prompts/cli/${name}.prompt.md`, 'utf8'))[0][1]).entries[0];
    assert.deepEqual(checkInput(input, entry.input_schema, 0).refusals, [], `${name} must admit native input`);
    if (result !== undefined) assert.deepEqual(checkInput(result, entry.result_schema, 0).refusals, [], `${name} must admit native result`);
  }
});

for (const change of ['person', 'claim', 'closed', 'labels', 'title', 'body', 'missing-assignees', 'missing-labels']) test(`split-parent close rejects late ${change} during final native child validation`, async () => {
  const w = mixedFixture('split'); await w.seed(); await tick(w);
  assert.equal(w.issues.length, 3);
  w.issues.slice(1).forEach(x => { x.state = 'closed'; x.state_reason = 'completed'; });
  let insideAdmission = false, injected = false, patches = 0;
  const issue = w.ports.github.issue;
  w.ports.github.issue = async args => {
    const result = await issue(args);
    if (insideAdmission && !injected && args.issue === w.issues.at(-1).number) {
      injected = true;
      const parent = w.issues[0];
      if (change === 'person') parent.assignees = [{ login: 'person' }];
      if (change === 'claim') w.claims.push({ issue: key(1), active: true, owner: 'worker' });
      if (change === 'closed') parent.state = 'closed';
      if (change === 'labels') w.label('pdd:owner-whole');
      if (change === 'title') parent.title += ' changed';
      if (change === 'body') parent.body += ' changed';
      if (change === 'missing-assignees') delete parent.assignees;
      if (change === 'missing-labels') delete parent.labels;
    }
    return result;
  };
  const native = createDependencyReadPorts({}, {
    admitMutation: async action => {
      insideAdmission = true;
      try { return await action(); } finally { insideAdmission = false; }
    },
    execFile: async (_file, args) => {
      if (args[args.indexOf('--method') + 1] === 'PATCH') { patches++; w.issues[0].state = 'closed'; }
      return { code: 0, stdout: JSON.stringify(w.issues[0]) };
    },
  });
  w.ports.github.sortUpdate = native.github.sortUpdate;
  await tick(w);
  assert.equal(injected, true, 'reach the final child read inside native admission');
  assert.equal(patches, 0, 'changed parent must not receive a PATCH');
  assert.equal(w.issues[0].state, change === 'closed' ? 'closed' : 'open');
});

for (const authority of ['outsider', 'owner']) test(`malformed mixed elements from ${authority} preserve snapshot and sort authority`, async () => {
  const valid = { area: 'cli', evidence: ['src/cli.mjs'] };
  for (const touchedAreas of [[null], [valid, null], [false], [17], ['runtime'], [[]], [{}], [{ area: null, evidence: ['source'] }], [{ area: 'cli', evidence: null }], [{ area: 'cli', evidence: [null] }], [valid, valid]]) {
    const w = mixedFixture(); const original = await w.seed();
    const malformed = { ...original, touchedAreas };
    const comment = w.append(1, `<!-- pdd-issue-sort:v1 -->\n\`\`\`json\n${JSON.stringify(malformed)}\n\`\`\``, authority);
    let snapshot;
    await assert.doesNotReject(async () => { snapshot = await read(w); });
    assert.equal(snapshot.complete, true);
    const subject = snapshot.issues.find(x => x.key === key(1));
    const head = subject.sorts.find(x => x.id === String(comment.id));
    assert.equal(head.record, null);
    assert.equal(head.intact, false);
    assert.equal(head.authority, authority === 'owner' ? 'trusted' : 'outsider');
    assert.equal(validSort(malformed), false);
    assert.deepEqual(selectedSort(snapshot, subject), authority === 'owner' ? null : original);
    assert.equal(sortPlan({ snapshot }).queued.includes(key(1)), authority === 'owner');
  }
});

// Keep native admission, request construction and readback. Only transport is fake.
function nativeSplitWrites(w) {
  let phase = '', insideAdmission = false;
  const effects = [];
  const native = createDependencyReadPorts({}, {
    admitMutation: async action => {
      insideAdmission = true;
      try { return await action(); } finally { insideAdmission = false; }
    },
    execFile: async (_file, args, options) => {
      const method = args[args.indexOf('--method') + 1];
      const endpoint = args[args.indexOf('--method') + 2].split('?')[0];
      const match = /\/issues\/(\d+)(?:\/(sub_issues|dependencies\/blocked_by))?$/.exec(endpoint);
      assert.ok(match, 'use the native issue or relationship endpoint');
      const issue = Number(match[1]), target = w.issues.find(x => x.number === issue);
      if (method === 'POST' || method === 'PATCH') {
        const input = JSON.parse(options.input);
        effects.push({ phase, method, issue, input, assignees: structuredClone(target.assignees), claims: structuredClone(w.claims) });
        if (method === 'POST') w.links.push({ issue, childId: String(input.sub_issue_id ?? input.issue_id), kind: match[2] === 'sub_issues' ? 'sub' : 'blocker' });
        else {
          if (input.assignees) target.assignees = input.assignees.map(login => ({ login }));
          if (input.state) target.state = input.state;
        }
      }
      const value = match[2] ? w.links.filter(x => x.issue === issue && x.kind === (match[2] === 'sub_issues' ? 'sub' : 'blocker')).map(x => ({ id: Number(x.childId) })) : target;
      return { code: 0, stdout: JSON.stringify(value) };
    },
  });
  w.ports.github.ensureSortLink = args => {
    phase = args.issue !== 1 ? 'order' : args.kind === 'sub' ? 'sub' : 'parent-blocker';
    return native.github.ensureSortLink(args);
  };
  w.ports.github.sortUpdate = args => {
    phase = args.assignee ? 'assignment' : 'close';
    return native.github.sortUpdate(args);
  };
  return { effects, get admission() { return insideAdmission ? phase : ''; } };
}

for (const phase of ['sub', 'parent-blocker', 'order', 'assignment']) {
  for (const change of ['parent-person', 'parent-claim', 'child-person']) test(`${phase} rejects ${change} arriving in native child claim validation`, async () => {
    const w = mixedFixture('split'); await w.seed();
    const native = nativeSplitWrites(w), owners = w.ports.owners.read;
    let injected = false;
    w.ports.owners.read = async args => {
      const lastChild = phase !== 'order' || args.issues[0] === w.issues.find(x => x.title.startsWith('runtime part'))?.html_url;
      if (!injected && native.admission === phase && args.issues[0] !== key(1) && lastChild) {
        injected = true;
        const target = change.startsWith('parent') ? w.issues[0] : w.issues.find(x => x.html_url === args.issues[0]);
        if (change.endsWith('person')) target.assignees = [{ login: 'person' }];
        else w.claims.push({ issue: target.html_url, active: true, owner: 'worker' });
      }
      return owners(args);
    };
    await tick(w);
    assert.equal(injected, true, 'reach child claim validation inside native admission');
    assert.equal(native.effects.filter(x => x.phase === phase).length, 0, 'owned endpoints must stop native transport');
    assert.equal(w.writes.filter(x => x.kind === 'comment').length, 0);
    assert.equal(w.issues.length, 3);
    if (change.endsWith('person')) assert.ok(w.issues.some(x => x.assignees.some(a => a.login === 'person')));
  });
}

test('ordering admission checks both child issues after the last child claim read', async () => {
  const w = mixedFixture('split'); await w.seed();
  const native = nativeSplitWrites(w), owners = w.ports.owners.read;
  let injected = false;
  w.ports.owners.read = async args => {
    const first = w.issues.find(x => x.title.startsWith('runtime part'));
    if (!injected && native.admission === 'order' && args.issues[0] === first?.html_url) {
      injected = true;
      w.issues.find(x => x.title.startsWith('cli part')).assignees = [{ login: 'person' }];
    }
    return owners(args);
  };
  await tick(w);
  assert.equal(injected, true);
  assert.equal(native.effects.filter(x => x.phase === 'order').length, 0, 'both relationship endpoints need current assignees');
});

test('split resumes a completed unassigned part before its first link and permits local completion', async () => {
  const w = mixedFixture('split'); await w.seed();
  w.ports.github.ensureSortLink = async () => { throw Error('controlled interruption before first relationship'); };
  await tick(w);
  assert.equal(w.issues.length, 3);
  assert.equal(w.links.length, 0);
  const remote = w.issues.find(x => x.title.startsWith('runtime part')), cli = w.issues.find(x => x.title.startsWith('cli part'));
  remote.state = 'closed'; remote.state_reason = 'completed';
  const native = nativeSplitWrites(w);
  await tick(w); await tick(w);
  assert.equal(w.writes.filter(x => x.kind === 'part').length, 2, 'recover completed children without replacement');
  assert.equal(w.links.length, 5, 'confirm all missing relationships for the completed child');
  assert.equal(native.effects.filter(x => x.phase === 'assignment').length, 0, 'do not assign completed work');
  assert.deepEqual(remote.assignees, []);
  assert.equal(w.writes.filter(x => x.kind === 'comment').length, 1);
  assert.equal((await read(w)).issues[0].sortSplit.parts.length, 2);
  assert.equal(w.issues[0].state, 'open');
  w.save(w.record(cli.number, { touchedAreas: [{ area: 'cli', evidence: ['src/cli.mjs:12'] }], rootCause: '' })); w.review(cli.number);
  assert.ok((await tick(w)).eligible.includes(cli.html_url), 'local child can start after completed remote work');
  cli.state = 'closed'; cli.state_reason = 'completed';
  await tick(w); await tick(w);
  assert.equal(w.issues[0].state, 'closed');
  assert.equal(native.effects.filter(x => x.phase === 'close').length, 1);
  assert.equal(w.writes.filter(x => x.kind === 'comment' && x.body.includes('pdd-issue-split:v1')).length, 1);
  assert.equal(w.links.length, 5);
  assert.equal(w.issues.length, 3);
});

for (const ownership of ['person', 'claim']) test(`completed child held by ${ownership} can resume missing links when released`, async () => {
  const w = mixedFixture('split'); await w.seed();
  w.ports.github.ensureSortLink = async () => { throw Error('controlled interruption before links'); };
  await tick(w);
  const remote = w.issues.find(x => x.title.startsWith('runtime part'));
  remote.state = 'closed'; remote.state_reason = 'completed';
  if (ownership === 'person') remote.assignees = [{ login: 'person' }];
  else w.claims.push({ issue: remote.html_url, active: true, owner: 'worker' });
  const native = nativeSplitWrites(w);
  await tick(w); await tick(w);
  assert.equal(w.issues.length, 3);
  assert.equal(w.links.filter(x => x.childId === String(remote.id)).length, 0);
  assert.equal(native.effects.filter(x => x.phase === 'assignment').length, 0);
  assert.equal(w.writes.filter(x => x.kind === 'comment').length, 0);
  if (ownership === 'person') assert.deepEqual(remote.assignees, [{ login: 'person' }]);
  remote.assignees = []; w.claims.length = 0;
  await tick(w); await tick(w);
  assert.equal(w.links.length, 5, 'release must permit the same completed child to finish its split');
  assert.equal((await read(w)).issues[0].sortSplit.parts.length, 2);
  assert.equal(w.issues.length, 3);
  assert.equal(native.effects.filter(x => x.phase === 'assignment').length, 0);
});

test('completion during native assignment admission holds transport and resumes without assignment', async () => {
  const w = mixedFixture('split'); await w.seed();
  const native = nativeSplitWrites(w), owners = w.ports.owners.read;
  let injected = false;
  w.ports.owners.read = async args => {
    if (!injected && native.admission === 'assignment' && args.issues[0] !== key(1)) {
      injected = true;
      const child = w.issues.find(x => x.html_url === args.issues[0]);
      child.state = 'closed'; child.state_reason = 'completed';
    }
    return owners(args);
  };
  await tick(w);
  assert.equal(injected, true);
  assert.equal(native.effects.filter(x => x.phase === 'assignment').length, 0, 'completed work must not receive an assignment PATCH');
  await tick(w); await tick(w);
  assert.equal(native.effects.filter(x => x.phase === 'assignment').length, 0);
  assert.equal((await read(w)).issues[0].sortSplit.parts.length, 2);
  assert.equal(w.links.length, 5);
  assert.equal(w.issues.length, 3);
});
