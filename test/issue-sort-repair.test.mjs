import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createDependencyReadPorts, readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { routeSortIssues, pacedSortWrites } from '../src/issue-sort-github.mjs';
import { reconcileDependencyIntake } from '../src/issue-dependencies-intake.mjs';
import { interfaceBlocks, proseSha256, promptRefusal, checkInput } from '../src/runtime-preflight.mjs';
import { fixture, complete, repository, key } from './helpers/issue-sort-fixture.mjs';
const fixed = w => ({ ...w.record(1).status, state: 'fixed', fix: 'https://github.com/example/project/pull/90' });
const snapshot = async w => (await readDependencySnapshot({ repository }, w.ports)).snapshot;
const http = value => ({ code: 0, stdout: `HTTP/2.0 200 OK\r\n\r\n${JSON.stringify(value)}` });

for (const update of [{ close: true }, { assignee: 'helper' }, { label: 'pdd:needs-owner' }]) test(`native sort admission covers ${Object.keys(update)[0]}`, async () => {
  let guarded = 0, sent = 0;
  const native = createDependencyReadPorts({}, {
    admitMutation: async () => { guarded++; throw Error('stopped'); },
    execFile: async (_file, args) => { if (args[args.indexOf('--method') + 1] !== 'GET') sent++; return http({ labels: [] }); },
  });
  await assert.rejects(native.github.sortUpdate({ repository, issue: 1, ...update }));
  assert.equal(sent, 0); assert.equal(guarded, 1);
});

test('stop during the final source read prevents the native close PATCH', async () => {
  const w = fixture(); w.save(w.record(1, { status: fixed(w) }));
  let enabled = true, reads = 0, guarded = 0, mutations = 0;
  const native = createDependencyReadPorts({}, {
    admitMutation: async action => { guarded++; if (!enabled) throw Error('stopped'); return action(); },
    execFile: async (_file, args) => {
      const method = args[args.indexOf('--method') + 1];
      if (method === 'PATCH') { mutations++; w.issues[0].state = 'closed'; }
      return http(w.issues[0]);
    },
  });
  const s = await snapshot(w), contextRead = w.ports.context.read;
  w.ports.context.read = async args => { if (++reads === 3) enabled = false; return contextRead(args); };
  w.ports.github.sortUpdate = native.github.sortUpdate;
  const result = await routeSortIssues({ repository, snapshot: s, mode: 'auto' }, w.ports);
  assert.equal(result.failed.length, 1);
  assert.equal(result.failed[0].issue, key(1));
  assert.ok(result.failed[0].reason.length);
  assert.equal(enabled, false); assert.equal(mutations, 0); assert.equal(guarded, 1);
  assert.equal(w.issues[0].state, 'open');
});

test('a pdd-prefixed area label change during pacing stales its owner', async () => {
  const w = fixture([1], { context: { areas: [
    { name: 'first', owner: 'first-owner', match: { labels: ['pdd:first'] } },
    { name: 'second', owner: 'second-owner', match: { labels: ['pdd:second'] } },
  ] } });
  w.issues[0].labels = ['pdd:first'];
  // Copy the observed row. This case does not assume the fingerprint algorithm.
  const s = await snapshot(w), r = w.record(1);
  r.inputs.find(x => x.key.endsWith('#sort-labels')).revision = s.inputs.find(x => x.key.endsWith('#sort-labels')).revision;
  w.save(r); w.review(1);
  w.ports.wait.sleep = async () => { w.issues[0].labels = ['pdd:second']; };
  await reconcileDependencyIntake({ repository, mode: 'auto' }, w.ports);
  assert.deepEqual(w.issues[0].assignees, []);
});

test('a tick routes at most ten fixed issues and the next tick resumes', async () => {
  const w = fixture(Array.from({ length: 12 }, (_, i) => i + 1));
  for (let n = 1; n <= 12; n++) { w.save(w.record(n, { status: fixed(w) })); w.review(n); }
  await reconcileDependencyIntake({ repository, mode: 'auto' }, w.ports);
  assert.equal(w.issues.filter(x => x.state === 'closed').length, 10);
  assert.equal(w.writes.length, 20);
  await reconcileDependencyIntake({ repository, mode: 'auto' }, w.ports);
  assert.equal(w.issues.filter(x => x.state === 'closed').length, 12);
});

test('the shared stream stops at twenty attempts and checks the budget during effects', async () => {
  const w = fixture(); let effects = 0, budget = true;
  w.ports.sortBudget = async () => budget;
  const write = pacedSortWrites(w.ports, { repository });
  await write(async () => { effects++; budget = false; });
  await assert.rejects(write(async () => { effects++; }));
  assert.equal(effects, 1);
  const bounded = pacedSortWrites(fixture().ports, { repository });
  for (let i = 0; i < 20; i++) await bounded(async () => {});
  await assert.rejects(bounded(async () => { effects++; }));
  assert.equal(effects, 1);
});

test('native sort effects stop if the GitHub budget becomes low in a read', async () => {
  let budget = true, writes = 0;
  const native = createDependencyReadPorts({}, {
    sortBudget: async () => budget,
    execFile: async (_file, args) => {
      const method = args[args.indexOf('--method') + 1];
      if (method === 'GET') budget = false; else writes++;
      return http({ labels: [] });
    },
  });
  await assert.rejects(native.github.sortUpdate({ repository, issue: 1, label: 'pdd:needs-owner' }));
  assert.equal(writes, 0);
});

test('native retries do not attach a label which is already present', async () => {
  let writes = 0;
  const native = createDependencyReadPorts({}, { execFile: async (_file, args) => {
    if (args[args.indexOf('--method') + 1] !== 'GET') writes++;
    return http({ labels: [{ name: 'pdd:needs-owner' }] });
  } });
  assert.equal((await native.github.sortUpdate({ repository, issue: 1, label: 'pdd:needs-owner' })).ok, true);
  assert.equal(writes, 0);
});

const owners = ['autopilot-areas','issue-sort','issue-sort-github','issue-dependencies','issue-dependencies-github','issue-dependencies-intake'];
for (const owner of owners) test(`the ${owner} contract admits native use as a current approved contract`, () => {
  const path = `prompts/cli/${owner}.prompt.md`, source = readFileSync(path, 'utf8');
  const iface = JSON.parse(interfaceBlocks(source)[0][1]);
  assert.equal(promptRefusal({ path, interface: iface, prose: proseSha256(source) }, 'repair'), null);
  assert.equal(iface.status, 'approved');
});

test('the workflow-runner contract admits native use with its current interface', () => {
  const path = 'prompts/cli/workflow-runner.prompt.md', source = readFileSync(path, 'utf8');
  const iface = JSON.parse(interfaceBlocks(source)[0][1]);
  assert.equal(promptRefusal({ path, interface: iface, prose: proseSha256(source) }, 'repair'), null);
});

test('the public unconfirmed sort result conforms to its Runtime schema', async () => {
  const w = fixture();
  const append = w.ports.github.appendComment;
  w.ports.github.appendComment = args => args.body.includes('pdd-issue-sort:') ? { json: '{}' } : append(args);
  const result = await complete(w, [w.record(1)]);
  assert.equal(result.state, 'pending'); assert.equal(result.pendingStage, 'sort');
  const iface = JSON.parse(interfaceBlocks(readFileSync('prompts/cli/issue-dependencies-intake.prompt.md', 'utf8'))[0][1]);
  const schema = iface.entries.find(x => x.operation === 'completeDependencyIntake').result_schema;
  assert.deepEqual(checkInput(result, schema, 0).refusals, []);
});

for (const action of ['label-create','umbrella-create']) test(`native admission covers ${action}`, async () => {
  let guarded = 0, sent = 0;
  const native = createDependencyReadPorts({}, {
    admitMutation: async () => { guarded++; throw Error('stopped'); },
    execFile: async (_file, args) => {
      if (args[args.indexOf('--method') + 1] === 'GET') throw Object.assign(Error('absent'), { status: 404 });
      sent++; return http({});
    },
  });
  if (action === 'label-create') await assert.rejects(native.github.ensureSortLabel({ repository, label: 'pdd:needs-owner', write: action => action() }));
  else {
    assert.equal(typeof native.github.createSortUmbrella, 'function');
    await assert.rejects(native.github.createSortUmbrella({ repository, title: 'Global fix: shared-context', body: '<!-- pdd-issue-group:v1 shared-context -->' }));
  }
  assert.equal(guarded, 1); assert.equal(sent, 0);
});

test('observe routes beyond the first ten progress on later ticks without reposting labels', async () => {
  const w = fixture(Array.from({ length: 12 }, (_, i) => i + 1), { mode: 'observe' });
  for (let n = 1; n <= 12; n++) { w.save(w.record(n, { status: fixed(w) })); w.review(n); }
  await reconcileDependencyIntake({ repository, mode: 'observe' }, w.ports);
  assert.equal(w.writes.filter(x => x.kind === 'label').length, 10);
  await reconcileDependencyIntake({ repository, mode: 'observe' }, w.ports);
  assert.equal(w.writes.filter(x => x.kind === 'label').length, 12);
  assert.equal(w.writes.filter(x => x.kind === 'comment').length, 12);
  assert.ok(w.issues.every(x => x.state === 'open' && x.labels.includes('pdd:close-proposed')));
});

test('newly claimed stale candidates do not starve later actionable routes', async () => {
  const bounded = fixture(Array.from({ length: 12 }, (_, i) => i + 1));
  for (let n = 1; n <= 12; n++) { bounded.save(bounded.record(n, { status: fixed(bounded) })); bounded.review(n); }
  await routeSortIssues({ repository, snapshot: await snapshot(bounded), mode: 'auto' }, bounded.ports);
  assert.equal(bounded.issues.filter(x => x.state === 'closed').length, 10);
  const w = fixture(Array.from({ length: 12 }, (_, i) => i + 1));
  for (let n = 1; n <= 12; n++) { w.save(w.record(n, { status: fixed(w) })); w.review(n); }
  const s = await snapshot(w);
  for (let n = 1; n <= 10; n++) w.claims.push({ issue: `https://github.com/example/project/issues/${n}`, active: true, owner: 'worker' });
  await routeSortIssues({ repository, snapshot: s, mode: 'auto' }, w.ports);
  assert.equal(w.issues.slice(0,10).filter(x => x.state === 'closed').length, 0);
  assert.equal(w.issues.slice(10).filter(x => x.state === 'closed').length, 2);
});
