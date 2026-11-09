import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {applyDependencyChanges, createDependencyReadPorts, readDependencySnapshot, saveDependencyReview, saveDependencyImpact} from '../src/issue-dependencies-github.mjs';
import {reconcileDependencyIntake} from '../src/issue-dependencies-intake.mjs';
import {projectIssueGraph} from '../src/issue-dependencies.mjs';
import {fixture, repository, key, revision} from './helpers/issue-sort-fixture.mjs';

function pendingWorld() {
  const w = fixture([1,2]); delete w.ports.sortContext;
  w.held = false; w.edges = []; w.mutations = [];
  const page = w.ports.github.page;
  w.ports.manualAuthority = {read:async () => ({known:true, allowed:true})};
  w.hold = value => {w.held = value; w.issues[0].labels = value ? ['pdd:manual'] : [];};
  w.ports.github.page = async args => {
    const items = args.kind === 'timeline' && args.issue === 1 && w.held
      ? [{event:'labeled', label:{name:'pdd:manual'}, actor:{login:'writer'}}]
      : args.kind === 'blockedBy' ? w.edges.filter(e => e.dependent === key(args.issue)).map(e => ({html_url:e.blocker}))
      : args.kind === 'blocking' ? w.edges.filter(e => e.blocker === key(args.issue)).map(e => ({html_url:e.dependent})) : null;
    return items ? {json:JSON.stringify({items, next:''})} : page(args);
  };
  w.ports.github.addBlocker = async ({issue, blockerId}) => {
    w.mutations.push({issue, blockerId});
    w.edges.push({dependent:key(issue), blocker:key(Number(blockerId))});
    return {ok:true};
  };
  w.review = {analysis:'Requires the parser', base:[], continuation:'', issue:key(1),
    inputs:[{key:key(1), revision:revision(w.issues[0])}],
    candidates:w.issues.map(i => ({key:i.html_url, revision:revision(i)})),
    outcome:'pending', dependencies:[{key:key(2), reason:'Required parser', evidence:[key(2)]}], questions:[], effects:'pending'};
  w.intent = String(w.append(1, `<!-- pdd-dependency-review:v1 -->\n\`\`\`json\n${JSON.stringify({schema_version:'pdd.dependency-review.v1', review:w.review})}\n\`\`\``).id);
  return w;
}

test('manual hold excludes saved pending dependency effects and retains the intent until removal', async () => {
  const w = pendingWorld(); w.hold(true);
  const before = (await readDependencySnapshot({repository},w.ports)).snapshot;
  assert.ok(before.issues.find(i => i.key === key(1)).holds.includes('pdd:manual'));
  assert.equal(projectIssueGraph({snapshot:before}).nodes.find(n => n.key === key(1)).executionState, 'held');
  await reconcileDependencyIntake({repository, mode:'auto'}, w.ports);
  assert.equal(w.mutations.length, 0, 'held pending intent mutated a dependency');
  assert.equal(w.writes.length, 0, 'held pending intent appended a comment');
  assert.ok(w.comments.get(1).some(c => String(c.id) === w.intent));
  w.hold(false);
  await reconcileDependencyIntake({repository, mode:'auto'}, w.ports);
  assert.equal(w.mutations.length, 1);
  const after = (await readDependencySnapshot({repository},w.ports)).snapshot;
  assert.ok(after.reviews.some(r => r.continuation === w.intent && r.effects === 'confirmed'));
});

test('dependency effects recheck a hold after preparation and at each remaining boundary', async () => {
  for (const boundary of ['mutation','confirmation','question','review','impact']) {
    const w = pendingWorld();
    // A frozen prepared snapshot cannot see a later label. Safety reads must.
    const snapshot = (await readDependencySnapshot({repository},w.ports)).snapshot;
    w.ports.snapshots = {read:async () => ({snapshot:structuredClone(snapshot)})};
    if (boundary === 'confirmation') snapshot.edges.push({dependent:key(1),blocker:key(2)});
    if (boundary === 'question') {
      const page = w.ports.github.page;
      w.ports.github.page = async args => {
        const reply = await page(args);
        if (args.kind !== 'timeline' || args.issue !== 1) return reply;
        const value = JSON.parse(reply.json);
        value.items.push({event:'blocked_by_removed', blocked_by:{number:2,repository:{full_name:repository}}});
        return {json:JSON.stringify(value)};
      };
    }
    w.ports.admitEffect = async () => {w.hold(true); return true;};
    let result;
    if (boundary === 'review' || boundary === 'impact') {
      w.hold(true);
      result = boundary === 'review' ? await saveDependencyReview({repository,issue:key(1),review:w.review},w.ports)
        : await saveDependencyImpact({repository,issue:key(1),impact:{inputs:[],reviews:[],affected:[],complete:true}},w.ports);
    } else result = await applyDependencyChanges({repository,issue:key(1),reviewId:w.intent},w.ports);
    assert.equal(w.held,true, `${boundary}: effect boundary was not reached`);
    assert.equal(result.state, 'pending', boundary);
    assert.equal(w.mutations.length, 0, `${boundary}: held issue mutated a dependency`);
    assert.equal(w.writes.length, 0, `${boundary}: held issue appended a comment`);
  }
});

test('intake observes every pending node before applying any saved effect', async () => {
  const w = pendingWorld(), observed = [];
  // The tick has already confirmed the hold. A clear snapshot must not override it.
  w.ports.manualHold = {read:async ({issue}) => {
    observed.push(issue); return {known:true,held:issue === 1};
  }};
  await reconcileDependencyIntake({repository,mode:'auto'},w.ports);
  assert.deepEqual([...new Set(observed)].sort(), [1,2]);
  assert.equal(w.mutations.length, 0, 'pending node escaped the early hold observation');
  assert.equal(w.writes.length, 0);
});

test('a label arriving during native mutation admission prevents transport', async () => {
  const w = pendingWorld();
  const snapshot = (await readDependencySnapshot({repository},w.ports)).snapshot;
  const native = createDependencyReadPorts({}, {
    ...w.ports, github:undefined, snapshots:{read:async () => ({snapshot:structuredClone(snapshot)})},
    githubFloor:{blocked:() => false,observe:() => {}},
    admitMutation:async action => {w.hold(true); return action();},
    execFile:async (_file,args) => {
      const method = args[args.indexOf('--method') + 1], endpoint = args.find(a => a.startsWith('repos/'));
      let value;
      if (method === 'POST') { w.mutations.push(endpoint); value = {}; }
      else if (endpoint === `repos/${repository}/issues/1`) value = w.issues[0];
      else if (endpoint === `repos/${repository}/issues/1/timeline?per_page=100`) value = w.held
        ? [{event:'labeled',label:{name:'pdd:manual'},actor:{login:'writer'}}] : [];
      else assert.fail(`Unexpected native endpoint: ${method} ${endpoint}`);
      return {code:0,stdout:`HTTP/2 200 OK\r\n\r\n${JSON.stringify(value)}`,stderr:''};
    },
  });
  const result = await applyDependencyChanges({repository,issue:key(1),reviewId:w.intent},native);
  assert.equal(w.held,true, 'native admission was not reached');
  assert.equal(result.state,'pending');
  assert.equal(w.mutations.length,0,'held native dependency request reached transport');
});

// The table executes every route before comparing counts. One early failure
// must not hide a different automatic effect on the same held authority.
test('manual exclusion covers every automatic effect kind', async t => {
  const {factoryWorld} = await import('./helpers/factory/world.mjs');
  const {scriptedAgent} = await import('./helpers/factory/agent.mjs');
  const {writeFileSync} = await import('node:fs');
  const {saveSortBatch} = await import('../src/issue-sort-github.mjs');
  const effects = [
    ['resume', async () => {
      const w = await factoryWorld(t, {workflow:'bug'}); await w.begin();
      await scriptedAgent(w).until(run => Boolean(run.done.reproduce));
      await w.command(['workflow','status','17']);
      const before = w.record(), state = w.state();
      state.coordinatorId = 'manual-table-replacement';
      state.ownerLaunch.coordinator.coordinatorId = state.coordinatorId;
      writeFileSync(w.stateFile,JSON.stringify(state));
      w.herdr.workspaces = []; w.herdr.tabs = []; w.herdr.panes = []; w.time += 120000;
      await w.github.gh(['issue','edit','17','--add-label','pdd:manual']); await w.tick();
      return w.herdr.panes.filter(p => p.cwd === before.root && p.agent).length;
    }],
    ['wake', async () => {
      const w = await factoryWorld(t); await w.begin();
      await scriptedAgent(w).until(run => run.area === 1);
      await w.command(['workflow','status','17']);
      await w.command(['workflow','park','--reason','Waiting for PDD issue #3129','--blocker','pdd','--until','#3129'],{cwd:w.record().root});
      const root = w.record().root;
      w.installedPddCapabilities = []; await w.tick();
      assert.equal(w.record().parking?.phase,'parked');
      w.installedPddCapabilities = undefined;
      await w.github.gh(['issue','edit','17','--add-label','pdd:manual']); await w.tick();
      return w.herdr.panes.filter(p => p.cwd === root && p.agent).length;
    }],
    ['claim', async () => {
      const w = await factoryWorld(t);
      await w.github.gh(['issue','edit','17','--add-label','pdd:manual']);
      await w.start(); await w.tick(); w.messages();
      return Number(w.github.issues.get(17).labels.includes('pdd:working'))
        + w.packets.flatMap(p => p.issues).filter(i => i.number === 17 && i.eligible).length;
    }],
    ['dependency', async () => {
      const w = pendingWorld(); w.hold(true);
      await reconcileDependencyIntake({repository,mode:'auto'},w.ports);
      return w.mutations.length;
    }],
    ['sort', async () => {
      const w = fixture(); w.issues[0].labels = ['pdd:manual'];
      w.ports.manualAuthority = {read:async () => ({known:true,allowed:true})};
      const page = w.ports.github.page;
      w.ports.github.page = args => args.kind === 'timeline' ? {json:JSON.stringify({items:[{event:'labeled',label:{name:'pdd:manual'},actor:{login:'writer'}}],next:''})} : page(args);
      const snapshot = (await readDependencySnapshot({repository},w.ports)).snapshot;
      await saveSortBatch({repository,snapshot,sorts:[w.record(1)]},w.ports).catch(() => {});
      return w.writes.length;
    }],
    ['comment', async () => {
      const w = pendingWorld(); w.hold(true);
      await saveDependencyReview({repository,issue:key(1),review:w.review},w.ports);
      return w.writes.length;
    }],
  ];
  const actual = [];
  for (const [kind, run] of effects) actual.push({kind, count:await run()});
  assert.deepEqual(actual, effects.map(([kind]) => ({kind,count:0})), 'a held issue received an automatic effect');
});
