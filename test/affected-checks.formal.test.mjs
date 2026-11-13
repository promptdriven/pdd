import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {mkdtempSync, mkdirSync, writeFileSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {baselineReport, buildCheckPlan, checkPlanResults, selectCheckTests} from '../src/runtime-seam.mjs';
import {fullCheckPass} from '../src/workflow-story-card.mjs';

// Oracles: the Rules to check in affected-story-selection.md and
// affected-baseline-report.md, qualified by the approved planner/client contracts.
// Exhaustive only over the finite domains below. Supplied roles/closures do not
// prove Git classification. Supplied observations do not authenticate receipts.
// No CLI, network, approval, publication, merge or native-suite effect is proved.
const path = name => `test/runtime/${name}.json`;
const planOf = stories => ({schema_version:'pdd.check-plan.v1', stories});
function firstOccurrences(values) {
  const answer = [];
  for (const value of values) if (!answer.includes(value)) answer.push(value);
  return answer;
}
function* words(alphabet, length) {
  if (length === 0) { yield []; return; }
  for (const prefix of words(alphabet, length - 1))
    for (const item of alphabet) yield [...prefix, item];
}
function* orders(remaining, prefix = []) {
  yield prefix;
  for (const item of remaining) yield* orders(remaining.filter(value => value !== item), [...prefix, item]);
}
function sandbox(t) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-affected-formal-'));
  t.after(() => rmSync(root, {recursive:true, force:true}));
  return root;
}
function json(root, relative, value) {
  const full = join(root, relative);
  mkdirSync(join(full, '..'), {recursive:true});
  writeFileSync(full, JSON.stringify(value));
}

test('formal: every supplied target variant survives selection; empty target set falls back to full', t => {
  // Every ordered subset of A,B,C; each role; four layouts per Story including
  // empty, one variant, two variants and reversed duplicate variants; all modes.
  let count = 0;
  for (const order of orders(['A','B','C']))
    for (const assignments of words(['target','baseline'], order.length))
      for (const layouts of words([0,1,2,3], order.length)) {
        const stories = order.map((name, i) => ({role:assignments[i], tests:[[],
          [path(name)], [path(name),path(`${name}.recorded`)],
          [path(`${name}.recorded`),path(name),path(`${name}.recorded`)]][layouts[i]]}));
        const all = [], targets = [], baselines = [];
        for (const story of stories) for (const value of story.tests) {
          all.push(value);
          (story.role === 'target' ? targets : baselines).push(value);
        }
        for (const mode of ['default','full','affected']) {
          const expected = {mode:mode === 'affected' ? 'affected' : 'full',
            tests:firstOccurrences(mode === 'affected' && targets.length ? targets : all),
            baseline_tests:firstOccurrences(mode === 'affected' && targets.length ? baselines : [])};
          const input = planOf(stories), before = structuredClone(input);
          const got = mode === 'default' ? selectCheckTests(input)
            : selectCheckTests(input, {affected:mode === 'affected'});
          assert.deepEqual(got, expected, `FORMAL_SELECTION ${JSON.stringify({stories,mode})}`);
          assert.deepEqual(input, before, 'selection must not rewrite supplied inventory');
          count++;
        }
      }
  assert.equal(count, 10443);
  t.diagnostic(`selection: ${count} cases; all ordered subsets, roles, layouts and three modes`);
});

const outcomes = ['waiting','sent','passed','failed','refused','partial','not run','local-unsent'];
function observation(state, index, name, currentness, stage) {
  const local = state === 'local-unsent';
  return {story_path:`user_stories/${name}.md`,test:path(name),batch:`synthetic-original-${index}`,
    request_id:local ? null : `00000000-0000-4000-8000-${String(index + 1).padStart(12,'0')}`,
    evidence_kind:local ? 'local' : 'receipt',state:local ? 'not run' : state,
    reason:state === 'passed' ? null : {code:'synthetic-outcome',message:`Original ${state}`},
    created_at:'2026-11-01T10:00:00Z',report_url:local ? null : 'https://runtime.example.test/r/original',
    source_sha256:'a'.repeat(64),currentness,currentness_scope:'original-batch',stage};
}

test('formal: baseline histories retain every original outcome and identity without inventing current rows', t => {
  // All sequences of 0..3 canonical outcomes plus a local unsent alternative.
  // Uniform currentness/stage per sequence; either C-only or alternating C/D.
  // Availability and warnings vary independently. Target/unselected noise exists.
  const plan = planOf([{role:'target',tests:[path('A'),path('A.recorded')]},
    {role:'baseline',tests:[path('C'),path('D'),path('C')]}]);
  let count = 0;
  for (let length = 0; length <= 3; length++) for (const states of words(outcomes, length))
    for (const currentness of ['current','stale','unavailable'])
      for (const stage of ['current','pr1','before','unavailable'])
        for (const availability of ['available','partial','unavailable'])
          for (const alternate of [false,true]) for (const warnings of [[],['Synthetic incomplete history.']]) {
            const expectedObservations = states.map((state, i) => observation(state, i,
              alternate && i % 2 ? 'D' : 'C', currentness, stage));
            const observations = [observation('passed', 8, 'A', 'current', 'current'),
              ...expectedObservations, observation('failed', 9, 'Z', 'current', 'current')];
            const input = {plan,observations,availability,warnings}, before = structuredClone(input);
            const got = baselineReport(input);
            const expected = {schema_version:'pdd.baseline-report.v1',availability,tests:[path('C'),path('D')],
              observations:expectedObservations,
              missing_tests:['C','D'].filter(name => !expectedObservations.some(row => row.test === path(name))).map(path),
              warnings};
            assert.deepEqual(got, expected,
              `FORMAL_HISTORY ${JSON.stringify({states,currentness,stage,availability,alternate,warnings})}`);
            assert.deepEqual(input, before, 'history projection must not rewrite original inputs');
            count++;
          }
  assert.equal(count, 84240);
  t.diagnostic(`history: ${count} cases; every outcome sequence length 0..3 within stated metadata bounds`);
});

test('formal: missing or nonpassing current rows cannot become a current full result', t => {
  const domain = ['absent','passed','failed','refused','not_run','unknown','running'];
  const plan = planOf([{role:'target',tests:[path('A'),path('A.recorded')]},
    {role:'baseline',tests:[path('C')]}]);
  let count = 0;
  for (const states of words(domain, 3)) {
    const names = ['A','A.recorded','C'];
    const rows = names.flatMap((name, i) => states[i] === 'absent' ? [] : [{test:path(name),state:states[i]}]);
    const got = checkPlanResults(plan, rows);
    for (const [role, positions] of [['target',[0,1]],['baseline',[2]]]) {
      const expected = {tests:positions.map(i => path(names[i])).sort(), passed:[],failures:[],unresolved:[]};
      for (const i of positions) expected[states[i] === 'passed' ? 'passed' : states[i] === 'failed' ? 'failures' : 'unresolved'].push(path(names[i]));
      for (const key of ['passed','failures','unresolved']) expected[key].sort();
      expected.state = expected.failures.length ? 'failed' : expected.unresolved.length ? 'not_run' : 'passed';
      assert.deepEqual(got[role], expected, `FORMAL_CURRENT_ROWS ${JSON.stringify({states,role})}`);
    }
    count++;
  }
  assert.equal(count, 343);
  t.diagnostic(`current row projection: ${count} cases; seven states for each of three tests`);
});

test('formal: planner uncertainty preserves all obligations within supplied change/closure bounds', t => {
  const root = sandbox(t), names = ['A','B','C'];
  // Known changed paths need readable permitted bytes in both revisions. The
  // capture port supplies closures; it does not replace the source file port.
  const knownFiles = new Map([
    ['docs/shared.md', 'Shared dependency without an implementation owner.\n'],
    ['prompts/A.prompt.md', '# Story A prompt\n']
  ]);
  for (const [path,content] of knownFiles) {
    mkdirSync(join(root,path,'..'), {recursive:true});
    writeFileSync(join(root,path), content);
  }
  const gitBlob = content => createHash('sha1')
    .update(`blob ${Buffer.byteLength(content)}\0`).update(content).digest('hex');
  const selected = names.flatMap(name => (name === 'A' ? [path(name),path('A.recorded')] : [path(name)])
    .map(testPath => ({path:testPath,storyPath:`user_stories/${name}.md`})));
  const changes = [null,[],['docs/unrelated.md'],['docs/shared.md'],['prompts/A.prompt.md'],
    ['pdd-source.json'],['pdd-workspace.json'],['pdd-bindings.json']];
  let count = 0;
  for (const changed of changes) for (const missingClosure of [null,...names]) for (const oldMetadata of [true,false]) {
    const plan = buildCheckPlan({root,found:{visible:new Set(knownFiles.keys()),workspace:{configured:false}},selected,full:true,affected:true}, {
      git(_root,args) {
        if (changed === null) throw Error('Synthetic unavailable comparison');
        if (args[0] === 'ls-tree' && !oldMetadata) throw Error('Synthetic unavailable old metadata');
        if (args[0] === 'ls-tree') return [...knownFiles]
          .filter(([path]) => args.slice(args.indexOf('--') + 1).includes(path))
          .map(([path,content]) => `100644 blob ${gitBlob(content)}\t${path}\0`).join('');
        if (args[0] === 'show') {
          const path = args[1].slice(args[1].indexOf(':') + 1);
          if (!knownFiles.has(path)) throw Error('Synthetic unavailable old file');
          return knownFiles.get(path);
        }
        if (args[0] === 'diff' && !args.includes('--diff-filter=D')) return changed.join('\0');
        return '';
      },
      capture() { return {stories:names.map(name => ({story_path:`user_stories/${name}.md`,
        unavailable:missingClosure === name,files:[{path:`prompts/${name}.prompt.md`},
          ...(name !== 'C' ? [{path:'docs/shared.md'}] : [])]}))}; }
    });
    const conservative = changed === null || changed.length === 0 || missingClosure !== null
      || !oldMetadata || changed[0] === 'docs/unrelated.md' || changed[0].startsWith('pdd-');
    const expectedNames = conservative ? names : changed[0] === 'docs/shared.md' ? ['A','B'] : ['A'];
    const expected = selected.filter(row => expectedNames.some(name => row.storyPath === `user_stories/${name}.md`)).map(row => row.path);
    assert.deepEqual(selectCheckTests(plan,{affected:true}).tests, expected,
      `FORMAL_UNCERTAINTY ${JSON.stringify({changed,missingClosure,oldMetadata})}`);
    assert.equal(plan.stories.length, 3, 'classification retains the complete inventory');
    count++;
  }
  assert.equal(count, 64);
  t.diagnostic(`planner: ${count} cases; supplied Git answers, closure availability and old metadata`);
});

test('formal: historical baseline snapshots cannot grant the real fullCheckPass gate', t => {
  const root = sandbox(t), state = join(root,'state'), batchA = '20261101-100000-aaaa', batchC = '20261101-090000-cccc';
  for (const name of ['A','C']) json(root,path(name),{schema_version:'prompt-runtime.program-scenario.v1',
    story_path:`user_stories/${name}.md`,criteria:[{id:'AC1'},{id:'AC2'}],steps:[]});
  const plan = planOf([{role:'target',tests:[path('A')]},{role:'baseline',tests:[path('C')]}]);
  const domain = ['missing','passed','failed','refused','partial','waiting','sent','not run','unknown','running'];
  let count = 0;
  for (const currentState of domain) for (const source of ['current','stale','unavailable'])
    for (const passedCriteria of [0,1,2]) for (const historicalState of ['passed','failed','local-unsent']) {
      const report = baselineReport({plan,observations:[observation(historicalState,0,'C','current','current')],availability:'available',warnings:[]});
      const save = (id,name,row,metadata = {}) => {
        const common = {batch:id,source_sha256:(name === 'A' ? 'a' : 'c').repeat(64),rows:[row],...metadata};
        json(state,`batches/${id}/batch.json`,{...common,intent:'check',root,created_at:'2026-11-01T10:00:00Z'});
        json(state,`batches/${id}/summary.json`,{...common,repo:root});
      };
      save(batchA,'A',{test:path('A'),state:'passed',criteria:{total:2,passed:2}},
        {baseline_report:report,check_selection:{mode:'affected',tests:[path('A')],baseline_tests:[path('C')]}});
      rmSync(join(state,'batches',batchC),{recursive:true,force:true});
      if (currentState !== 'missing') save(batchC,'C',{test:path('C'),state:currentState,criteria:{total:2,passed:passedCriteria}});
      const got = fullCheckPass({root},{env:{PDD_STATE_DIR:state},
        findTests:() => ({tests:['A','C'].map(name => ({path:path(name)}))}),
        capture(_root,selection) {
          if (selection.tests.includes(path('C')) && source === 'unavailable') throw Error('Synthetic capture unavailable');
          return {sha256:(selection.tests.includes(path('C')) ? source === 'current' ? 'c' : 'd' : 'a').repeat(64)};
        }});
      const expected = currentState === 'passed' && source === 'current' && passedCriteria === 2;
      assert.equal(got.pass, expected,
        `FORMAL_FULL_GATE ${JSON.stringify({currentState,source,passedCriteria,historicalState})}`);
      if (currentState === 'missing') assert.ok(got.problems.some(row => row.path === path('C') && row.kind === 'missing'));
      count++;
    }
  assert.equal(count, 270);
  t.diagnostic(`fullCheckPass: ${count} cases; saved row state, source freshness, criterion count and historical snapshot`);
});
