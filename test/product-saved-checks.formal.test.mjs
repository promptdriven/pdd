import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { productStatus, productNext } from '../src/product.mjs';

// Independent oracle: approved product-saved-checks Story, Rules to check.
// This checks product decisions through the real public operations. Owner
// evidence is injected; receipt parsing, source capture and default-reader
// integration are deliberately outside this bounded proof.
const files = JSON.parse(readFileSync(new URL('./runtime/product-saved-checks.json', import.meta.url))).initial_world.files;
const cwd = '/project';
const repository = 'example/coffee';
const marker = run => `<!-- pdd-product: run=${run} -->`;
const issue = (run, number) => ({ number, body: marker(run), state: 'OPEN',
  user: { login: 'member' }, author_association: 'MEMBER', created_at: '2026-10-01T00:00:00Z' });
const localRun = (name, number, root) => ({ workflow: 'feature', number,
  issue: { number }, productMarker: marker(name), root, state: 'running', done: {},
  stage: { id: 'prompt-story' }, pr: [], baseBranch: 'alpha' });
const row = (id, current, verdict, at) => ({ story: `user_stories/server/${id}-check.md`,
  current, pass: verdict === 'pass', result: verdict === 'pass' ? '✓' : 'no verdict', at });
const part = (status, name) => status.parts.find(item => item.part === name);

function fixture() {
  const state = { issues: [], runs: [], workflow: [], saved: [], reads: [],
    prs: [], base: '/base', closed: [], starts: [], creates: [], productState: null };
  const ports = {
    readFile: async path => {
      if (!files[path]) throw Object.assign(Error('missing synthetic input'), { code: 'ENOENT' });
      return files[path].content;
    },
    resolveRepository: async () => ({ repository, defaultBranch: 'alpha' }),
    listRuns: async () => state.runs,
    storyEvidence: async (run, options) => {
      state.reads.push({ owner: 'workflow', root: run.root, ...options });
      return structuredClone(state.workflow);
    },
    savedStoryEvidence: async input => {
      state.reads.push({ owner: 'saved', ...input });
      return { stories: structuredClone(input.root === cwd ? state.saved : []), warnings: [] };
    },
    issuePage: async ({ page, perPage }) => ({
      items: state.issues.slice((page - 1) * perPage, page * perPage),
      total_count: state.issues.length, incomplete_results: false,
    }),
    issueByNumber: async ({ number }) => state.issues.find(item => item.number === number),
    timelinePage: async ({ issue: number }) => state.prs.filter(pr => pr.issue === number).map(pr => ({
      event: 'cross-referenced', source: { issue: { pull_request: { html_url: pr.url } } },
    })),
    pullRequest: async ({ number }) => state.prs.find(pr => pr.number === number),
    currentActor: async () => ({ login: 'member' }),
    planOnBase: async () => true,
    openBaseSource: async () => ({ root: state.base, handle: state.base ? 'owned-base-view' : null }),
    closeBaseSource: async ({ handle }) => { state.closed.push(handle); return {}; },
    readProductState: async () => ({ json: state.productState }),
    writeProductState: async ({ json }) => { state.productState = json; return {}; },
    lockProductState: async () => ({ handle: 'owned-product-lock' }),
    unlockProductState: async () => ({}),
    now: async () => ({ milliseconds: 100000 }),
    startRun: async input => { state.starts.push(input); assert.fail('status/next started a workflow'); },
    createIssue: async input => { state.creates.push(input); assert.fail('status/next created an issue'); },
    execFile: async () => assert.fail('unexpected subprocess outside the injected raw ports'),
  };
  return { state, ports };
}

function expectServer(status, pass, stale, label) {
  assert.deepEqual(part(status, 'server'), { part: 'server', total: 4, pass, stale,
    notRun: 4 - pass - stale }, label);
  assert.deepEqual(status.slices, [{ slice: '1', total: 13, pass, stale,
    notRun: 13 - pass - stale }], label);
}

test('FORMAL standalone progress neither completes implementation nor supplies Needs', async t => {
  for (const link of ['absent', 'verified', 'unverified']) {
    const f = fixture();
    if (link !== 'absent') {
      f.state.issues = [issue('server-1', 81)];
      f.state.runs = [localRun('server-1', 81, '/server-worktree')];
      if (link === 'unverified') f.ports.issueByNumber = async () => ({ ...issue('other-run', 81) });
    }
    f.state.saved = ['S01', 'S02', 'S03', 'S04', 'S010'].map(id => row(id, true, 'pass', 2));
    const status = await productStatus({ cwd }, f.ports);
    expectServer(status, 4, 0, link);
    const server = status.runs.find(item => item.run === 'server-1');
    assert.equal(server.state, link === 'absent' ? 'planned' : link === 'verified' ? 'running (step: prompt-story)' : 'unverified', link);
    assert.ok(!status.ready.includes('journeys'), link);
    const next = await productNext({ cwd }, f.ports);
    assert.deepEqual(next.waiting.find(item => item.run === 'journeys').needs,
      ['server-1', 'phone-1', 'barista-1'], link);
    if (link !== 'verified') assert.ok(f.state.reads.every(read => read.root === cwd), link);
    assert.deepEqual(f.state.starts, []);
    assert.deepEqual(f.state.creates, []);
  }
  t.diagnostic('3 link states; 4 exact saved passes plus S010 noise; status and next');
});

// A row is decisive exactly when no other matching row outranks it under the
// Story relation. This relational witness oracle uses neither a production
// helper nor production sorting/accumulation. Unequal times avoid unspecified
// ties between conflicting results.
function oracle(rows) {
  const matches = rows.filter(item => item && item.id === 'S01');
  const decisive = matches.find(candidate => !matches.some(other =>
    (other.current && !candidate.current) ||
    (other.current === candidate.current && other.at > candidate.at)));
  return { pass: Number(Boolean(decisive?.current && decisive.verdict === 'pass')),
    stale: Number(Boolean(decisive && !decisive.current && decisive.verdict === 'pass')) };
}

test('FORMAL all bounded evidence pairs obey exact identity, precedence and one-count rules', async t => {
  const domain = [null];
  for (const id of ['S01', 'S010']) for (const current of [false, true])
    for (const verdict of ['pass', 'failure', 'unknown']) domain.push({ id, current, verdict });
  const placements = [['workflow', 'saved'], ['saved', 'workflow'], ['workflow', 'workflow'], ['saved', 'saved']];
  let cases = 0;
  for (const first of domain) for (const second of domain)
    for (const placement of placements) for (const reverse of [false, true]) {
      const f = fixture();
      f.state.issues = [issue('server-1', 81)];
      f.state.runs = [localRun('server-1', 81, '/server-worktree')];
      const observations = [first && { ...first, at: 1 }, second && { ...second, at: 2 }];
      for (const index of reverse ? [1, 0] : [0, 1]) {
        const item = observations[index];
        if (item) f.state[placement[index]].push(row(item.id, item.current, item.verdict, item.at));
      }
      const expected = oracle(observations);
      const label = JSON.stringify({ observations, placement, reverse });
      const status = await productStatus({ cwd }, f.ports);
      expectServer(status, expected.pass, expected.stale, label);
      assert.equal(status.runs.find(item => item.run === 'server-1').state,
        'running (step: prompt-story)', label);
      assert.ok(!status.ready.includes('journeys'), label);
      cases++;
    }
  assert.equal(cases, 1352);
  t.diagnostic(`${cases} cases: 13 x 13 optional row values x 4 source placements x 2 row orders; times 1 < 2`);
});

test('FORMAL merged comparisons scope cwd evidence to its planned run', async t => {
  for (const base of ['/base', null]) {
    const f = fixture();
    f.state.base = base;
    f.state.issues = [issue('server-1', 81), issue('phone-1', 82)];
    f.state.runs = [localRun('server-1', 81, '/server-worktree'), localRun('phone-1', 82, '/phone-worktree')];
    f.state.runs[0].pr = [{ number: 30, stage: 'code', branch: 'server-code' }];
    f.state.prs = [{ issue: 81, number: 30, url: `https://github.com/${repository}/pull/30`,
      body: `${marker('server-1')}\n<!-- pdd-workflow:synthetic:code -->`, state: 'MERGED',
      updatedAt: '2026-10-02T00:00:00Z', headRefName: 'server-code', isCrossRepository: false,
      headRepository: { name: 'coffee' }, headRepositoryOwner: { login: 'example' } }];
    f.ports.savedStoryEvidence = async input => {
      f.state.reads.push({ owner: 'saved', ...input });
      // Raw owner observation: cwd has an old S01 pass, current only under
      // its own files. P01 is current for the independent unmerged run.
      const comparedWithOwnFiles = !Object.hasOwn(input, 'comparisonRoot') || input.comparisonRoot === cwd;
      return { stories: input.root === cwd ? [row('S01', comparedWithOwnFiles, 'pass', 1),
        { story: 'user_stories/phone/P01-check.md', pass: true, current: true, result: '✓', at: 1 }] : [], warnings: [] };
    };
    const status = await productStatus({ cwd }, f.ports);
    assert.deepEqual(part(status, 'server'), { part: 'server', total: 4, pass: 0, stale: 1, notRun: 3 });
    assert.deepEqual(part(status, 'phone'), { part: 'phone', total: 4, pass: 1, stale: 0, notRun: 3 });
    assert.deepEqual(status.slices, [{ slice: '1', total: 13, pass: 1, stale: 1, notRun: 11 }]);
    assert.equal(status.runs.find(item => item.run === 'server-1').state, 'merged');
    for (const root of [cwd, '/server-worktree']) assert.ok(f.state.reads.some(read =>
      read.owner === 'saved' && read.root === root && Object.hasOwn(read, 'comparisonRoot') && read.comparisonRoot === base),
    `saved evidence from ${root} must compare with ${base}`);
    assert.deepEqual(f.state.closed, base ? ['owned-base-view'] : []);
  }
  t.diagnostic('2 base availability states; merged S01 and unmerged P01 share cwd evidence without cross-run promotion');
});
