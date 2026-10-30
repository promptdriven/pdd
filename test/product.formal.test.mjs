import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { productStatus, productStart } from '../src/product.mjs';

// Reuse only the approved input files. The oracle is the Story's four phone
// Stories plus four server Stories, four barista Stories and one journey.
const files = JSON.parse(readFileSync(new URL('./runtime/product-status.json', import.meta.url))).initial_world.files;
const marker = run => `<!-- pdd-product: run=${run} -->`;
function fixture() {
  const state = { issues: [], rows: [], local: false, split: false, created: 0, starts: [] };
  const ports = {
    readProductState: async () => ({ json: state.productState ?? null }),
    writeProductState: async ({ json }) => { state.productState = json; return {}; },
    now: async () => ({ milliseconds: (state.clock = (state.clock ?? 0) + 60000) }),
    issueByNumber: async ({ number }) => {
      if (state.fail) throw Error('GitHub unavailable');
      const row = (state.pages?.flat() ?? state.issues).find(item => item.number === number);
      return row && { author_association: 'MEMBER', user: { login: 'member' }, created_at: '2026-10-01T00:00:00Z', ...row };
    },
    readFile: async path => { if (!files[path]) throw Object.assign(Error('missing'), { code: 'ENOENT' }); return files[path].content; },
    resolveRepository: async () => ({ repository: 'example/coffee', defaultBranch: 'alpha' }),
    planOnBase: async () => true,
    listRuns: async () => state.local ? [{ number: 81, state: 'running', pr: [], rows: state.rows }] : [],
    storyEvidence: async run => run.rows,
    startRun: async input => { state.starts.push(input); return { exitCode: 0, message: 'Started.' }; },
    execFile: async (file, args) => {
      assert.equal(file, 'gh');
      if (args[0] === 'api') return {stdout:JSON.stringify(args[1].includes('/timeline?') ? [] : {items:state.issues.map(item=>({author_association:'MEMBER',user:{login:'member'},created_at:'2026-10-01T00:00:00Z',...item})),total_count:state.issues.length,incomplete_results:false})};
      assert.equal(args[0], 'issue'); assert.equal(args[1], 'create');
      state.created++;
      state.issues.push({ number: 100, state: 'OPEN', body: args[args.indexOf('--body') + 1] });
      return { stdout: 'https://github.com/example/coffee/issues/100\n' };
    },
  };
  return { state, ports };
}

test('FORMAL bounded local evidence never promotes stale or near-prefix Stories', async t => {
  const names = [id => id, id => `${id}-menu`, id => `user_stories/${id}-menu.md`, id => `${id}.menu`];
  let cases = 0;
  for (let code = 0; code < 4 ** 4; code++) for (const name of names) for (const noise of [false, true]) {
    const f = fixture(); f.state.local = true; f.state.issues = [{ number: 81, state: 'OPEN', body: marker('phone-1') }];
    const states = Array.from({ length: 4 }, (_, i) => Math.floor(code / 4 ** i) % 4);
    for (let i = 0; i < 4; i++) {
      const id = `P0${i + 1}`, kind = states[i];
      // Domain: 0 missing; 1 current pass; 2 stale pass; 3 current failure.
      if (kind) f.state.rows.push({ story: name(id), pass: kind !== 3, current: kind !== 2 });
      if (noise) for (const unrelated of [`${id}0-noise`, `${id.toLowerCase()}-noise`, `X${id}-noise`]) f.state.rows.push({ story: unrelated, pass: true, current: true });
    }
    const pass = states.filter(kind => kind === 1).length, stale = states.filter(kind => kind === 2).length;
    const status = await productStatus({ cwd: '/project' }, f.ports);
    assert.deepEqual(status.parts, [
      { part: 'phone', total: 4, pass, stale, notRun: 4 - pass - stale },
      { part: 'server', total: 4, pass: 0, stale: 0, notRun: 4 },
      { part: 'barista', total: 4, pass: 0, stale: 0, notRun: 4 },
      { part: 'journeys', total: 1, pass: 0, stale: 0, notRun: 1 },
    ], `evidence code=${code}, noise=${noise}`);
    assert.deepEqual(status.slices, [{ slice: '1', total: 13, pass, stale, notRun: 13 - pass - stale }]);
    cases++;
  }
  t.diagnostic(`${cases} status cases: 4^4 evidence states x 4 basename styles x 2 noise modes`);
});

test('FORMAL bounded sequential starts respect exact markers and no-run/unknown effects', async t => {
  let sequences = 0, unknown = 0;
  for (const existing of ['none', 'open', 'closed', 'near', 'later']) for (const noRun of [false, true]) for (const agent of ['codex', 'claude']) {
    const f = fixture();
    if (existing === 'near' || existing === 'later') f.state.issues.push({ number: 80, state: 'OPEN', body: marker('phone-10') });
    if (['open', 'closed', 'later'].includes(existing)) f.state.issues.push({ number: 81, state: existing === 'closed' ? 'CLOSED' : 'OPEN', body: marker('phone-1') });
    f.state.split = existing === 'later';
    const input = { cwd: '/project', run: 'phone-1', noRun, agent };
    const first = await productStart(input, f.ports), second = await productStart(input, f.ports);
    assert.equal(first.exitCode, 0); assert.equal(second.exitCode, 0); assert.equal(second.issue, first.issue);
    assert.equal(f.state.created, ['none', 'near'].includes(existing) ? 1 : 0);
    assert.equal(second.created, false); assert.equal(first.started, !noRun); assert.equal(second.started, !noRun);
    assert.equal(f.state.starts.length, noRun ? 0 : 2);
    for (const start of f.state.starts) { assert.equal(start.issue, first.issue); assert.equal(start.agent, agent); }
    const creates = f.state.created, starts = f.state.starts.length;
    const result = await productStart({ ...input, run: 'unknown-run' }, f.ports);
    assert.notEqual(result.exitCode, 0); assert.equal(result.started, false);
    assert.equal(f.state.created, creates); assert.equal(f.state.starts.length, starts);
    sequences++; unknown++;
  }
  t.diagnostic(`${sequences} start sequences x 2 calls; ${unknown} unknown-run calls; all no-run effects suppressed`);
});
