import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { promisify } from 'node:util';
import {
  AUTO_DEPS_MARKER_PREFIX,
  acquireFileClaim,
  activeFileConflicts,
  inspectEdgeTimeline,
  issueContentHash,
  parseExplicitDependencies,
  reconcileAutoDependencies,
  releaseFileClaim,
  sweepExpiredClaims,
} from '../../src/autopilot/intake/auto-deps.mjs';
import * as intakeFacade from '../../src/autopilot-intake.mjs';

const execFileAsync = promisify(execFile);
const AUTO_DEPS_URL = pathToFileURL(new URL('../../src/autopilot/intake/auto-deps.mjs', import.meta.url).pathname).href;

const REPO = 'acme/platform';

function makeTempDir(t, prefix) {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
}

function makeFakeGh({ openPages = [[]], issues = {}, blockedBy = {}, timelines = {}, comments = {}, addHandler = null } = {}) {
  const liveBlocked = new Map(Object.entries(blockedBy).map(([k, list]) => [Number(k), list.map(item => (typeof item === 'number' ? { number: item } : { ...item }))]));
  const liveComments = new Map(Object.entries(comments).map(([k, list]) => [Number(k), [...list]]));
  const calls = { listOpenPages: [], added: [], removed: [], commented: [] };

  const gh = {
    calls,
    liveBlocked,
    liveComments,
    listOpenIssues: async ({ page }) => {
      calls.listOpenPages.push(page);
      const idx = page - 1;
      return { items: openPages[idx] ?? [], hasNext: idx + 1 < openPages.length };
    },
    getIssue: async num => {
      if (Object.hasOwn(issues, num)) {
        const entry = issues[num];
        if (entry?.status === 404) return entry;
        return entry;
      }
      return { status: 404 };
    },
    listBlockedBy: async num => {
      const entry = liveBlocked.get(num);
      if (entry && !Array.isArray(entry) && entry.status === 404) return entry;
      return entry ?? [];
    },
    listTimeline: async num => timelines[num] ?? [],
    listComments: async num => liveComments.get(num) ?? [],
    addBlockedBy: async (dep, blocker) => {
      calls.added.push({ dep, blocker: blocker.number });
      if (typeof addHandler === 'function') {
        const custom = await addHandler(dep, blocker);
        if (custom !== undefined) return custom;
      }
      const list = liveBlocked.get(dep) ?? [];
      const key = x => x.html_url ?? `local#${x.number}`;
      if (!list.some(x => key(x) === key(blocker))) list.push(blocker);
      liveBlocked.set(dep, list);
      return { status: 201 };
    },
    removeBlockedBy: async (dep, blocker) => {
      calls.removed.push({ dep, blocker: blocker.number });
      const key = x => x.html_url ?? `local#${x.number}`;
      liveBlocked.set(dep, (liveBlocked.get(dep) ?? []).filter(x => key(x) !== key(blocker)));
      return { status: 200 };
    },
    createComment: async (dep, body) => {
      calls.commented.push({ dep, body });
      const list = liveComments.get(dep) ?? [];
      list.push({ body });
      liveComments.set(dep, list);
      return { status: 201 };
    },
  };
  return gh;
}

test('auto-deps: re-exports from autopilot-intake.mjs and parses only explicit directed prerequisites (ignoring negations, fences, foreign repos)', () => {
  assert.equal(intakeFacade.reconcileAutoDependencies, reconcileAutoDependencies);
  assert.equal(intakeFacade.acquireFileClaim, acquireFileClaim);
  assert.equal(intakeFacade.sweepExpiredClaims, sweepExpiredClaims);

  const parsed = parseExplicitDependencies({
    number: 20,
    title: 'Add webhook delivery',
    body: [
      'Blocked by #10, acme/platform#11 and https://github.com/acme/platform/issues/12.',
      'Must land before #30 and #31.',
      'This is NOT blocked by #99 and no longer depends on #98.',
      "This isn't currently blocked by #5; Un-blocked by #9; The form requires #3.",
      'Inline code `blocked by #7` must not trigger an edge.',
      'Does not block #97 and ignores foreign repo other/repo#55.',
      'Depends on #20 (self-ref ignored).',
      '```md',
      'Blocked by #88',
      '```',
      '> Blocked by #87',
      '<!-- Blocked by #86 -->',
    ].join('\n'),
  }, { repo: REPO });

  assert.deepEqual(parsed.blockedBy.map(x => x.target), [10, 11, 12]);
  assert.deepEqual(parsed.blocking.map(x => x.target), [30, 31]);
  assert.ok(parsed.blockedBy.every(x => x.kind === 'explicit-prerequisite'));
});

test('auto-deps: rejects direct and transitive cycles via dag.mjs and never writes native blocked_by for file overlap', async t => {
  const stateDir = makeTempDir(t, 'pdd-autodeps-cycle-');
  const issue1 = { number: 1, title: 'Base', body: 'Blocked by #3' };
  const issue2 = { number: 2, title: 'Mid', body: '' };
  const issue3 = { number: 3, title: 'Top', body: '' };
  const gh = makeFakeGh({
    openPages: [[issue1, issue2, issue3]],
    issues: { 1: issue1, 2: issue2, 3: issue3 },
    blockedBy: { 2: [issue1], 3: [issue2] },
  });

  const res = await reconcileAutoDependencies({
    repo: REPO,
    subjectIssue: issue1,
    contractDependencies: [
      { dependent: 1, blocker: 2, kind: 'file-overlap', contract: 'both touch src/router.mjs', confirmed: false },
      { dependent: 2, blocker: 1, kind: 'file-overlap', contract: 'shared file only', confirmed: true },
    ],
    gh,
    stateDir,
    now: () => Date.parse('2026-11-22T10:00:00Z'),
  });

  assert.equal(gh.calls.added.length, 0, 'cyclic edge 1->3 and overlap-only edges must never call addBlockedBy');
  assert.ok(res.actions.some(a => a.action === 'skip-cycle' && a.dependent === 1 && a.blocker === 3));
  assert.equal(res.actions.filter(a => a.action === 'skip-overlap-only').length, 2);

  // Reciprocal batch cycle: #10 says "Blocked by #11" and #11 says "Blocked by #10" -> at most one edge lands, never both!
  const i10 = { number: 10, title: 'A', body: 'Blocked by #11' };
  const i11 = { number: 11, title: 'B', body: 'Blocked by #10' };
  const gh2 = makeFakeGh({ openPages: [[i10, i11]], issues: { 10: i10, 11: i11 } });
  const res2 = await reconcileAutoDependencies({ repo: REPO, subjectIssue: i10, gh: gh2, stateDir });
  assert.equal(gh2.calls.added.length, 1);
  assert.ok(res2.actions.some(a => a.action === 'add' && a.dependent === 10 && a.blocker === 11));
  assert.ok(res2.actions.some(a => a.action === 'skip-cycle' && a.dependent === 11 && a.blocker === 10));
});

test('auto-deps: paginated bidirectional discovery, confirmed contract edges, secret-redacted idempotent comments, and hash skip', async t => {
  const stateDir = makeTempDir(t, 'pdd-autodeps-bidir-');
  const i1 = { number: 1, title: 'Schema', body: 'Base schema' };
  const i2 = { number: 2, title: 'Consumer', body: 'Depends on #5 with token ghp_secretLeakValue123456' };
  const i3 = { number: 3, title: 'Contract target', body: 'Uses exported API' };
  const subject = { number: 5, title: 'Core API', body: 'Blocked by #1 (auth Bearer secret-token-xyz)' };

  const gh = makeFakeGh({
    openPages: [[i1, subject], [i2, i3]],
    issues: { 1: i1, 2: i2, 3: i3, 5: subject },
  });

  const r1 = await reconcileAutoDependencies({
    repo: REPO,
    subjectIssue: subject,
    contractDependencies: [{ dependent: 3, blocker: 5, contract: 'REST response v2 schema', confirmed: true }],
    gh,
    stateDir,
    now: () => Date.parse('2026-11-22T11:00:00Z'),
  });

  assert.deepEqual(gh.calls.listOpenPages, [1, 2], 'must paginate through all open issue pages');
  assert.deepEqual(
    gh.calls.added.sort((a, b) => a.dep - b.dep || a.blocker - b.blocker),
    [{ dep: 2, blocker: 5 }, { dep: 3, blocker: 5 }, { dep: 5, blocker: 1 }],
  );
  assert.equal(r1.commentsPosted, 3);
  for (const c of gh.calls.commented) {
    assert.ok(c.body.includes(AUTO_DEPS_MARKER_PREFIX), 'comment must carry v1 marker');
    assert.doesNotMatch(c.body, /ghp_secretLeakValue123456|secret-token-xyz/, 'secrets must be redacted from comments');
  }

  // Same content hash + same confirmed contracts short-circuits with zero GitHub writes.
  const contracts = [{ dependent: 3, blocker: 5, contract: 'REST response v2 schema', confirmed: true }];
  const r2 = await reconcileAutoDependencies({ repo: REPO, subjectIssue: subject, contractDependencies: contracts, gh, stateDir });
  assert.equal(r2.skipped, true);
  assert.equal(r2.reason, 'unchanged-content-hash');
  assert.equal(gh.calls.added.length, 3);
  assert.equal(gh.calls.commented.length, 3);

  // Adding a NEW confirmed contract on unchanged issue text MUST NOT be skipped!
  const i4 = { number: 4, title: 'New consumer', body: 'Uses v2 schema' };
  const ghNewContract = makeFakeGh({
    openPages: [[i1, subject, i4], [i2, i3]],
    issues: { 1: i1, 2: i2, 3: i3, 4: i4, 5: subject },
    blockedBy: { 2: [subject], 3: [subject], 5: [i1] },
  });
  const r2b = await reconcileAutoDependencies({
    repo: REPO, subjectIssue: subject,
    contractDependencies: [...contracts, { dependent: 4, blocker: 5, contract: 'v2 schema', confirmed: true }],
    gh: ghNewContract, stateDir,
  });
  assert.equal(r2b.skipped, false);
  assert.ok(r2b.actions.some(a => a.action === 'add' && a.dependent === 4 && a.blocker === 5));

  // Forced replay is fully idempotent: 0 new adds, 0 duplicate comments.
  const r3 = await reconcileAutoDependencies({
    repo: REPO, subjectIssue: subject,
    contractDependencies: contracts,
    gh, stateDir, force: true,
  });
  assert.equal(r3.skipped, false);
  assert.equal(r3.commentsPosted, 0);
  assert.equal(gh.calls.added.length, 3);
  assert.equal(r3.actions.filter(a => a.action === 'noop-exists').length, 3);
});

test('auto-deps: distinguishes GitHub 404 (fail-closed hold, never auto-dispatch) vs 422 (idempotent no-op)', async t => {
  const stateDir = makeTempDir(t, 'pdd-autodeps-404-422-');
  const existing = { number: 42, title: 'Known blocker', body: '' };
  const subject = { number: 50, title: 'Feature', body: 'Blocked by #404 and #42' };
  const gh = makeFakeGh({
    openPages: [[existing, subject]],
    issues: { 42: existing, 50: subject, 404: { status: 404 } },
    addHandler: async (dep, blk) => {
      if (dep === 50 && blk.number === 42) throw Object.assign(new Error('Validation Failed: already linked'), { status: 422 });
      return { status: 201 };
    },
  });

  const res = await reconcileAutoDependencies({ repo: REPO, subjectIssue: subject, gh, stateDir });
  assert.equal(res.holds.length, 1);
  assert.deepEqual(res.holds[0], { issue: 50, blocker: 404, dispatchable: false, reason: 'blocker-unavailable-404' });
  assert.ok(res.actions.some(a => a.action === 'hold-unknown' && a.blocker === 404 && a.dispatchable === false));
  assert.ok(res.actions.some(a => a.action === 'noop-exists' && a.blocker === 42 && a.status === 422 && a.idempotent === true));

  // Also test 404 coming directly from addBlockedBy (e.g., blocker deleted mid-flight).
  const subject2 = { number: 51, title: 'Race', body: 'Blocked by #42' };
  const gh2 = makeFakeGh({
    openPages: [[existing, subject2]],
    issues: { 42: existing, 51: subject2 },
    addHandler: async () => ({ status: 404 }),
  });
  const res2 = await reconcileAutoDependencies({ repo: REPO, subjectIssue: subject2, gh: gh2, stateDir });
  assert.equal(res2.holds.length, 1);
  assert.equal(res2.holds[0].dispatchable, false);
});

test('auto-deps: human always wins — never re-adds human-removed edge (unless human restores) and never removes human-added edge', async t => {
  const stateDir = makeTempDir(t, 'pdd-autodeps-human-');
  const b1 = { number: 10, title: 'Blocker 10', body: '' };
  const b2 = { number: 11, title: 'Blocker 11', body: '' };
  const bHuman = { number: 12, title: 'Human blocker', body: '' };
  const subject = { number: 60, title: 'Work item', body: 'Blocked by #10 and #11' };

  // Timeline shows Autopilot added #10 at T1, then human alice removed #10 at T2.
  const gh = makeFakeGh({
    openPages: [[b1, b2, bHuman, subject]],
    issues: { 10: b1, 11: b2, 12: bHuman, 60: subject },
    blockedBy: { 60: [bHuman] }, // human manually added #12
    timelines: {
      60: [
        { event: 'blocked_by_added', blocker: 10, actor: { login: 'pdd-bot' }, created_at: '2026-11-22T09:00:00Z' },
        { event: 'blocked_by_removed', blocker: 10, actor: { login: 'alice' }, created_at: '2026-11-22T09:05:00Z' },
        { event: 'blocked_by_added', blocker: 12, actor: { login: 'alice' }, created_at: '2026-11-22T09:06:00Z' },
      ],
    },
  });

  const r1 = await reconcileAutoDependencies({
    repo: REPO, subjectIssue: subject, gh, stateDir, autopilotLogins: ['pdd-bot'],
    now: () => Date.parse('2026-11-22T10:00:00Z'),
  });
  assert.ok(r1.actions.some(a => a.action === 'skip-human-removed' && a.blocker === 10), 'must never re-add human-removed #10');
  assert.ok(r1.actions.some(a => a.action === 'add' && a.blocker === 11), 'must still add #11');
  assert.ok(r1.actions.some(a => a.action === 'skip-human-owned' && a.blocker === 12), 'must preserve human-added #12');
  assert.equal(gh.calls.removed.length, 0);

  // Now edit #60 scope to remove #11 -> Autopilot removes stale Autopilot-added #11, STILL preserves human #12!
  const edited = { number: 60, title: 'Work item (narrowed)', body: 'No prerequisites anymore.' };
  const r2 = await reconcileAutoDependencies({
    repo: REPO, subjectIssue: edited, gh, stateDir, autopilotLogins: ['pdd-bot'],
    now: () => Date.parse('2026-11-22T11:00:00Z'),
  });
  assert.ok(r2.actions.some(a => a.action === 'remove-stale' && a.blocker === 11), 'stale Autopilot edge #11 must be removed');
  assert.ok(r2.actions.some(a => a.action === 'skip-human-owned' && a.blocker === 12), 'human edge #12 must remain untouched');
  assert.deepEqual(gh.calls.removed, [{ dep: 60, blocker: 11 }]);
  assert.deepEqual(gh.liveBlocked.get(60).map(x => x.number), [12]);

  // Verify human restore clears the humanRemovedBlocksReadd lock.
  const restored = inspectEdgeTimeline([
    { event: 'blocked_by_removed', blocker: 10, actor: { login: 'alice' }, created_at: '2026-11-22T09:05:00Z' },
    { event: 'blocked_by_added', blocker: 10, actor: { login: 'alice' }, created_at: '2026-11-22T09:15:00Z' },
  ], 10, { autopilotLogins: ['pdd-bot'], existsInLive: true });
  assert.equal(restored.humanRemovedBlocksReadd, false);
  assert.equal(restored.humanOwned, true);
});

test('auto-deps: blocker closed as not_planned marks dependent for re-triage (never silently unblocks) with idempotent comment', async t => {
  const stateDir = makeTempDir(t, 'pdd-autodeps-notplanned-');
  const closedBlocker = { number: 70, title: 'Won’t fix API', state: 'closed', state_reason: 'not_planned' };
  const dependent = { number: 71, title: 'Dependent feature', body: 'Blocked by #70' };
  const gh = makeFakeGh({
    openPages: [[dependent]],
    issues: { 70: closedBlocker, 71: dependent },
    blockedBy: { 71: [closedBlocker] },
  });

  const r1 = await reconcileAutoDependencies({ repo: REPO, subjectIssue: dependent, gh, stateDir });
  assert.equal(r1.retriage.length, 1);
  assert.deepEqual(r1.retriage[0], { issue: 71, blocker: 70, dispatchable: false, needsRetriage: true, reason: 'blocker-closed-not-planned' });
  assert.equal(r1.commentsPosted, 1);
  assert.match(gh.calls.commented[0].body, /not_planned/);

  // Re-running with force must not post a duplicate re-triage comment.
  const r2 = await reconcileAutoDependencies({ repo: REPO, subjectIssue: dependent, gh, stateDir, force: true });
  assert.equal(r2.retriage.length, 1);
  assert.equal(r2.commentsPosted, 0);
  assert.equal(gh.calls.commented.length, 1);

  // Closing an already-indexed open blocker as `not_planned` (without changing title/body) must still trigger re-triage!
  const openBlocker = { number: 75, title: 'Prereq 75', body: '', state: 'open' };
  const waitingDep = { number: 76, title: 'Waiting 76', body: 'Blocked by #75', state: 'open' };
  const gh3 = makeFakeGh({ openPages: [[openBlocker, waitingDep]], issues: { 75: openBlocker, 76: waitingDep }, blockedBy: { 76: [openBlocker] } });
  await reconcileAutoDependencies({ repo: REPO, subjectIssue: openBlocker, gh: gh3, stateDir });
  const closed75 = { ...openBlocker, state: 'closed', state_reason: 'not_planned' };
  gh3.liveBlocked.set(76, [closed75]);
  const r3 = await reconcileAutoDependencies({ repo: REPO, subjectIssue: closed75, gh: gh3, stateDir });
  assert.equal(r3.skipped, false);
  assert.equal(r3.retriage.length, 1);
  assert.equal(r3.retriage[0].issue, 76);
  assert.equal(r3.retriage[0].blocker, 75);
});

test('file-claim reservations: atomic TTL claims, conflict independence from GitHub edges, expiry sweep, and symlink guard', async t => {
  const stateDir = makeTempDir(t, 'pdd-file-claims-');
  let clock = Date.parse('2026-11-22T12:00:00Z');
  const now = () => clock;

  const c1 = acquireFileClaim(stateDir, {
    owner: 'worker-a', issue: 101, leaseId: 'lease-101',
    files: ['./src/auth/token.mjs', 'src/router'], ttlMs: 10 * 60 * 1000, now,
  });
  assert.equal(c1.acquired, true);
  assert.deepEqual(c1.claim.files, ['src/auth/token.mjs', 'src/router']);
  assert.equal(statSync(join(stateDir, 'file-claims.json')).mode & 0o777, 0o600);

  // Overlapping exact file OR child under claimed directory must conflict without touching GitHub.
  const c2 = acquireFileClaim(stateDir, {
    owner: 'worker-b', issue: 102, leaseId: 'lease-102',
    files: ['src/router/handler.mjs'], ttlMs: 10 * 60 * 1000, now,
  });
  assert.equal(c2.acquired, false);
  assert.equal(c2.conflict, true);
  assert.equal(c2.conflicts[0].owner, 'worker-a');
  assert.deepEqual(c2.conflicts[0].overlappingFiles, ['src/router/handler.mjs']);

  // Removing a GitHub blocked_by edge NEVER erases a live local file-claim collision!
  const i101 = { number: 101, title: 'Auth', body: 'Blocked by #100' };
  const i100 = { number: 100, title: 'Prereq', body: '' };
  const gh = makeFakeGh({ openPages: [[i100, i101]], issues: { 100: i100, 101: i101 } });
  await reconcileAutoDependencies({ repo: REPO, subjectIssue: i101, gh, stateDir, now });
  await reconcileAutoDependencies({ repo: REPO, subjectIssue: { number: 101, title: 'Auth', body: 'Standalone' }, gh, stateDir, now });
  assert.equal(gh.calls.removed.length, 1, 'GitHub stale edge removed');
  const stillConflicting = activeFileConflicts(stateDir, { files: ['src/auth/token.mjs'], excludeOwner: 'worker-b', excludeIssue: 102, now });
  assert.equal(stillConflicting.hasConflict, true, 'removing GitHub edge must never erase a live file collision');

  // Same lease can refresh TTL cleanly.
  const refreshed = acquireFileClaim(stateDir, {
    owner: 'worker-a', issue: 101, leaseId: 'lease-101',
    files: ['src/auth/token.mjs'], ttlMs: 5 * 60 * 1000, now,
  });
  assert.equal(refreshed.acquired, true);

  // Advance clock past TTL -> conflict clears and sweep prunes expired claim.
  clock += 6 * 60 * 1000;
  assert.equal(activeFileConflicts(stateDir, { files: ['src/auth/token.mjs'], now }).hasConflict, false);
  const swept = sweepExpiredClaims(stateDir, { now });
  assert.equal(swept.sweptCount, 1);
  assert.equal(swept.active.length, 0);

  // Worker B now acquires cleanly and releases cleanly.
  const c3 = acquireFileClaim(stateDir, { owner: 'worker-b', issue: 102, leaseId: 'lease-102', files: ['src/auth/token.mjs'], ttlMs: 10 * 60 * 1000, now });
  assert.equal(c3.acquired, true);
  const rel = releaseFileClaim(stateDir, { leaseId: 'lease-102', now });
  assert.equal(rel.releasedCount, 1);
  assert.equal(rel.remaining.length, 0);

  // Symlink guard rejects symlinked state file and path traversal files are refused.
  const symDir = makeTempDir(t, 'pdd-file-claims-sym-');
  const outside = join(makeTempDir(t, 'pdd-outside-'), 'evil.json');
  writeFileSync(outside, '{"claims":[]}\n');
  symlinkSync(outside, join(symDir, 'file-claims.json'));
  assert.throws(() => activeFileConflicts(symDir, { files: ['src/a.mjs'], now }), /unsafe_state_path|symlink/i);
  assert.throws(() => acquireFileClaim(stateDir, { owner: 'w', issue: 9, leaseId: 'l9', files: ['../escape.mjs'], now }), /invalid_claim|valid files/i);
  assert.equal(issueContentHash({ title: 'a', body: 'b' }).length, 16);
  assert.equal(JSON.parse(readFileSync(join(stateDir, 'file-claims.json'), 'utf8')).claims.length, 0);
});

test('auto-deps Fable regressions: persistent holds, fail-closed 422, no false stale pruning, PR filter, cross-repo key, transient 404, delayed actor, incremental persist, BFS cost', async t => {
  const stateDir = makeTempDir(t, 'pdd-autodeps-fable-');

  // #1: Holds persist across runs (hash NOT saved when holds occurred).
  const s1 = { number: 201, title: 'Needs missing', body: 'Blocked by #999' };
  const ghHold = makeFakeGh({ openPages: [[s1]], issues: { 201: s1, 999: { status: 404 } } });
  const h1 = await reconcileAutoDependencies({ repo: REPO, subjectIssue: s1, gh: ghHold, stateDir });
  const h2 = await reconcileAutoDependencies({ repo: REPO, subjectIssue: s1, gh: ghHold, stateDir });
  assert.equal(h1.holds.length, 1);
  assert.equal(h2.skipped, false, 'held issue must not be skipped on second run');
  assert.equal(h2.holds.length, 1, 'hold must persist across runs');

  // #3: Non-duplicate 422 (e.g., limit/validation rejected, edge absent on re-read) MUST fail closed into hold!
  const b202 = { number: 202, title: 'Target', body: '' };
  const s203 = { number: 203, title: 'Limit hit', body: 'Blocked by #202' };
  const gh422 = makeFakeGh({
    openPages: [[b202, s203]], issues: { 202: b202, 203: s203 },
    addHandler: async () => ({ status: 422, message: 'Dependency limit reached' }),
  });
  const r422 = await reconcileAutoDependencies({ repo: REPO, subjectIssue: s203, gh: gh422, stateDir });
  assert.equal(r422.holds.length, 1);
  assert.equal(r422.holds[0].reason, 'blocker-write-rejected-422');
  assert.equal(r422.actions.some(a => a.action === 'noop-exists'), false);

  // #4, #5, #16, #17, #18: Bound listOpenIssues, filter PRs, never prune when openIssues:[] or error 500, no contradictory remove-stale + skip-human-owned.
  const s210 = { number: 210, title: 'Core', body: '' };
  const other211 = { number: 211, title: 'Consumer', body: 'Depends on #210' };
  const pr212 = { number: 212, title: 'Stacked PR', body: 'Depends on #210', pull_request: { url: 'https://api.github.com/repos/acme/platform/pulls/212' } };
  let boundThisOk = false;
  const gh4 = makeFakeGh({ openPages: [[s210, other211, pr212]], issues: { 210: s210, 211: other211, 212: pr212 } });
  const origList = gh4.listOpenIssues;
  gh4.marker = 'bound-ok';
  gh4.listOpenIssues = async function (p) { if (this?.marker === 'bound-ok') boundThisOk = true; return origList(p); };
  const r4a = await reconcileAutoDependencies({ repo: REPO, subjectIssue: s210, gh: gh4, stateDir });
  assert.equal(boundThisOk, true, 'listOpenIssues must preserve gh `this` binding');
  assert.deepEqual(gh4.calls.added, [{ dep: 211, blocker: 210 }], 'PR #212 must be filtered out');
  // Now call with openIssues: [] (incomplete open index) -> MUST NOT remove valid edge 211->210 as stale!
  const r4b = await reconcileAutoDependencies({ repo: REPO, subjectIssue: { ...s210, body: 'edited' }, openIssues: [], gh: gh4, stateDir });
  assert.equal(gh4.calls.removed.length, 0, 'empty openIssues must never prune edge declared by another issue');
  assert.equal(r4b.actions.some(a => a.action === 'remove-stale'), false);
  // Error status 500 from listOpenIssues records a hold instead of empty list.
  const gh500 = { ...gh4, listOpenIssues: async () => ({ status: 500, message: 'Server Error' }) };
  const r500 = await reconcileAutoDependencies({ repo: REPO, subjectIssue: { ...s210, body: 'edited2' }, gh: gh500, stateDir });
  assert.ok(r500.holds.some(h => h.reason === 'open-issues-unavailable-500'));

  // #6: Transient 404 from listBlockedBy MUST NOT poison humanRemovedEdges permanently.
  const b220 = { number: 220, title: 'Prereq', body: '' };
  const s221 = { number: 221, title: 'Dep', body: 'Blocked by #220' };
  const gh6 = makeFakeGh({ openPages: [[b220, s221]], issues: { 220: b220, 221: s221 } });
  await reconcileAutoDependencies({ repo: REPO, subjectIssue: s221, gh: gh6, stateDir });
  gh6.liveBlocked.set(221, { status: 404 });
  const r6a = await reconcileAutoDependencies({ repo: REPO, subjectIssue: { ...s221, body: 'Blocked by #220 (v2)' }, gh: gh6, stateDir });
  assert.equal(r6a.holds.length, 1);
  // 404 clears (edge missing on live but previously managed): simulate edge cleared by autopilot/empty timeline not poisoned by transient 404
  const stateAfter404 = JSON.parse(readFileSync(join(stateDir, 'auto-deps-state.json'), 'utf8'));
  assert.equal(stateAfter404.humanRemovedEdges['221->220'], undefined, 'transient 404 must never write humanRemovedEdges');

  // #7: Default actor detection (no autopilotLogins) handles 30s delay cleanly without turning own add into human-owned.
  const t0 = Date.parse('2026-11-22T12:00:00Z');
  const tlDelayed = inspectEdgeTimeline(
    [{ id: 9001, event: 'blocked_by_added', blocker: 220, actor: { login: 'owner' }, created_at: new Date(t0 + 30_000).toISOString() }],
    220,
    { repo: REPO, managedEdge: { addedAt: new Date(t0).toISOString(), windowStartMs: t0, windowEndMs: t0 }, existsInLive: true },
  );
  assert.equal(tlDelayed.humanOwned, false, '30s API delay must not misclassify own add as human-owned');

  // #8 & #13: Mid-run 403 persists earlier add incrementally; missing addBlockedBy records hold (no phantom add).
  const b230 = { number: 230, title: 'B1', body: '' }, b231 = { number: 231, title: 'B2', body: '' };
  const s232 = { number: 232, title: 'Two deps', body: 'Blocked by #230 and #231' };
  const gh8 = makeFakeGh({
    openPages: [[b230, b231, s232]], issues: { 230: b230, 231: b231, 232: s232 },
    addHandler: async (_d, blk) => { if (blk.number === 231) throw Object.assign(new Error('Forbidden'), { status: 403 }); return { status: 201 }; },
  });
  await assert.rejects(() => reconcileAutoDependencies({ repo: REPO, subjectIssue: s232, gh: gh8, stateDir }), /Forbidden/);
  const savedAfter403 = JSON.parse(readFileSync(join(stateDir, 'auto-deps-state.json'), 'utf8'));
  assert.ok(savedAfter403.managedEdges['232->230'], 'first add must be persisted before second add throws 403');
  const ghNoWriter = { listOpenIssues: async () => [b230, s232], listBlockedBy: async () => [], getIssue: async n => ({ number: n }) };
  const rNoW = await reconcileAutoDependencies({ repo: REPO, subjectIssue: { number: 233, title: 'No writer', body: 'Blocked by #230' }, gh: ghNoWriter, stateDir });
  assert.ok(rNoW.holds.some(h => h.reason === 'missing-add-blocked-by-writer'));
  assert.equal(rNoW.actions.some(a => a.action === 'add'), false);

  // #11: Newly linked candidate pointing to a `not_planned` blocker flags re-triage immediately.
  const np240 = { number: 240, title: 'Wontfix', state: 'closed', state_reason: 'not_planned' };
  const s241 = { number: 241, title: 'New dep on wontfix', body: 'Blocked by #240' };
  const gh11 = makeFakeGh({ openPages: [[s241]], issues: { 240: np240, 241: s241 } });
  const r11 = await reconcileAutoDependencies({ repo: REPO, subjectIssue: s241, gh: gh11, stateDir });
  assert.equal(r11.retriage.length, 1);
  assert.equal(gh11.calls.added.length, 0);

  // #12 & #14 & #17: Cross-repo blocker does not collide with local #5; scoped BFS avoids unrelated open issues & catches closed-node cycles; remove-stale has no contradictory skip-human-owned.
  const unrelated = Array.from({ length: 30 }, (_, i) => ({ number: 500 + i, title: `Unrelated ${i}`, body: '' }));
  const local5 = { number: 5, title: 'Local 5', body: '' };
  const s250 = { number: 250, title: 'Cross-repo test', body: 'Blocked by #5' };
  let blockedByCalls = 0;
  const gh12 = makeFakeGh({
    openPages: [[local5, s250, ...unrelated]], issues: { 5: local5, 250: s250 },
    blockedBy: { 250: [{ number: 5, html_url: 'https://github.com/other/repo/issues/5' }] },
  });
  const baseListBlocked = gh12.listBlockedBy;
  gh12.listBlockedBy = async n => { blockedByCalls += 1; return baseListBlocked(n); };
  const r12 = await reconcileAutoDependencies({ repo: REPO, subjectIssue: s250, gh: gh12, stateDir });
  assert.ok(blockedByCalls <= 3, `scoped BFS should not scan 30 unrelated issues (got ${blockedByCalls})`);
  assert.ok(r12.actions.some(a => a.action === 'add' && a.dependent === 250 && a.blocker === 5), 'other/repo#5 must not block linking local acme/platform#5');
  // Scope edit removes 250->5 and must NOT emit contradictory skip-human-owned for 250->5!
  const r17 = await reconcileAutoDependencies({ repo: REPO, subjectIssue: { number: 250, title: 'Cross-repo test', body: 'Standalone' }, gh: gh12, stateDir });
  assert.ok(r17.actions.some(a => a.action === 'remove-stale' && a.blocker === 5));
  assert.equal(r17.actions.some(a => a.action === 'skip-human-owned' && a.blocker === 5), false);
});

test('file-claim Fable regressions (#9, #10): cross-process lock serializes concurrent workers, corrupt JSON fails closed, lease hijack rejected', async t => {
  const stateDir = makeTempDir(t, 'pdd-claims-lock-');
  const workerScript = `
    import { acquireFileClaim } from ${JSON.stringify(AUTO_DEPS_URL)};
    const [dir, owner, issue, leaseId] = process.argv.slice(1);
    const res = acquireFileClaim(dir, { owner, issue: Number(issue), leaseId, files: ['src/shared/hot.mjs'], ttlMs: 60000 });
    process.stdout.write(JSON.stringify(res));
  `;
  const [p1, p2] = await Promise.all([
    execFileAsync(process.execPath, ['--input-type=module', '-e', workerScript, stateDir, 'worker-1', '11', 'lease-1']),
    execFileAsync(process.execPath, ['--input-type=module', '-e', workerScript, stateDir, 'worker-2', '12', 'lease-2']),
  ]);
  const res1 = JSON.parse(p1.stdout), res2 = JSON.parse(p2.stdout);
  assert.equal([res1.acquired, res2.acquired].filter(Boolean).length, 1, 'concurrent processes must serialize so exactly one acquires');
  assert.equal([res1.conflict, res2.conflict].filter(Boolean).length, 1);

  // Lease hijack by different owner reusing an active leaseId must be rejected!
  const winner = res1.acquired ? res1.claim : res2.claim;
  const hijack = acquireFileClaim(stateDir, { owner: 'attacker', issue: 99, leaseId: winner.leaseId, files: ['src/other.mjs'], ttlMs: 60000 });
  assert.equal(hijack.acquired, false);
  assert.equal(hijack.error, 'lease-owner-mismatch');

  // Corrupt/truncated file-claims.json must fail closed (NEVER treat as empty)!
  const corruptDir = makeTempDir(t, 'pdd-claims-corrupt-');
  writeFileSync(join(corruptDir, 'file-claims.json'), '{"version":1,"claims":[{"owner":"w1"');
  const acqCorrupt = acquireFileClaim(corruptDir, { owner: 'w2', issue: 2, leaseId: 'l2', files: ['src/a.mjs'] });
  assert.equal(acqCorrupt.acquired, false);
  assert.equal(acqCorrupt.error, 'corrupt-claims-store');
  const chkCorrupt = activeFileConflicts(corruptDir, { files: ['src/a.mjs'] });
  assert.equal(chkCorrupt.hasConflict, true);
  assert.equal(chkCorrupt.error, 'corrupt-claims-store');
  assert.throws(() => sweepExpiredClaims(corruptDir), /corrupt_claims_store|corrupt/i);
  assert.throws(() => releaseFileClaim(corruptDir, { leaseId: 'l2' }), /corrupt_claims_store|corrupt/i);
});
