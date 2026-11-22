import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, rmSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
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
      if (!list.some(x => x.number === blocker.number)) list.push(blocker);
      liveBlocked.set(dep, list);
      return { status: 201 };
    },
    removeBlockedBy: async (dep, blocker) => {
      calls.removed.push({ dep, blocker: blocker.number });
      liveBlocked.set(dep, (liveBlocked.get(dep) ?? []).filter(x => x.number !== blocker.number));
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

  // Same content hash short-circuits with zero GitHub writes.
  const r2 = await reconcileAutoDependencies({ repo: REPO, subjectIssue: subject, gh, stateDir });
  assert.equal(r2.skipped, true);
  assert.equal(r2.reason, 'unchanged-content-hash');
  assert.equal(gh.calls.added.length, 3);
  assert.equal(gh.calls.commented.length, 3);

  // Forced replay is fully idempotent: 0 new adds, 0 duplicate comments.
  const r3 = await reconcileAutoDependencies({
    repo: REPO, subjectIssue: subject,
    contractDependencies: [{ dependent: 3, blocker: 5, contract: 'REST response v2 schema', confirmed: true }],
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
