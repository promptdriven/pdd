import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { completeDependencyIntake, prepareDependencyIntake, reconcileDependencyIntake } from '../src/issue-dependencies-intake.mjs';

// Synthetic GitHub world. Issue revisions follow the adapter's public rule:
// SHA-256 of the issue's title and body.
const repository = 'example/project', runtime = 'example/runtime';
const sha = value => createHash('sha256').update(value).digest('hex');
const reply = value => ({ json: JSON.stringify(value) });
const key = (number, repo = repository) => `https://github.com/${repo}/issues/${number}`;
const issue = (number, overrides = {}) => ({ id: 1000 + number, number, html_url: key(number), title: `Issue ${number}`,
  body: `Please fix synthetic case ${number}.`, state: 'open', user: { login: 'owner' }, labels: [], assignees: [], ...overrides });
const row = item => ({ key: item.html_url, revision: sha(JSON.stringify({ title: item.title, body: item.body })) });
const recordBody = review => `Dependencies checked.\n\n<!-- pdd-dependency-review:v1 -->\n\`\`\`json\n${JSON.stringify({ schema_version: 'pdd.dependency-review.v1', review })}\n\`\`\``;
const comment = (id, body, login = 'owner') => ({ id, body, created_at: '2026-11-06T10:00:00Z', updated_at: '2026-11-06T10:00:00Z', user: { login } });
function savedReview(id, subject, candidates, dependencies = []) {
  return comment(id, recordBody({ analysis: 'Checked what this issue needs first.', base: [], continuation: '', issue: subject.html_url,
    inputs: [row(subject)], candidates: candidates.map(row), outcome: 'complete', dependencies, questions: [], effects: dependencies.length ? 'confirmed' : 'none' }));
}

function world({ issues, comments = {}, blockedBy = {} }) {
  let nextId = 900;
  const find = (repo, number) => issues.find(item => item.html_url === key(number, repo));
  const github = {
    issue: async ({ repository: repo, issue: number }) => reply(find(repo, number) ?? { error: 'GitHub issue unavailable', status: 404 }),
    page: async ({ repository: repo, kind, issue: number }) => {
      if (kind === 'issues') return reply({ items: issues.filter(item => item.html_url.startsWith(`https://github.com/${repo}/`) && item.state === 'open'), next: '' });
      const subject = key(number, repo);
      const items = kind === 'comments' ? comments[subject] ?? []
        : kind === 'blockedBy' ? (blockedBy[subject] ?? []).map(html_url => ({ html_url }))
        : kind === 'blocking' ? Object.entries(blockedBy).filter(([, blockers]) => blockers.includes(subject)).map(([html_url]) => ({ html_url }))
        : [];
      return reply({ items, next: '' });
    },
    appendComment: async ({ repository: repo, issue: number, body }) => {
      const saved = comment(String(nextId++), body);
      (comments[key(number, repo)] ??= []).push(saved);
      return reply(saved);
    },
    addBlocker: async ({ repository: repo, issue: number, blockerId }) => {
      const blocker = issues.find(item => String(item.id) === blockerId);
      (blockedBy[key(number, repo)] ??= []).push(blocker.html_url);
      return { ok: true };
    },
  };
  const ports = (extra = {}) => ({
    github,
    authority: { read: async () => ({ authority: 'trusted' }) },
    context: { read: async () => reply({ inputs: [], conditions: [], execution: [], nativeExecution: true }) },
    owners: { read: async () => reply({ localOwner: 'coordinator', claims: [], runs: [], runsKnown: true }) },
    evidence: { read: async () => reply({ source: [], requirements: [] }) },
    clock: { now: async () => ({ iso: '2026-11-06T12:00:00.000Z' }) },
    ...extra,
  });
  return { issues, comments, blockedBy, ports };
}

async function graph(w, ports = w.ports(), cwd = '') {
  const { snapshot } = await readDependencySnapshot({ cwd, repository }, ports);
  const projected = projectIssueGraph({ snapshot });
  return { snapshot, node: (number, repo) => projected.nodes.find(node => node.key === key(number, repo)) };
}

test('a new or edited unrelated issue leaves an existing current review current', async () => {
  const i17 = issue(17), i18 = issue(18);
  const w = world({ issues: [i17, i18], comments: { [key(17)]: [savedReview('501', i17, [i17, i18])] } });
  let g = await graph(w);
  assert.equal(g.node(17).reviewState, 'current');
  assert.equal(g.node(17).eligible, true);

  w.issues.push(issue(103));
  g = await graph(w);
  assert.equal(g.node(17).reviewState, 'current');
  assert.equal(g.node(17).eligible, true);
  assert.equal(g.node(17).reasons.includes('Stale review'), false);
  assert.equal(g.node(103).reviewState, 'unchecked');

  i18.body = 'An unrelated edit that issue 17 did not use or name.';
  g = await graph(w);
  assert.equal(g.node(17).reviewState, 'current');
  assert.equal(g.node(17).eligible, true);
});

test('an edit to an issue that a review used or names makes that review stale', async () => {
  const i17 = issue(17), i18 = issue(18, { state: 'closed', state_reason: 'completed' }), i20 = issue(20);
  const needs18 = [{ key: key(18), reason: 'Issue 20 extends the parser from issue 18.', evidence: [key(18)] }];
  const w = world({ issues: [i17, i18, i20], blockedBy: { [key(20)]: [key(18)] }, comments: {
    [key(17)]: [savedReview('501', i17, [i17, i20])], [key(20)]: [savedReview('502', i20, [i17, i18, i20], needs18)] } });
  let g = await graph(w);
  assert.equal(g.node(17).reviewState, 'current');
  assert.equal(g.node(20).reviewState, 'current');
  assert.equal(g.node(20).eligible, true, 'the named prerequisite is completed');

  i17.body = 'Issue 17 now asks for a different change.';
  g = await graph(w);
  assert.equal(g.node(17).reviewState, 'stale');
  assert.ok(g.node(17).reasons.includes('Stale review'));
  assert.equal(g.node(17).eligible, false);
  assert.equal(g.node(20).reviewState, 'current', 'issue 20 did not use or name issue 17');

  i18.body = 'Issue 18 was rewritten after the review.';
  g = await graph(w);
  assert.equal(g.node(20).reviewState, 'stale');
  assert.equal(g.node(20).eligible, false);
});

test('a linked issue in another repository without a checkout uses GitHub data and the snapshot completes', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-cross-repo-')); t.after(() => rmSync(dir, { recursive: true, force: true }));
  mkdirSync(join(dir, '.git'));
  // The local checkout trusts "helper" as an extra name. That name must not apply to the other repository.
  writeFileSync(join(dir, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: ['helper'] } }));
  const http = value => ({ stdout: `HTTP/2.0 200 OK\r\ncontent-type: application/json\r\n\r\n${JSON.stringify(value)}`, stderr: '', code: 0 });
  const github = { [`repos/${repository}`]: { owner: { login: 'owner' } }, [`repos/${repository}/collaborators?per_page=100`]: [{ login: 'owner', permissions: { admin: true } }],
    [`repos/${runtime}`]: { owner: { login: 'example' } }, [`repos/${runtime}/collaborators?per_page=100`]: [{ login: 'runtime-dev', permissions: { push: true } }, { login: 'reader', permissions: { pull: true } }] };
  const execFile = async (file, args) => {
    if (file === 'git' && args.join(' ') === 'remote get-url origin') return { stdout: `https://github.com/${repository}.git\n`, stderr: '', code: 0 };
    if (file === 'git' && args.join(' ') === 'rev-parse --show-toplevel') return { stdout: `${dir}\n`, stderr: '', code: 0 };
    if (file === 'git' && args.join(' ') === 'rev-parse --path-format=absolute --git-common-dir') return { stdout: `${join(dir, '.git')}\n`, stderr: '', code: 0 };
    if (file === 'gh' && args[0] === 'repo' && args[1] === 'view') return { stdout: JSON.stringify({ nameWithOwner: repository, defaultBranchRef: { name: 'main' }, url: `https://github.com/${repository}` }), stderr: '', code: 0 };
    if (file === 'gh' && args[0] === 'api' && Object.hasOwn(github, args[4])) return http(github[args[4]]);
    throw Error(`unexpected command: ${file} ${args.join(' ')}`);
  };
  const i10 = issue(10), i11 = issue(11, { user: { login: 'helper' } });
  const r5 = { ...issue(5, { user: { login: 'runtime-dev' } }), id: 5005, html_url: key(5, runtime) };
  const r6 = { ...issue(6, { user: { login: 'helper' } }), id: 5006, html_url: key(6, runtime) };
  // A person set "blocked by" in GitHub; no saved review names these links.
  const w = world({ issues: [i10, i11, r5, r6], blockedBy: { [key(10)]: [key(5, runtime)], [key(11)]: [key(6, runtime)] },
    comments: { [key(10)]: [savedReview('501', i10, [i10, i11])], [key(11)]: [savedReview('502', i11, [i10, i11])] } });
  const ports = () => { const { authority, ...rest } = w.ports(); return { ...rest, execFile }; };

  let g = await graph(w, ports(), dir);
  assert.equal(g.snapshot.complete, true, JSON.stringify(g.snapshot.warnings));
  assert.deepEqual(g.snapshot.warnings, []);
  const authority = k => g.snapshot.issues.find(item => item.key === k).authority;
  assert.equal(authority(key(5, runtime)), 'trusted', 'a write collaborator of the other repository');
  assert.equal(authority(key(6, runtime)), 'untrusted', 'local extra trust does not apply to another repository');
  assert.equal(authority(key(11)), 'trusted', 'local extra trust still applies to the checkout repository');
  assert.equal(g.node(10).dependencyState, 'waiting');
  assert.ok(g.node(10).reasons.includes('Open prerequisite'));
  assert.ok(g.node(10).reasons.includes('GitHub dependency; no saved reason'));
  assert.equal(g.node(10).reasons.includes('Incomplete relevant observations'), false);
  assert.equal(g.node(10).eligible, false);

  Object.assign(r5, { state: 'closed', state_reason: 'completed' });
  Object.assign(r6, { state: 'closed', state_reason: 'completed' });
  g = await graph(w, ports(), dir);
  assert.equal(g.snapshot.complete, true);
  assert.equal(g.node(10).dependencyState, 'clear');
  assert.equal(g.node(10).eligible, true);
  assert.equal(g.node(11).eligible, true, 'for a prerequisite only its open or closed state matters');
});

test('a new issue with no prerequisites becomes eligible after its single review', async () => {
  const i17 = issue(17), i103 = issue(103);
  const w = world({ issues: [i17, i103], comments: { [key(17)]: [savedReview('501', i17, [i17])] } });
  let g = await graph(w);
  assert.equal(g.node(17).eligible, true);
  assert.equal(g.node(103).reviewState, 'unchecked');
  assert.equal(g.node(103).eligible, false);

  const delivered = [];
  const pending = { state: {}, read: async () => reply(pending.state), save: async ({ json }) => { pending.state = JSON.parse(json); return { ok: true }; },
    deliver: async ({ requestJson }) => { delivered.push(JSON.parse(requestJson)); return { state: 'delivered' }; } };
  const tick = await reconcileDependencyIntake({ repository, trigger: 'tick', mode: 'auto' }, w.ports({ pending }));
  assert.equal(delivered.length, 1);
  assert.deepEqual(delivered[0].issues, [key(103)], 'only the new issue is reviewed');
  assert.ok(tick.eligible.includes(key(17)));

  const request = delivered[0], prepared = JSON.parse(request.snapshotJson);
  const candidates = prepared.issues.filter(item => item.key.startsWith(`https://github.com/${repository}/`)).map(({ key, revision }) => ({ key, revision }));
  const result = await completeDependencyIntake({ request, analysis: { impactJson: '', reviews: [{ analysis: 'Issue 103 needs no open issue first.',
    base: [], continuation: '', issue: key(103), inputs: [row(i103)], candidates, outcome: 'complete', dependencies: [], questions: [], effects: 'none' }] } }, w.ports());
  assert.equal(result.state, 'complete');
  assert.equal(result.reviewIds.length, 1);

  g = await graph(w);
  assert.equal(g.node(103).reviewState, 'current');
  assert.equal(g.node(103).eligible, true);
  assert.equal(g.node(17).reviewState, 'current');
  const next = await reconcileDependencyIntake({ repository, trigger: 'tick', mode: 'auto' }, w.ports({ pending }));
  assert.equal(delivered.length, 1, 'nothing is left to review');
  assert.ok(next.eligible.includes(key(103)));
});

test('a new issue that needs an open issue first records a GitHub blocked-by link', async () => {
  const i17 = issue(17), i104 = issue(104);
  const w = world({ issues: [i17, i104], comments: { [key(17)]: [savedReview('501', i17, [i17])] } });
  const { request } = await prepareDependencyIntake({ repository }, w.ports());
  assert.deepEqual(request.issues, [key(104)]);
  const candidates = JSON.parse(request.snapshotJson).issues.map(({ key, revision }) => ({ key, revision }));
  const result = await completeDependencyIntake({ request, analysis: { impactJson: '', reviews: [{ analysis: 'Issue 104 changes code that issue 17 adds.',
    base: [], continuation: '', issue: key(104), inputs: [row(i104)], candidates, outcome: 'pending',
    dependencies: [{ key: key(17), reason: 'Issue 104 changes the code that issue 17 adds.', evidence: [key(17)] }], questions: [], effects: 'pending' }] } }, w.ports());
  assert.equal(result.state, 'complete');
  assert.deepEqual(w.blockedBy[key(104)], [key(17)]);
  const g = await graph(w);
  assert.equal(g.node(104).reviewState, 'current');
  assert.equal(g.node(104).dependencyState, 'waiting');
  assert.equal(g.node(104).eligible, false);
});

test('new and unchecked issues are reviewed first in small batches', async () => {
  const stale = [issue(5), issue(6)], current = issue(7), fresh = Array.from({ length: 12 }, (_, i) => issue(101 + i));
  const comments = Object.fromEntries([...stale, current].map((item, i) => [item.html_url, [savedReview(String(501 + i), item, [item])]]));
  for (const item of stale) item.body = `Changed requirement for ${item.number}.`;
  const w = world({ issues: [...stale, current, ...fresh], comments });

  const first = await prepareDependencyIntake({ repository }, w.ports());
  assert.equal(first.queued.length, 10);
  assert.deepEqual(first.queued, fresh.slice(2).reverse().map(item => item.html_url), 'newest unchecked issues first');
  assert.deepEqual(first.request.issues, first.queued);

  w.issues.splice(w.issues.indexOf(fresh[0]), 1);
  w.issues.splice(w.issues.indexOf(fresh[1]), 1);
  for (const item of fresh.slice(2)) w.comments[item.html_url] = [savedReview(`7${item.number}`, item, [item])];
  const second = await prepareDependencyIntake({ repository }, w.ports());
  assert.deepEqual(second.queued, [key(6), key(5)], 'changed reviews follow when no unchecked issue waits');

  const named = await prepareDependencyIntake({ repository, issue: '5' }, w.ports());
  assert.deepEqual(named.queued, [key(5)]);
});
