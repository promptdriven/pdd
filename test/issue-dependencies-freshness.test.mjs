import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { applyDependencyChanges, readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
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
  return { snapshot, node: (number, repo) => projected.nodes.find(node => node.key === key(number, repo)),
    authority: (number, repo) => snapshot.issues.find(item => item.key === key(number, repo))?.authority };
}

// The coordinator's answer for one subject of a prepared request.
function answer(request, subject, { base = [], outcome = 'complete', dependencies = [], questions = [] } = {}) {
  const prepared = JSON.parse(request.snapshotJson);
  const candidates = prepared.issues.filter(item => item.key.startsWith(`https://github.com/${repository}/`)).map(({ key, revision }) => ({ key, revision }));
  return { analysis: `Checked what issue ${subject.number} needs first.`, base, continuation: '', issue: subject.html_url, inputs: [row(subject)],
    candidates, outcome, dependencies, questions, effects: dependencies.length ? 'pending' : 'none' };
}

// Issue 17 has a confirmed review that named 18, and the link "17 blocked by 18" exists.
function namedLinkWorld() {
  const i17 = issue(17), i18 = issue(18), i19 = issue(19);
  const needs18 = [{ key: key(18), reason: 'Issue 17 extends the parser from issue 18.', evidence: [key(18)] }];
  const w = world({ issues: [i17, i18, i19], blockedBy: { [key(17)]: [key(18)] }, comments: {
    [key(17)]: [savedReview('501', i17, [i17, i18, i19], needs18)], [key(18)]: [savedReview('502', i18, [i17, i18, i19])],
    [key(19)]: [savedReview('503', i19, [i17, i18, i19])] } });
  return { w, i17 };
}

// Native trust reads for a checkout of example/project with linked issues in
// example/runtime. A fault breaks one read the way git or GitHub can fail.
function trustWorld(t, fault = '') {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-trust-')); t.after(() => rmSync(dir, { recursive: true, force: true }));
  mkdirSync(join(dir, '.git'));
  writeFileSync(join(dir, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  const http = (value, status = 200) => ({ stdout: `HTTP/2.0 ${status} X\r\ncontent-type: application/json\r\n\r\n${JSON.stringify(value)}`, stderr: '', code: 0 });
  const replies = { [`repos/${repository}`]: http({ owner: { login: 'owner' } }), [`repos/${repository}/collaborators?per_page=100`]: http([{ login: 'owner', permissions: { admin: true } }]),
    [`repos/${runtime}`]: fault === 'repo' ? http({ message: 'Server Error' }, 500) : http({ owner: { login: 'example' } }),
    [`repos/${runtime}/collaborators?per_page=100`]: fault === 'collaborators' ? http({ message: 'Must have push access to view repository collaborators.' }, 403)
      : http([{ login: 'runtime-dev', permissions: { push: true } }, { login: 'reader', permissions: { pull: true } }]) };
  const execFile = async (file, args) => {
    const command = args.join(' ');
    if (file === 'git' && command === 'remote get-url origin') return fault === 'checkout' ? { stdout: '', stderr: 'fatal: no such remote', code: 2 } : { stdout: `https://github.com/${repository}.git\n`, stderr: '', code: 0 };
    if (file === 'git' && command === 'rev-parse --show-toplevel') return { stdout: `${dir}\n`, stderr: '', code: 0 };
    if (file === 'git' && command === 'rev-parse --path-format=absolute --git-common-dir') return { stdout: `${join(dir, '.git')}\n`, stderr: '', code: 0 };
    if (file === 'gh' && args[0] === 'repo' && args[1] === 'view') return { stdout: JSON.stringify({ nameWithOwner: repository, defaultBranchRef: { name: 'main' }, url: `https://github.com/${repository}` }), stderr: '', code: 0 };
    if (file === 'gh' && args[0] === 'api' && Object.hasOwn(replies, args[4])) return replies[args[4]];
    throw Error(`unexpected command: ${file} ${command}`);
  };
  // 10 needs runtime#5 (by a write collaborator), 11 needs runtime#6 (by a reader); 12 is unrelated.
  const i10 = issue(10), i11 = issue(11), i12 = issue(12);
  const r5 = { ...issue(5, { user: { login: 'runtime-dev' }, state: 'closed', state_reason: 'completed' }), id: 5005, html_url: key(5, runtime) };
  const r6 = { ...issue(6, { user: { login: 'reader' }, state: 'closed', state_reason: 'completed' }), id: 5006, html_url: key(6, runtime) };
  const w = world({ issues: [i10, i11, i12, r5, r6], blockedBy: { [key(10)]: [key(5, runtime)], [key(11)]: [key(6, runtime)] },
    comments: Object.fromEntries([i10, i11, i12].map((item, i) => [item.html_url, [savedReview(String(601 + i), item, [i10, i11, i12])]])) });
  const ports = () => { const { authority, ...rest } = w.ports(); return { ...rest, execFile }; };
  return { w, ports, dir };
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

test('a person removes a link that the review named: the review is stale, queued again, and the new review makes the issue eligible', async () => {
  const { w, i17 } = namedLinkWorld();
  let g = await graph(w);
  assert.equal(g.node(17).reviewState, 'current');
  assert.equal(g.node(17).dependencyState, 'waiting');

  w.blockedBy[key(17)] = []; // A person removes "17 blocked by 18" in GitHub.
  g = await graph(w);
  assert.equal(g.node(17).reviewState, 'stale');
  assert.ok(g.node(17).reasons.includes('Stale review'));
  assert.ok(g.node(17).reasons.includes('Human dependency change'));
  assert.equal(g.node(17).dependencyState, 'clear');
  assert.equal(g.node(17).eligible, false);

  const { request, queued } = await prepareDependencyIntake({ repository }, w.ports());
  assert.deepEqual(queued, [key(17)]);
  const result = await completeDependencyIntake({ request, analysis: { impactJson: '', reviews: [answer(request, i17, { base: ['501'] })] } }, w.ports());
  assert.equal(result.state, 'complete');
  g = await graph(w);
  assert.equal(g.node(17).reviewState, 'current');
  assert.equal(g.node(17).dependencyState, 'clear');
  assert.equal(g.node(17).eligible, true, 'no other prerequisite remains');
  assert.deepEqual(w.blockedBy[key(17)], [], "the person's removal stands");
  assert.deepEqual((await prepareDependencyIntake({ repository }, w.ports())).queued, [], 'nothing is left to review');
});

test('a new review cannot add back a link that a person removed; it records a question instead', async () => {
  const { w, i17 } = namedLinkWorld();
  w.blockedBy[key(17)] = []; // A person removes "17 blocked by 18" in GitHub.
  const { request } = await prepareDependencyIntake({ repository }, w.ports());
  assert.deepEqual(request.issues, [key(17)]);
  const saved = w.comments[key(17)].length;
  const needs18 = [{ key: key(18), reason: 'Issue 17 still extends issue 18.', evidence: [key(18)] }];
  await assert.rejects(completeDependencyIntake({ request, analysis: { impactJson: '',
    reviews: [answer(request, i17, { base: ['501'], outcome: 'pending', dependencies: needs18 })] } }, w.ports()), { code: 'invalid-analysis' });
  assert.equal(w.comments[key(17)].length, saved, 'nothing is saved');
  assert.deepEqual(w.blockedBy[key(17)], []);

  const question = 'A person removed the link to issue 18. Does issue 17 still need issue 18 first?';
  const result = await completeDependencyIntake({ request, analysis: { impactJson: '',
    reviews: [answer(request, i17, { base: ['501'], outcome: 'question', questions: [question] })] } }, w.ports());
  assert.equal(result.state, 'question');
  let g = await graph(w);
  assert.equal(g.node(17).reviewState, 'question');
  assert.equal(g.node(17).eligible, false);
  assert.deepEqual(g.node(17).facts.map(fact => fact.text), [question]);
  assert.deepEqual(w.blockedBy[key(17)], []);

  // A pending intent from another coordinator cannot add the link back either.
  w.comments[key(17)].push(comment('950', recordBody({ analysis: 'Issue 17 needs issue 18 first.', base: [result.reviewIds[0]], continuation: '', issue: key(17),
    inputs: [row(i17)], candidates: [row(i17)], outcome: 'pending', dependencies: needs18, questions: [], effects: 'pending' })));
  g = await graph(w);
  assert.equal(g.node(17).reviewState, 'pending');
  const applied = await applyDependencyChanges({ repository, issue: key(17), reviewId: '950' }, w.ports());
  assert.equal(applied.state, 'pending');
  assert.ok(applied.warnings.includes('Human dependency change'));
  assert.deepEqual(w.blockedBy[key(17)], []);
});

test('a person adds a link: the dependent waits at once and the reviews at both ends are queued again', async () => {
  const i18 = issue(18), i19 = issue(19);
  const w = world({ issues: [i18, i19] });
  let { request } = await prepareDependencyIntake({ repository }, w.ports());
  assert.deepEqual(request.issues, [key(19), key(18)]);
  let result = await completeDependencyIntake({ request, analysis: { impactJson: '', reviews: [answer(request, i19), answer(request, i18)] } }, w.ports());
  assert.equal(result.state, 'complete');
  let g = await graph(w);
  assert.equal(g.node(19).eligible, true);
  assert.equal(g.node(18).eligible, true);
  const heads = { 18: g.node(18).review, 19: g.node(19).review };

  const named = (await prepareDependencyIntake({ repository, issue: '19' }, w.ports())).request;
  w.blockedBy[key(19)] = [key(18)]; // A person sets "19 blocked by 18" in GitHub.
  g = await graph(w);
  assert.equal(g.node(19).dependencyState, 'waiting');
  assert.ok(g.node(19).reasons.includes('Open prerequisite'));
  assert.ok(g.node(19).reasons.includes('GitHub dependency; no saved reason'));
  assert.equal(g.node(19).eligible, false);
  assert.equal(g.node(19).reviewState, 'stale');
  assert.equal(g.node(18).reviewState, 'stale', 'a link from its issue changed too');

  const comments = w.comments[key(19)].length;
  result = await completeDependencyIntake({ request: named, analysis: { impactJson: '', reviews: [answer(named, i19, { base: [heads[19]] })] } }, w.ports());
  assert.equal(result.state, 'pending', 'an answer prepared before the link change is not saved');
  assert.equal(w.comments[key(19)].length, comments);

  ({ request } = await prepareDependencyIntake({ repository }, w.ports()));
  assert.deepEqual(request.issues, [key(19), key(18)]);
  result = await completeDependencyIntake({ request, analysis: { impactJson: '',
    reviews: [answer(request, i19, { base: [heads[19]] }), answer(request, i18, { base: [heads[18]] })] } }, w.ports());
  assert.equal(result.state, 'complete');
  g = await graph(w);
  assert.equal(g.node(19).reviewState, 'current');
  assert.equal(g.node(19).dependencyState, 'waiting', "the person's link still applies");
  assert.equal(g.node(18).reviewState, 'current');
  assert.equal(g.node(18).eligible, true);
  assert.deepEqual((await prepareDependencyIntake({ repository }, w.ports())).queued, [], 'nothing is left to review');
});

test('a failed owner or collaborator lookup for another repository leaves its issue unverified; only its dependents wait', async t => {
  const healthy = trustWorld(t);
  let g = await graph(healthy.w, healthy.ports(), healthy.dir);
  assert.equal(g.authority(5, runtime), 'trusted');
  assert.equal(g.node(10).eligible, true, 'control: the closed prerequisite of a trusted author is satisfied');

  for (const fault of ['collaborators', 'repo']) {
    const { w, ports, dir } = trustWorld(t, fault);
    g = await graph(w, ports(), dir);
    assert.equal(g.authority(5, runtime), 'unknown', fault);
    assert.equal(g.authority(6, runtime), 'unknown', fault);
    assert.equal(g.snapshot.complete, false, fault);
    assert.ok(g.snapshot.warnings.includes(`Issue authority unavailable: ${key(5, runtime)}`), fault);
    for (const dependent of [10, 11]) {
      assert.equal(g.node(dependent).eligible, false, `${fault}: ${dependent}`);
      assert.ok(g.node(dependent).reasons.includes('Incomplete relevant observations'), `${fault}: ${dependent}`);
    }
    assert.equal(g.authority(12), 'trusted', fault);
    assert.equal(g.node(12).reviewState, 'current', fault);
    assert.equal(g.node(12).eligible, true, `${fault}: an unrelated issue is not affected`);
  }
});

test('a checkout that cannot be found trusts no author in any repository', async t => {
  const { w, ports, dir } = trustWorld(t, 'checkout');
  const g = await graph(w, ports(), dir);
  assert.equal(g.snapshot.complete, false);
  assert.equal(g.authority(5, runtime), 'unknown');
  assert.equal(g.authority(10), 'unknown');
  assert.equal(g.node(10).eligible, false);
  assert.ok(g.node(10).reasons.includes('Incomplete relevant observations'));
  assert.equal(g.authority(12), 'unknown', 'the default policy is not applied to an unresolved checkout');
  assert.equal(g.node(12).reviewState, 'unverified');
  assert.equal(g.node(12).eligible, false);
});

test('with no checkout the default policy applies: write collaborators are trusted, others are not, and a failed lookup is unverified', async t => {
  const healthy = trustWorld(t);
  let g = await graph(healthy.w, healthy.ports(), '');
  assert.equal(g.snapshot.complete, true, JSON.stringify(g.snapshot.warnings));
  assert.equal(g.authority(5, runtime), 'trusted', 'a write collaborator of the other repository');
  assert.equal(g.authority(6, runtime), 'untrusted', 'a reader of the other repository');
  assert.equal(g.authority(12), 'trusted', 'the owner of the root repository');
  assert.equal(g.node(10).eligible, true);

  const { w, ports } = trustWorld(t, 'collaborators');
  g = await graph(w, ports(), '');
  assert.equal(g.authority(5, runtime), 'unknown');
  assert.equal(g.node(10).eligible, false);
  assert.ok(g.node(10).reasons.includes('Incomplete relevant observations'));
  assert.equal(g.node(12).eligible, true, 'an unrelated issue is not affected');
});
