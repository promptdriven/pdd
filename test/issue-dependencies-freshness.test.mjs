import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { applyDependencyChanges, readDependencySnapshot, saveDependencyReview } from '../src/issue-dependencies-github.mjs';
import { completeDependencyIntake, prepareDependencyIntake, reconcileDependencyIntake } from '../src/issue-dependencies-intake.mjs';
import { autopilotLaunchFingerprint, tickAutopilot } from '../src/autopilot-launcher.mjs';

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

// `timeline` holds native events, for example a GitHub "blocked_by_removed" event
// that names its blocker. `outsiders` are authors that the trust owner does not trust.
// `files` holds the current revision of each readable file locator.
function world({ issues, comments = {}, blockedBy = {}, timeline = {}, outsiders = [], files = {} }) {
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
        : kind === 'timeline' ? timeline[subject] ?? []
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
    authority: { read: async ({ author }) => ({ authority: outsiders.includes(author) ? 'outsider' : 'trusted' }) },
    // A requirement comment row is read again from the comment itself, as the native port does.
    context: { read: async ({ inputs = [] } = {}) => reply({ inputs: inputs.flatMap(({ key: k }) => {
      if (Object.hasOwn(files, k)) return [{ key: k, revision: files[k] }];
      const found = Object.values(comments).flat().find(c => k.endsWith(`#issuecomment-${c.id}`));
      return found ? [{ key: k, revision: sha(found.body) }] : [];
    }), conditions: [], execution: [], nativeExecution: true }) },
    owners: { read: async () => reply({ localOwner: 'coordinator', claims: [], runs: [], runsKnown: true }) },
    evidence: { read: async () => reply({ source: [], requirements: [] }) },
    clock: { now: async () => ({ iso: '2026-11-06T12:00:00.000Z' }) },
    ...extra,
  });
  return { issues, comments, blockedBy, timeline, files, ports };
}

// A native GitHub timeline event about one link. A "blocked_by" event names the
// blocker; a "blocking" event names the dependent.
const linkEvent = (event, number, repo = repository) => ({ event, [event.startsWith('blocking') ? 'blocking' : 'blocked_by']: { number, repository: { full_name: repo } } });
// One reconcile delivery port that records each delivered request.
function deliveries() {
  const delivered = [];
  const pending = { state: {}, read: async () => reply(pending.state), save: async ({ json }) => { pending.state = JSON.parse(json); return { ok: true }; },
    deliver: async ({ requestJson }) => { delivered.push(JSON.parse(requestJson)); return { state: 'delivered' }; } };
  return { delivered, pending };
}
// One review round: prepare, answer each subject (with its current head as base) and complete.
async function round(w, all, answers = {}, extra = {}) {
  const { request } = await prepareDependencyIntake({ repository, ...extra }, w.ports());
  const g = projectIssueGraph({ snapshot: JSON.parse(request.snapshotJson) });
  const reviews = request.issues.map(k => {
    const head = g.nodes.find(n => n.key === k).review;
    return answer(request, all.find(item => item.html_url === k), { base: head ? [head] : [], ...(answers[k] ?? {}) });
  });
  return { request, result: await completeDependencyIntake({ request, analysis: { impactJson: '', reviews } }, w.ports()) };
}
const needs = (number, why, repo = repository) => ({ outcome: 'pending', dependencies: [{ key: key(number, repo), reason: why, evidence: [key(number, repo)] }] });

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
  // The refused write ends as one visible question, not as a pending intent.
  w.comments[key(17)].push(comment('950', recordBody({ analysis: 'Issue 17 needs issue 18 first.', base: [result.reviewIds[0]], continuation: '', issue: key(17),
    inputs: [row(i17)], candidates: [row(i17)], outcome: 'pending', dependencies: needs18, questions: [], effects: 'pending' })));
  g = await graph(w);
  assert.equal(g.node(17).reviewState, 'pending');
  const applied = await applyDependencyChanges({ repository, issue: key(17), reviewId: '950' }, w.ports());
  assert.equal(applied.state, 'question');
  assert.ok(applied.warnings.includes('Human dependency change'));
  assert.equal(applied.questions.length, 1);
  assert.deepEqual(w.blockedBy[key(17)], []);
  g = await graph(w);
  assert.equal(g.node(17).reviewState, 'question');
  assert.deepEqual(g.node(17).facts.map(fact => fact.text), applied.questions);
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

test('a person adds and then removes a link: a later review that names another issue writes that link', async () => {
  const i17 = issue(17), i18 = issue(18), i19 = issue(19), all = [i17, i18, i19];
  const w = world({ issues: all });
  assert.equal((await round(w, all)).result.state, 'complete');

  // A person adds "17 blocked by 18" in GitHub, and later removes it.
  w.blockedBy[key(17)] = [key(18)];
  w.timeline[key(17)] = [linkEvent('blocked_by_added', 18)];
  w.timeline[key(18)] = [linkEvent('blocking_added', 17)];
  let g = await graph(w);
  assert.equal(g.node(17).reviewState, 'stale');
  assert.equal((await round(w, all)).result.state, 'complete');
  w.blockedBy[key(17)] = [];
  w.timeline[key(17)].push(linkEvent('blocked_by_removed', 18));
  w.timeline[key(18)].push(linkEvent('blocking_removed', 17));
  g = await graph(w);
  assert.equal(g.node(17).reviewState, 'stale');

  // The new review names 19. The person's removal was about 18, so the link to 19 is written.
  const { request, result } = await round(w, all, { [key(17)]: needs(19, 'Issue 17 calls the API that issue 19 adds.') });
  assert.deepEqual(request.issues, [key(18), key(17)]);
  assert.equal(result.state, 'complete');
  assert.deepEqual(w.blockedBy[key(17)], [key(19)]);
  g = await graph(w);
  assert.equal(g.node(17).reviewState, 'current');
  assert.equal(g.node(17).dependencyState, 'waiting');
  assert.ok(g.node(17).reasons.includes('Open prerequisite'));
  assert.equal(g.node(19).reviewState, 'current', 'the link that PDD wrote does not make 19 stale');
  assert.equal(g.node(19).eligible, true);
  const tick = await reconcileDependencyIntake({ repository, trigger: 'tick', mode: 'auto' }, w.ports());
  assert.deepEqual(tick.queued, []);
  assert.deepEqual(tick.eligible.sort(), [key(18), key(19)].sort());
});

test('a refused link write becomes one visible question, not a pending intent that nothing delivers again', async () => {
  const i17 = issue(17), i18 = issue(18), i19 = issue(19), i20 = issue(20), all = [i17, i18, i19, i20];
  const w = world({ issues: all });
  assert.equal((await round(w, all)).result.state, 'complete');
  // A person added and removed "17 blocked by 18". Its most recent event is a removal.
  w.timeline[key(17)] = [linkEvent('blocked_by_added', 18), linkEvent('blocked_by_removed', 18)];

  const saved = w.comments[key(17)].length;
  let { result } = await round(w, all, { [key(17)]: needs(18, 'Issue 17 extends the parser from issue 18.') }, { issue: '17' });
  assert.equal(result.state, 'question');
  assert.equal(result.questions.length, 1);
  assert.match(result.questions[0], /A person removed the GitHub link/);
  assert.equal(w.comments[key(17)].length, saved + 2, 'the intent and one question');
  assert.deepEqual(w.blockedBy[key(17)] ?? [], [], "the person's removal stands");
  let g = await graph(w);
  assert.equal(g.node(17).reviewState, 'question');
  assert.ok(g.node(17).reasons.includes('Review question'));
  assert.deepEqual(g.node(17).facts.map(fact => fact.text), result.questions);
  const tick = await reconcileDependencyIntake({ repository, trigger: 'tick', mode: 'auto' }, w.ports());
  assert.deepEqual(tick.queued, []);
  assert.equal(w.comments[key(17)].length, saved + 2, 'no retry and no second question');

  // A removal event whose blocker GitHub does not name refuses every addition, also as a question.
  w.timeline[key(19)] = [{ event: 'blocked_by_removed' }];
  ({ result } = await round(w, all, { [key(19)]: needs(20, 'Issue 19 uses the table that issue 20 adds.') }, { issue: '19' }));
  assert.equal(result.state, 'question');
  assert.match(result.questions[0], /cannot tell which one/);
  assert.deepEqual(w.blockedBy[key(19)] ?? [], []);
  g = await graph(w);
  assert.equal(g.node(19).reviewState, 'question');
  assert.equal(g.node(20).reviewState, 'current');
});

test('a removed link where the issue is the prerequisite does not stop links that the issue needs', async () => {
  const i17 = issue(17), i18 = issue(18), i19 = issue(19), all = [i17, i18, i19];
  const w = world({ issues: all });
  assert.equal((await round(w, all)).result.state, 'complete');
  // A person adds and removes "19 blocked by 17". In 17's history this is a "blocking" change.
  w.blockedBy[key(19)] = [key(17)];
  w.timeline[key(19)] = [linkEvent('blocked_by_added', 17)];
  w.timeline[key(17)] = [linkEvent('blocking_added', 19)];
  assert.equal((await round(w, all)).result.state, 'complete');
  w.blockedBy[key(19)] = [];
  w.timeline[key(19)].push(linkEvent('blocked_by_removed', 17));
  w.timeline[key(17)].push(linkEvent('blocking_removed', 19));
  let g = await graph(w);
  assert.equal(g.node(17).reviewState, 'stale');

  const { result } = await round(w, all, { [key(17)]: needs(18, 'Issue 17 calls the API that issue 18 adds.') });
  assert.equal(result.state, 'complete');
  assert.deepEqual(w.blockedBy[key(17)], [key(18)]);
  g = await graph(w);
  assert.equal(g.node(17).reviewState, 'current');
  assert.equal(g.node(17).dependencyState, 'waiting');
  assert.equal(g.node(18).eligible, true);
});

test("an outsider's open issue does not hold the batch: a new trusted issue is reviewed and becomes eligible", async () => {
  const i17 = issue(17), i50 = issue(50, { user: { login: 'stranger' } }), i103 = issue(103);
  const w = world({ issues: [i17, i50, i103], outsiders: ['stranger'], comments: { [key(17)]: [savedReview('501', i17, [i17])] } });
  const { delivered, pending } = deliveries();
  await reconcileDependencyIntake({ repository, trigger: 'tick', mode: 'auto' }, w.ports({ pending }));
  assert.equal(delivered.length, 1);
  assert.deepEqual(delivered[0].issues, [key(103)], 'the outsider issue is not a subject');
  const result = await completeDependencyIntake({ request: delivered[0], analysis: { impactJson: '', reviews: [answer(delivered[0], i103)] } }, w.ports());
  assert.equal(result.state, 'complete');

  const g = await graph(w);
  assert.equal(g.node(103).reviewState, 'current');
  assert.equal(g.node(103).eligible, true);
  assert.equal(g.node(50).eligible, false);
  assert.ok(g.node(50).reasons.includes('Untrusted issue'));
  const next = await reconcileDependencyIntake({ repository, trigger: 'tick', mode: 'auto' }, w.ports({ pending }));
  assert.deepEqual(next.queued, []);
  assert.ok(next.eligible.includes(key(103)));
  assert.equal(delivered.length, 1);
  assert.deepEqual((await prepareDependencyIntake({ repository, issue: '50' }, w.ports())).queued, [], 'not even by name');
});

test('an edit to a named prerequisite in another repository, or to an unrelated comment, during the review does not hold the result', async () => {
  const i17 = issue(17), i20 = issue(20), r5 = { ...issue(5), id: 5005, html_url: key(5, runtime) };
  const note = comment('530', 'Issue 20 also changes the parser.');
  const w = world({ issues: [i17, i20, r5], blockedBy: { [key(20)]: [key(5, runtime)] }, comments: { [key(20)]: [savedReview('520', i20, [i17, i20]), note] } });
  const { delivered, pending } = deliveries();
  await reconcileDependencyIntake({ repository, trigger: 'tick', mode: 'auto' }, w.ports({ pending }));
  assert.deepEqual(delivered[0].issues, [key(17)]);

  r5.body = 'A person edits runtime issue 5 while the coordinator reviews issue 17.';
  note.body = 'Issue 20 also changes the parser and the lexer.'; // Issue 17's review did not use this comment.
  const review = answer(delivered[0], i17, needs(5, 'Issue 17 needs the runtime API from runtime issue 5.', runtime));
  const result = await completeDependencyIntake({ request: delivered[0], analysis: { impactJson: '', reviews: [review] } }, w.ports());
  assert.equal(result.state, 'complete');
  assert.deepEqual(w.blockedBy[key(17)], [key(5, runtime)]);
  const g = await graph(w);
  assert.equal(g.node(17).reviewState, 'current');
  assert.equal(g.node(17).dependencyState, 'waiting');
  const next = await reconcileDependencyIntake({ repository, trigger: 'tick', mode: 'auto' }, w.ports({ pending }));
  assert.deepEqual(next.queued, [], 'no saved review used the edited comment');
});

test("a link that PDD writes from a review does not make the prerequisite's review stale; a person's change to it does", async () => {
  const i17 = issue(17), i104 = issue(104), all = [i17, i104];
  const w = world({ issues: [i17] });
  assert.equal((await round(w, all)).result.state, 'complete');
  w.issues.push(i104);
  const { result } = await round(w, all, { [key(104)]: needs(17, 'Issue 104 changes the code that issue 17 adds.') });
  assert.equal(result.state, 'complete');
  assert.deepEqual(w.blockedBy[key(104)], [key(17)]);
  let g = await graph(w);
  assert.equal(g.node(17).reviewState, 'current', 'B blocked by A, written by PDD, does not delay A');
  assert.equal(g.node(17).eligible, true);
  assert.equal(g.node(104).dependencyState, 'waiting');
  assert.deepEqual((await prepareDependencyIntake({ repository }, w.ports())).queued, [], 'nothing is left to review');

  w.blockedBy[key(104)] = []; // A person removes the link that PDD wrote.
  g = await graph(w);
  assert.equal(g.node(17).reviewState, 'stale', 'a person changed a link from 17');
  assert.equal(g.node(104).reviewState, 'stale');
  assert.ok(g.node(104).reasons.includes('Human dependency change'));
});

test("a person's answer to a dependency question queues the issue for review again", async () => {
  const i17 = issue(17), all = [i17];
  const w = world({ issues: all, outsiders: ['stranger'] });
  const asked = 'Must the installer from issue 17 ship first? Please answer here.';
  assert.equal((await round(w, all, { [key(17)]: { outcome: 'question', questions: [asked] } })).result.state, 'question');
  const { delivered, pending } = deliveries();
  let tick = await reconcileDependencyIntake({ repository, trigger: 'tick', mode: 'auto' }, w.ports({ pending }));
  assert.deepEqual(tick.queued, [], 'an unanswered question is not sent again');

  w.comments[key(17)].push(comment('960', 'I am not a maintainer, but please hurry.', 'stranger'));
  let g = await graph(w);
  assert.equal(g.node(17).reviewState, 'question', "an outsider's comment is not an answer");

  const answerText = 'No. Issue 17 needs nothing first.';
  w.comments[key(17)].push(comment('961', answerText));
  g = await graph(w);
  assert.equal(g.node(17).reviewState, 'stale');
  assert.equal(g.node(17).eligible, false);
  tick = await reconcileDependencyIntake({ repository, trigger: 'tick', mode: 'auto' }, w.ports({ pending }));
  assert.deepEqual(tick.queued, [key(17)]);
  assert.equal(delivered.length, 1);
  assert.deepEqual(delivered[0].issues, [key(17)]);

  const head = projectIssueGraph({ snapshot: JSON.parse(delivered[0].snapshotJson) }).nodes.find(n => n.key === key(17)).review;
  const review = { ...answer(delivered[0], i17, { base: [head] }) };
  review.inputs = [...review.inputs, { key: `${key(17)}#issuecomment-961`, revision: sha(answerText) }];
  const result = await completeDependencyIntake({ request: delivered[0], analysis: { impactJson: '', reviews: [review] } }, w.ports());
  assert.equal(result.state, 'complete');
  g = await graph(w);
  assert.equal(g.node(17).reviewState, 'current');
  assert.equal(g.node(17).eligible, true);
});

test('a PDD link keeps the prerequisite current in one batch and when a later review names a link that a person made', async () => {
  // New issues 30 and 31 are reviewed in one request, and 31's review names 30.
  const i30 = issue(30), i31 = issue(31), all = [i30, i31];
  const w = world({ issues: all });
  const { request, result } = await round(w, all, { [key(31)]: needs(30, 'Issue 31 uses the schema that issue 30 adds.') });
  assert.deepEqual(request.issues, [key(31), key(30)]);
  assert.equal(result.state, 'complete');
  let g = await graph(w);
  assert.equal(g.node(30).reviewState, 'current');
  assert.equal(g.node(30).eligible, true);
  assert.equal(g.node(31).dependencyState, 'waiting');

  // A person adds "32 blocked by 30". Both ends are reviewed again, and 30's row now holds the link.
  const i32 = issue(32); all.push(i32); // `all` is the world's issue list
  assert.equal((await round(w, all)).result.state, 'complete');
  w.blockedBy[key(32)] = [key(30)];
  assert.equal((await round(w, all)).result.state, 'complete');
  g = await graph(w);
  assert.equal(g.node(30).reviewState, 'current');
  // A later review of 32 names the link that the person made. That is not a link change for 30.
  assert.equal((await round(w, all, { [key(32)]: needs(30, 'Issue 32 extends the schema from issue 30.') }, { issue: '32' })).result.state, 'complete');
  g = await graph(w);
  assert.equal(g.node(32).reviewState, 'current');
  assert.equal(g.node(30).reviewState, 'current');
  assert.equal(g.node(30).eligible, true);
});

test("a link row saved in a batch does not depend on whether the batch's own link write happens", async () => {
  // 30 names 31. 31 is newer, so its review is saved first; then the save of 30's intent fails.
  const i30 = issue(30), i31 = issue(31);
  const w = world({ issues: [i30, i31] });
  const { request } = await prepareDependencyIntake({ repository }, w.ports());
  assert.deepEqual(request.issues, [key(31), key(30)]);
  const reviews = [answer(request, i31), answer(request, i30, needs(31, 'Issue 30 uses the table that issue 31 adds.'))];
  const reviewsPort = { save: (args, ports) => args.issue === key(30) ? { id: '', state: 'pending', warnings: [] } : saveDependencyReview(args, ports) };
  const result = await completeDependencyIntake({ request, analysis: { impactJson: '', reviews } }, w.ports({ reviews: reviewsPort }));
  assert.equal(result.state, 'pending');
  assert.equal(result.pendingStage, 'review-save');
  const g = await graph(w);
  assert.equal(g.node(31).reviewState, 'current', 'the link that was not written leaves no trace in the row');
  assert.equal(g.node(31).eligible, true);
  assert.equal(g.node(30).reviewState, 'unchecked');
});

// One fake clock, delivery port and completion note for every tick and completion.
// The delivery port records the repeat marker that intake saved before the send,
// as the launcher reads it.
const start = Date.parse('2026-11-06T12:00:00.000Z');
function redelivery(w) {
  let at = start;
  const sent = [], note = { json: '{}' };
  const pending = { state: {}, read: async () => reply(pending.state), save: async ({ json }) => { pending.state = JSON.parse(json); return { ok: true }; },
    deliver: async ({ requestJson }) => { sent.push({ request: JSON.parse(requestJson), again: pending.state.redelivery ?? null }); return { state: 'delivered' }; } };
  const results = { read: async () => ({ json: note.json }), save: async ({ json }) => { note.json = json; return { ok: true }; } };
  const ports = (extra = {}) => w.ports({ pending, results, clock: { now: async () => ({ iso: new Date(at).toISOString() }) }, ...extra });
  const tick = (minutes, extra) => { at = start + minutes * 60000; return reconcileDependencyIntake({ repository, trigger: 'tick', mode: 'auto' }, ports(extra)); };
  return { sent, pending, ports, tick };
}
// A GitHub server error on the comments of one issue while the snapshot is read again.
const serverError = (w, number) => ({ github: { ...w.ports().github, page: async args => {
  if (args.kind === 'comments' && args.issue === number) throw Error('HTTP 502');
  return w.ports().github.page(args);
} } });
const claimedBy = (owner, number) => ({ owners: { read: async () => reply({ localOwner: 'coordinator', claims: [{ issue: key(number), owner, active: true }], runs: [], runsKnown: true }) } });

test('a request that ends pending is delivered again at the next tick 30 minutes later, names its reason, and completes when the cause is gone', async () => {
  const file = `https://github.com/${repository}/blob/HEAD/src/parser.mjs`;
  const i17 = issue(17);
  const modes = {
    'observations-incomplete': { ports: w => serverError(w, 103) },
    'answer-row-mismatch': { answer: review => ({ ...review, candidates: review.candidates.filter(x => x.key !== key(17)) }), rows: [row(i17)] },
    'input-changed': { examined: { key: file, revision: 'r1' }, change: w => { w.files[file] = 'r2'; }, rows: [{ key: file, revision: 'r2' }] },
    'owner-changed': { ports: () => claimedBy('another-coordinator', 103) },
  };
  for (const [reason, mode] of Object.entries(modes)) {
    const i103 = issue(103);
    const w = world({ issues: [i17, i103], comments: { [key(17)]: [savedReview('501', i17, [i17])] }, files: { [file]: 'r1' } });
    const r = redelivery(w);
    await r.tick(0);
    assert.equal(r.sent.length, 1, reason);
    const first = r.sent[0].request;
    assert.deepEqual(first.issues, [key(103)], reason);

    let review = answer(first, i103);
    if (mode.examined) review.inputs = [...review.inputs, mode.examined]; // an extra input that the review used
    if (mode.answer) review = mode.answer(review);
    mode.change?.(w);
    const result = await completeDependencyIntake({ request: first, analysis: { impactJson: '', reviews: [review] } }, r.ports(mode.ports?.(w)));
    assert.equal(result.state, 'pending', reason);
    assert.equal(result.reason, reason, 'the result names the reason');
    assert.deepEqual(result.rows ?? [], mode.rows ?? [], reason);
    assert.equal(w.comments[key(103)], undefined, `${reason}: nothing is saved`);

    // The cause is gone. Nothing that the delivery fingerprint tracks changed.
    assert.deepEqual((await r.tick(10)).queued, [key(103)], reason);
    assert.equal(r.sent.length, 1, `${reason}: no delivery before 30 minutes`);
    await r.tick(31);
    assert.equal(r.sent.length, 2, `${reason}: the next tick 30 minutes later delivers again`);
    const again = r.sent[1];
    assert.deepEqual(again.request.issues, [key(103)], `${reason}: the same subjects`);
    assert.notEqual(again.request.id, first.id, `${reason}: a fresh prepare`);
    assert.deepEqual(again.again, { attempt: 1, cap: 3, reason, rows: mode.rows ?? [] }, reason);
    await r.tick(45);
    assert.equal(r.sent.length, 2, `${reason}: one delivery for each wait`);

    review = answer(again.request, i103);
    if (mode.examined) review.inputs = [...review.inputs, { key: file, revision: 'r2' }];
    const done = await completeDependencyIntake({ request: again.request, analysis: { impactJson: '', reviews: [review] } }, r.ports());
    assert.equal(done.state, 'complete', reason);
    const g = await graph(w);
    assert.equal(g.node(103).reviewState, 'current', reason);
    assert.equal(g.node(103).eligible, true, reason);
    const next = await r.tick(80);
    assert.equal(r.sent.length, 2, `${reason}: nothing is left to deliver`);
    assert.ok(next.eligible.includes(key(103)), reason);
  }
});

test('after three repeated deliveries the issue gets one visible question with the reason, and nothing is sent again until a person answers', async () => {
  const i17 = issue(17), i103 = issue(103);
  const w = world({ issues: [i17, i103], comments: { [key(17)]: [savedReview('501', i17, [i17])] } });
  const r = redelivery(w);
  for (let i = 0; i < 4; i++) {
    await r.tick(i * 31);
    assert.equal(r.sent.length, i + 1);
    const { request, again } = r.sent[i];
    assert.deepEqual(request.issues, [key(103)]);
    assert.deepEqual(again, i ? { attempt: i, cap: 3, reason: 'observations-incomplete', rows: [] } : null);
    const result = await completeDependencyIntake({ request, analysis: { impactJson: '', reviews: [answer(request, i103)] } }, r.ports(serverError(w, 103)));
    assert.equal(result.reason, 'observations-incomplete');
  }
  await r.tick(4 * 31, { reviews: { save: async () => ({ id: '', state: 'pending', warnings: [] }) } });
  assert.equal(r.sent.length, 4, 'the cap holds: no fifth delivery');
  assert.equal(w.comments[key(103)], undefined, 'the question save is not confirmed');
  await r.tick(5 * 31);
  assert.equal(r.sent.length, 4);
  assert.equal(w.comments[key(103)].length, 1, 'one question on the issue, tried again after the unconfirmed save');
  assert.match(w.comments[key(103)][0].body, /Question: PDD sent the dependency review of .*issues\/103 4 times.*Last reason: observations-incomplete/);
  let g = await graph(w);
  assert.equal(g.node(103).reviewState, 'question');
  assert.ok(g.node(103).reasons.includes('Review question'));
  assert.equal(g.node(103).eligible, false);
  assert.match(g.node(103).facts[0].text, /Last reason: observations-incomplete/, 'the graph shows the question');
  const head = g.node(103).review;

  for (const minutes of [6 * 31, 7 * 31, 10 * 31]) assert.deepEqual((await r.tick(minutes)).queued, []);
  assert.equal(r.sent.length, 4, 'no silent retries');
  assert.equal(w.comments[key(103)].length, 1, 'no second question');

  const words = 'Issue 103 needs no other issue first.';
  w.comments[key(103)].push(comment('970', words));
  await r.tick(11 * 31);
  assert.equal(r.sent.length, 5, "a person's answer queues the issue again");
  const { request, again } = r.sent[4];
  assert.equal(again, null, 'the answer starts a new delivery, not a repeat');
  const review = answer(request, i103, { base: [head] });
  review.inputs = [...review.inputs, { key: `${key(103)}#issuecomment-970`, revision: sha(words) }];
  assert.equal((await completeDependencyIntake({ request, analysis: { impactJson: '', reviews: [review] } }, r.ports())).state, 'complete');
  g = await graph(w);
  assert.equal(g.node(103).reviewState, 'current');
  assert.equal(g.node(103).eligible, true);
});

// A saved review whose own outcome is pending and that names no link, as an
// earlier version accepted it.
const barePending = (id, subject, candidates) => comment(id, recordBody({ analysis: 'Could not decide yet.', base: [], continuation: '', issue: subject.html_url,
  inputs: [row(subject)], candidates: candidates.map(row), outcome: 'pending', dependencies: [], questions: [], effects: 'none' }));

test('a pending answer that names no link saves nothing; after three repeated deliveries the issue gets one question, and then nothing is sent', async () => {
  for (const start of ['new issue', 'old pending review with no link']) {
    const i17 = issue(17), i103 = issue(103);
    const w = world({ issues: [i17, i103], comments: { [key(17)]: [savedReview('501', i17, [i17])],
      ...(start === 'new issue' ? {} : { [key(103)]: [barePending('777', i103, [i17, i103])] }) } });
    const r = redelivery(w);
    const saved = () => (w.comments[key(103)] ?? []).length, before = saved();
    let answered = 0;
    // Six hours of 30-minute ticks. The coordinator answers each delivery with outcome pending and no link.
    for (let minutes = 0; minutes <= 12 * 31; minutes += 31) {
      await r.tick(minutes);
      while (answered < r.sent.length) {
        const { request } = r.sent[answered++];
        const head = (await graph(w)).node(103).review;
        const review = answer(request, i103, { base: head ? [head] : [], outcome: 'pending' });
        await assert.rejects(completeDependencyIntake({ request, analysis: { impactJson: '', reviews: [review] } }, r.ports()), { code: 'invalid-analysis' }, start);
        assert.equal(saved(), before, `${start}: a refused answer saves nothing`);
      }
    }
    assert.equal(r.sent.length, 4, `${start}: one delivery and 3 repeats, no flood`);
    assert.deepEqual(r.sent.map(s => s.again?.attempt ?? 0), [0, 1, 2, 3], start);
    assert.equal(saved(), before + 1, `${start}: exactly one question`);
    assert.match(w.comments[key(103)].at(-1).body, /Question: PDD sent the dependency review of .*issues\/103 4 times.*Last reason: not-completed/, start);
    const g = await graph(w);
    assert.equal(g.node(103).reviewState, 'question', start);
    assert.equal(g.node(103).eligible, false, start);
  }
});

test('an old saved pending review that names no link is reviewed again, and a complete answer makes the issue eligible', async () => {
  const i17 = issue(17), i103 = issue(103);
  const w = world({ issues: [i17, i103], comments: { [key(17)]: [savedReview('501', i17, [i17])], [key(103)]: [barePending('777', i103, [i17, i103])] } });
  let g = await graph(w);
  assert.equal(g.node(103).reviewState, 'stale');
  assert.ok(g.node(103).reasons.includes('Stale review'));
  assert.equal(g.node(103).eligible, false);
  const r = redelivery(w);
  assert.deepEqual((await r.tick(0)).queued, [key(103)], 'the old review is queued again');
  assert.equal(r.sent.length, 1);
  const { request } = r.sent[0];
  const result = await completeDependencyIntake({ request, analysis: { impactJson: '', reviews: [answer(request, i103, { base: ['777'] })] } }, r.ports());
  assert.equal(result.state, 'complete');
  g = await graph(w);
  assert.equal(g.node(103).reviewState, 'current');
  assert.equal(g.node(103).eligible, true);
  const next = await r.tick(31);
  assert.deepEqual(next.queued, []);
  assert.ok(next.eligible.includes(key(103)));
  assert.equal(r.sent.length, 1, 'nothing more is sent');
});

test('the launcher names a repeated request and its reason, and does not send it while an earlier submission has uncertain custody', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-redeliver-')); t.after(() => rmSync(dir, { recursive: true, force: true }));
  const cwd = join(dir, 'repo'), home = join(dir, 'home'), stateRoot = join(dir, 'state');
  for (const folder of [cwd, home, stateRoot]) mkdirSync(folder);
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  const file = join(stateRoot, `${sha(cwd).slice(0, 20)}.json`), activation = '2026-11-06T11:00:00Z';
  const coordinator = { version: 'pdd.autopilot-coordinator.v1', repository, coordinatorId: 'c', machine: 'm', activation };
  writeFileSync(file, JSON.stringify({ enabled: true, cwd, repo: repository, stateFile: file, coordinatorId: 'c', machine: 'm', activatedAt: activation,
    agent: { id: 'codex', kind: 'codex', command: 'codex' }, recipeDelivered: true, environment: { HOME: home }, paneId: 'p', workspaceId: 'w',
    ownerLaunch: { paneId: 'p', startedAt: 1, coordinator, profile: { agent: { id: 'codex', kind: 'codex' }, home, definitionHome: home, configHome: null }, fingerprint: autopilotLaunchFingerprint({ cwd, agent: { kind: 'codex' } }) } }));
  const i17 = issue(17), i103 = issue(103);
  const w = world({ issues: [i17, i103], comments: { [key(17)]: [savedReview('501', i17, [i17])] } });
  const note = { json: '{}' }, results = { read: async () => ({ json: note.json }), save: async ({ json }) => { note.json = json; return { ok: true }; } };
  const { clock, ...observed } = w.ports({ results }); // the launcher supplies the clock
  let now = start;
  const prompts = [], warnings = [];
  const live = { pane_id: 'p', workspace_id: 'w', cwd, foreground_cwd: cwd, tab_id: 't', terminal_id: 'term', agent: 'codex', agent_status: 'idle', agent_session: 'session' };
  const ports = { stateRoot, now: () => now, warn: text => warnings.push(text), queryIssues: async () => ({ status: 304 }),
    run: async command => command === 'git' ? { code: 0, stdout: `${cwd}\n` } : { code: 0, stdout: JSON.stringify({ nameWithOwner: repository, url: `https://github.com/${repository}` }) },
    reconcileDependencyIntake: (args, intakePorts) => reconcileDependencyIntake(args, { ...intakePorts, ...observed, reviewerCoordinator: undefined, reviewerIdentity: async () => null }),
    herdr: async args => {
      if (args[0] === 'agent' && args[1] === 'get') return { result: { type: 'agent_info', agent: live } };
      if (args[0] === 'pane' && args[1] === 'get') return { result: { type: 'pane_info', pane: live } };
      if (args[0] === 'workspace' && args[1] === 'get') return { result: { type: 'workspace_info', workspace: { workspace_id: 'w' } } };
      if (args[0] === 'pane' && args[1] === 'read') return '';
      if (args[0] === 'agent' && args[1] === 'prompt') { prompts.push(args.at(-1)); return {}; }
      throw Error(args.join(' '));
    } };
  const requestIn = text => JSON.parse(readFileSync(JSON.parse(/Artifact path: (.+)/.exec(text)[1]), 'utf8'));

  await tickAutopilot(file, ports);
  assert.equal(prompts.length, 1);
  assert.doesNotMatch(prompts[0], /Repeated request/);
  const first = requestIn(prompts[0]);
  assert.deepEqual(first.issues, [key(103)]);
  // The coordinator completes while another coordinator holds 103 for a moment.
  const result = await completeDependencyIntake({ request: first, analysis: { impactJson: '', reviews: [answer(first, i103)] } }, w.ports({ results, ...claimedBy('another-coordinator', 103) }));
  assert.equal(result.reason, 'owner-changed');

  // 31 minutes later an earlier submission has uncertain custody: nothing is sent.
  now += 31 * 60000;
  const saved = JSON.parse(readFileSync(file, 'utf8'));
  writeFileSync(file, JSON.stringify({ ...saved, deliveryIntent: { version: 2, paneId: 'p', workspaceId: 'w', at: now - 1000, fingerprint: 'earlier', payloadDigest: 'earlier' } }));
  await tickAutopilot(file, ports);
  assert.equal(prompts.length, 1, 'no repeated request while custody is uncertain');
  assert.ok(warnings.some(text => /dependency review waits: a previous submission has uncertain custody/.test(text)));
  assert.equal(JSON.parse(readFileSync(file, 'utf8')).dependencyPending.redelivered, 0, 'a refused send is not counted');

  // Custody is known again: the next tick sends the fresh request once, with the reason.
  const known = JSON.parse(readFileSync(file, 'utf8')); delete known.deliveryIntent; writeFileSync(file, JSON.stringify(known));
  now += 60000;
  await tickAutopilot(file, ports);
  assert.equal(prompts.length, 2);
  assert.match(prompts[1], /Repeated request 1 of 3: the last delivery of these issues did not finish\. Last reason: owner-changed\./);
  const again = requestIn(prompts[1]);
  assert.deepEqual(again.issues, [key(103)]);
  assert.notEqual(again.id, first.id);
  now += 60000;
  await tickAutopilot(file, ports);
  assert.equal(prompts.length, 2, 'one repeated request for each wait');
  assert.equal((await completeDependencyIntake({ request: again, analysis: { impactJson: '', reviews: [answer(again, i103)] } }, w.ports({ results }))).state, 'complete');
  assert.equal((await graph(w)).node(103).eligible, true);

  // A coordinator that stops after delivery: the repeat says that no result came.
  const i104 = issue(104); w.issues.push(i104);
  now += 60000;
  await tickAutopilot(file, ports);
  assert.equal(prompts.length, 3);
  assert.deepEqual(requestIn(prompts[2]).issues, [key(104)]);
  now += 31 * 60000;
  await tickAutopilot(file, ports);
  assert.equal(prompts.length, 4);
  assert.match(prompts[3], /Repeated request 1 of 3: .*Last reason: not-completed\./);
});
