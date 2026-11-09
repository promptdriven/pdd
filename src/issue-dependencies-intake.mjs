import {parkingSummary} from './autopilot-parking.mjs';
// Generated from prompts/cli/issue-dependencies-intake.prompt.md (sha256: d098606e91907fb1c461bb31a880cb4f1ed316f6ecbca17460e9ee61781061ca).
import { syncMixedParts } from './issue-mixed.mjs';
import { sortRequestFingerprint, sortSubjects, prepareSortContext, validateSortBatch, saveSortBatch, routeSortIssues, syncSortGroups, pacedSortWrites } from './issue-sort-github.mjs';
import { sortPlan } from './issue-sort.mjs';
import { randomUUID } from 'node:crypto';
import { execFile as nodeExecFile } from 'node:child_process';
import { mkdirSync, readFileSync, renameSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { promisify } from 'node:util';
import { gitContext } from './workflow-runs.mjs';
import { dependencyLinks, projectIssueGraph, validateDependencyChange, issueKey } from './issue-dependencies.mjs';
import { createDependencyReadPorts, readDependencySnapshot, saveDependencyReview, saveDependencyImpact, applyDependencyChanges, commandGithubFloor } from './issue-dependencies-github.mjs';

const snapshotRead = (ports, args) => ports.snapshots?.read ? ports.snapshots.read(args) : readDependencySnapshot(args, ports);
const root = (key, repository) => key.toLowerCase().startsWith(`https://github.com/${repository.toLowerCase()}/issues/`);
const json = value => typeof value === 'string' ? JSON.parse(value) : value;
const rows = snapshot => new Map([...snapshot.issues.map(x => [x.key, x.revision]), ...snapshot.inputs.map(x => [x.key, x.revision])]);
const sameRows = (a, b) => a.every(x => b.get(x.key) === x.revision);
const ownedElsewhere = (owners, issue) => (owners.claims || []).some(x => x.issue === issue && x.active && (!x.owner || x.owner !== owners.localOwner || owners.localMachine && x.machine && x.machine !== owners.localMachine));
// coordinatorId is the launcher's stable machine/repository owner, not its pane.
const reviewOwner = owners => owners.localOwner ? { coordinatorId: owners.localOwner, machine: owners.localMachine ?? '' } : null;
const sameReviewOwner = (bound, owners) => !bound || bound.coordinatorId === owners.localOwner && (!bound.machine || bound.machine === owners.localMachine);
const exact = (obj, keys) => obj && typeof obj === 'object' && !Array.isArray(obj) && Object.keys(obj).sort().join(',') === keys.slice().sort().join(',');
const strings = a => Array.isArray(a) && a.every(x => typeof x === 'string');
const validRows = a => Array.isArray(a) && a.every(x => exact(x, ['key','revision']) && typeof x.key === 'string' && typeof x.revision === 'string' && x.key && x.revision) && new Set(a.map(x => x.key)).size === a.length;
const REVIEW_BATCH = 10;
// A request whose subjects stay unchecked or stale is delivered again after one
// tick interval, at most AGAIN_CAP times; then each subject gets one question.
const AGAIN_AFTER = 30 * 60 * 1000, AGAIN_CAP = 3;
const REASONS = ['observations-incomplete', 'input-changed', 'answer-row-mismatch', 'owner-changed', 'write-unconfirmed', 'github-limit'];
// A completion that a failed read, a lost write or the GitHub limit stopped is kept and finished later without a new
// analysis. Transient failures retain it until validation ends it. A completion, idle wake or worker yield within SAVED_FRESH of the last full
// observation delivers from the saved snapshot.
const RESUMABLE = ['observations-incomplete', 'write-unconfirmed', 'github-limit'], SAVED_FRESH = 10 * 60 * 1000;
// The claims that this process's last snapshot read for these root issues, else one owners read.
async function ownersFor(ports, repository, issues) {
  const seen = ports.dependencyReads?.owners;
  if (!ports.snapshots && seen?.repository === repository.toLowerCase() && issues.every(key => seen.issues.includes(issueKey(key) ?? key))) {
    if (typeof seen.json !== 'string') throw Error('Claim observations are incomplete');
    return { json: seen.json };
  }
  return ports.owners.read({ repository, issues });
}
// The kept completion of this repository: the request and analysis of a stopped completion. Supplied as
// `completions`, else the file beside the saved snapshot of an Autopilot repository.
const keptFor = (ports, repository) => ports.completions ?? ports.dependencyReads?.completions(repository) ?? null;
const invalidAnalysis = () => Object.assign(new Error('invalid-analysis'), { code: 'invalid-analysis' });
// A pending result names its reason and, where they exist, the rows behind it.
const pendingResult = (reason, { rows = [], stage, issue, reviewIds = [], questions = [] } = {}) => ({
  state: 'pending', reason, ...(rows.length ? { rows: [...new Map(rows.map(x => [x.key, x])).values()].slice(0, 20) } : {}),
  reviewIds, eligible: [], questions, ...(stage ? { pendingStage: stage } : {}), ...(issue ? { pendingIssue: issue } : {}),
});
// The last pending completion result, kept in the repository's Git common dir so
// that a later tick can name its reason. It is a note for the coordinator and
// never decides a delivery. Direct callers without a checkout keep no note.
function nativeResults(cwd, ports) {
  const file = async () => {
    const context = await gitContext(cwd, ports.execFile ? { execFile: ports.execFile } : {});
    if (!context) throw Error('No checkout');
    return join(context.commonDir, 'pdd', 'dependency-result.json');
  };
  return {
    read: async () => { try { return { json: readFileSync(await file(), 'utf8') }; } catch { return { json: '{}' }; } },
    save: async ({ json: text }) => {
      try {
        const path = await file(), temp = `${path}.${randomUUID()}.tmp`;
        mkdirSync(dirname(path), { recursive: true, mode: 0o700 }); writeFileSync(temp, text, { mode: 0o600 }); renameSync(temp, path);
        return { ok: true };
      } catch { return { ok: false }; }
    },
  };
}
const resultsPort = (cwd, ports) => ports.results ?? (cwd ? nativeResults(cwd, ports) : null);
const sameStringList = (a, b) => a.length === b.length && [...a].sort().every((x, i) => x === [...b].sort()[i]);
function sameImpactRecord(saved, issue, impact) {
  return saved.host === issue && saved.authority === 'trusted' && saved.intact === true
    && saved.complete === true && impact.complete === true
    && saved.inputs?.length === impact.inputs.length
    && sameRows(impact.inputs, new Map(saved.inputs.map(row => [row.key, row.revision])))
    && sameStringList(saved.reviews ?? [], impact.reviews)
    && sameStringList(saved.affected ?? [], impact.affected);
}

// Semantic packets carry observations, but text without verified authority is not instructions.
function packetSnapshot(snapshot) {
  const copy = structuredClone(snapshot);
  copy.issues = copy.issues.map(issue => issue.authority === 'trusted' ? {
    ...issue,
    // #3053: identity can explain a conflict; outsider sort prose is not instructions.
    ...(issue.sorts ? { sorts: issue.sorts.map(s => s.authority === 'trusted' && s.intact ? s : { ...s, record: null }) } : {}),
  } : {
    key: issue.key, nodeId: issue.nodeId, title: '', revision: issue.revision,
    state: issue.state, authority: issue.authority, conditions: [], execution: issue.execution,
    holds: issue.holds, ...(issue.executionClaim ? { executionClaim: issue.executionClaim } : {}),
    ...(issue.runIds ? { runIds: issue.runIds } : {}),
  });
  copy.reviews = copy.reviews.map(review => review.authority === 'trusted' && review.intact ? review : {
    id: review.id, analysis: '', base: [], continuation: '', issue: review.issue,
    inputs: [], candidates: [], outcome: review.outcome, dependencies: [],
    questions: [], intact: review.intact, effects: review.effects, authority: review.authority,
  });
  const currentRows = rows(copy);
  const issueKeys = new Set(copy.issues.map(issue => issue.key));
  const reviewIds = new Set(copy.reviews.map(review => review.id));
  copy.impacts = copy.impacts.map(impact => impact.authority === 'trusted' && impact.intact ? impact : ({
    id: impact.id, host: impact.host, inputs: impact.inputs.filter(row => currentRows.get(row.key) === row.revision),
    reviews: impact.reviews.filter(id => reviewIds.has(id)), affected: impact.affected.filter(key => issueKeys.has(key)),
    complete: impact.complete, trusted: impact.trusted, intact: impact.intact,
    ...(impact.authority ? { authority: impact.authority } : {}),
  }));
  return copy;
}


export async function checkDependencyStart({ cwd = '', repository, issue, coordinator }, ports = {}) {
  try {
    ports = createDependencyReadPorts({ cwd }, ports);
    // The subject of a start is read live: its claim, its labels and its links never come from the saved snapshot.
    const subjectNumber = Number(issueKey(issue)?.split('/').pop());
    if (Number.isSafeInteger(subjectNumber)) ports.dependencyReads?.live(repository, subjectNumber);
    const [settings, read, ownerReply] = await Promise.all([
      ports.settings.read({ cwd, repository }), snapshotRead(ports, { cwd, repository }), ports.owners.read({ repository, issues: [issue] })
    ]);
    const owners = json(ownerReply.json); const snapshot = read.snapshot;
    if (settings.mode === 'off') return { allowed: false, reason: 'off' };
    if (settings.healthPaused === true) return { allowed: false, reason: 'health' };
    if (settings.parkingWakePending?.length) return {allowed: false, reason: 'runs'};
    const key = issueKey(issue);
    const selected = key && root(key, repository) ? key : null;
    const claim = selected && (owners.claims || []).find(x => issueKey(x.issue) === selected && x.active);
    if (!coordinator || coordinator.repository?.toLowerCase() !== repository.toLowerCase() || !coordinator.coordinatorId || owners.localOwner !== coordinator.coordinatorId || !coordinator.machine || !coordinator.claim?.commentId || !coordinator.claim?.labelEventId || !claim || claim.owner !== coordinator.coordinatorId || claim.coordinatorId !== coordinator.coordinatorId || claim.machine !== coordinator.machine || claim.commentId !== coordinator.claim.commentId || claim.labelEventId !== coordinator.claim.labelEventId) return { allowed: false, reason: 'owner' };
    if (settings.activation !== coordinator.activation || settings.runs !== coordinator.runs) return { allowed: false, reason: 'stale' };
    if (owners.runsKnown !== true || !Array.isArray(owners.runs)) return { allowed: false, reason: 'runs' };
    const slots = new Map();
    for (const run of owners.runs) {
      const key = run.runId || run.issue;
      const working = run.working ?? (run.occupied === true || parkingSummary([run], 1).working > 0);
      // A duplicate observation cannot hide working custody.
      const prior = slots.get(key);
      slots.set(key, {run, working: working || prior?.working === true});
    }
    const occupied = [...slots.values()].filter(slot => slot.working).map(slot => slot.run);
    const runCap = settings.runs ?? settings.capacityRuns;
    if (runCap !== undefined) {
      if (!Number.isSafeInteger(runCap) || runCap < 1) return { allowed: false, reason: 'runs' };
      if (occupied.length + (occupied.some(x => selected && issueKey(x.issue) === selected) ? 0 : 1) > runCap) return { allowed: false, reason: 'runs' };
      const parkedCap = settings.maxParked ?? 2 * runCap;
      if (!Number.isSafeInteger(parkedCap) || parkedCap < 1 || slots.size - occupied.length >= parkedCap) return {allowed: false, reason: 'parked'};
    }
    if (owners.runs.some(run => selected && issueKey(run.issue) === selected)) return { allowed: false, reason: 'dependency' };
    const copy = structuredClone(snapshot); const subject = copy.issues.find(x => selected && issueKey(x.key) === selected);
    if (subject && subject.executionClaim?.coordinatorId === claim.coordinatorId && subject.executionClaim?.commentId === claim.commentId && subject.executionClaim?.labelEventId === claim.labelEventId) {
      subject.execution = 'idle'; subject.holds = subject.holds.filter(x => !/^(running|claim|claimed)$/i.test(x));
    }
    const node = projectIssueGraph({ snapshot: copy }).nodes.find(x => selected && issueKey(x.key) === selected);
    if (!node || node.reasons.includes('Incomplete relevant observations')) return { allowed: false, reason: 'unknown' };
    if (node.eligible && ports.checkPaneCapacity) {
      try { await ports.checkPaneCapacity(); }
      catch (error) { return {allowed:false,reason:error.code === 'herdr_pane_budget' ? 'panes' : 'unknown'}; }
    }
    return node.eligible ? { allowed: true, reason: 'ok' } : { allowed: false, reason: 'dependency' };
  } catch { return { allowed: false, reason: 'unknown' }; }
}

// Selected heads come from the model, including confirmed continuations. For
// unresolved observations retain conservative identities until they are resolved.
function headIds(snapshot, graph = projectIssueGraph({ snapshot })) {
  const selected = new Set(graph.nodes.map(node => node.review).filter(Boolean));
  const unresolved = new Set(graph.nodes.filter(node => !node.review).map(node => node.key));
  return snapshot.reviews.filter(review => review.authority === 'trusted' && review.intact &&
    (selected.has(review.id) || (unresolved.has(review.issue) && !snapshot.reviews.some(other => other.base.includes(review.id)))))
    .map(review => review.id).sort();
}

// A stale review has a changed input, a changed named prerequisite or an
// affected impact, so it needs a new review. Unchecked (new) issues go first.
// An outsider's issue can never be eligible, so it is never a subject: one such
// issue must not hold every batch.
function selectSubjects(graph, snapshot, repository, issue) {
  const number = key => Number(key.split('/').pop());
  const outsider = new Set(snapshot.issues.filter(i => i.authority === 'untrusted').map(i => issueKey(i.key)));
  return graph.nodes.filter(x => root(x.key, repository) && x.nativeState === 'open' && !outsider.has(x.key) && !snapshot.issues.find(i => i.key === x.key)?.holds?.includes('pdd:manual') && (issue ? x.key === issue || x.key.endsWith(`/issues/${issue}`) : (['unchecked', 'stale'].includes(x.reviewState) || sortSubjects(snapshot).includes(x.key))))
    .sort((a, b) => (a.reviewState === 'unchecked' ? 0 : 1) - (b.reviewState === 'unchecked' ? 0 : 1) || number(b.key) - number(a.key));
}

export async function prepareDependencyIntake({ cwd = '', repository, issue }, ports = {}) {
  ports = createDependencyReadPorts({ cwd }, ports);
  const observed = await snapshotRead(ports, { cwd, repository });
  const snapshot = observed.snapshot;
  const graph = projectIssueGraph({ snapshot });
  const selected = selectSubjects(graph, snapshot, repository, issue);
  let owners = { claims: [] }; if (selected.length) owners = json((await ownersFor(ports, repository, selected.map(node => node.key))).json);
  const skipped = selected.filter(x => x.reasons.includes('Incomplete relevant observations') || ownedElsewhere(owners, x.key)).map(x => x.key);
  // Small batches: one new issue never waits for a large review.
  const queued = selected.filter(x => !skipped.includes(x.key)).map(x => x.key).slice(0, REVIEW_BATCH);
  let contextJson = queued.length ? (await ports.evidence.read({ cwd, repository, issues: queued })).json : JSON.stringify({ source: [], requirements: [] });
  const bound = reviewOwner(owners);
  contextJson = JSON.stringify({ ...json(contextJson), ...prepareSortContext(snapshot), ...(bound ? { reviewOwner: bound } : {}) });
  const evidence = json(contextJson);
  if (!Array.isArray(evidence.source) || !Array.isArray(evidence.requirements) || evidence.requirements.some(x => x.authority !== 'trusted')) throw Error('invalid-input');
  const current = rows(snapshot);
  for (const item of evidence.source || []) if (item.key && item.revision) { const prev = current.get(item.key); if (!prev) snapshot.inputs.push({ key: item.key, revision: item.revision }); }
  return { request: { id: randomUUID(), repository, issues: queued, snapshotJson: JSON.stringify(packetSnapshot(snapshot)), contextJson }, queued, skipped };
}

// A review that an earlier call of the same request already saved: the same trusted, intact record on the subject.
// A repeated or resumed completion skips it, so finished work is never saved twice and never discarded.
const withoutLinkRow = rows => rows.filter(row => !/#dependencies$/i.test(row.key));
const sameReview = (saved, review) => saved.issue === review.issue && saved.authority === 'trusted' && saved.intact === true
  && ['analysis', 'continuation', 'outcome', 'effects'].every(key => saved[key] === review[key])
  && JSON.stringify([...saved.base].sort()) === JSON.stringify([...review.base].sort())
  && JSON.stringify(saved.candidates) === JSON.stringify(review.candidates) && JSON.stringify(saved.dependencies) === JSON.stringify(review.dependencies)
  && JSON.stringify(saved.questions) === JSON.stringify(review.questions) && JSON.stringify(withoutLinkRow(saved.inputs)) === JSON.stringify(review.inputs);

export async function completeDependencyIntake({ cwd = '', request, analysis }, ports = {}) {
  ports = createDependencyReadPorts({ cwd }, ports);
  if (!exact(request, ['id','repository','issues','snapshotJson','contextJson']) || !request.id || typeof request.repository !== 'string' || !strings(request.issues) || new Set(request.issues).size !== request.issues.length || !(exact(analysis, ['reviews','impactJson']) || exact(analysis, ['reviews','impactJson','sorts'])) || !Array.isArray(analysis.reviews) || typeof analysis.impactJson !== 'string') throw invalidAnalysis();
  for (const r of analysis.reviews) if (!exact(r, ['analysis','base','continuation','issue','inputs','candidates','outcome','dependencies','questions','effects']) || typeof r.analysis !== 'string' || !r.analysis || !strings(r.base) || typeof r.continuation !== 'string' || typeof r.issue !== 'string' || !validRows(r.inputs) || !validRows(r.candidates) || !Array.isArray(r.dependencies) || !r.dependencies.every(d => exact(d, ['key','reason','evidence']) && typeof d.key === 'string' && typeof d.reason === 'string' && strings(d.evidence)) || !strings(r.questions)) throw invalidAnalysis();
  const prepared = json(request.snapshotJson); const context = json(request.contextJson);
  if (prepared.repository.toLowerCase() !== request.repository.toLowerCase()) throw invalidAnalysis();
  if (context.reviewOwner !== undefined && (!exact(context.reviewOwner, ['coordinatorId','machine']) || typeof context.reviewOwner.coordinatorId !== 'string' || !context.reviewOwner.coordinatorId || typeof context.reviewOwner.machine !== 'string')) throw invalidAnalysis();
  const original = analysis;
  // Code owns each subject's link row: drop a carried copy and add the current one before saving.
  const links = (snapshot, issue, dependencies) => { try { return dependencyLinks({ snapshot, issue, dependencies }); } catch { throw invalidAnalysis(); } };
  analysis = { ...analysis, reviews: analysis.reviews.map(r => ({ ...r, inputs: r.inputs.filter(x => !/#dependencies$/i.test(x.key)) })) };
  const extra = [...(prepared.inputs || []).filter(x => !/#(?:autopilot-areas|sort-labels)$/.test(x.key)), ...(analysis.sorts ?? []).flatMap(r => r.inputs ?? []).filter(x => !/#(?:autopilot-areas|sort-labels)$/.test(x.key) && !prepared.issues.some(i => i.key === x.key)), ...analysis.reviews.flatMap(r => r.inputs || []).filter(x => !prepared.issues.some(i => i.key === x.key))];
  const inputMap = new Map(extra.map(x => [x.key, x]));
  const args = { cwd, repository: request.repository }; if (inputMap.size) args.inputs = [...inputMap.values()];
  // Each pending result is kept as a note, so a later delivery of these subjects can name its reason. A pending result
  // that a later call can finish keeps its request and analysis; any other result ends the kept completion.
  const results = resultsPort(cwd, ports), kept = keptFor(ports, request.repository);
  const finish = async result => {
    if (result.state === 'pending' && result.reason === 'observations-incomplete' && (ports.githubFloor?.stopped || ports.githubFloor?.blocked?.('core'))) result = { ...result, reason: 'github-limit' };
    if (result.state === 'pending' && results) try { await results.save({ repository: request.repository, json: JSON.stringify({ request: request.id, reason: result.reason, rows: result.rows ?? [] }) }); } catch { /* The note is optional. */ }
    if (kept) try {
      if (result.state === 'pending' && RESUMABLE.includes(result.reason)) {
        const prior = await kept.read();
        await kept.save({ request, analysis: original, reason: result.reason, attempts: prior?.request?.id === request.id ? (prior.attempts ?? 0) + 1 : 1 });
      } else { const prior = await kept.read(); if (!prior || prior.request?.id === request.id) await kept.clear(); }
    } catch { /* A lost kept completion only means a new analysis later. */ }
    return result;
  };
  let snapshot;
  try { ({ snapshot } = await snapshotRead(ports, args)); } catch { return finish(pendingResult('observations-incomplete')); }
  // Saved intents need no duplicate append; their pending effects still need confirmation.
  const savedIds = new Map();
  for (const review of analysis.reviews) {
    const saved = snapshot.reviews.find(r => !prepared.reviews.some(p => p.id === r.id) && sameReview(r, review));
    if (saved) savedIds.set(review.issue, saved.id);
  }
  const subjects = request.issues.filter(key => !savedIds.has(key)), remaining = analysis.reviews.filter(r => !savedIds.has(r.issue));
  if (request.issues.some(key => snapshot.issues.find(i => i.key === key)?.holds?.includes('pdd:manual'))) return finish(pendingResult('input-changed'));
  if (request.issues.length && !subjects.length && analysis.reviews.length === request.issues.length
    && analysis.reviews.every(r => r.effects !== 'pending' || !r.dependencies.length)) {
    const questions = analysis.reviews.flatMap(r => r.questions);
    return finish({ state: questions.length ? 'question' : 'complete', reviewIds: analysis.reviews.map(r => savedIds.get(r.issue)), eligible: [], questions });
  }
  const current = rows(snapshot); const prior = rows(prepared);
  const relevantIncomplete = value => { try { const graph = projectIssueGraph({ snapshot: value }); return (!value.complete && !request.issues.length) || subjects.some(key => { const node = graph.nodes.find(n => n.key === issueKey(key)); return !node || node.reasons.includes('Incomplete relevant observations'); }); } catch { return true; } };
  // Check only what freshness tracks: the rows the reviews used, the subjects, their
  // heads and links, and named prerequisites in the root repository. A change
  // elsewhere (an unrelated input, or a prerequisite in another repository, where
  // only open or closed matters) must not hold the result.
  if (relevantIncomplete(prepared) || relevantIncomplete(snapshot)) return finish(pendingResult('observations-incomplete'));
  const currentRow = row => ({ key: row.key, revision: current.get(row.key) ?? '' });
  const changedSubjects = subjects.filter(k => !prior.has(k) || current.get(k) !== prior.get(k) || snapshot.issues.find(i => i.key === k)?.authority !== 'trusted');
  if (changedSubjects.length) return finish(pendingResult('input-changed', { rows: changedSubjects.map(key => currentRow({ key })) }));
  // A used row whose revision is not the prepared one is the answer's error; a
  // prepared or extra examined row that differs now is a change after prepare.
  const used = remaining.flatMap(r => r.inputs).filter(x => current.get(x.key) !== x.revision);
  const miscopied = used.filter(x => prior.has(x.key) && prior.get(x.key) !== x.revision);
  if (miscopied.length) return finish(pendingResult('answer-row-mismatch', { rows: miscopied.map(x => ({ key: x.key, revision: prior.get(x.key) })) }));
  if (used.length) return finish(pendingResult('input-changed', { rows: used.map(currentRow) }));
  // Only the subjects' own heads and the issues their reviews name must be
  // unchanged. A new or edited unrelated issue or review does not matter.
  const subjectHeads = value => headIds(value).filter(id => subjects.includes(value.reviews.find(r => r.id === id)?.issue));
  if (subjectHeads(prepared).join('\0') !== subjectHeads(snapshot).join('\0')) return finish(pendingResult('input-changed'));
  const rootNamed = k => k && root(k, request.repository) && prior.has(k);
  const named = remaining.flatMap(r => r.dependencies.map(d => issueKey(d.key))).filter(k => rootNamed(k) && current.get(k) !== prior.get(k));
  if (named.length) return finish(pendingResult('input-changed', { rows: named.map(key => currentRow({ key })) }));
  // A link change to or from a subject after prepare means its analysis saw old links.
  const relinked = subjects.map(k => links(snapshot, k).row).filter((row, i) => links(prepared, subjects[i]).row.revision !== row.revision);
  if (relinked.length) return finish(pendingResult('input-changed', { rows: relinked }));
  const ownershipSubjects = [...new Set([...subjects, ...analysis.reviews.filter(r => r.effects === 'pending' && r.dependencies.length).map(r => r.issue)])];
  let owners;
  try { owners = ownershipSubjects.length ? json((await ports.owners.read({ repository: request.repository, issues: ownershipSubjects })).json) : { claims: [] }; }
  catch { return finish(pendingResult('observations-incomplete')); }
  if (!sameReviewOwner(context.reviewOwner, owners) || ownershipSubjects.some(k => ownedElsewhere(owners, k))) return finish(pendingResult('owner-changed'));
  const impact = analysis.impactJson ? json(analysis.impactJson) : null;
  if (impact && (!exact(impact, ['inputs','reviews','affected','complete']) || !validRows(impact.inputs) || !strings(impact.reviews) || !strings(impact.affected) || typeof impact.complete !== 'boolean' || !sameRows(impact.inputs, current))) throw invalidAnalysis();
  if (impact && !request.issues.length) throw invalidAnalysis();
  if (analysis.reviews.length !== request.issues.length || new Set(analysis.reviews.map(r => r.issue)).size !== request.issues.length || analysis.reviews.some(r => !request.issues.includes(r.issue))) throw invalidAnalysis();
  const candidates = prepared.issues.filter(x => root(x.key, request.repository)).map(x => ({ key: x.key, revision: x.revision }));
  // Impact is optional: each subject answers only what it needs first.
  const priorHeads = headIds(prepared), proposed = structuredClone(snapshot);
  for (const review of remaining) {
    const base = priorHeads.filter(id => prepared.reviews.find(r => r.id === id)?.issue === review.issue);
    const required = [{ key: review.issue, revision: prior.get(review.issue) }, ...(context.source || []).filter(x => x.issues.includes(review.issue)), ...(context.requirements || []).filter(x => x.issue === review.issue && x.authority === 'trusted')];
    // The answer must copy the request's base, candidates and required rows exactly; name each one it missed.
    const given = new Map(review.candidates.map(x => [x.key, x.revision])), inputs = new Map(review.inputs.map(x => [x.key, x.revision]));
    const mismatch = [...(base.length !== review.base.length || !base.every(id => review.base.includes(id)) ? [{ key: `${review.issue}#base`, revision: JSON.stringify(base.slice().sort()) }] : []),
      ...candidates.filter(x => given.get(x.key) !== x.revision), ...review.candidates.filter(x => !candidates.some(c => c.key === x.key)).map(x => ({ key: x.key, revision: '' })),
      ...required.filter(x => inputs.get(x.key) !== x.revision)];
    if (mismatch.length) return finish(pendingResult('answer-row-mismatch', { rows: mismatch.map(({ key, revision }) => ({ key, revision })) }));
    // A person's removal of a link is authoritative: a review records a question instead of adding it back.
    const { removed } = links(snapshot, review.issue);
    if (review.dependencies.some(d => removed.includes(issueKey(d.key)))) throw invalidAnalysis();
    if ((review.outcome === 'pending' && !review.dependencies.length) || (review.outcome === 'question' && (review.dependencies.length || review.effects !== 'none')) || (review.dependencies.length && (review.outcome !== 'pending' || review.effects !== 'pending')) || (!review.dependencies.length && review.effects !== 'none') || !['complete','question','pending'].includes(review.outcome) || !Array.isArray(review.dependencies) || !Array.isArray(review.questions) || (review.outcome === 'complete' && review.questions.length) || review.dependencies.some(d => !d.reason?.trim() || !Array.isArray(d.evidence) || !d.evidence.length)) throw invalidAnalysis();
    for (const dependency of review.dependencies) { const decision = validateDependencyChange({ snapshot: proposed, dependent: review.issue, blocker: dependency.key }); if (!decision.allowed && decision.reason !== 'duplicate') throw invalidAnalysis(); if (decision.allowed) proposed.edges.push({ dependent: review.issue, blocker: dependency.key }); }
    // The proposed state holds this intent, so its links are PDD links in every saved link row.
    if (review.dependencies.length) proposed.reviews.push({ ...review, id: '', authority: 'trusted', intact: true });
  }
  // #3053: validate all sorts after ordinary review validation, before effects.
  let sorts;
  try { sorts = validateSortBatch({ snapshot, prepared, issues: request.issues, sorts: analysis.sorts }); }
  catch (error) { if (error.message === 'input-changed') return finish(pendingResult('input-changed')); throw error; }
  if (prepared.sortContext && !['auto','observe'].includes((await ports.settings.read({ cwd, repository: request.repository })).mode)) return finish(pendingResult('input-changed'));
  // Persist fully validated impact before unrelated per-subject saves/effects.
  // Exact current local-host records make normal retries append-free.
  const impactIssue = request.issues[0];
  if (impact && !snapshot.impacts.some(saved => sameImpactRecord(saved, impactIssue, impact))) {
    const saved = await (ports.reviews?.saveImpact ?? saveDependencyImpact)({ repository: request.repository, issue: impactIssue, impact }, ports);
    if (saved.state !== 'saved') return finish(pendingResult('write-unconfirmed', { stage: 'impact-save', issue: impactIssue }));
  }
  const ids = []; const questions = [];
  for (const review of analysis.reviews) {
    let id = savedIds.get(review.issue);
    if (!id) {
      // The link row holds the subject's links after this request's validated additions.
      const saved = { ...review, inputs: [...review.inputs, links(proposed, review.issue, review.dependencies).row] };
      const result = await (ports.reviews?.save ?? saveDependencyReview)({ repository: request.repository, issue: review.issue, review: saved }, ports);
      if (result.state !== 'saved' || !result.id) return finish(pendingResult('write-unconfirmed', { stage: 'review-save', issue: review.issue, reviewIds: ids, questions }));
      id = result.id;
    }
    ids.push(id); questions.push(...review.questions);
    if (review.effects === 'pending' && review.dependencies.length) {
      if (savedIds.has(review.issue)) {
        const node = projectIssueGraph({ snapshot }).nodes.find(n => n.key === review.issue);
        const head = snapshot.reviews.find(r => r.id === node?.review && r.authority === 'trusted' && r.intact);
        if (head?.continuation === id && head.outcome === 'complete' && head.effects === 'confirmed') continue;
        if (head?.base.includes(id) && head.outcome === 'question') { ids.push(head.id); questions.push(...head.questions); continue; }
      }
      const applied = await (ports.reviews?.apply ?? applyDependencyChanges)({ cwd, repository: request.repository, issue: review.issue, reviewId: id }, ports);
      // A refused write (a person removed the link, or it closes a cycle) ends as one saved question.
      if (applied.state === 'question') { if (applied.reviewId) ids.push(applied.reviewId); questions.push(...(applied.questions ?? [])); continue; }
      if (applied.state !== 'confirmed') return finish(pendingResult('write-unconfirmed', { stage: 'edge-confirmation', issue: review.issue, reviewIds: ids, questions }));
    }
  }
  // The saved snapshot takes the new reviews now, so the next request comes from it without another full observation.
  if (analysis.reviews.length && ports.dependencyReads?.stored(request.repository) && !ports.snapshots) {
    try { await snapshotRead(ports, { cwd, repository: request.repository }); } catch { /* The next tick reads the changes. */ }
  }
  // #3053: one paced effect stream; route only after complete validation.
  if (prepared.sortContext) {
    try {
      const write = pacedSortWrites(ports, { cwd, repository: request.repository });
      await saveSortBatch({ repository: request.repository, snapshot, sorts }, ports, write);
      const settings = await ports.settings.read({ cwd, repository: request.repository });
      await syncSortGroups({ cwd, repository: request.repository, snapshot, mode: settings.mode }, ports, write);
      await syncMixedParts({ cwd, repository: request.repository, snapshot, mode: settings.mode }, ports, write);
      await routeSortIssues({ cwd, repository: request.repository, snapshot, mode: settings.mode }, ports, write);
    } catch { return finish(pendingResult('write-unconfirmed', { stage: 'sort', reviewIds: ids, questions })); }
  }
  return finish({ state: questions.length ? 'question' : 'complete', reviewIds: ids, eligible: [], questions });
}

export async function reconcileDependencyIntake({ cwd = '', repository, trigger, mode }, ports = {}) {
  ports = createDependencyReadPorts({ cwd }, ports);
  const reads = ports.dependencyReads;
  // A completion, an idle wake or a worker yield soon after the last full observation reads no issue list: it
  // delivers the next request from the saved snapshot. Other triggers read what changed.
  const saved = trigger === 'completion' && !ports.snapshots && !!reads?.recentList(repository, SAVED_FRESH);
  let snapshot;
  if (saved) reads.savedList = true;
  try { ({ snapshot } = await snapshotRead(ports, { cwd, repository })); } finally { if (saved) reads.savedList = false; }
  const pending = (ports.pending ? json((await ports.pending.read({ repository })).json || '{}') : {}) || {};
  if (mode === 'off') return { queued: [], eligible: [], skipped: [], pending: false };
  // A completion that stopped (a failed read, a lost write or the GitHub limit) is finished first, without a new analysis.
  if (await resumeCompletion({ cwd, repository }, ports)) ({ snapshot } = await snapshotRead(ports, { cwd, repository }));
  if (!ports.snapshots && reads?.owners?.repository === repository.toLowerCase() && reads.owners.json === null)
    return { queued: [], eligible: [], skipped: [], pending: true, claims: [] };
  // #3053: current records can finish a route without another semantic call.
  if (snapshot.sortContext) {
    try {
      const write = pacedSortWrites(ports, { cwd, repository });
      await syncSortGroups({ cwd, repository, snapshot, mode }, ports, write);
      await syncMixedParts({ cwd, repository, snapshot, mode }, ports, write);
      await routeSortIssues({ cwd, repository, snapshot, mode }, ports, write);
    }
    catch { /* Unconfirmed effects wait; graph holds routed issues. */ }
  }
  let graph = projectIssueGraph({ snapshot });
  const subjects = graph.nodes.filter(n => root(n.key, repository) && n.nativeState === 'open' && !snapshot.issues.find(i => i.key === n.key)?.holds?.includes('pdd:manual')).map(n => n.key);
  // The claim scan of the snapshot gives the claims: the open issues are not read again.
  const owners = subjects.length ? json((await ownersFor(ports, repository, subjects)).json) : { claims: [] };
  const skipped = subjects.filter(x => ownedElsewhere(owners, x));
  let recovered = false;
  for (const node of graph.nodes) {
    const review = snapshot.reviews.find(r => r.id === node.review);
    if (!skipped.includes(node.key) && !node.reasons.includes('Incomplete relevant observations') && node.reviewState === 'pending' && review?.effects === 'pending') {
      await (ports.reviews?.apply ?? applyDependencyChanges)({ cwd, repository, issue: node.key, reviewId: review.id }, ports); recovered = true;
    }
  }
  if (recovered) { ({ snapshot } = await snapshotRead(ports, { cwd, repository })); graph = projectIssueGraph({ snapshot }); }
  const candidates = selectSubjects(graph, snapshot, repository);
  const incomplete = candidates.filter(n => n.reasons.includes('Incomplete relevant observations'));
  const queued = candidates.filter(n => !skipped.includes(n.key) && !n.reasons.includes('Incomplete relevant observations')).map(n => n.key);
  const eligible = graph.nodes.filter(n => subjects.includes(n.key) && !skipped.includes(n.key) && n.eligible).map(n => n.key);
  // The observed winning claims, with heartbeat and expiry facts, for the tick.
  const claims = Array.isArray(owners.claims) ? owners.claims : [];
  if (!queued.length || !ports.pending) return { queued, eligible, skipped, pending: Boolean(queued.length || incomplete.length), claims, groups: snapshot.sortContext ? sortPlan({ snapshot }).groups : [] };
  const prepared = await prepareDependencyIntake({ cwd, repository }, { ...ports, snapshots: { read: async () => ({ snapshot }) }, owners: { read: async () => ({ json: JSON.stringify(owners) }) } });
  const order = a => a.slice().sort((x,y) => x.key.localeCompare(y.key) || x.revision.localeCompare(y.revision));
  const selectedSnapshot = JSON.parse(prepared.request.snapshotJson);
  const context = JSON.parse(prepared.request.contextJson);
  const relevant = new Set([...(context.source || []).filter(x => x.issues?.some(i => prepared.queued.includes(i))).map(x => x.key), ...(context.requirements || []).filter(x => prepared.queued.includes(x.issue)).map(x => x.key), ...selectedSnapshot.reviews.filter(r => prepared.queued.includes(r.issue)).flatMap(r => r.inputs.map(x => x.key))]);
  const linkRows = prepared.queued.map(issue => dependencyLinks({ snapshot: selectedSnapshot, issue }).row);
  const fingerprint = JSON.stringify({ repository: repository.toLowerCase(), reviewOwner: context.reviewOwner ?? null, issues: prepared.queued.slice().sort(), inputs: order([...selectedSnapshot.inputs.filter(x => relevant.has(x.key)), ...selectedSnapshot.issues.filter(i => root(i.key, repository)).map(i => ({ key: i.key, revision: i.revision })), ...linkRows]), heads: headIds(selectedSnapshot), sort: sortRequestFingerprint(selectedSnapshot, prepared.queued) });
  const now = Date.parse((await ports.clock.now({})).iso), subjectSet = JSON.stringify(prepared.queued.slice().sort());
  const save = async () => (await ports.pending.save({ repository, json: JSON.stringify(pending) })).ok;
  // One delivery through the existing route. `redelivery` marks a repeated request
  // while it is sent, so the launcher can name it and refuse it under uncertain custody.
  const send = async again => {
    // Snapshot ownership can predate a restart or takeover. Check before AI work.
    try {
      const live = json((await ports.owners.read({ repository, issues: prepared.queued })).json);
      if (!sameReviewOwner(context.reviewOwner, live) || prepared.queued.some(key => ownedElsewhere(live, key))) return false;
    } catch { return false; }
    pending.requested = fingerprint;
    if (again) pending.redelivery = again; else delete pending.redelivery;
    if (!await save()) return false;
    const delivered = await ports.pending.deliver({ repository, requestJson: JSON.stringify(prepared.request) });
    delete pending.redelivery;
    if (delivered.state === 'delivered') {
      if (pending.subjects !== subjectSet) pending.redelivered = 0;
      Object.assign(pending, { delivered: fingerprint, request: prepared.request.id, deliveredAt: now, subjects: subjectSet });
      if (again) pending.redelivered = again.attempt;
    }
    await save();
    return delivered.state === 'delivered';
  };
  if (fingerprint !== pending.delivered || trigger === 'refresh') {
    if (!await send(null)) return { queued, eligible, skipped, pending: true, claims, groups: snapshot.sortContext ? sortPlan({ snapshot }).groups : [] };
  } else if (pending.subjects !== subjectSet || !Number.isFinite(pending.deliveredAt)) {
    // A delivery saved without its time or subjects: the wait starts now.
    Object.assign(pending, { subjects: subjectSet, deliveredAt: now, redelivered: 0 });
    await save();
  } else if (now - pending.deliveredAt >= AGAIN_AFTER) {
    // The same subjects are still unchecked or stale and nothing changed: the last
    // completion was pending, or it never came. Deliver the fresh request again.
    const last = await lastResult(ports, cwd, repository, pending.request);
    const count = pending.redelivered ?? 0;
    if (count < AGAIN_CAP) {
      if (!await send({ attempt: count + 1, cap: AGAIN_CAP, ...last })) return { queued, eligible, skipped, pending: true, claims, groups: snapshot.sortContext ? sortPlan({ snapshot }).groups : [] };
    }
    else if (await askAfterCap({ repository, request: prepared.request, snapshot: selectedSnapshot, context, last }, ports)) {
      for (const key of ['subjects', 'redelivered', 'deliveredAt']) delete pending[key];
      await save();
    }
  }
  return { queued, eligible, skipped, pending: Boolean(incomplete.length || pending.requested !== pending.delivered), claims, groups: snapshot.sortContext ? sortPlan({ snapshot }).groups : [] };
}

// Finish a kept completion: the same request and analysis, with the reviews that are already saved skipped. True when
// it saved or ended something, so the caller reads the snapshot again. An invalid or foreign kept value is removed.
async function resumeCompletion({ cwd, repository }, ports) {
  const kept = keptFor(ports, repository);
  if (!kept) return false;
  let value;
  try { value = await kept.read(); } catch { return false; }
  if (!value) return false;
  const drop = async () => { try { await kept.clear(); } catch { /* removed later */ } return false; };
  if (!value.request || !value.analysis || String(value.request.repository).toLowerCase() !== repository.toLowerCase()) return drop();
  if (ports.admitEffect && !await ports.admitEffect()) return false;
  try {
    const result = await completeDependencyIntake({ cwd, request: value.request, analysis: value.analysis }, ports);
    return result.state !== 'pending' || (result.reviewIds ?? []).length > 0;
  } catch { return drop(); }
}

// The reason of the last completion of the delivered request, from the note that
// completion kept. Only known reasons and plain issue or file locators are used.
async function lastResult(ports, cwd, repository, id) {
  try {
    const results = resultsPort(cwd, ports), saved = results && json((await results.read({ repository })).json || '{}');
    if (saved?.request === id && REASONS.includes(saved.reason)) {
      const rows = (Array.isArray(saved.rows) ? saved.rows : []).filter(x => typeof x?.key === 'string' && /^https:\/\/github\.com\/[^\s]{1,300}$/.test(x.key) && typeof x.revision === 'string').slice(0, 20);
      return { reason: saved.reason, rows: rows.map(({ key, revision }) => ({ key, revision })) };
    }
  } catch { /* Without a readable note the reason is unknown. */ }
  return { reason: 'not-completed', rows: [] };
}

// After the cap, each subject gets one visible question through the ordinary
// question review. A person's answer makes the question stale, so the issue is
// reviewed again; until then nothing is delivered again.
async function askAfterCap({ repository, request, snapshot, context, last }, ports) {
  const shown = last.rows.slice(0, 5).map(x => x.key).join(', ') + (last.rows.length > 5 ? ` and ${last.rows.length - 5} more` : '');
  const candidates = snapshot.issues.filter(i => root(i.key, repository)).map(({ key, revision }) => ({ key, revision }));
  for (const issue of request.issues) {
    const text = `PDD sent the dependency review of ${issue} ${AGAIN_CAP + 1} times, and it did not finish. Last reason: ${last.reason}${shown ? ` (${shown})` : ''}. Which open issues must ${issue} wait for? Answer "none" if it needs no other issue first.`;
    const inputs = [...new Map([{ key: issue, revision: snapshot.issues.find(i => issueKey(i.key) === issue)?.revision ?? '' },
      ...(context.source || []).filter(x => x.issues?.includes(issue)), ...(context.requirements || []).filter(x => x.issue === issue),
      dependencyLinks({ snapshot, issue }).row].map(({ key, revision }) => [key, { key, revision }])).values()];
    const review = { analysis: `The automatic dependency review of ${issue} did not finish after ${AGAIN_CAP} repeated deliveries.`,
      base: headIds(snapshot).filter(id => snapshot.reviews.find(r => r.id === id)?.issue === issue), continuation: '', issue, inputs, candidates,
      outcome: 'question', dependencies: [], questions: [text], effects: 'none' };
    if (ports.admitEffect && !await ports.admitEffect()) return false;
    let saved;
    try { saved = await (ports.reviews?.save ?? saveDependencyReview)({ repository, issue, review }, ports); } catch { return false; }
    if (saved.state !== 'saved') return false;
  }
  return true;
}

export async function runDependencyIntake({ command, cwd = '', issue, stdin }, ports = {}) {
  try {
    let result;
    if (command === 'prepare') {
      const repo = ports.repository?.read ? await ports.repository.read({ cwd }) : (await promisify(nodeExecFile)('gh', ['repo', 'view', '--json', 'nameWithOwner', '--jq', '.nameWithOwner'], { cwd })).stdout.trim();
      const repository = typeof repo === 'string' ? repo : repo.repository;
      const githubFloor = await commandGithubFloor({ cwd, repository }, ports);
      result = await prepareDependencyIntake({ cwd, repository, issue }, githubFloor ? { ...ports, githubFloor } : ports);
    } else if (command === 'complete') {
      const input = json(stdin); if (!input || Object.keys(input).sort().join(',') !== 'analysis,request') throw Error('invalid-input');
      // Below the floor of an Autopilot repository, the command's non-safety reads stop and its analysis is kept.
      const githubFloor = await commandGithubFloor({ cwd, repository: input.request?.repository }, ports);
      result = await completeDependencyIntake({ cwd, ...input }, githubFloor ? { ...ports, githubFloor } : ports);
    } else throw Error('invalid-input');
    return { exitCode: 0, message: JSON.stringify(result) + '\n' };
  } catch (error) { return { exitCode: 2, message: `${error.message}\n` }; }
}
