import { randomUUID } from 'node:crypto';
import { execFile as nodeExecFile } from 'node:child_process';
import { promisify } from 'node:util';
import { projectIssueGraph, validateDependencyChange } from './issue-dependencies.mjs';
import { createDependencyReadPorts, readDependencySnapshot, saveDependencyReview, saveDependencyImpact, applyDependencyChanges } from './issue-dependencies-github.mjs';

const snapshotRead = (ports, args) => ports.snapshots?.read ? ports.snapshots.read(args) : readDependencySnapshot(args, ports);
const root = (key, repository) => key.toLowerCase().startsWith(`https://github.com/${repository.toLowerCase()}/issues/`);
// Apply the shared model's canonical GitHub issue identity at this boundary.
const issueKey = value => {
  const m = /^https:\/\/github\.com\/([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)\/issues\/([1-9][0-9]*)\/?$/.exec(value ?? '');
  return m ? `https://github.com/${m[1].toLowerCase()}/issues/${m[2]}` : null;
};
const json = value => typeof value === 'string' ? JSON.parse(value) : value;
const rows = snapshot => new Map([...snapshot.issues.map(x => [x.key, x.revision]), ...snapshot.inputs.map(x => [x.key, x.revision])]);
const sameRows = (a, b) => a.every(x => b.get(x.key) === x.revision);
const ownedElsewhere = (owners, issue) => (owners.claims || []).some(x => x.issue === issue && x.active && (!x.owner || x.owner !== owners.localOwner));
const exact = (obj, keys) => obj && typeof obj === 'object' && !Array.isArray(obj) && Object.keys(obj).sort().join(',') === keys.slice().sort().join(',');
const strings = a => Array.isArray(a) && a.every(x => typeof x === 'string');
const validRows = a => Array.isArray(a) && a.every(x => exact(x, ['key','revision']) && typeof x.key === 'string' && typeof x.revision === 'string' && x.key && x.revision) && new Set(a.map(x => x.key)).size === a.length;
const invalidAnalysis = () => Object.assign(new Error('invalid-analysis'), { code: 'invalid-analysis' });
const pendingResult = (pendingStage, pendingIssue, reviewIds = [], questions = []) => ({
  state: 'pending', reviewIds, eligible: [], questions,
  ...(pendingStage ? { pendingStage } : {}), ...(pendingIssue ? { pendingIssue } : {}),
});
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
  copy.issues = copy.issues.map(issue => issue.authority === 'trusted' ? issue : {
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
    const [settings, read, ownerReply] = await Promise.all([
      ports.settings.read({ cwd, repository }), snapshotRead(ports, { cwd, repository }), ports.owners.read({ repository, issues: [issue] })
    ]);
    const owners = json(ownerReply.json); const snapshot = read.snapshot;
    if (settings.mode === 'off') return { allowed: false, reason: 'off' };
    const key = issueKey(issue);
    const selected = key && root(key, repository) ? key : null;
    const claim = selected && (owners.claims || []).find(x => issueKey(x.issue) === selected && x.active);
    if (!coordinator || coordinator.repository?.toLowerCase() !== repository.toLowerCase() || !coordinator.coordinatorId || owners.localOwner !== coordinator.coordinatorId || !coordinator.machine || !coordinator.claim?.commentId || !coordinator.claim?.labelEventId || !claim || claim.owner !== coordinator.coordinatorId || claim.coordinatorId !== coordinator.coordinatorId || claim.machine !== coordinator.machine || claim.commentId !== coordinator.claim.commentId || claim.labelEventId !== coordinator.claim.labelEventId) return { allowed: false, reason: 'owner' };
    if (settings.activation !== coordinator.activation || settings.runs !== coordinator.runs) return { allowed: false, reason: 'stale' };
    if (owners.runsKnown !== true || !Array.isArray(owners.runs)) return { allowed: false, reason: 'runs' };
    const occupied = owners.runs.filter(run => !(['waiting', 'paused', 'stuck', 'question'].includes(run.state) && run.occupied === false));
    if (settings.runs !== undefined) {
      if (!Number.isSafeInteger(settings.runs) || settings.runs < 1) return { allowed: false, reason: 'runs' };
      const slots = new Map();
      for (const run of occupied) {
        slots.set(run.runId || run.issue, run);
      }
      if (slots.size + ([...slots.values()].some(x => selected && issueKey(x.issue) === selected) ? 0 : 1) > settings.runs) return { allowed: false, reason: 'runs' };
    }
    if (occupied.some(run => selected && issueKey(run.issue) === selected)) return { allowed: false, reason: 'dependency' };
    const copy = structuredClone(snapshot); const subject = copy.issues.find(x => selected && issueKey(x.key) === selected);
    if (subject && subject.executionClaim?.coordinatorId === claim.coordinatorId && subject.executionClaim?.commentId === claim.commentId && subject.executionClaim?.labelEventId === claim.labelEventId) {
      subject.execution = 'idle'; subject.holds = subject.holds.filter(x => !/^(running|claim|claimed)$/i.test(x));
    }
    const node = projectIssueGraph({ snapshot: copy }).nodes.find(x => selected && issueKey(x.key) === selected);
    if (!node || node.reasons.includes('Incomplete relevant observations')) return { allowed: false, reason: 'unknown' };
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

function selectSubjects(graph, snapshot, repository, issue) {
  let selected = graph.nodes.filter(x => root(x.key, repository) && x.nativeState === 'open' && (issue ? x.key === issue || x.key.endsWith(`/issues/${issue}`) : ['unchecked', 'stale'].includes(x.reviewState)));
  // An unchanged review with only candidate coverage missing is covered by impact of new subjects.
  selected = selected.filter(x => {
    if (issue || x.reviewState !== 'stale') return true;
    const old = snapshot.reviews.find(r => r.id === x.review) ?? null;
    const affected = old && snapshot.impacts.some(i => i.complete && i.intact && i.trusted && i.reviews.includes(old.id) && i.affected.includes(x.key) && sameRows(i.inputs, rows(snapshot)));
    return !old || affected || !sameRows(old.inputs, rows(snapshot));
  });
  return selected;
}

// A bounded fallback gives unchanged stale heads a normal impact producer when
// all ordinary subjects are unavailable; it does not change graph readiness.
function impactFallback(graph, snapshot, repository) {
  const current = rows(snapshot);
  return graph.nodes.filter(node => {
    if (!root(node.key, repository) || node.nativeState !== 'open' || node.reviewState !== 'stale' || node.executionState !== 'idle' || node.facts.length || node.reasons.includes('Incomplete relevant observations')) return false;
    const issue = snapshot.issues.find(item => item.key === node.key), review = snapshot.reviews.find(item => item.id === node.review);
    if (issue?.authority !== 'trusted' || !Array.isArray(issue.assignees) || issue.assignees.length || !review || review.outcome !== 'complete' || review.questions?.length || !sameRows(review.inputs, current)) return false;
    const candidates = new Map(review.candidates.map(row => [row.key, row.revision]));
    return snapshot.issues.some(item => root(item.key, repository) && item.state !== 'unknown' && candidates.get(item.key) !== item.revision);
  });
}
function availableSubjects(graph, snapshot, repository, issue, owners) {
  const ordinary = selectSubjects(graph, snapshot, repository, issue);
  if (issue || ordinary.some(node => node.executionState === 'idle' && !(owners.claims ?? []).some(claim => claim.issue === node.key && claim.active) && !node.reasons.includes('Incomplete relevant observations'))) return ordinary;
  const fallback = impactFallback(graph, snapshot, repository).find(node => !(owners.claims ?? []).some(claim => claim.issue === node.key && claim.active));
  return fallback ? [...ordinary, fallback] : ordinary;
}

export async function prepareDependencyIntake({ cwd = '', repository, issue }, ports = {}) {
  ports = createDependencyReadPorts({ cwd }, ports);
  const observed = await snapshotRead(ports, { cwd, repository });
  const snapshot = observed.snapshot;
  const graph = projectIssueGraph({ snapshot });
  const candidates = selectSubjects(graph, snapshot, repository, issue);
  const fallback = issue ? [] : impactFallback(graph, snapshot, repository);
  const ownerKeys = [...new Set([...candidates, ...fallback].map(node => node.key))];
  let owners = { claims: [] }; if (ownerKeys.length) owners = json((await ports.owners.read({ repository, issues: ownerKeys })).json);
  const selected = availableSubjects(graph, snapshot, repository, issue, owners);
  const skipped = selected.filter(x => x.reasons.includes('Incomplete relevant observations') || ownedElsewhere(owners, x.key)).map(x => x.key);
  const queued = selected.filter(x => !skipped.includes(x.key)).map(x => x.key);
  const contextJson = queued.length ? (await ports.evidence.read({ cwd, repository, issues: queued })).json : JSON.stringify({ source: [], requirements: [] });
  const evidence = json(contextJson);
  if (!Array.isArray(evidence.source) || !Array.isArray(evidence.requirements) || evidence.requirements.some(x => x.authority !== 'trusted')) throw Error('invalid-input');
  const current = rows(snapshot);
  for (const item of evidence.source || []) if (item.key && item.revision) { const prev = current.get(item.key); if (!prev) snapshot.inputs.push({ key: item.key, revision: item.revision }); }
  return { request: { id: randomUUID(), repository, issues: queued, snapshotJson: JSON.stringify(packetSnapshot(snapshot)), contextJson }, queued, skipped };
}

export async function completeDependencyIntake({ cwd = '', request, analysis }, ports = {}) {
  ports = createDependencyReadPorts({ cwd }, ports);
  if (!exact(request, ['id','repository','issues','snapshotJson','contextJson']) || !request.id || typeof request.repository !== 'string' || !strings(request.issues) || new Set(request.issues).size !== request.issues.length || !exact(analysis, ['reviews','impactJson']) || !Array.isArray(analysis.reviews) || typeof analysis.impactJson !== 'string') throw invalidAnalysis();
  for (const r of analysis.reviews) if (!exact(r, ['analysis','base','continuation','issue','inputs','candidates','outcome','dependencies','questions','effects']) || typeof r.analysis !== 'string' || !r.analysis || !strings(r.base) || typeof r.continuation !== 'string' || typeof r.issue !== 'string' || !validRows(r.inputs) || !validRows(r.candidates) || !Array.isArray(r.dependencies) || !r.dependencies.every(d => exact(d, ['key','reason','evidence']) && typeof d.key === 'string' && typeof d.reason === 'string' && strings(d.evidence)) || !strings(r.questions)) throw invalidAnalysis();
  const prepared = json(request.snapshotJson); const context = json(request.contextJson);
  if (prepared.repository.toLowerCase() !== request.repository.toLowerCase()) throw invalidAnalysis();
  const extra = [...(prepared.inputs || []), ...analysis.reviews.flatMap(r => r.inputs || []).filter(x => !prepared.issues.some(i => i.key === x.key))];
  const inputMap = new Map(extra.map(x => [x.key, x]));
  const args = { cwd, repository: request.repository }; if (inputMap.size) args.inputs = [...inputMap.values()];
  const { snapshot } = await snapshotRead(ports, args); const current = rows(snapshot); const prior = rows(prepared);
  const relevantIncomplete = value => { try { const graph = projectIssueGraph({ snapshot: value }); return (!value.complete && !request.issues.length) || request.issues.some(key => { const node = graph.nodes.find(n => n.key === issueKey(key)); return !node || node.reasons.includes('Incomplete relevant observations'); }); } catch { return true; } };
  if (relevantIncomplete(prepared) || relevantIncomplete(snapshot) || request.issues.some(k => !prior.has(k) || current.get(k) !== prior.get(k) || snapshot.issues.find(i => i.key === k)?.authority !== 'trusted') || !sameRows([...inputMap.values()], current)) return pendingResult();
  if (headIds(prepared).join('\0') !== headIds(snapshot).join('\0')) return pendingResult();
  const currentCandidates = snapshot.issues.filter(x => root(x.key, request.repository));
  const preparedCandidates = prepared.issues.filter(x => root(x.key, request.repository));
  if (currentCandidates.length !== preparedCandidates.length || !sameRows(preparedCandidates.map(x => ({key:x.key, revision:x.revision})), current)) return pendingResult();
  const owners = request.issues.length ? json((await ports.owners.read({ repository: request.repository, issues: request.issues })).json) : { claims: [] };
  if (request.issues.some(k => ownedElsewhere(owners, k))) return pendingResult();
  const impact = analysis.impactJson ? json(analysis.impactJson) : null;
  if (impact && (!exact(impact, ['inputs','reviews','affected','complete']) || !validRows(impact.inputs) || !strings(impact.reviews) || !strings(impact.affected) || typeof impact.complete !== 'boolean' || !sameRows(impact.inputs, current))) throw invalidAnalysis();
  if (impact && !request.issues.length) throw invalidAnalysis();
  if (analysis.reviews.length !== request.issues.length || new Set(analysis.reviews.map(r => r.issue)).size !== request.issues.length || analysis.reviews.some(r => !request.issues.includes(r.issue))) throw invalidAnalysis();
  const candidates = prepared.issues.filter(x => root(x.key, request.repository)).map(x => ({ key: x.key, revision: x.revision }));
  const requiredHeads = headIds(prepared);
  if (requiredHeads.length && (!impact || !impact.complete || !requiredHeads.every(id => impact.reviews.includes(id)))) throw invalidAnalysis();
  const proposed = structuredClone(snapshot);
  for (const review of analysis.reviews) {
    const subjectHeads = requiredHeads.filter(id => prepared.reviews.find(r => r.id === id)?.issue === review.issue);
    const required = [{ key: review.issue, revision: prior.get(review.issue) }, ...(context.source || []).filter(x => x.issues.includes(review.issue)), ...(context.requirements || []).filter(x => x.issue === review.issue && x.authority === 'trusted')];
    if (subjectHeads.length !== review.base.length || !subjectHeads.every(id => review.base.includes(id)) || (review.candidates.length !== candidates.length || !sameRows(candidates, new Map((review.candidates || []).map(x => [x.key, x.revision])))) || !sameRows(required, new Map((review.inputs || []).map(x => [x.key, x.revision]))) || !sameRows(review.inputs || [], current)) return pendingResult();
    if ((review.outcome === 'question' && (review.dependencies.length || review.effects !== 'none')) || (review.dependencies.length && (review.outcome !== 'pending' || review.effects !== 'pending')) || (!review.dependencies.length && review.effects !== 'none') || !['complete','question','pending'].includes(review.outcome) || !Array.isArray(review.dependencies) || !Array.isArray(review.questions) || (review.outcome === 'complete' && review.questions.length) || review.dependencies.some(d => !d.reason?.trim() || !Array.isArray(d.evidence) || !d.evidence.length)) throw invalidAnalysis();
    for (const dependency of review.dependencies) { const decision = validateDependencyChange({ snapshot: proposed, dependent: review.issue, blocker: dependency.key }); if (!decision.allowed && decision.reason !== 'duplicate') throw invalidAnalysis(); if (decision.allowed) proposed.edges.push({ dependent: review.issue, blocker: dependency.key }); }
  }
  // Persist fully validated impact before unrelated per-subject saves/effects.
  // Exact current local-host records make normal retries append-free.
  const impactIssue = request.issues[0];
  if (impact && !snapshot.impacts.some(saved => sameImpactRecord(saved, impactIssue, impact))) {
    const saved = await (ports.reviews?.saveImpact ?? saveDependencyImpact)({ repository: request.repository, issue: impactIssue, impact }, ports);
    if (saved.state !== 'saved') return pendingResult('impact-save', impactIssue);
  }
  const ids = []; const questions = [];
  for (const review of analysis.reviews) {
    const result = await (ports.reviews?.save ?? saveDependencyReview)({ repository: request.repository, issue: review.issue, review }, ports);
    if (result.state !== 'saved' || !result.id) return pendingResult('review-save', review.issue, ids, questions);
    ids.push(result.id); questions.push(...review.questions);
    if (review.effects === 'pending' && review.dependencies.length) {
      const applied = await (ports.reviews?.apply ?? applyDependencyChanges)({ cwd, repository: request.repository, issue: review.issue, reviewId: result.id }, ports);
      if (applied.state !== 'confirmed') return pendingResult('edge-confirmation', review.issue, ids, questions);
    }
  }
  return { state: questions.length ? 'question' : analysis.reviews.some(r => r.outcome === 'pending' && r.effects !== 'pending') ? 'pending' : 'complete', reviewIds: ids, eligible: [], questions };
}

export async function reconcileDependencyIntake({ cwd = '', repository, trigger, mode }, ports = {}) {
  ports = createDependencyReadPorts({ cwd }, ports);
  let { snapshot } = await snapshotRead(ports, { cwd, repository });
  const pending = (ports.pending ? json((await ports.pending.read({ repository })).json || '{}') : {}) || {};
  if (mode === 'off') return { queued: [], eligible: [], skipped: [], pending: false };
  let graph = projectIssueGraph({ snapshot });
  const subjects = graph.nodes.filter(n => root(n.key, repository) && n.nativeState === 'open').map(n => n.key);
  const owners = subjects.length ? json((await ports.owners.read({ repository, issues: subjects })).json) : { claims: [] };
  const skipped = subjects.filter(x => ownedElsewhere(owners, x));
  let recovered = false;
  for (const node of graph.nodes) {
    const review = snapshot.reviews.find(r => r.id === node.review);
    if (!skipped.includes(node.key) && !node.reasons.includes('Incomplete relevant observations') && node.reviewState === 'pending' && review?.effects === 'pending') {
      await (ports.reviews?.apply ?? applyDependencyChanges)({ cwd, repository, issue: node.key, reviewId: review.id }, ports); recovered = true;
    }
  }
  if (recovered) { ({ snapshot } = await snapshotRead(ports, { cwd, repository })); graph = projectIssueGraph({ snapshot }); }
  const candidates = availableSubjects(graph, snapshot, repository, undefined, owners);
  const incomplete = candidates.filter(n => n.reasons.includes('Incomplete relevant observations'));
  const queued = candidates.filter(n => !skipped.includes(n.key) && !n.reasons.includes('Incomplete relevant observations')).map(n => n.key);
  const eligible = graph.nodes.filter(n => subjects.includes(n.key) && !skipped.includes(n.key) && n.eligible).map(n => n.key);
  if (!queued.length || !ports.pending) return { queued, eligible, skipped, pending: Boolean(queued.length || incomplete.length) };
  const prepared = await prepareDependencyIntake({ cwd, repository }, { ...ports, snapshots: { read: async () => ({ snapshot }) }, owners: { read: async () => ({ json: JSON.stringify(owners) }) } });
  const order = a => a.slice().sort((x,y) => x.key.localeCompare(y.key) || x.revision.localeCompare(y.revision));
  const selectedSnapshot = JSON.parse(prepared.request.snapshotJson);
  const context = JSON.parse(prepared.request.contextJson);
  const relevant = new Set([...(context.source || []).filter(x => x.issues?.some(i => prepared.queued.includes(i))).map(x => x.key), ...(context.requirements || []).filter(x => prepared.queued.includes(x.issue)).map(x => x.key), ...selectedSnapshot.reviews.filter(r => prepared.queued.includes(r.issue)).flatMap(r => r.inputs.map(x => x.key))]);
  const fingerprint = JSON.stringify({ repository: repository.toLowerCase(), issues: prepared.queued.slice().sort(), inputs: order([...selectedSnapshot.inputs.filter(x => relevant.has(x.key)), ...selectedSnapshot.issues.filter(i => root(i.key, repository)).map(i => ({ key: i.key, revision: i.revision }))]), heads: headIds(selectedSnapshot) });
  if (fingerprint !== pending.delivered || trigger === 'refresh') {
    pending.requested = fingerprint;
    const stored = await ports.pending.save({ repository, json: JSON.stringify(pending) });
    if (!stored.ok) return { queued, eligible, skipped, pending: true };
    const delivered = await ports.pending.deliver({ repository, requestJson: JSON.stringify(prepared.request) });
    if (delivered.state === 'delivered') pending.delivered = fingerprint;
    await ports.pending.save({ repository, json: JSON.stringify(pending) });
  }
  return { queued, eligible, skipped, pending: Boolean(incomplete.length || pending.requested !== pending.delivered) };
}

export async function runDependencyIntake({ command, cwd = '', issue, stdin }, ports = {}) {
  try {
    let result;
    if (command === 'prepare') {
      const repo = ports.repository?.read ? await ports.repository.read({ cwd }) : (await promisify(nodeExecFile)('gh', ['repo', 'view', '--json', 'nameWithOwner', '--jq', '.nameWithOwner'], { cwd })).stdout.trim();
      const repository = typeof repo === 'string' ? repo : repo.repository;
      result = await prepareDependencyIntake({ cwd, repository, issue }, ports);
    } else if (command === 'complete') {
      const input = json(stdin); if (!input || Object.keys(input).sort().join(',') !== 'analysis,request') throw Error('invalid-input');
      result = await completeDependencyIntake({ cwd, ...input }, ports);
    } else throw Error('invalid-input');
    return { exitCode: 0, message: JSON.stringify(result) + '\n' };
  } catch (error) { return { exitCode: 2, message: `${error.message}\n` }; }
}
