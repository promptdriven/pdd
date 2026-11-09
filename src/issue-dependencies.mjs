import { projectSortGraph } from './issue-sort.mjs';
// Generated from prompts/cli/issue-dependencies.prompt.md (sha256: 9dd1aafacf95cd2361eb7a0afc1127cfc320e5cdb1051c8f3f075398788cc196).
const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const unique = xs => [...new Set(xs)];
// The one canonical GitHub issue identity: OWNER/REPO ignores letter case.
export const issueKey = value => {
  const m = /^https:\/\/github\.com\/([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)\/issues\/([1-9][0-9]*)\/?$/.exec(value ?? '');
  return m ? `https://github.com/${m[1].toLowerCase()}/issues/${m[2]}` : null;
};
const issueRepository = value => issueKey(value)?.split('/').slice(3, 5).join('/') ?? null;
const locator = x => issueKey(x) ?? String(x).replace(/^(https:\/\/github\.com\/)([^/]+\/[^/]+)/, (_, a, b) => a + b.toLowerCase());
const coverageIssueKey = value => issueKey(typeof value === 'string' ? value.replace(/#issuecomment-[1-9][0-9]*$/, '') : value);
const rows = xs => (xs ?? []).map(x => ({ key: locator(x.key), revision: x.revision }));
const rowMap = xs => new Map(rows(xs).map(x => [x.key, x.revision]));
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const invalid = () => { throw Object.assign(Error('invalid-snapshot'), { code: 'invalid-snapshot' }); };
const LINKS = '#dependencies';

function observations(snapshot) {
  if (!object(snapshot) || typeof snapshot.repository !== 'string' || typeof snapshot.complete !== 'boolean'
    || !['issues', 'edges', 'reviews', 'impacts', 'inputs'].every(k => Array.isArray(snapshot[k]))) invalid();
  const issues = new Map();
  for (const raw of snapshot.issues) {
    const key = issueKey(raw.key);
    if (!key || !Array.isArray(raw.conditions) || !Array.isArray(raw.holds)) invalid();
    if (issues.has(key)) continue;
    issues.set(key, { ...raw, key });
  }
  const edges = [], seen = new Set();
  for (const raw of snapshot.edges) {
    const dependent = issueKey(raw.dependent), blocker = issueKey(raw.blocker);
    if (!dependent || !blocker) invalid();
    for (const key of [dependent, blocker]) if (!issues.has(key)) issues.set(key, {
      key, nodeId: '', title: key, revision: '', state: 'unknown', authority: 'unknown', conditions: [], execution: 'unknown', holds: [],
    });
    const id = `${dependent}\n${blocker}`;
    if (!seen.has(id)) { seen.add(id); edges.push({ dependent, blocker }); }
  }
  const reviews = snapshot.reviews.map(r => ({ ...r, issue: issueKey(r.issue), inputs: rows(r.inputs), candidates: rows(r.candidates),
    dependencies: (r.dependencies ?? []).map(d => ({ ...d, key: issueKey(d.key) })) }));
  return { issues, edges, reviews };
}

// Supersession depends on named identities. Comment order and timestamps have no vote.
function selectReview(records, display = false) {
  const considered = records.filter(r => r.authority !== 'outsider'), byId = new Map(considered.map(r => [r.id, r]));
  const valid = new Map(), visiting = new Set();
  function accepted(r) {
    if (valid.has(r.id)) return valid.get(r.id);
    if (visiting.has(r.id)) return false;
    visiting.add(r.id);
    let ok = (r.authority === 'trusted' || display && r.authority === 'unverified') && r.intact === true && Array.isArray(r.base)
      && ['complete', 'question', 'pending'].includes(r.outcome) && typeof r.analysis === 'string' && !!r.analysis
      && r.base.every(id => id !== r.id && byId.has(id));
    if (ok && r.continuation) {
      const intent = byId.get(r.continuation);
      ok = !!intent && intent.outcome === 'pending' && intent.effects === 'pending' && accepted(intent)
        && r.outcome === 'complete' && r.effects === 'confirmed'
        && ['analysis', 'base', 'issue', 'inputs', 'candidates', 'dependencies'].every(k => same(r[k], intent[k]));
    }
    // A replacement can explicitly resolve an edited or revoked observation,
    // but a cycle of replacements is never a resolution.
    if (ok) for (const id of r.base) {
      if (visiting.has(id)) { ok = false; break; }
      const base = byId.get(id);
      if ((base?.authority === 'trusted' || display && base?.authority === 'unverified') && base.intact && !accepted(base)) { ok = false; break; }
    }
    visiting.delete(r.id); valid.set(r.id, ok); return ok;
  }
  considered.forEach(accepted);
  const superseded = new Set();
  for (const r of considered) if (valid.get(r.id)) {
    for (const id of r.base) superseded.add(id);
    if (r.continuation) superseded.add(r.continuation);
  }
  const heads = considered.filter(r => !superseded.has(r.id));
  if (heads.some(r => !valid.get(r.id))) return { state: 'unverified', head: null, heads };
  if (heads.length > 1) return { state: 'conflict', head: null, heads };
  return { state: heads.length ? 'selected' : 'unchecked', head: heads[0] ?? null, heads };
}

function coverageRows(snapshot) {
  if (snapshot.coverage === undefined) return snapshot.complete ? null : false;
  const c = snapshot.coverage, fields = ['issue','authority','comments','blockedBy','blocking','timeline','context','execution','reviewImpact'];
  if (!object(c) || Object.keys(c).sort().join(',') !== 'issues,scope' || c.scope !== true || !Array.isArray(c.issues)) return false;
  const result = new Map();
  for (const row of c.issues) {
    const key = issueKey(row?.key);
    if (!key || result.has(key) || !object(row) || Object.keys(row).sort().join(',') !== ['key',...fields,'missing'].sort().join(',') || fields.some(k => typeof row[k] !== 'boolean') || !Array.isArray(row.missing) || row.missing.some(x => typeof x !== 'string')) return false;
    result.set(key, row);
  }
  const keys = new Set((snapshot.issues ?? []).map(issue => issueKey(issue.key)));
  if (keys.has(null) || keys.size !== result.size || [...keys].some(key => !result.has(key))) return false;
  return result;
}
function subjectCovered(key, outgoing, coverage) {
  if (coverage === null) return true;
  if (coverage === false) return false;
  const visited = new Set(), todo = [key];
  while (todo.length) {
    const current = todo.pop(); if (visited.has(current)) continue; visited.add(current);
    const row = coverage.get(current);
    if (!row || !['issue','authority','comments','blockedBy','blocking','timeline','context','execution'].every(k => row[k])) return false;
    todo.push(...(outgoing.get(current) ?? []));
  }
  return true;
}

function coverageReasons(key, outgoing, coverage, snapshot) {
  if (coverage === null) return [];
  if (coverage === false) return [snapshot.coverage?.scope === false ? 'Open issue index unavailable' : 'Observation coverage unavailable'];
  const result = [], seen = new Set(), todo = [key];
  while (todo.length) {
    const current = todo.pop(); if (seen.has(current)) continue; seen.add(current);
    const row = coverage.get(current);
    if (!row) { result.push(`Observation unavailable: issue ${current}`); continue; }
    for (const field of ['issue','authority','comments','blockedBy','blocking','timeline','context','execution'])
      if (!row[field]) result.push(`Observation unavailable: ${field} ${current}`);
    todo.push(...(outgoing.get(current) ?? []));
  }
  return result;
}

// PDD links: "D blocked by X" that a trusted, intact review of D with pending or
// confirmed effects names. PDD writes them from a review, so they are not a
// person's link change for X. A confirmed one that is now absent was removed by a
// person (PDD never removes a link).
function pddLinks(reviews) {
  const written = new Set(), confirmed = [];
  for (const r of reviews) if (r.issue && r.authority === 'trusted' && r.intact === true && ['pending', 'confirmed'].includes(r.effects))
    for (const d of r.dependencies) if (d.key) {
      written.add(`${r.issue}\n${d.key}`);
      if (r.effects === 'confirmed') confirmed.push({ dependent: r.issue, blocker: d.key });
    }
  return { written, confirmed };
}

// The link row of a review records the person-made links to and from its issue.
// The links that the review itself names are left out, so its own effects never
// change the row. A PDD link from another issue's review is left out too, so
// "B blocked by A" written for B never makes A stale. A removed named link is
// checked separately in freshness.
function linkRow(issue, edges, reviews, named = []) {
  const own = new Set(named), { written, confirmed } = pddLinks(reviews), links = [];
  for (const e of edges) {
    if (e.dependent === issue && !own.has(e.blocker)) links.push(`blocked-by ${e.blocker}`);
    if (e.blocker === issue && !written.has(`${e.dependent}\n${issue}`)) links.push(`blocking ${e.dependent}`);
  }
  for (const l of confirmed) if (l.blocker === issue && !edges.some(e => e.dependent === l.dependent && e.blocker === issue)) links.push(`blocking-removed ${l.dependent}`);
  return { key: `${issue}${LINKS}`, revision: JSON.stringify(unique(links).sort()) };
}
// A saved link row is compared without the links that are PDD links now. So a
// later review that names a link a person made does not make the other issue stale.
function savedLinkRow(revision, issue, written) {
  let list;
  try { list = JSON.parse(revision); } catch { return revision; }
  if (!Array.isArray(list)) return revision;
  return JSON.stringify(list.filter(x => !(typeof x === 'string' && x.startsWith('blocking ') && written.has(`${x.slice(9)}\n${issue}`))).sort());
}
function currentRows(head, snapshot, issues, edges, reviews) {
  const current = new Map([...rowMap(snapshot.inputs), ...[...issues.values()].filter(i => i.revision).map(i => [i.key, i.revision])]);
  const links = linkRow(head.issue, edges, reviews, head.dependencies.map(d => d.key));
  return current.set(links.key, links.revision);
}

// A review depends only on what it used (its inputs, including its link row)
// and the issues it names as prerequisites, at their examined candidate
// revisions. A new or edited unrelated issue is not part of that answer.
function freshnessInputs(head, snapshot, issues, edges, reviews) {
  const current = currentRows(head, snapshot, issues, edges, reviews), { written } = pddLinks(reviews), links = `${head.issue}${LINKS}`;
  const candidates = rowMap(head.candidates);
  const required = new Map(head.inputs.map(i => [i.key, i.key === links ? savedLinkRow(i.revision, head.issue, written) : i.revision]));
  for (const { key } of head.dependencies) if (!required.has(key) && candidates.has(key)) required.set(key, candidates.get(key));
  return { current, deficits: [...required].filter(([key, revision]) => !current.has(key) || current.get(key) !== revision) };
}

// A trusted requirement comment on the issue that a question did not examine is
// a person's answer, so the question needs a new review.
const answered = (head, snapshot) => head.outcome === 'question' && rows(snapshot.inputs).some(r => /#issuecomment-[1-9][0-9]*$/.test(r.key)
  && coverageIssueKey(r.key) === head.issue && !head.inputs.some(i => i.key === r.key));

const namedLinkRemoved = (head, edges) => head.outcome === 'complete'
  && head.dependencies.some(d => !edges.some(e => e.dependent === head.issue && e.blocker === d.key));

function freshness(head, snapshot, issues, edges, reviews) {
  // PDD never removes a link, so a named link that is now absent is a person's change.
  if (namedLinkRemoved(head, edges) || answered(head, snapshot)) return false;
  const { current, deficits } = freshnessInputs(head, snapshot, issues, edges, reviews);
  const coverage = coverageRows(snapshot), headRepository = issueRepository(head.issue);
  // Only current impacts hosted in the head's root repository that name this head apply.
  const impacts = snapshot.impacts.filter(i => headRepository && issueRepository(i.host) === headRepository && i.authority !== 'outsider'
    && (i.reviews ?? []).includes(head.id) && (i.inputs ?? []).every(r => current.get(locator(r.key)) === r.revision));
  const trusted = i => i.intact && (i.authority === 'trusted' || !i.authority && i.trusted);
  const affected = i => (i.affected ?? []).some(k => issueKey(k) === head.issue);
  // A complete trusted impact that names this review as affected queues reanalysis.
  if (impacts.some(i => i.complete && trusted(i) && affected(i))) return false;
  if (deficits.length && coverage === false) return false;
  for (const [key] of deficits) {
    const issueCandidate = coverageIssueKey(key);
    if (!current.has(key) || (coverage !== null && issueCandidate && !coverage.get(issueCandidate)?.reviewImpact)) return false;
    const covering = impacts.filter(i => (i.inputs ?? []).some(r => locator(r.key) === key && r.revision === current.get(key)));
    if (covering.some(i => !trusted(i) || affected(i))) return false;
    if (!covering.some(i => i.complete && trusted(i))) return false;
  }
  return true;
}

export function projectIssueGraph({ snapshot }) {
  const { issues, edges, reviews } = observations(snapshot), selected = new Map(), coverage = coverageRows(snapshot);
  for (const key of issues.keys()) selected.set(key, selectReview(reviews.filter(r => r.issue === key)));
  const outgoing = new Map([...issues.keys()].map(k => [k, edges.filter(e => e.dependent === k).map(e => e.blocker)]));
  const reachesCycle = (key, stack = new Set(), done = new Set()) => {
    if (stack.has(key)) return true;
    if (done.has(key)) return false;
    stack.add(key);
    for (const next of outgoing.get(key) ?? []) if (reachesCycle(next, stack, done)) return true;
    stack.delete(key); done.add(key); return false;
  };
  const ownFacts = new Map();
  for (const [key, issue] of issues) {
    const facts = issue.conditions.map(text => {
      const provenance = issue.conditionSources?.find(x => x.text === text);
      return { kind: 'condition', text, issue: key, source: provenance?.source ?? key,
        inputs: provenance?.inputs ?? [{ key, revision: issue.revision }] };
    });
    for (const r of selected.get(key).heads) for (const text of r.questions ?? []) facts.push({
      kind: 'question', text, issue: key, source: /^\d+$/.test(r.id) ? `${key}#issuecomment-${r.id}` : key, inputs: r.inputs,
    });
    ownFacts.set(key, facts);
  }
  const graphEdges = edges.map(e => {
    const s = selected.get(e.dependent), head = s.head;
    const reason = head && freshness(head, snapshot, issues, edges, reviews) && head.dependencies.find(d => d.key === e.blocker);
    if (reason) return { ...e, reason: reason.reason, evidence: reason.evidence };
    const observed = selectReview(reviews.filter(r => r.issue === e.dependent), true).head;
    const changed = observed && new Set(freshnessInputs(observed, snapshot, issues, edges, reviews).deficits.map(([k]) => k));
    const displayReason = observed && observed.inputs.every(i => !changed.has(i.key))
      && observed.dependencies.find(d => d.key === e.blocker);
    return { ...e, reason: displayReason ? `Unverified saved reason: ${displayReason.reason}` : 'GitHub dependency; no saved reason',
      evidence: displayReason?.evidence ?? [] };
  });
  const nodes = [...issues.values()].map(issue => {
    const { key } = issue, selection = selected.get(key), head = selection.head, blockers = outgoing.get(key), reasons = [];
    let covered = subjectCovered(key, outgoing, coverage);
    const currentInputs = new Set([...snapshot.inputs.map(row => locator(row.key)), ...issues.keys(), `${key}${LINKS}`]);
    if (head && head.inputs.some(row => !currentInputs.has(locator(row.key)))) { reasons.push('Required context unavailable', `Observation unavailable: context ${key}`); covered = false; }
    let reviewState = selection.state, review = head?.id ?? '';
    // A head whose own outcome is pending with no effects to apply (a bare pending
    // answer that an earlier version saved) is reviewed again.
    if (head) reviewState = !freshness(head, snapshot, issues, edges, reviews) || (head.outcome === 'pending' && head.effects !== 'pending') ? 'stale' : head.outcome === 'complete' ? 'current' : head.outcome;
    // A removed named link makes the review stale, so intake reviews it again.
    const humanChange = !!head && namedLinkRemoved(head, edges);
    const reviewReason = { unchecked: 'Unchecked', stale: 'Stale review', question: 'Review question', pending: 'Pending effects',
      unverified: 'Unverified review', conflict: 'Conflicting reviews' };
    if (reviewReason[reviewState]) reasons.push(reviewReason[reviewState]);
    if (humanChange) reasons.push('Human dependency change');
    if (!snapshot.complete) reasons.push('Incomplete sync');
    if (!covered) { reasons.push('Incomplete relevant observations'); reasons.push(...coverageReasons(key, outgoing, coverage, snapshot)); }
    if (head && reviewState === 'stale' && coverage && coverage !== false) {
      const missing = freshnessInputs(head, snapshot, issues, edges, reviews).deficits.find(([candidate]) => { const issue = coverageIssueKey(candidate); return issue && !coverage.get(issue)?.reviewImpact; });
      if (missing) { const issue = coverageIssueKey(missing[0]); reasons.push('Impact discovery unavailable: ' + key); reasons.push('Observation unavailable: comments ' + issue); }
    }
    const facts = [...ownFacts.get(key)], visited = new Set([key]);
    function prerequisiteFacts(k) {
      if (visited.has(k)) return;
      visited.add(k); facts.push(...ownFacts.get(k));
      for (const b of outgoing.get(k) ?? []) prerequisiteFacts(b);
    }
    blockers.forEach(prerequisiteFacts);
    let dependencyState = covered ? 'clear' : 'unknown';
    for (const b of blockers) {
      const blocker = issues.get(b);
      if (blocker.state === 'unknown') { dependencyState = 'unknown'; reasons.push('Unknown prerequisite'); }
      else if (blocker.state !== 'completed' || ownFacts.get(b).length) {
        if (dependencyState !== 'unknown') dependencyState = 'waiting';
        if (blocker.state === 'open') reasons.push('Open prerequisite');
        if (blocker.state === 'not_planned') reasons.push('Prerequisite not planned');
      }
    }
    if (facts.length) reasons.push('Required condition');
    if (reachesCycle(key)) { dependencyState = 'cycle'; reasons.push('Dependency cycle'); }
    if (issue.authority !== 'trusted') reasons.push('Untrusted issue');
    if (issue.state === 'completed') reasons.push('Issue completed');
    if (issue.state === 'not_planned') reasons.push('Issue not planned');
    // An expired claim is a note for readers, not a hold: it leaves selection open.
    const notes = issue.holds.filter(hold => /^Expired claim\b/.test(hold));
    const holds = issue.holds.filter(hold => hold !== 'Open PR' && !notes.includes(hold));
    reasons.push(...holds, ...notes);
    if (graphEdges.some(e => e.dependent === key && e.reason === 'GitHub dependency; no saved reason')) reasons.push('GitHub dependency; no saved reason');
    const executionState = issue.execution === 'running' ? 'running' : holds.length ? 'held' : issue.execution;
    const assigneesKnown = Array.isArray(issue.assignees) && issue.assignees.every(name => typeof name === 'string' && name.trim());
    const unassigned = assigneesKnown && issue.assignees.length === 0;
    if (!assigneesKnown) reasons.push('Assignees unknown');
    else if (!unassigned) reasons.push('Assigned');
    return { key, title: issue.title, reviewState, dependencyState, executionState,
      eligible: issue.state === 'open' && reviewState === 'current' && dependencyState === 'clear' && issue.authority === 'trusted'
        && executionState === 'idle' && !holds.length && unassigned && !ownFacts.get(key).length && covered,
      reasons: unique(reasons), blockers, review, nativeState: issue.state, facts };
  });
  return projectSortGraph(snapshot, { repository: snapshot.repository, capturedAt: snapshot.capturedAt, complete: snapshot.complete, nodes, edges: graphEdges });
}

// The link facts that a dependency review records and respects. `row` is the
// review's link row: its issue's current person-made links, without the links in
// `dependencies`. `removed` lists the blockers that a trusted confirmed review of
// the issue named and that are no longer linked. PDD never removes a link, so a
// person removed them, and a new review must not add them back.
export function dependencyLinks({ snapshot, issue, dependencies = [] }) {
  const { edges, reviews } = observations(snapshot), key = issueKey(issue);
  if (!key) invalid();
  const linked = new Set(edges.filter(e => e.dependent === key).map(e => e.blocker));
  const removed = unique(reviews.filter(r => r.issue === key && r.authority === 'trusted' && r.intact === true && r.effects === 'confirmed')
    .flatMap(r => r.dependencies.map(d => d.key)).filter(blocker => blocker && !linked.has(blocker)));
  return { row: linkRow(key, edges, reviews, dependencies.map(d => issueKey(d?.key ?? d)).filter(Boolean)), removed };
}

export function validateDependencyChange({ snapshot, dependent, blocker }) {
  const d = issueKey(dependent), b = issueKey(blocker), { issues, edges } = observations(snapshot);
  const result = reason => ({ allowed: reason === 'ok', reason });
  if (d && d === b) return result('self');
  if (edges.some(e => e.dependent === d && e.blocker === b)) return result('duplicate');
  const outgoing = new Map([...issues.keys()].map(key => [key, edges.filter(edge => edge.dependent === key).map(edge => edge.blocker)]));
  const coverage = coverageRows(snapshot);
  if (!d || !b || !issues.has(d) || !issues.has(b) || !subjectCovered(d, outgoing, coverage) || !subjectCovered(b, outgoing, coverage)
    || issues.get(d).state === 'unknown' || issues.get(b).state === 'unknown') return result('unknown');
  const seen = new Set(); let unknown = false, cycle = false;
  function visit(k) {
    if (k === d) { cycle = true; return; }
    if (seen.has(k)) return;
    seen.add(k);
    if (!issues.has(k) || issues.get(k).state === 'unknown') unknown = true;
    for (const edge of edges) if (edge.dependent === k) visit(edge.blocker);
  }
  visit(b);
  return result(unknown ? 'unknown' : cycle ? 'cycle' : 'ok');
}
