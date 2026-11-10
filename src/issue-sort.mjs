// Generated from prompts/cli/issue-sort.prompt.md (sha256: a049bfb1a69bb2d4dc3afcb4885ab7c7cc7ebca04cb93bc936481fc0f1a94965).
import { resolveMixed } from './issue-mixed.mjs';
import { resolveArea } from './autopilot-areas.mjs';
const issueURL = x => typeof x === 'string' && /^https:\/\/github\.com\/[\w.-]+\/[\w.-]+\/issues\/[1-9]\d*$/.test(x);
const text = x => typeof x === 'string';
const list = x => Array.isArray(x) && x.every(text);
const exact = (x, keys) => x && typeof x === 'object' && !Array.isArray(x) && Object.keys(x).sort().join() === keys.split(',').sort().join();
const fixLocator = value => /https:\/\/github\.com\/[\w.-]+\/[\w.-]+\/(?:pull\/[1-9]\d*|commit\/[a-f\d]{7,64})\b/i.test(value)
  || /\b[a-f\d]{7,64}\b/i.test(value) || /(?:^|[\s(`])(?:[\w.-]+\/)*[\w.-]+\.[a-z\d]+:[1-9]\d*\b/i.test(value);
export function validSort(record) {
  const r = record;
  return !!(exact(Object.fromEntries(Object.entries(r ?? {}).filter(([k]) => !['touchedAreas','splitOrder'].includes(k))), 'schema_version,issue,base,inputs,belongs,status,genuine,paths,rootCause,severity,question')
    && (r.touchedAreas === undefined || Array.isArray(r.touchedAreas) && r.touchedAreas.length > 0 && r.touchedAreas.every(x => exact(x, 'area,evidence') && text(x.area) && x.area.trim() && list(x.evidence) && x.evidence.length && x.evidence.every(v => v.trim())) && new Set(r.touchedAreas.map(x => x.area)).size === r.touchedAreas.length)
    && (r.splitOrder === undefined || exact(r.splitOrder, 'first,evidence') && text(r.splitOrder.first) && r.splitOrder.first.trim() && list(r.splitOrder.evidence) && r.splitOrder.evidence.length && r.splitOrder.evidence.every(v => v.trim())) && r.schema_version === 'pdd.issue-sort.v1' && issueURL(r.issue)
    && list(r.base) && new Set(r.base).size === r.base.length && Array.isArray(r.inputs) && r.inputs.length && r.inputs.every(x => exact(x, 'key,revision') && text(x.key) && x.key && text(x.revision) && x.revision) && new Set(r.inputs.map(x => x.key)).size === r.inputs.length
    && exact(r.belongs, 'kind,area,repository') && ['area','repository','old-code','unknown'].includes(r.belongs.kind) && text(r.belongs.area) && text(r.belongs.repository)
    && (r.belongs.kind !== 'repository' || /^[\w.-]+\/[\w.-]+$/.test(r.belongs.repository))
    && exact(r.status, 'state,release,fix,evidence') && ['still-happens','partly-fixed','fixed','unclear'].includes(r.status.state) && text(r.status.release) && r.status.release && text(r.status.fix) && (r.status.state !== 'fixed' || fixLocator(r.status.fix)) && list(r.status.evidence) && r.status.evidence.length && r.status.evidence.every(x => x.trim())
    && exact(r.genuine, 'kind,duplicateOf,reason') && ['bug','feature','docs','duplicate','not-genuine','unclear'].includes(r.genuine.kind) && text(r.genuine.reason) && text(r.genuine.duplicateOf)
    && (r.genuine.kind !== 'duplicate' || issueURL(r.genuine.duplicateOf) && r.genuine.duplicateOf !== r.issue)
    && (!['not-genuine'].includes(r.genuine.kind) && r.belongs.kind !== 'old-code' || r.genuine.reason.trim())
    && list(r.paths) && r.paths.every(x => x && !x.startsWith('/') && !x.split('/').includes('..')) && text(r.rootCause) && (!r.rootCause || /^[a-z\d]+(?:-[a-z\d]+)*$/.test(r.rootCause)) && ['high','medium','low'].includes(r.severity) && text(r.question));
}
export function sortInputs(snapshot, issue) {
  return [{ key: issue.key, revision: issue.revision }, ...(snapshot.inputs ?? []).filter(x => x.key === snapshot.sortContext?.key || x.key === `${issue.key}#sort-labels` || x.key.startsWith(`${issue.key}#issuecomment-`))];
}
export function sortCovered(snapshot, issue) {
  if (!snapshot.coverage) return snapshot.complete === true;
  const row = snapshot.coverage.issues?.find(x => x.key === issue.key);
  return snapshot.coverage.scope === true && !!row && ['issue','authority','comments','context','execution'].every(k => row[k] === true);
}
export const sortSourceKey = (repository, path) => `https://github.com/${repository.toLowerCase()}/blob/HEAD/${path.split('/').map(encodeURIComponent).join('/')}`;
export const noActiveRun = issue => issue?.execution === 'idle'
  && !(issue.holds ?? []).some(h => h === 'Claimed' || h === 'Stuck' || h === 'Waiting for the interpreter');
export function endedRunQuestion(issue, value) {
  if (!noActiveRun(issue) || !text(value) || !value.trim()) return false;
  const own = `${issue.title ?? ''}\n${issue.sortText ?? ''}`.toLowerCase();
  for (const m of value.matchAll(/\bbatch\s+(\d{8}-\d{6}-[a-z0-9]+)\b/gi))
    if (!own.includes(m[1].toLowerCase())) return true;
  const whatBatch = /\bwhat\s+happened\s+to\s+batch\s+([^\s?,.;:)]+)/i.exec(value);
  if (whatBatch && !own.includes(whatBatch[1].toLowerCase())) return true;
  if ((/\b(?:preserve|resume|retry|continue|reconcil\w*)\s+the\s+(?:existing|retained|saved|old|previous|cancelled|ended)\s+(?:[a-z0-9_-]+\s+)*run\b/i.test(value)
    || /\b(?:existing|retained|saved|old|previous|cancelled|ended)\s+(?:[a-z0-9_-]+\s+)*run(?:'s|\s+#?\d+|\s+before\s+(?:it\s+resumes|retrying|any\s+new\s+check|further\s+hosted\s+work))\b/i.test(value)
    || /\bin\s+the\s+(?:existing|retained|saved|old|previous|cancelled|ended)\s+(?:[a-z0-9_-]+\s+)*run\b/i.test(value)
    || /\bbefore\s+(?:this|the)\s+run\s+(?:continues|resumes|retries|proceeds)\b/i.test(value))
    && !/\b(?:existing|retained|saved|old|previous|cancelled|ended)\s+(?:[a-z0-9_-]+\s+)*run\b/i.test(own)) return true;
  return false;
}
export function selectedSort(snapshot, issue) {
  if (!issue || !sortCovered(snapshot, issue)) return null;
  const all = (issue.sorts ?? []).filter(x => x.authority !== 'outsider');
  const superseded = new Set(all.filter(x => x.authority === 'trusted' && x.intact && validSort(x.record)).flatMap(x => x.record.base));
  const heads = all.filter(x => !superseded.has(x.id));
  if (heads.length !== 1) return null;
  const head = heads[0], r = head.record;
  if ((snapshot.sortContext?.groups ?? []).some(g => g.merged && g.recheck?.some(x => x.issue === issue.key && x.heads.includes(head.id)))) return null;
  if (!head.intact || head.authority !== 'trusted' || !validSort(r) || r.issue !== issue.key || r.status.release !== snapshot.sortContext?.release) return null;
  const current = new Map([...snapshot.issues, ...snapshot.inputs].map(x => [x.key, x.revision]));
  if (r.paths.some(path => !r.inputs.some(x => x.key === sortSourceKey(snapshot.repository, path))) || r.inputs.some(x => current.get(x.key) !== x.revision) || sortInputs(snapshot, issue).some(x => !r.inputs.some(y => y.key === x.key && y.revision === x.revision))) return null;
  if (r.question && endedRunQuestion(issue, r.question)) {
    if (r.belongs.kind === 'unknown' || r.status.state === 'unclear' || r.genuine.kind === 'unclear') return null;
    return { ...r, question: '' };
  }
  return r;
}
export function sortPlan({ snapshot }) {
  const queued = [], routes = [], groups = [];
  if (!snapshot.sortContext) return { queued, routes, groups };
  const prefix = `https://github.com/${snapshot.repository.toLowerCase()}/issues/`;
  for (const issue of snapshot.issues.filter(x => x.key.startsWith(prefix) && x.state === 'open' && x.authority === 'trusted')) {
    const record = selectedSort(snapshot, issue), route = { issue: issue.key, action: 'hold', area: '', owner: '', reason: '', record, umbrella: '', members: [], evidence: record?.status.evidence ?? [] };
    routes.push(route);
    const live = issue.execution !== 'idle' || issue.sortOpenPr === true || issue.holds.some(x => /claim/i.test(x) && !/^Expired claim\b/.test(x));
    if (!Array.isArray(issue.assignees) || issue.assignees.length) { route.reason = 'owned'; continue; }
    if (issue.sortSplit) {
      route.record = record ?? issue.sorts?.find(x => x.authority === 'trusted' && x.intact && x.record)?.record ?? null;
      route.reason = 'split-parts';
      const done = issue.sortSplit.parts.every(p => snapshot.issues.some(x => x.key === p.issue && x.authority === 'trusted' && x.state === 'completed' && x.sortCompleted === true && sortCovered(snapshot, x)));
      route.action = done && !live ? 'close' : 'hold';
      if (done) route.evidence = issue.sortSplit.parts.map(p => `${p.area}: ${p.issue} completed`);
      if (issue.sortOwnerChoice === 'whole' || issue.sortOwnerChoice === 'conflict') { route.action = live ? 'hold' : 'question'; route.reason = 'needs-owner'; }
      continue;
    }
    if (issue.sortPart) {
      const parent = snapshot.issues.find(x => x.key === issue.sortPart.parent);
      if (!parent?.sortSplit?.parts.some(x => x.issue === issue.key && x.area === issue.sortPart.area)) { route.reason = 'split-pending'; continue; }
    }
    if (!record) { if (!live) queued.push(issue.key); route.reason = 'sort-required'; continue; }
    if (live) route.reason = 'owned';
    if (record.status.state === 'fixed' || record.belongs.kind === 'old-code' || ['duplicate','not-genuine'].includes(record.genuine.kind)) {
      route.action = live ? 'hold' : 'close'; route.reason = record.belongs.kind === 'old-code' ? 'old-code' : record.genuine.kind === 'duplicate' ? 'duplicate' : record.status.state === 'fixed' ? 'fixed' : 'not-genuine'; continue;
    }
    const mixed = resolveMixed({ snapshot, issue, record });
    if (mixed) { Object.assign(route, mixed); if (live) { route.action = 'hold'; route.reason = 'owned'; } continue; }
    const area = resolveArea({ ...snapshot.sortContext, evidence: { paths: record.paths, keywords: [issue.title, issue.sortText ?? ''], labels: issue.labels ?? [], repository: record.belongs.kind === 'repository' ? record.belongs.repository : '', area: record.belongs.area } });
    Object.assign(route, { area: area.area, owner: area.owner });
    if (record.belongs.kind === 'unknown' || area.state === 'unsure') { route.action = live ? 'hold' : 'question'; route.reason = 'needs-owner'; continue; }
    if (record.belongs.kind === 'repository' && area.owner === 'autopilot') { route.action = live ? 'hold' : 'link'; route.owner = `repo:${record.belongs.repository}`; route.reason = 'another-repository'; continue; }
    if (area.owner !== 'autopilot') { route.action = live ? 'hold' : area.owner.startsWith('repo:') ? 'link' : 'assign'; route.reason = 'another-owner'; continue; }
    if (record.question || record.status.state === 'unclear' || record.genuine.kind === 'unclear') { route.action = live ? 'hold' : 'question'; route.reason = 'needs-answer'; continue; }
    route.action = live ? 'hold' : 'work'; route.reason = live ? 'owned' : 'local';
  }
  const saved = snapshot.sortContext.groups ?? [];
  const umbrellaKeys = new Set(saved.filter(x => !x.merged && !x.members.includes(x.umbrella)).map(x => x.umbrella).filter(Boolean));
  const synthetic = issue => /<!-- pdd-issue-group:v1 ([a-z\d]+(?:-[a-z\d]+)*) -->/.test(issue.sortText ?? '');
  const byCause = new Map();
  for (const route of routes.filter(x => x.action === 'work' && !snapshot.issues.find(i => i.key === x.issue)?.sortPart && x.record?.rootCause && !umbrellaKeys.has(x.issue) && !synthetic(snapshot.issues.find(i => i.key === x.issue)))) {
    const key = route.record.rootCause;
    if (!byCause.has(key)) byCause.set(key, []);
    byCause.get(key).push(route);
  }
  // Saved groups are compared with the same current records. A stale member
  // holds its previous group, but cannot authorize a new join or an effect.
  for (const old of saved.filter(x => !x.merged)) {
    const members = byCause.get(old.rootCause) ?? [];
    for (const key of old.members) {
      const route = routes.find(x => x.issue === key);
      const retainedWork = key === old.umbrella && route?.reason === 'owned' && route.record?.rootCause === old.rootCause;
      if (route && (!route.record || retainedWork) && !members.includes(route)) members.push(route);
    }
    if (members.length || old.umbrella && !old.members.includes(old.umbrella)) byCause.set(old.rootCause, members);
  }
  for (const [rootCause, members] of byCause) {
    members.sort((a,b) => Number(a.issue.split('/').pop()) - Number(b.issue.split('/').pop()));
    const old = saved.find(x => !x.merged && x.rootCause === rootCause);
    if (members.length < 2 && !old?.umbrella) continue;
    const keys = members.map(x => x.issue), area = [...new Set(members.map(x => x.area).filter(Boolean))].sort().join(',');
    const dedicated = members.length >= 3 || area.includes(',') || old?.umbrella && !old.members.includes(old.umbrella);
    const recovered = snapshot.issues.filter(x => x.authority === 'trusted' && x.state === 'open' && x.sortText?.includes(`<!-- pdd-issue-group:v1 ${rootCause} -->`));
    if (dedicated && recovered.length > 1) {
      for (const match of recovered) { const route = routes.find(x => x.issue === match.key); if (route) { route.action = 'hold'; route.reason = 'group-umbrella-conflict'; } }
    }
    const occupiedWork = old?.umbrella && routes.find(x => x.issue === old.umbrella)?.reason === 'owned';
    const umbrella = occupiedWork ? old.umbrella : dedicated ? (old?.umbrella && !old.members.includes(old.umbrella) ? old.umbrella : recovered.length === 1 ? recovered[0].key : '') : old?.umbrella && snapshot.issues.find(x => x.key === old.umbrella)?.state !== 'open' ? old.umbrella : keys[0];
    groups.push({ area, rootCause, umbrella, members: keys, notified: old?.notified ?? old?.members ?? keys });
    for (const member of members) Object.assign(member, { umbrella, members: keys });
    const umbrellaRoute = routes.find(x => x.issue === umbrella);
    if (umbrellaRoute) Object.assign(umbrellaRoute, { umbrella, members: keys });
    if (!umbrella) for (const member of members) { member.action = 'hold'; member.reason = 'group-umbrella-pending'; }
  }
  for (const route of routes) if (route.action === 'work' && synthetic(snapshot.issues.find(x => x.key === route.issue)) && !groups.some(g => g.umbrella === route.issue)) { route.action = 'hold'; route.reason = 'orphan-group-umbrella'; }
  // Keep the merge boundary until all previous heads have been superseded.
  for (const group of saved.filter(x => x.merged)) groups.push(group);
  return { queued, routes, groups };
}
export function projectSortGraph(snapshot, graph) {
  if (!snapshot.sortContext) return graph;
  const plan = sortPlan({ snapshot }), unsafeGroups = new Set();
  graph.groups = plan.groups;
  const uncertainSibling = (area, cause) => snapshot.issues.some(issue => issue.key.startsWith(`https://github.com/${snapshot.repository.toLowerCase()}/issues/`) && issue.state === 'open' && issue.authority === 'trusted' && !selectedSort(snapshot, issue)
    && (issue.sorts ?? []).some(saved => saved.authority === 'trusted' && saved.intact && validSort(saved.record) && saved.record.rootCause === cause
      && resolveArea({ ...snapshot.sortContext, evidence: { paths: saved.record.paths, keywords: [issue.title, issue.sortText ?? ''], labels: issue.labels ?? [], area: saved.record.belongs.area } }).area.split(',').some(x => area.split(',').includes(x))));
  for (const group of plan.groups.filter(x => !x.merged)) {
    const umbrella = graph.nodes.find(x => x.key === group.umbrella);
    const members = graph.nodes.filter(x => group.members.includes(x.key));
    if (!umbrella) { for (const member of members) { unsafeGroups.add(member.key); member.eligible = false; member.reasons.push('Group umbrella pending'); } continue; }
    if (!members.length) { unsafeGroups.add(group.umbrella); umbrella.eligible = false; umbrella.reasons.push('Group has no open members'); }
    if (group.members.some(key => { const member = snapshot.issues.find(x => x.key === key); return !selectedSort(snapshot, member); }) || uncertainSibling(group.area, group.rootCause)) { unsafeGroups.add(group.umbrella); umbrella.eligible = false; umbrella.reasons.push('Group sort pending'); }
    if (members.some(x => x.key === group.umbrella ? !['idle','running'].includes(x.executionState) : x.executionState !== 'idle')) unsafeGroups.add(group.umbrella);
    if (unsafeGroups.has(group.umbrella)) umbrella.eligible = false;
    const blockers = [...new Set(members.flatMap(x => x.blockers))];
    if (members.some(x => x.reviewState !== 'current' || x.reasons.includes('Incomplete relevant observations') || x.facts.length)) {
      unsafeGroups.add(group.umbrella); umbrella.eligible = false; umbrella.reasons.push('Group review pending');
    }
    if (blockers.some(x => group.members.includes(x))) {
      unsafeGroups.add(group.umbrella); for (const member of members) { member.eligible = false; member.reasons.push('Group needs dependency review'); }
    }
    const prospective = [...graph.edges, ...group.members.filter(x => x !== group.umbrella).map(dependent => ({ dependent, blocker: group.umbrella }))];
    const cycle = (key, stack = new Set(), done = new Set()) => {
      if (stack.has(key)) return true;
      if (done.has(key)) return false;
      stack.add(key);
      if (prospective.filter(x => x.dependent === key).some(x => cycle(x.blocker, stack, done))) return true;
      stack.delete(key); done.add(key); return false;
    };
    if (cycle(group.umbrella)) { unsafeGroups.add(group.umbrella); for (const member of members) { member.eligible = false; member.reasons.push('Group dependency cycle'); } }
    for (const blocker of blockers.filter(x => !group.members.includes(x))) {
      if (!umbrella.blockers.includes(blocker)) umbrella.blockers.push(blocker);
      const native = graph.nodes.find(x => x.key === blocker);
      if (!native || native.nativeState !== 'completed') { unsafeGroups.add(group.umbrella); umbrella.eligible = false; umbrella.reasons.push('Group prerequisite pending'); }
    }
  }
  for (const node of graph.nodes) {
    const route = plan.routes.find(x => x.issue === node.key);
    if (!route) continue;
    if (!route.umbrella && route.record?.rootCause && uncertainSibling(route.area, route.record.rootCause)) { unsafeGroups.add(node.key); node.eligible = false; node.reasons.push('Group sort pending'); }
    node.sort = { action: route.action, area: route.area, owner: route.owner, umbrella: route.umbrella, members: route.members, rootCause: route.record?.rootCause ?? plan.groups.find(g => g.umbrella === node.key)?.rootCause ?? '', ready: !unsafeGroups.has(route.umbrella || node.key) };
    if (route.action !== 'work' || route.umbrella && route.umbrella !== node.key) {
      node.eligible = false;
      node.reasons.push(route.umbrella && route.umbrella !== node.key ? 'Waiting for root-cause umbrella' : `Sort: ${route.reason}`);
      if (route.umbrella && route.umbrella !== node.key) { node.blockers.push(route.umbrella); node.dependencyState = 'waiting'; graph.edges.push({ dependent: node.key, blocker: route.umbrella, reason: 'Shared root cause', evidence: route.evidence }); }
    }
  }
  return graph;
}

export function sortClosingReferences({ snapshot, issue, code, graph }) {
  const group = sortPlan({ snapshot }).groups.find(x => x.umbrella === issue);
  if (!group || graph?.nodes.find(x => x.key === issue)?.sort?.ready !== true) return [];
  return (group?.members ?? []).filter(x => x !== issue).map(key => `Refs ${key}`);
}
