// Implements prompts/cli/issue-sort.prompt.md.
import { resolveArea } from './autopilot-areas.mjs';
const issueURL = x => typeof x === 'string' && /^https:\/\/github\.com\/[\w.-]+\/[\w.-]+\/issues\/[1-9]\d*$/.test(x);
const text = x => typeof x === 'string';
const list = x => Array.isArray(x) && x.every(text);
const exact = (x, keys) => x && typeof x === 'object' && !Array.isArray(x) && Object.keys(x).sort().join() === keys.split(',').sort().join();
export function validSort(record) {
  const r = record;
  return !!(exact(r, 'schema_version,issue,base,inputs,belongs,status,genuine,paths,rootCause,severity,question') && r.schema_version === 'pdd.issue-sort.v1' && issueURL(r.issue)
    && list(r.base) && new Set(r.base).size === r.base.length && Array.isArray(r.inputs) && r.inputs.length && r.inputs.every(x => exact(x, 'key,revision') && text(x.key) && x.key && text(x.revision) && x.revision) && new Set(r.inputs.map(x => x.key)).size === r.inputs.length
    && exact(r.belongs, 'kind,area,repository') && ['area','repository','old-code','unknown'].includes(r.belongs.kind) && text(r.belongs.area) && text(r.belongs.repository)
    && (r.belongs.kind !== 'repository' || /^[\w.-]+\/[\w.-]+$/.test(r.belongs.repository))
    && exact(r.status, 'state,release,fix,evidence') && ['still-happens','partly-fixed','fixed','unclear'].includes(r.status.state) && text(r.status.release) && r.status.release && text(r.status.fix) && (r.status.state !== 'fixed' || r.status.fix.trim()) && list(r.status.evidence) && r.status.evidence.length && r.status.evidence.every(x => x.trim())
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
export function selectedSort(snapshot, issue) {
  if (!issue || !sortCovered(snapshot, issue)) return null;
  const all = (issue.sorts ?? []).filter(x => x.authority !== 'outsider');
  const superseded = new Set(all.filter(x => x.authority === 'trusted' && x.intact && validSort(x.record)).flatMap(x => x.record.base));
  const heads = all.filter(x => !superseded.has(x.id));
  if (heads.length !== 1) return null;
  const head = heads[0], r = head.record;
  if (!head.intact || head.authority !== 'trusted' || !validSort(r) || r.issue !== issue.key || r.status.release !== snapshot.sortContext?.release) return null;
  const current = new Map([...snapshot.issues, ...snapshot.inputs].map(x => [x.key, x.revision]));
  if (r.paths.some(path => !r.inputs.some(x => x.key === sortSourceKey(snapshot.repository, path))) || r.inputs.some(x => current.get(x.key) !== x.revision) || sortInputs(snapshot, issue).some(x => !r.inputs.some(y => y.key === x.key && y.revision === x.revision))) return null;
  return r;
}
export function sortPlan({ snapshot }) {
  const queued = [], routes = [], groups = [];
  if (!snapshot.sortContext) return { queued, routes, groups };
  const prefix = `https://github.com/${snapshot.repository.toLowerCase()}/issues/`;
  for (const issue of snapshot.issues.filter(x => x.key.startsWith(prefix) && x.state === 'open' && x.authority === 'trusted')) {
    const record = selectedSort(snapshot, issue), route = { issue: issue.key, action: 'hold', area: '', owner: '', reason: '', record, umbrella: '', members: [], evidence: record?.status.evidence ?? [] };
    routes.push(route);
    const live = issue.execution === 'running' || issue.holds.some(x => /claim/i.test(x) && !/^Expired claim\b/.test(x));
    if (!Array.isArray(issue.assignees) || issue.assignees.length) { route.reason = 'owned'; continue; }
    if (!record) { if (!live) queued.push(issue.key); route.reason = 'sort-required'; continue; }
    if (live) route.reason = 'owned';
    if (record.status.state === 'fixed' || record.belongs.kind === 'old-code' || ['duplicate','not-genuine'].includes(record.genuine.kind)) {
      route.action = live ? 'hold' : 'close'; route.reason = record.belongs.kind === 'old-code' ? 'old-code' : record.genuine.kind === 'duplicate' ? 'duplicate' : record.status.state === 'fixed' ? 'fixed' : 'not-genuine'; continue;
    }
    const area = resolveArea({ ...snapshot.sortContext, evidence: { paths: record.paths, keywords: [issue.title], labels: issue.labels ?? [], repository: record.belongs.kind === 'repository' ? record.belongs.repository : '', area: record.belongs.area } });
    Object.assign(route, { area: area.area, owner: area.owner });
    if (record.belongs.kind === 'unknown' || area.state === 'unsure') { route.action = live ? 'hold' : 'question'; route.reason = 'needs-owner'; continue; }
    if (record.belongs.kind === 'repository' && area.owner === 'autopilot') { route.action = live ? 'hold' : 'link'; route.owner = `repo:${record.belongs.repository}`; route.reason = 'another-repository'; continue; }
    if (area.owner !== 'autopilot') { route.action = live ? 'hold' : area.owner.startsWith('repo:') ? 'link' : 'assign'; route.reason = 'another-owner'; continue; }
    if (record.question || record.status.state === 'unclear' || record.genuine.kind === 'unclear') { route.action = live ? 'hold' : 'question'; route.reason = 'needs-answer'; continue; }
    route.action = live ? 'hold' : 'work'; route.reason = live ? 'owned' : 'local';
  }
  const byCause = new Map();
  for (const route of routes.filter(x => (x.action === 'work' || x.action === 'hold' && x.reason === 'owned' && x.owner === 'autopilot') && x.record?.rootCause)) {
    const key = `${route.area}\0${route.record.rootCause}`;
    if (!byCause.has(key)) byCause.set(key, []);
    byCause.get(key).push(route);
  }
  for (const members of byCause.values()) {
    if (members.length < 2) continue;
    members.sort((a,b) => Number(a.issue.split('/').pop()) - Number(b.issue.split('/').pop()));
    const live = members.filter(x => x.action === 'hold' || snapshot.issues.find(i => i.key === x.issue)?.executionClaim);
    if (live.length > 1) { for (const member of members) { member.action = 'hold'; member.reason = 'multiple-runs'; } continue; }
    const umbrella = (live[0] ?? members[0]).issue, keys = members.map(x => x.issue);
    groups.push({ area: members[0].area, rootCause: members[0].record.rootCause, umbrella, members: keys });
    for (const member of members) Object.assign(member, { umbrella, members: keys });
  }
  return { queued, routes, groups };
}
export function projectSortGraph(snapshot, graph) {
  if (!snapshot.sortContext) return graph;
  const plan = sortPlan({ snapshot });
  for (const group of plan.groups) {
    const umbrella = graph.nodes.find(x => x.key === group.umbrella);
    const members = graph.nodes.filter(x => group.members.includes(x.key));
    const blockers = [...new Set(members.flatMap(x => x.blockers))];
    if (members.some(x => x.reviewState !== 'current' || x.reasons.includes('Incomplete relevant observations') || x.facts.length)) {
      umbrella.eligible = false; umbrella.reasons.push('Group review pending');
    }
    if (blockers.some(x => group.members.includes(x))) {
      for (const member of members) { member.eligible = false; member.reasons.push('Group needs dependency review'); }
    }
    const prospective = [...graph.edges, ...group.members.filter(x => x !== group.umbrella).map(dependent => ({ dependent, blocker: group.umbrella }))];
    const cycle = (key, stack = new Set(), done = new Set()) => {
      if (stack.has(key)) return true;
      if (done.has(key)) return false;
      stack.add(key);
      if (prospective.filter(x => x.dependent === key).some(x => cycle(x.blocker, stack, done))) return true;
      stack.delete(key); done.add(key); return false;
    };
    if (cycle(group.umbrella)) for (const member of members) { member.eligible = false; member.reasons.push('Group dependency cycle'); }
    for (const blocker of blockers.filter(x => !group.members.includes(x))) {
      if (!umbrella.blockers.includes(blocker)) umbrella.blockers.push(blocker);
      const native = graph.nodes.find(x => x.key === blocker);
      if (!native || native.nativeState !== 'completed') { umbrella.eligible = false; umbrella.reasons.push('Group prerequisite pending'); }
    }
  }
  for (const node of graph.nodes) {
    const route = plan.routes.find(x => x.issue === node.key);
    if (!route) continue;
    node.sort = { action: route.action, area: route.area, owner: route.owner, umbrella: route.umbrella, members: route.members };
    if (route.action !== 'work' || route.umbrella && route.umbrella !== node.key) {
      node.eligible = false;
      node.reasons.push(route.umbrella && route.umbrella !== node.key ? 'Waiting for root-cause umbrella' : `Sort: ${route.reason}`);
      if (route.umbrella && route.umbrella !== node.key) { node.blockers.push(route.umbrella); node.dependencyState = 'waiting'; graph.edges.push({ dependent: node.key, blocker: route.umbrella, reason: 'Shared root cause', evidence: route.evidence }); }
    }
  }
  return graph;
}

export function sortClosingReferences({ snapshot, issue, code }) {
  const group = sortPlan({ snapshot }).groups.find(x => x.umbrella === issue);
  return (group?.members ?? []).filter(x => x !== issue).map(key => `${code ? 'Closes' : 'Refs'} ${key}`);
}
