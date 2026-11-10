// Generated from prompts/cli/issue-sort-github.prompt.md (sha256: 5b778c0619d18fa61e12b685e099a3b4d512f6b6c4442ff544edfd8f1019b4ed).
import { createHash, randomUUID } from 'node:crypto';
import { readFileSync, readdirSync, mkdirSync, renameSync, writeFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { validSort, selectedSort, sortInputs, sortPlan, sortSourceKey, splitGroupMember } from './issue-sort.mjs';
import { gitContext } from './workflow-runs.mjs';
import { currentSplitParent, readOwnerChoice } from './issue-mixed.mjs';
import { draftAreas } from './autopilot-areas.mjs';
const parse = x => typeof x === 'string' ? JSON.parse(x) : x;
const WORK_LABELS = new Set(['pdd:working', 'pdd:stuck', 'pdd:code-pending', 'pdd:close-proposed', 'pdd:needs-owner']);
const routingLabels = (labels, areas) => labels.filter(x => !WORK_LABELS.has(x) || (areas ?? []).some(a => a.match?.labels?.includes(x))).slice().sort();
const hash = x => createHash('sha256').update(x).digest('hex');
export const sortBookkeeping = body => /<!--\s*pdd-issue-(?:sort|route):v1\s*-->/.test(body ?? '');
export function readSortComment(comment, authority) {
  if (!/<!--\s*pdd-issue-sort:v1\s*-->/.test(comment.body ?? '')) return null;
  let record;
  try { record = JSON.parse(/```json\s*([\s\S]*?)```/.exec(comment.body)?.[1]); } catch { /* Keep invalid trusted heads visible. */ }
  return { id: String(comment.id), record: validSort(record) ? record : null, authority, intact: validSort(record) && typeof comment.created_at === 'string' && comment.created_at === comment.updated_at };
}
export async function addSortContext(snapshot, cwd, ports, groups) {
  if (!cwd && !ports.sortContext) return snapshot;
  let context;
  if (ports.sortContext) context = await ports.sortContext.read({ cwd, repository: snapshot.repository });
  else {
    const read = path => { try { return readFileSync(join(cwd, path), 'utf8'); } catch (e) { if (e.code === 'ENOENT') return ''; throw e; } };
    const settings = JSON.parse(read('pdd.json') || '{}'), pkg = JSON.parse(read('package.json') || '{}');
    const codeowners = read('.github/CODEOWNERS') || read('CODEOWNERS') || read('docs/CODEOWNERS');
    const folders = readdirSync(cwd, { withFileTypes: true }).filter(x => x.isDirectory() && !x.name.startsWith('.')).map(x => x.name);
    context = { areas: settings.autopilot?.areas, codeowners, release: pkg.version || 'unversioned', folders };
  }
  const key = `https://github.com/${snapshot.repository.toLowerCase()}#autopilot-areas`;
  const revision = hash(JSON.stringify({ areas: context.areas, codeowners: context.codeowners, release: context.release }));
  for (const issue of snapshot.issues) {
    const key = `${issue.key}#sort-labels`;
    snapshot.inputs = snapshot.inputs.filter(x => x.key !== key);
    snapshot.inputs.push({ key, revision: hash(JSON.stringify(routingLabels(issue.labels ?? [], context.areas))) });
  }
  snapshot.sortContext = { ...context, key, revision, groups: groups ?? await readSortGroups({ cwd, repository: snapshot.repository }, ports), draft: context.areas === undefined ? draftAreas({ ...context, labels: [...new Set(snapshot.issues.flatMap(x => x.labels ?? []))], assignees: [...new Set(snapshot.issues.flatMap(x => [...(x.assignees ?? []), ...(x.pastAssignees ?? [])]))] }) : null };
  snapshot.inputs = snapshot.inputs.filter(x => x.key !== key); snapshot.inputs.push({ key, revision });
  return snapshot;
}
export function sortSubjects(snapshot) { return sortPlan({ snapshot }).queued; }
export function prepareSortContext(snapshot) {
  if (!snapshot.sortContext) return {};
  return { sort: { ...snapshot.sortContext, schema: 'pdd.issue-sort.v1', required: sortSubjects(snapshot), records: snapshot.issues.flatMap(x => selectedSort(snapshot, x) ?? []) } };
}
export function validateSortBatch({ snapshot, prepared, issues, sorts }) {
  if (!prepared.sortContext) { if (sorts !== undefined) throw Error('invalid-analysis'); return []; }
  const assigned = key => [prepared, snapshot].some(value => value.issues.find(x => x.key === key)?.assignees?.length);
  const required = issues.filter(key => !assigned(key));
  if (!Array.isArray(sorts) || sorts.some(x => !validSort(x)) || new Set(sorts.map(x => x.issue)).size !== sorts.length || sorts.some(x => !issues.includes(x.issue))) throw Error('invalid-analysis');
  sorts = sorts.filter(x => !assigned(x.issue));
  if (sorts.length !== required.length || required.some(key => !sorts.some(x => x.issue === key))) throw Error('invalid-analysis');
  const current = new Map([...snapshot.issues, ...snapshot.inputs].map(x => [x.key, x.revision]));
  for (const record of sorts) {
    const issue = snapshot.issues.find(x => x.key === record.issue), old = prepared.issues.find(x => x.key === record.issue);
    if (JSON.stringify(selectedSort(snapshot, issue)) === JSON.stringify(record)) continue;
    const ids = (old?.sorts ?? []).filter(x => x.authority !== 'outsider');
    const superseded = new Set(ids.filter(x => x.intact && validSort(x.record)).flatMap(x => x.record.base));
    const heads = ids.filter(x => !superseded.has(x.id)).map(x => x.id).sort();
    if (record.paths.some(path => !record.inputs.some(x => x.key === sortSourceKey(snapshot.repository, path)))) throw Error('invalid-analysis');
    if (!issue || issue.authority !== 'trusted' || record.status.release !== snapshot.sortContext?.release || JSON.stringify(record.base.slice().sort()) !== JSON.stringify(heads)
      || sortInputs(snapshot, issue).some(x => !record.inputs.some(y => y.key === x.key && y.revision === x.revision)) || record.inputs.some(x => current.get(x.key) !== x.revision)) throw Error('input-changed');
    const currentHeads = (issue.sorts ?? []).map(x => [x.id, x.intact]);
    if (JSON.stringify(currentHeads) !== JSON.stringify((old.sorts ?? []).map(x => [x.id, x.intact]))) throw Error('input-changed');
  }
  return sorts;
}
// One effect stream per operation; the caller shares it for saving and routing.
export function pacedSortWrites(ports, { cwd = ports.cwd ?? '', repository } = {}) {
  let last = null, attempts = 0;
  const write = async action => {
    if (attempts >= 20) throw Error('sort-budget-pending');
    const now = Date.parse((await ports.clock.now({})).iso);
    if (last !== null && now - last < 1000) await (ports.wait?.sleep ?? (async ({ ms }) => new Promise(resolve => setTimeout(resolve, ms))))({ ms: 1000 - (now - last) });
    if (ports.settings && !['auto','observe'].includes((await ports.settings.read({ cwd, repository })).mode)) throw Error('sort-mode-changed');
    if (ports.admitEffect && !await ports.admitEffect()) throw Error('sort-write-pending');
    if (ports.sortBudget && !await ports.sortBudget()) throw Error('sort-budget-pending');
    attempts++;
    try { return await action(); }
    finally { last = Date.parse((await ports.clock.now({})).iso); }
  };
  Object.defineProperty(write, 'remaining', { get: () => 20 - attempts });
  return write;
}
export async function saveSortBatch({ repository, snapshot, sorts }, ports, write = pacedSortWrites(ports, { repository })) {
  const failed = [], skipped = [];
  for (const record of sorts) {
    const issue = snapshot.issues.find(x => x.key === record.issue);
    if (issue?.assignees?.length) { skipped.push({ issue: record.issue, reason: 'assigned to a person' }); continue; }
    let assigned = false;
    const onAssigned = raw => { assigned = true; issue.assignees = raw.assignees.map(x => x.login); };
    try {
      if (JSON.stringify(selectedSort(snapshot, issue)) === JSON.stringify(record)) continue;
      const body = `Sort: ${record.belongs.kind}; ${record.status.state}; ${record.genuine.kind}.\n${record.status.evidence.join('\n')}\n\n<!-- pdd-issue-sort:v1 -->\n\`\`\`json\n${JSON.stringify(record)}\n\`\`\``;
      const route = { issue: record.issue, record };
      const result = parse((await write(async () => {
        if (!await sortOwnership({ repository, route, areas: snapshot.sortContext.areas, onAssigned }, ports)) throw Error('sort-owner-changed');
        return ports.github.appendComment({ repository, issue: Number(record.issue.split('/').pop()), body, checkOwnership: () => sortOwnership({ repository, route, areas: snapshot.sortContext.areas, onAssigned }, ports) });
      })).json);
      if (!result.id) throw Error('sort-write-pending');
      (issue.sorts ??= []).push({ id: String(result.id), authority: 'trusted', intact: true, record });
    } catch (error) {
      const reason = assigned ? 'assigned to a person' : error.message || 'sort-write-pending';
      (reason === 'assigned to a person' ? skipped : failed).push({ issue: record.issue, reason });
    }
  }
  return { failed, skipped };
}
export async function currentSortIssue({ cwd, repository, snapshot, route }, ports) {
  if (snapshot.issues.find(x => x.key === route.issue)?.sortSplit) return currentSplitParent({ repository, snapshot, route }, ports, route.action === 'close');
  const issue = Number(route.issue.split('/').pop());
  const raw = parse((await ports.github.issue({ repository, issue })).json);
  const comments = []; const cursors = new Set(); let cursor = '';
  do {
    if (cursors.has(cursor)) return false;
    cursors.add(cursor);
    const page = parse((await ports.github.page({ repository, issue, kind: 'comments', cursor })).json);
    if (page.error || !Array.isArray(page.items) || typeof page.next !== 'string') return false;
    comments.push(...page.items); cursor = page.next;
  } while (cursor);
  const fresh = structuredClone(snapshot), subject = fresh.issues.find(x => x.key === route.issue);
  fresh.inputs = fresh.inputs.filter(x => !x.key.startsWith(`${route.issue}#issuecomment-`));
  subject.sorts = [];
  for (const comment of comments) {
    const authority = (await ports.authority.read({ repository, author: comment.user?.login ?? '' })).authority;
    if (!['trusted','outsider'].includes(authority)) return false;
    const sort = readSortComment(comment, authority);
    if (sort) subject.sorts.push(sort);
    else if (authority === 'trusted' && !sortBookkeeping(comment.body) && !/<!--\s*pdd(?:-dependency-(?:review|impact)|[: -](?:autopilot|claim|working|sync))/i.test(comment.body ?? '') && !(comment.body?.includes('"coordinatorId"') && comment.body?.includes('"labelEventId"'))) fresh.inputs.push({ key: `${route.issue}#issuecomment-${comment.id}`, revision: hash(comment.body ?? '') });
  }
  const source = route.record.inputs.filter(x => /\/blob\/HEAD\//.test(x.key));
  if (source.length) {
    const current = parse((await ports.context.read({ cwd: cwd, repository, inputs: source })).json);
    fresh.inputs = fresh.inputs.filter(x => !source.some(y => y.key === x.key)); fresh.inputs.push(...(current.inputs ?? []));
  }
  subject.labels = (raw.labels ?? []).map(x => typeof x === 'string' ? x : x.name);
  await addSortContext(fresh, cwd, ports);
  if (JSON.stringify(selectedSort(fresh, subject)) !== JSON.stringify(route.record)) return false;
  // PR ownership can change while pacing, even before a work label arrives.
  let timelineCursor = ''; const timelineSeen = new Set(), timeline = [];
  do {
    if (timelineSeen.has(timelineCursor)) return false;
    timelineSeen.add(timelineCursor);
    const page = parse((await ports.github.page({ repository, issue, kind: 'timeline', cursor: timelineCursor })).json);
    if (page.error || !Array.isArray(page.items) || typeof page.next !== 'string') return false;
    if (page.items.some(x => x.event === 'cross-referenced' && x.source?.issue?.pull_request && x.source.issue.state === 'open')) return false;
    timeline.push(...page.items); timelineCursor = page.next;
  } while (timelineCursor);
  if (await readOwnerChoice({ labels: subject.labels, comments, timeline }, author => ports.authority.read({ repository, author })) !== (snapshot.issues.find(x => x.key === route.issue).sortOwnerChoice ?? '')) return false;
  return sortOwnership({ repository, route, areas: fresh.sortContext.areas }, ports);
}
async function sortOwnership({ repository, route, areas, onAssigned }, ports) {
  // Keep these observations after all potentially long evidence reads. The native
  // update calls this again inside its mutation guard, after any admission wait.
  const owners = parse((await ports.owners.read({ repository, issues: [route.issue] })).json);
  const raw = parse((await ports.github.issue({ repository, issue: Number(route.issue.split('/').pop()) })).json);
  if (raw.assignees?.length) onAssigned?.(raw);
  const labels = Array.isArray(raw.labels) ? raw.labels.map(x => typeof x === 'string' ? x : x.name) : null;
  return hash(JSON.stringify({ title: raw.title ?? '', body: raw.body ?? '' })) === route.record.inputs.find(x => x.key === route.issue)?.revision
    && labels !== null && hash(JSON.stringify(routingLabels(labels, areas))) === route.record.inputs.find(x => x.key === `${route.issue}#sort-labels`)?.revision
    && Array.isArray(owners.claims) && raw.state === 'open' && Array.isArray(raw.assignees) && !raw.assignees.length
    && (!labels.includes('pdd:working') || owners.claims.some(x => x.issue === route.issue && x.expired === true && x.active === false))
    && !owners.claims.some(x => x.issue === route.issue && x.active);
}

const routeIdentity = (route, mode) => hash(JSON.stringify({ record: route.record, action: route.action, owner: route.owner, mode: route.action === 'close' ? mode : '' }));
export async function routeSortIssues({ cwd, repository, snapshot, mode }, ports, write = pacedSortWrites(ports, { cwd, repository })) {
  cwd ??= ports.cwd ?? '';
  const plan = sortPlan({ snapshot });
  if (!['auto','observe'].includes(mode)) return plan;
  const unfinished = plan.routes.filter(route => {
    if (!['close','assign','link','question'].includes(route.action)) return false;
    const subject = snapshot.issues.find(x => x.key === route.issue);
    const noted = subject.sortRouteNotes?.includes(routeIdentity(route, mode));
    const label = route.action === 'question' ? 'pdd:needs-owner' : 'pdd:close-proposed';
    return !(noted && (route.action === 'link' || (route.action === 'question' || route.action === 'close' && mode === 'observe') && subject.labels?.includes(label)));
  });
  let admitted = 0;
  const failed = [];
  for (const route of unfinished) {
    if (admitted >= 10) break;
    try {
      if (ports.sortBudget && !await ports.sortBudget()) throw Error('sort-budget-pending');
      const issue = Number(route.issue.split('/').pop());
      const unowned = () => currentSortIssue({ cwd, repository, snapshot, route }, ports);
      if (!await unowned()) continue;
      admitted++;
      const marker = `<!-- pdd-issue-route:v1 -->\n<!-- ${routeIdentity(route, mode)} -->`;
      const evidence = [...route.evidence, route.record.status.fix, route.record.genuine.duplicateOf, route.record.genuine.reason].filter(Boolean).join('\n');
      const partsNote = route.reason === 'mixed-whole' ? `Whole issue, including all parts:\n${route.record.touchedAreas.map(x => `${x.area}: ${x.evidence.join('; ')}`).join('\n')}\n` : '';
      const note = route.action === 'close' ? `${mode === 'auto' ? 'Closing' : 'Propose closing'}: ${route.reason}.\n${evidence}\nReopen this issue with current release evidence if the problem remains.`
        : route.action === 'assign' ? `This issue belongs to @${route.owner} (${route.area}).\n${partsNote}${evidence}`
        : route.action === 'link' ? `Please track this work in https://github.com/${route.owner.slice(5)} (${route.area}).\n${evidence}`
        : route.record.question || 'Which area and owner should handle this issue?';
      // The native comment port recovers equal bodies and verifies their readback.
      const mutate = action => write(async () => {
        // A pacing wait is not ownership evidence. Admit immediately before effect.
        if (ports.settings && (await ports.settings.read({ cwd: cwd, repository })).mode !== mode) throw Error('sort-mode-changed');
        if (!await unowned()) throw Error('sort-owner-changed');
        return action();
      });
      if (route.action === 'question' || route.action === 'close' && mode === 'observe') {
        if (!ports.github.sortUpdate) throw Error('sort-write-unavailable');
        if (ports.github.ensureSortLabel) await ports.github.ensureSortLabel({ repository, label: route.action === 'question' ? 'pdd:needs-owner' : 'pdd:close-proposed', write: action => mutate(action) });
        const updated = await mutate(() => ports.github.sortUpdate({ repository, issue, label: route.action === 'question' ? 'pdd:needs-owner' : 'pdd:close-proposed', checkOwnership: unowned }));
        if (updated?.ok !== true) throw Error('sort-write-pending');
      }
      const noted = parse((await mutate(() => ports.github.appendComment({ repository, issue, body: `${note}\n\n${marker}`, checkOwnership: unowned }))).json);
      if (!noted.id) throw Error('sort-write-pending');
      if (route.action === 'assign' || route.action === 'close' && mode === 'auto') {
        if (!ports.github.sortUpdate) throw Error('sort-write-unavailable');
        const updated = await mutate(() => ports.github.sortUpdate({ repository, issue, checkOwnership: unowned, ...(route.action === 'assign' ? { assignee: route.owner } : { close: true }) }));
        if (updated?.ok !== true) throw Error('sort-write-pending');
      }
    } catch (error) { failed.push({ issue: route.issue, reason: error.message || 'sort-write-pending' }); }
  }
  return failed.length ? { ...plan, failed } : plan;
}

export function sortRequestFingerprint(snapshot, subjects) {
  if (!snapshot.sortContext) return null;
  const issues = snapshot.issues.filter(x => subjects.includes(x.key));
  const keys = new Set(issues.flatMap(x => [...sortInputs(snapshot, x), ...(x.sorts ?? []).flatMap(s => s.record?.inputs ?? [])]).map(x => x.key));
  return { revision: snapshot.sortContext.revision,
    inputs: snapshot.inputs.filter(x => keys.has(x.key)).slice().sort((a,b) => a.key.localeCompare(b.key)),
    heads: issues.map(x => [x.key, (x.sorts ?? []).map(s => [s.id, s.intact, s.authority])]) };
}

export const sortPastAssignees = items => [...new Set(items.filter(x => x.event === 'assigned' && typeof x.assignee?.login === 'string').map(x => x.assignee.login))];

// Group decisions reuse saved sorts. The durable record keeps the umbrella and
// the exact old heads which a post-merge sort must replace.
function groupStore({ cwd, repository }, ports) {
  if (ports.sortGroups) return ports.sortGroups;
  if (!cwd) return { read: async () => ({ groups: [] }), save: async () => ({ ok: false }) };
  const file = async () => {
    const git = await gitContext(cwd, ports);
    if (!git) throw Error('sort-groups-unavailable');
    return join(git.commonDir, 'pdd', `issue-groups-${hash(repository.toLowerCase()).slice(0, 16)}.json`);
  };
  return {
    read: async () => {
      try { return JSON.parse(readFileSync(await file(), 'utf8')); }
      catch (error) { if (error.code === 'ENOENT') return { groups: [] }; throw error; }
    },
    save: async ({ groups }) => {
      const path = await file(), temp = `${path}.${randomUUID()}.tmp`;
      mkdirSync(dirname(path), { recursive: true, mode: 0o700 });
      writeFileSync(temp, JSON.stringify({ groups }), { mode: 0o600 }); renameSync(temp, path);
      return { ok: true };
    },
  };
}
export async function readSortGroups(args, ports = {}) {
  const { groups } = await groupStore(args, ports).read(args);
  const prefix = `https://github.com/${args.repository.toLowerCase()}/issues/`;
  const issue = key => typeof key === 'string' && key.startsWith(prefix) && /^[1-9]\d*$/.test(key.slice(prefix.length));
  if (!Array.isArray(groups) || groups.some(g => !g || typeof g.rootCause !== 'string' || !g.rootCause.trim() || typeof g.area !== 'string'
    || !Array.isArray(g.members) || g.members.some(x => !issue(x)) || new Set(g.members).size !== g.members.length || !(g.umbrella === '' || issue(g.umbrella))
    || g.merged !== undefined && !/^https:\/\/github\.com\/[\w.-]+\/[\w.-]+\/pull\/[1-9]\d*$/.test(g.merged)
    || g.recheck !== undefined && (!Array.isArray(g.recheck) || g.recheck.some(x => !issue(x.issue) || !Array.isArray(x.heads) || x.heads.some(h => typeof h !== 'string')))
    || g.notified !== undefined && (!Array.isArray(g.notified) || g.notified.some(x => !issue(x)))
    || g.splitOut !== undefined && (!Array.isArray(g.splitOut) || g.splitOut.some(x => !issue(x))))) throw Error('sort-groups-unavailable');
  return groups;
}

export async function syncSortGroups({ cwd = '', repository, snapshot, mode, failures = [] }, ports, write = pacedSortWrites(ports, { cwd, repository })) {
  if (!snapshot.sortContext || !['auto','observe'].includes(mode)) return [];
  const saved = snapshot.sortContext.groups ?? [], before = JSON.stringify(saved);
  // An ordinary close is not a merge. The native adapter checks the actual
  // closing event's PR. An unreadable result preserves the existing hold.
  for (const group of saved.filter(x => !x.merged && x.umbrella)) {
    const umbrella = snapshot.issues.find(x => x.key === group.umbrella);
    if (umbrella?.state !== 'completed' || umbrella.authority !== 'trusted' || !ports.github.sortMergedFix) continue;
    const result = await ports.github.sortMergedFix({ repository, issue: Number(group.umbrella.split('/').pop()) });
    if (!result.url) continue;
    group.merged = result.url;
    group.recheck = group.members.map(issue => ({ issue, heads: (snapshot.issues.find(x => x.key === issue)?.sorts ?? []).map(x => x.id) }));
  }
  const groups = sortPlan({ snapshot }).groups;
  const current = async group => {
    if (ports.settings && (await ports.settings.read({ cwd, repository })).mode !== mode) return false;
    if (!snapshot.complete) return false;
    const plan = sortPlan({ snapshot });
    return group.members.length > 0 && (await Promise.all(group.members.filter(issue => snapshot.issues.find(x => x.key === issue)?.execution !== 'running').map(issue => {
      const route = plan.routes.find(x => x.issue === issue);
      return route?.record && route.action === 'work'
        ? currentSortIssue({ cwd, repository, snapshot, route }, ports) : false;
    }))).every(Boolean);
  };
  let operations = 0;
  try {
    for (const group of groups.filter(x => !x.merged)) {
      try {
        const needsNote = group.umbrella && snapshot.issues.find(x => x.key === group.umbrella)?.execution === 'running'
          && JSON.stringify(group.notified ?? []) !== JSON.stringify(group.members);
        if (!needsNote) continue;
        if (++operations > 10) break;
        const result = await write(async () => {
          if (!await current(group)) throw Error('sort-owner-changed');
          return ports.github.appendComment({ repository, issue: Number(group.umbrella.split('/').pop()),
            body: `Group members (${group.rootCause}):\n${group.members.map(x => `- ${x}`).join('\n')}\n\n<!-- pdd-issue-route:v1 -->\n<!-- group-${hash(JSON.stringify(group.members))} -->` });
        });
        if (!parse(result.json).id) throw Error('sort-write-pending');
        group.notified = [...group.members];
      } catch (error) { failures.push({ issue: group.umbrella || group.members[0], reason: error.message || 'sort-write-pending' }); }
    }
  } finally {
    if (JSON.stringify(groups) !== before) {
      if (!(await groupStore({ cwd, repository }, ports).save({ cwd, repository, groups })).ok) throw Error('sort-write-pending');
    }
    snapshot.sortContext.groups = groups;
  }
  return groups;
}

export async function claimSortGroup({ cwd = '', repository, group, umbrella: targetUmbrella, coordinatorId = 'coordinator', machine = 'local' }, ports = {}) {
  if (!group && targetUmbrella && (cwd || ports.sortGroups)) {
    const groups = await readSortGroups({ cwd, repository }, ports).catch(() => []);
    group = groups.find(g => !g.merged && (g.umbrella === targetUmbrella || g.members.includes(targetUmbrella))) ?? null;
  }
  if (!group || !Array.isArray(group.members) || group.members.length < 2 || !group.members.includes(group.umbrella)
    || !ports.claimIssue || !ports.releaseClaim) return { ok: false, umbrella: '', members: [], claims: [], reason: 'group-claim-unavailable' };
  const umbrella = group.umbrella;
  const ordered = [umbrella, ...group.members.filter(m => m !== umbrella)];
  const claims = [], created = [];
  try {
    for (const key of ordered) {
      const result = await ports.claimIssue({ cwd, repository, issue: key, group: { umbrella, members: group.members }, coordinatorId, machine });
      const claim = result?.claim;
      if (result?.ok !== true || !claim || claim.issue !== key || claim.coordinatorId !== coordinatorId || claim.machine !== machine
        || claim.owner !== coordinatorId || claim.active !== true || !/^[1-9][0-9]*$/.test(String(claim.commentId ?? ''))
        || !/^[1-9][0-9]*$/.test(String(claim.labelEventId ?? ''))) throw Error(result?.reason || 'claim-failed');
      claims.push({ issue: key, commentId: String(claim.commentId), labelEventId: String(claim.labelEventId), coordinatorId, machine, active: true, owner: coordinatorId });
      if (result.created === true) created.push(claims.at(-1));
    }
    return { ok: true, umbrella, members: ordered, claims, createdIssues: created.map(claim => claim.issue) };
  } catch (error) {
    const rollback = [];
    for (const claim of created.reverse()) {
      try {
        const result = await ports.releaseClaim({ cwd, repository, claim, coordinatorId, machine });
        if (result?.state !== 'released') rollback.push({ issue: claim.issue, reason: 'claim-release-unconfirmed' });
      } catch { rollback.push({ issue: claim.issue, reason: 'claim-release-unavailable' }); }
    }
    return { ok: false, umbrella, members: [], claims: [], rollback, reason: error.message || 'claim-failed' };
  }
}

export async function releaseSortGroup({ cwd = '', repository, claims = [], coordinatorId = 'coordinator', machine = 'local' }, ports = {}) {
  if (!Array.isArray(claims) || !ports.releaseClaim) return { ok: false, released: [], failed: [] };
  const released = [], failed = [];
  for (const claim of claims) {
    if (!claim || typeof claim.issue !== 'string' || claim.coordinatorId !== coordinatorId || claim.machine !== machine
      || claim.owner !== coordinatorId || claim.active !== true || !/^[1-9][0-9]*$/.test(String(claim.commentId ?? ''))
      || !/^[1-9][0-9]*$/.test(String(claim.labelEventId ?? ''))) {
      failed.push({ issue: claim?.issue ?? '', reason: 'claim-identity-invalid' });
      continue;
    }
    try {
      const result = await ports.releaseClaim({ cwd, repository, claim, coordinatorId, machine });
      if (result?.state === 'released') released.push(claim.issue);
      else failed.push({ issue: claim.issue, reason: 'claim-release-unconfirmed' });
    } catch { failed.push({ issue: claim.issue, reason: 'claim-release-unavailable' }); }
  }
  return { ok: failed.length === 0, released, failed };
}

export async function splitSortGroupMember({ cwd = '', repository, umbrella, member, reason = 'member-diverged', coordinatorId = 'coordinator', machine = 'local', claim = null }, ports = {}) {
  const store = groupStore({ cwd, repository }, ports);
  const { groups = [] } = await store.read({ cwd, repository });
  const targetKey = typeof member === 'string' && member.startsWith('https://github.com/') ? member : '';
  const targetNum = String(member ?? '').replace(/^#/, '').split('/').pop();
  const idx = groups.findIndex(g => !g.merged && (g.umbrella === umbrella || g.members.some(m => m === member || m.split('/').pop() === targetNum)));
  if (idx < 0) return { ok: true, umbrella: '', members: [], splitOut: [targetKey || member], standalone: null, alreadySplit: true };
  const current = groups[idx];
  const existingMember = current.members.find(m => m === member || m.split('/').pop() === targetNum);
  if (!existingMember) return { ok: current.splitOut?.some(m => m === member || m.split('/').pop() === targetNum) === true,
    umbrella: current.umbrella, members: current.members, splitOut: current.splitOut ?? [], standalone: null, alreadySplit: true };
  const split = splitGroupMember({ group: current, member: existingMember, reason });
  if (claim) {
    const enriched = { ...claim, coordinatorId, machine, active: true, owner: coordinatorId };
    const released = await releaseSortGroup({ cwd, repository, claims: [enriched], coordinatorId, machine }, ports);
    if (!released.ok) return { ok: false, ...split, release: released };
  }
  groups[idx] = split.group ?? { ...current, umbrella: split.umbrella, members: split.members, splitOut: split.splitOut };
  await store.save({ cwd, repository, groups });
  const issueNum = Number(split.splitMember.split('/').pop());
  const splitBody = `Split from group ${current.umbrella}: ${reason}.\n\n<!-- pdd-issue-route:v1 -->\n<!-- split-${hash(`${current.umbrella}:${split.splitMember}:${reason}`)} -->`;
  const comments = ports.github?.page ? parse((await ports.github.page({ repository, issue: issueNum, kind: 'comments', cursor: '' })).json) : null;
  if (!(comments?.items ?? []).some(row => row.body?.includes(`<!-- split-${hash(`${current.umbrella}:${split.splitMember}:${reason}`)} -->`))) {
    if (ports.github?.appendComment) await ports.github.appendComment({ repository, issue: issueNum, body: splitBody });
    else if (ports.execFile) await ports.execFile('gh', ['issue', 'comment', String(issueNum), '--body-file', '-'], { cwd, input: splitBody });
  }
  return { ok: true, ...split };
}
