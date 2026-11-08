import { machineJson } from './autopilot-store.mjs';
import { tracksReviewInput } from './issue-review-context.mjs';
// Implements prompts/cli/issue-sort-github.prompt.md.
import { createHash, randomUUID } from 'node:crypto';
import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { validSort, selectedSort, sortInputs, sortPlan, sortSourceKey } from './issue-sort.mjs';
import { gitContext, stateDirFor } from './workflow-runs.mjs';
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
  const legacyRevision = hash(JSON.stringify({ areas: context.areas, codeowners: context.codeowners, release: context.release }));
  const revision = snapshot.issues.some(i => Array.isArray(i.namedSources)) ? hash(JSON.stringify({ areas: context.areas, codeowners: context.codeowners })) : legacyRevision;
  for (const issue of snapshot.issues) {
    const key = `${issue.key}#sort-labels`;
    snapshot.inputs = snapshot.inputs.filter(x => x.key !== key);
    snapshot.inputs.push({ key, revision: hash(JSON.stringify(routingLabels(issue.labels ?? [], context.areas))) });
  }
  snapshot.sortContext = { ...context, key, revision, legacyRevision, groups: groups ?? await readSortGroups({ cwd, repository: snapshot.repository }, ports), draft: context.areas === undefined ? draftAreas({ ...context, labels: [...new Set(snapshot.issues.flatMap(x => x.labels ?? []))], assignees: [...new Set(snapshot.issues.flatMap(x => [...(x.assignees ?? []), ...(x.pastAssignees ?? [])]))] }) : null };
  snapshot.inputs = snapshot.inputs.filter(x => x.key !== key); snapshot.inputs.push({ key, revision });
  return snapshot;
}
export function sortSubjects(snapshot) { return sortPlan({ snapshot }).queued; }
export function prepareSortContext(snapshot) {
  if (!snapshot.sortContext) return {};
  return { sort: { ...snapshot.sortContext, schema: 'pdd.issue-sort.v1', required: sortSubjects(snapshot), records: snapshot.issues.flatMap(x => selectedSort(snapshot, x) ?? []) } };
}
const sameSort = (saved, record, issue) => !!saved
  && JSON.stringify({ ...saved, summary: undefined }) === JSON.stringify({ ...record, summary: undefined })
  && (saved.summary ?? issue.title.slice(0, 600)) === (record.summary ?? issue.title.slice(0, 600));
export function validateSortBatch({ snapshot, prepared, issues, sorts }) {
  if (!prepared.sortContext) { if (sorts !== undefined) throw Error('invalid-analysis'); return []; }
  if (!Array.isArray(sorts) || sorts.some(x => !validSort(x)) || new Set(sorts.map(x => x.issue)).size !== sorts.length || sorts.length !== issues.length || sorts.some(x => !issues.includes(x.issue))) throw Error('invalid-analysis');
  const current = new Map([...snapshot.issues, ...snapshot.inputs].map(x => [x.key, x.revision]));
  for (const record of sorts) {
    const issue = snapshot.issues.find(x => x.key === record.issue), old = prepared.issues.find(x => x.key === record.issue);
    if (sameSort(selectedSort(snapshot, issue), record, issue)) continue;
    const ids = (old?.sorts ?? []).filter(x => x.authority !== 'outsider');
    const superseded = new Set(ids.filter(x => x.intact && validSort(x.record)).flatMap(x => x.record.base));
    const heads = ids.filter(x => !superseded.has(x.id)).map(x => x.id).sort();
    if (record.paths.some(path => !record.inputs.some(x => x.key === sortSourceKey(snapshot.repository, path)))) throw Error('invalid-analysis');
    if (!issue || issue.authority !== 'trusted' || record.status.release !== snapshot.sortContext?.release || JSON.stringify(record.base.slice().sort()) !== JSON.stringify(heads)
      || sortInputs(snapshot, issue).some(x => !record.inputs.some(y => y.key === x.key && (y.revision === x.revision || x.key === snapshot.sortContext?.key && y.revision === snapshot.sortContext?.legacyRevision))) || record.inputs.some(x => current.get(x.key) !== x.revision && !(x.key === snapshot.sortContext?.key && x.revision === snapshot.sortContext?.legacyRevision))) throw Error('input-changed');
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
    const result = await action();
    last = Date.parse((await ports.clock.now({})).iso);
    return result;
  };
  Object.defineProperty(write, 'remaining', { get: () => 20 - attempts });
  return write;
}
export async function saveSortBatch({ repository, snapshot, sorts }, ports, write = pacedSortWrites(ports, { repository })) {
  for (const record of sorts) {
    const issue = snapshot.issues.find(x => x.key === record.issue);
    if (sameSort(selectedSort(snapshot, issue), record, issue)) continue;
    if (ports.reviewAccess?.managed && (issue.execution !== 'idle' || issue.sortOpenPr === true
      || !Array.isArray(issue.assignees) || issue.assignees.length
      || issue.holds.some(hold => /claim/i.test(hold) && !/^Expired claim\b/.test(hold)))) continue;
    record.summary ??= issue.title.slice(0, 600);
    const body = `Sort: ${record.belongs.kind}; ${record.status.state}; ${record.genuine.kind}.\n${record.status.evidence.join('\n')}\n\n<!-- pdd-issue-sort:v1 -->\n\`\`\`json\n${JSON.stringify(record)}\n\`\`\``;
    const route = { issue: record.issue, record };
    const result = parse((await write(async () => { if (!await sortOwnership({ repository, route, areas: snapshot.sortContext.areas }, ports)) throw Error('sort-owner-changed'); return ports.github.appendComment({ repository, issue: Number(record.issue.split('/').pop()), body, checkOwnership: () => sortOwnership({ repository, route, areas: snapshot.sortContext.areas }, ports) }); })).json);
    if (!result.id) throw Error('sort-write-pending');
    (issue.sorts ??= []).push({ id: String(result.id), authority: 'trusted', intact: true, record });
  }
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
  const source = route.record.inputs.filter(x => /\/blob\/HEAD\//.test(x.key) && (tracksReviewInput(subject, x.key) || route.record.paths.some(path => x.key === `https://github.com/${repository.toLowerCase()}/blob/HEAD/${path.split('/').map(encodeURIComponent).join('/')}`)));
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
async function sortOwnership({ repository, route, areas }, ports) {
  // Keep these observations after all potentially long evidence reads. The native
  // update calls this again inside its mutation guard, after any admission wait.
  const owners = parse((await ports.owners.read({ repository, issues: [route.issue] })).json);
  const raw = parse((await ports.github.issue({ repository, issue: Number(route.issue.split('/').pop()) })).json);
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
  for (const route of unfinished) {
    if (admitted >= 10) break;
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
  }
  return plan;
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
  const storage = async () => {
    const git = await gitContext(cwd, ports);
    if (!git) throw Error('sort-groups-unavailable');
    const key = hash(repository.toLowerCase()).slice(0, 16);
    return machineJson({ root: ports.autopilotStateRoot ?? join(stateDirFor(ports), 'autopilot'),
      bucket: 'cache', key: `issue-groups:${key}`,
      file: join(git.commonDir, 'pdd', `issue-groups-${key}.json`) }, ports);
  };
  return {
    read: async () => (await storage()).read({ groups: [] }),
    save: async ({ groups }) => {
      (await storage()).write({ groups });
      return { ok: true };
    },
  };
}
export async function readSortGroups(args, ports = {}) {
  const { groups } = await groupStore(args, ports).read(args);
  const prefix = `https://github.com/${args.repository.toLowerCase()}/issues/`;
  const issue = key => typeof key === 'string' && key.startsWith(prefix) && /^[1-9]\d*$/.test(key.slice(prefix.length));
  if (!Array.isArray(groups) || groups.some(g => !g || !/^[a-z\d]+(?:-[a-z\d]+)*$/.test(g.rootCause) || typeof g.area !== 'string'
    || !Array.isArray(g.members) || g.members.some(x => !issue(x)) || new Set(g.members).size !== g.members.length || !(g.umbrella === '' || issue(g.umbrella))
    || g.merged !== undefined && !/^https:\/\/github\.com\/[\w.-]+\/[\w.-]+\/pull\/[1-9]\d*$/.test(g.merged)
    || g.recheck !== undefined && (!Array.isArray(g.recheck) || g.recheck.some(x => !issue(x.issue) || !Array.isArray(x.heads) || x.heads.some(h => typeof h !== 'string')))
    || g.notified !== undefined && (!Array.isArray(g.notified) || g.notified.some(x => !issue(x))))) throw Error('sort-groups-unavailable');
  return groups;
}
async function liveSortUmbrellas({ repository, rootCause }, ports) {
  const marker = `<!-- pdd-issue-group:v1 ${rootCause} -->`, found = [], seen = new Set();
  let cursor = '';
  do {
    if (seen.has(cursor)) throw Error('sort-groups-unavailable');
    seen.add(cursor);
    const page = parse((await ports.github.page({ repository, kind: 'issues', issue: 0, cursor })).json);
    if (page.error || !Array.isArray(page.items) || typeof page.next !== 'string') throw Error('sort-groups-unavailable');
    for (const issue of page.items.filter(x => !x.pull_request && x.state === 'open' && x.body?.includes(marker))) {
      const authority = (await ports.authority.read({ repository, author: issue.user?.login ?? '' })).authority;
      if (authority === 'outsider') continue;
      if (authority !== 'trusted' || !issue.html_url?.startsWith(`https://github.com/${repository.toLowerCase()}/issues/`)
        || !/^[1-9]\d*$/.test(issue.html_url.split('/').pop())) throw Error('sort-groups-unavailable');
      if (!found.includes(issue.html_url)) found.push(issue.html_url);
    }
    cursor = page.next;
  } while (cursor);
  return found;
}
const dedicatedGroup = group => group.umbrella && !group.members.includes(group.umbrella);
export async function syncSortGroups({ cwd = '', repository, snapshot, mode }, ports, write = pacedSortWrites(ports, { cwd, repository })) {
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
  let groups = sortPlan({ snapshot }).groups;
  const current = async group => {
    if (ports.settings && (await ports.settings.read({ cwd, repository })).mode !== mode) return false;
    if (!snapshot.complete) return false;
    const plan = sortPlan({ snapshot });
    return group.members.length > 0 && (await Promise.all(group.members.filter(issue => !(issue === group.umbrella && snapshot.issues.find(x => x.key === issue)?.execution === 'running')).map(issue => {
      const route = plan.routes.find(x => x.issue === issue);
      return route?.record && route.action === 'work' || route?.record && route.reason === 'group-umbrella-pending'
        ? currentSortIssue({ cwd, repository, snapshot, route }, ports) : false;
    }))).every(Boolean);
  };
  let operations = 0;
  try {
    for (const group of groups.filter(x => !x.merged)) {
      const needsUmbrella = group.members.length >= 3 || group.area.includes(',');
      const workRoute = sortPlan({ snapshot }).routes.find(x => x.issue === group.umbrella);
      const needsCreation = needsUmbrella && !dedicatedGroup(group) && workRoute?.reason !== 'owned' && mode === 'auto';
      const needsNote = group.umbrella && snapshot.issues.find(x => x.key === group.umbrella)?.execution === 'running'
        && JSON.stringify(group.notified ?? []) !== JSON.stringify(group.members);
      if (!needsCreation && !needsNote) continue;
      if (needsCreation && snapshot.issues.filter(x => x.authority === 'trusted' && x.state === 'open' && x.sortText?.includes(`<!-- pdd-issue-group:v1 ${group.rootCause} -->`)).length > 1) continue;
      if (++operations > 10) break;
      if (needsCreation) {
        const marker = `<!-- pdd-issue-group:v1 ${group.rootCause} -->`;
        // A trusted matching issue in the observed index recovers a lost save.
        const recovered = snapshot.issues.filter(x => x.authority === 'trusted' && x.state === 'open' && x.sortText?.includes(marker));
        if (recovered.length > 1) continue;
        if (recovered.length === 1) group.umbrella = recovered[0].key;
        else {
          if (!ports.github.createSortUmbrella || !ports.github.withSortGroupAdmission) continue;
          const umbrella = await ports.github.withSortGroupAdmission({ repository, rootCause: group.rootCause, write }, async () => {
            // A second machine may have completed after our snapshot. Recover under
            // shared admission, before any new issue POST.
            const live = await liveSortUmbrellas({ repository, rootCause: group.rootCause }, ports);
            if (live.length > 1) return '';
            if (live.length === 1) return live[0];
            const plan = sortPlan({ snapshot });
            const body = `Shared cause: ${group.rootCause}.\nOne fix: correct this shared cause once for all linked member requirements.\n\n${group.members.map(issue => `- ${issue}\n${(plan.routes.find(x => x.issue === issue)?.evidence ?? []).join('\n')}`).join('\n')}\n\n${marker}`;
            const created = await write(async () => {
              if (!await current(group)) return null;
              return ports.github.createSortUmbrella({ repository, title: `Global fix: ${group.rootCause}`, body });
            });
            if (created === null) return '';
            const value = parse(created.json);
            if (!value?.html_url?.startsWith(`https://github.com/${repository.toLowerCase()}/issues/`) || !Number.isSafeInteger(value.number) || value.number < 1
              || value.html_url !== `https://github.com/${repository.toLowerCase()}/issues/${value.number}`) throw Error('sort-write-pending');
            return value.html_url;
          });
          if (!umbrella) continue;
          group.umbrella = umbrella;
        }
        group.notified = [...group.members];
      }
      if (needsNote) {
        const result = await write(async () => {
          if (!await current(group)) throw Error('sort-owner-changed');
          return ports.github.appendComment({ repository, issue: Number(group.umbrella.split('/').pop()),
            body: `Group members (${group.rootCause}):\n${group.members.map(x => `- ${x}`).join('\n')}\n\n<!-- pdd-issue-route:v1 -->\n<!-- group-${hash(JSON.stringify(group.members))} -->` });
        });
        if (!parse(result.json).id) throw Error('sort-write-pending');
        group.notified = [...group.members];
      }
    }
  } finally {
    if (JSON.stringify(groups) !== before) {
      if (!(await groupStore({ cwd, repository }, ports).save({ cwd, repository, groups })).ok) throw Error('sort-write-pending');
    }
    snapshot.sortContext.groups = groups;
  }
  return groups;
}
