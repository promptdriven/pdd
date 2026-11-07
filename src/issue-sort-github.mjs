// Implements prompts/cli/issue-sort-github.prompt.md.
import { createHash } from 'node:crypto';
import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { validSort, selectedSort, sortInputs, sortPlan } from './issue-sort.mjs';
import { draftAreas } from './autopilot-areas.mjs';
const parse = x => typeof x === 'string' ? JSON.parse(x) : x;
const hash = x => createHash('sha256').update(x).digest('hex');
export const sortBookkeeping = body => /<!--\s*pdd-issue-(?:sort|route):v1\s*-->/.test(body ?? '');
export function readSortComment(comment, authority) {
  if (!/<!--\s*pdd-issue-sort:v1\s*-->/.test(comment.body ?? '')) return null;
  let record;
  try { record = JSON.parse(/```json\s*([\s\S]*?)```/.exec(comment.body)?.[1]); } catch { /* Keep invalid trusted heads visible. */ }
  return { id: String(comment.id), record: record ?? null, authority, intact: validSort(record) && typeof comment.created_at === 'string' && comment.created_at === comment.updated_at };
}
export async function addSortContext(snapshot, cwd, ports) {
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
  snapshot.sortContext = { ...context, key, revision, draft: context.areas === undefined ? draftAreas({ ...context, labels: [...new Set(snapshot.issues.flatMap(x => x.labels ?? []))], assignees: [...new Set(snapshot.issues.flatMap(x => x.assignees ?? []))] }) : null };
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
  if (!Array.isArray(sorts) || sorts.some(x => !validSort(x)) || new Set(sorts.map(x => x.issue)).size !== sorts.length || sorts.length !== issues.length || sorts.some(x => !issues.includes(x.issue))) throw Error('invalid-analysis');
  const current = new Map([...snapshot.issues, ...snapshot.inputs].map(x => [x.key, x.revision]));
  for (const record of sorts) {
    const issue = snapshot.issues.find(x => x.key === record.issue), old = prepared.issues.find(x => x.key === record.issue);
    if (JSON.stringify(selectedSort(snapshot, issue)) === JSON.stringify(record)) continue;
    const ids = (old?.sorts ?? []).filter(x => x.authority !== 'outsider');
    const superseded = new Set(ids.filter(x => x.intact && validSort(x.record)).flatMap(x => x.record.base));
    const heads = ids.filter(x => !superseded.has(x.id)).map(x => x.id).sort();
    if (!issue || issue.authority !== 'trusted' || record.status.release !== snapshot.sortContext?.release || JSON.stringify(record.base.slice().sort()) !== JSON.stringify(heads)
      || sortInputs(snapshot, issue).some(x => !record.inputs.some(y => y.key === x.key && y.revision === x.revision)) || record.inputs.some(x => current.get(x.key) !== x.revision)) throw Error('input-changed');
    const currentHeads = (issue.sorts ?? []).map(x => [x.id, x.intact]);
    if (JSON.stringify(currentHeads) !== JSON.stringify((old.sorts ?? []).map(x => [x.id, x.intact]))) throw Error('input-changed');
  }
  return sorts;
}
// One effect stream per operation; the caller shares it for saving and routing.
export function pacedSortWrites(ports) {
  let last = null;
  return async action => {
    const now = Date.parse((await ports.clock.now({})).iso);
    if (last !== null && now - last < 1000) await (ports.wait?.sleep ?? (async ({ ms }) => new Promise(resolve => setTimeout(resolve, ms))))({ ms: 1000 - (now - last) });
    if (ports.admitEffect && !await ports.admitEffect()) throw Error('sort-write-pending');
    const result = await action();
    last = Date.parse((await ports.clock.now({})).iso);
    return result;
  };
}
export async function saveSortBatch({ repository, snapshot, sorts }, ports, write = pacedSortWrites(ports)) {
  for (const record of sorts) {
    const issue = snapshot.issues.find(x => x.key === record.issue);
    if (JSON.stringify(selectedSort(snapshot, issue)) === JSON.stringify(record)) continue;
    const body = `Sort: ${record.belongs.kind}; ${record.status.state}; ${record.genuine.kind}.\n${record.status.evidence.join('\n')}\n\n<!-- pdd-issue-sort:v1 -->\n\`\`\`json\n${JSON.stringify(record)}\n\`\`\``;
    const result = parse((await write(() => ports.github.appendComment({ repository, issue: Number(record.issue.split('/').pop()), body }))).json);
    if (!result.id) throw Error('sort-write-pending');
    (issue.sorts ??= []).push({ id: String(result.id), authority: 'trusted', intact: true, record });
  }
}
export async function routeSortIssues({ repository, snapshot, mode }, ports, write = pacedSortWrites(ports)) {
  const plan = sortPlan({ snapshot });
  if (mode === 'off') return plan;
  for (const route of plan.routes.filter(x => ['close','assign','link','question'].includes(x.action))) {
    const issue = Number(route.issue.split('/').pop());
    const unowned = async () => {
      const raw = parse((await ports.github.issue({ repository, issue })).json);
      const owners = parse((await ports.owners.read({ repository, issues: [route.issue] })).json);
      return hash(JSON.stringify({ title: raw.title ?? '', body: raw.body ?? '' })) === route.record.inputs.find(x => x.key === route.issue)?.revision && Array.isArray(owners.claims) && raw.state === 'open' && Array.isArray(raw.assignees) && !raw.assignees.length && Array.isArray(raw.labels) && !raw.labels.some(x => (typeof x === 'string' ? x : x.name) === 'pdd:working') && !(owners.claims ?? []).some(x => x.issue === route.issue && x.active);
    };
    if (!await unowned()) continue;
    const marker = `<!-- pdd-issue-route:v1 -->\n<!-- ${hash(JSON.stringify({ record: route.record, action: route.action, owner: route.owner, mode: route.action === 'close' ? mode : '' }))} -->`;
    const evidence = [...route.evidence, route.record.status.fix, route.record.genuine.duplicateOf, route.record.genuine.reason].filter(Boolean).join('\n');
    const note = route.action === 'close' ? `${mode === 'auto' ? 'Closing' : 'Propose closing'}: ${route.reason}.\n${evidence}\nReopen this issue with current release evidence if the problem remains.`
      : route.action === 'assign' ? `This issue belongs to @${route.owner} (${route.area}).\n${evidence}`
      : route.action === 'link' ? `Please track this work in https://github.com/${route.owner.slice(5)} (${route.area}).\n${evidence}`
      : route.record.question || 'Which area and owner should handle this issue?';
    // The native comment port recovers equal bodies and verifies their readback.
    const mutate = async action => { if (!await unowned()) throw Error('sort-owner-changed'); return write(action); };
    if (route.action === 'question' || route.action === 'close' && mode === 'observe') {
      if (!ports.github.sortUpdate) throw Error('sort-write-unavailable');
      if (ports.github.ensureSortLabel) await ports.github.ensureSortLabel({ repository, label: route.action === 'question' ? 'pdd:needs-owner' : 'pdd:close-proposed', write: action => mutate(action) });
      await mutate(() => ports.github.sortUpdate({ repository, issue, label: route.action === 'question' ? 'pdd:needs-owner' : 'pdd:close-proposed' }));
    }
    await mutate(() => ports.github.appendComment({ repository, issue, body: `${note}\n\n${marker}` }));
    if (route.action === 'assign' || route.action === 'close' && mode === 'auto') {
      if (!ports.github.sortUpdate) throw Error('sort-write-unavailable');
      await mutate(() => ports.github.sortUpdate({ repository, issue, ...(route.action === 'assign' ? { assignee: route.owner } : { close: true }) }));
    }
  }
  return plan;
}
