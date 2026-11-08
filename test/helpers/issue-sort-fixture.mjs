// Synthetic GitHub ports, following issue-dependencies-freshness.test.mjs.
import { createHash } from 'node:crypto';
import { prepareDependencyIntake, completeDependencyIntake } from '../../src/issue-dependencies-intake.mjs';
export const repository = 'example/project';
export const key = n => `https://github.com/${repository}/issues/${n}`;
const hash = x => createHash('sha256').update(x).digest('hex');
const routingLabels = (labels, areas) => labels.filter(x => !['pdd:working','pdd:stuck','pdd:code-pending','pdd:close-proposed','pdd:needs-owner'].includes(x) || (areas ?? []).some(a => a.match?.labels?.includes(x))).slice().sort();
const reply = x => ({ json: JSON.stringify(x) });
export const revision = issue => hash(JSON.stringify({ title: issue.title, body: issue.body }));
export function fixture(numbers = [1], options = {}) {
  let now = Date.parse('2026-11-07T12:00:00Z'), next = 100;
  const context = { codeowners: '', release: '1.0.0', folders: ['src'], ...options.context };
  const issues = numbers.map(number => ({ id: number, number, html_url: key(number), title: `Synthetic issue ${number}`, body: 'A current product defect.', state: 'open', user: { login: 'owner' }, labels: [], assignees: [] }));
  let groups = [];
  const reservations = new Set();
  const comments = new Map(numbers.map(n => [n, []])), writes = [], waits = [], claims = [], files = new Map();
  const comment = (body, login = 'owner') => ({ id: String(next++), body, created_at: new Date(now).toISOString(), updated_at: new Date(now).toISOString(), user: { login } });
  const append = (n, body, login) => { const c = comment(body, login); comments.get(n).push(c); return c; };
  const ports = {
    sortGroups: { read: async () => ({ groups: structuredClone(groups) }), save: async ({ groups: next }) => { groups = structuredClone(next); return { ok: true }; } },
    sortContext: { read: async () => ({ ...context }) },
    settings: { read: async () => ({ mode: options.mode ?? 'auto' }) },
    authority: { read: async ({ author }) => ({ authority: author === 'outsider' ? 'outsider' : 'trusted' }) },
    owners: { read: async () => reply({ claims, runs: [], runsKnown: true, localOwner: 'coordinator' }) },
    context: { read: async ({ inputs = [] }) => reply({ inputs: inputs.flatMap(x => files.has(x.key) ? [{ key: x.key, revision: files.get(x.key) }] : []), conditions: [], execution: [] }) },
    evidence: { read: async () => reply({ source: [], requirements: [] }) },
    clock: { now: async () => ({ iso: new Date(now).toISOString() }) },
    wait: { sleep: async ({ ms }) => { waits.push(ms); now += ms; } },
    github: {
      issue: async ({ issue }) => reply(issues.find(x => x.number === issue)),
      page: async ({ kind, issue }) => reply({ items: kind === 'issues' ? issues.filter(x => x.state === 'open') : kind === 'comments' ? comments.get(issue) ?? [] : [], next: '' }),
      appendComment: async ({ issue, body }) => {
        const existing = comments.get(issue).find(x => x.body === body);
        if (existing) return reply(existing);
        writes.push({ at: now, issue, kind: 'comment', body }); return reply(append(issue, body));
      },
      sortUpdate: async ({ issue, label, assignee, close }) => {
        const raw = issues.find(x => x.number === issue);
        if (label && raw.labels.includes(label) || close && raw.state === 'closed' || assignee && raw.assignees.some(x => x.login === assignee)) return { ok: true };
        writes.push({ at: now, issue, kind: label ? 'label' : assignee ? 'assign' : 'close', label, assignee });
        if (label) raw.labels.push(label);
        if (assignee) raw.assignees = [{ login: assignee }];
        if (close) raw.state = 'closed';
        return { ok: true };
      },
      // A shared in-memory admission service. Native HTTP pacing is tested separately.
      withSortGroupAdmission: async ({ rootCause }, action) => {
        if (reservations.has(rootCause)) return '';
        reservations.add(rootCause);
        const result = await action();
        reservations.delete(rootCause);
        return result;
      },
      createSortUmbrella: async ({ title, body }) => {
        const number = Math.max(...issues.map(x => x.number)) + 100;
        const raw = { id: number, number, html_url: key(number), title, body, state: 'open', user: { login: 'owner' }, labels: [], assignees: [] };
        issues.push(raw); comments.set(number, []);
        writes.push({ at: now, issue: number, kind: 'umbrella', body }); return reply(raw);
      },
      sortMergedFix: async () => ({ url: options.mergedFix ?? '' }),
      addBlocker: async () => { throw Error('Unexpected native dependency mutation'); },
    },
  };
  const w = { issues, comments, ports, context, writes, waits, claims, files, append };
  w.record = (number, changes = {}) => {
    const issue = issues.find(x => x.number === number), contextKey = `https://github.com/${repository}#autopilot-areas`;
    const record = { schema_version: 'pdd.issue-sort.v1', issue: key(number), base: [],
      inputs: [{ key: key(number), revision: revision(issue) }, { key: `${key(number)}#sort-labels`, revision: hash(JSON.stringify(routingLabels(issue.labels, context.areas))) }, { key: contextKey, revision: hash(JSON.stringify({ areas: context.areas, codeowners: context.codeowners, release: context.release })) }],
      belongs: { kind: 'area', area: 'cli', repository: '' }, status: { state: 'still-happens', release: context.release, fix: '', evidence: ['src/cli.mjs:12'] },
      genuine: { kind: 'bug', duplicateOf: '', reason: '' }, paths: ['src/cli.mjs'], rootCause: 'shared-context', severity: 'medium', question: '', ...changes };
    for (const path of record.paths) {
      const key = `https://github.com/${repository}/blob/HEAD/${path.split('/').map(encodeURIComponent).join('/')}`;
      if (!files.has(key)) files.set(key, 'source-v1');
      record.inputs.push({ key, revision: files.get(key) });
    }
    return record;
  };
  w.save = record => append(Number(record.issue.split('/').pop()), `Sort record.\n<!-- pdd-issue-sort:v1 -->\n\`\`\`json\n${JSON.stringify(record)}\n\`\`\``);
  w.review = number => append(number, `<!-- pdd-dependency-review:v1 -->\n\`\`\`json\n${JSON.stringify({ schema_version: 'pdd.dependency-review.v1', review: { analysis: 'No prerequisite is needed.', base: [], continuation: '', issue: key(number), inputs: [{ key: key(number), revision: revision(issues.find(x => x.number === number)) }], candidates: issues.map(x => ({ key: x.html_url, revision: revision(x) })), outcome: 'complete', dependencies: [], questions: [], effects: 'none' } })}\n\`\`\``);
  return w;
}
export async function complete(w, records) {
  const { request } = await prepareDependencyIntake({ repository }, w.ports);
  const snapshot = JSON.parse(request.snapshotJson);
  const reviews = request.issues.map(issue => ({ analysis: 'No prerequisite is needed.', base: snapshot.reviews.filter(r => r.issue === issue).map(r => r.id), continuation: '', issue,
    inputs: [{ key: issue, revision: snapshot.issues.find(x => x.key === issue).revision }], candidates: snapshot.issues.map(x => ({ key: x.key, revision: x.revision })), outcome: 'complete', dependencies: [], questions: [], effects: 'none' }));
  return completeDependencyIntake({ request, analysis: { reviews, impactJson: '', sorts: records } }, w.ports);
}
