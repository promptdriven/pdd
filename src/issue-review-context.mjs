// Implements prompts/cli/issue-review-context.prompt.md. Pure retrieval, never authority.
const source = key => /^https:\/\/github\.com\/[^/]+\/[^/]+\/blob\/HEAD\//.test(key);
const canonicalSource = (repository, path) => `https://github.com/${repository.toLowerCase()}/blob/HEAD/${path.split('/').map(encodeURIComponent).join('/')}`;
export function namedReviewSourceLinks(repository, text) {
  const links = new Set();
  for (const match of String(text ?? '').matchAll(/https:\/\/github\.com\/([\w.-]+\/[\w.-]+)\/blob\/([^\s`<>#?)]+)/g)) {
    if (match[1].toLowerCase() !== repository.toLowerCase()) continue;
    const tail = match[2].replace(/[.,;:!\]'"}]+$/, '');
    if (tail.split('/').length < 2 || tail.split('/').some(part => !part)) continue;
    links.add(`https://github.com/${repository.toLowerCase()}/blob/${tail}`);
  }
  return [...links].sort();
}
export function namedReviewSources(repository, text) {
  const paths = new Set();
  const add = path => {
    try { path = decodeURIComponent(path); } catch { return; }
    if (!path || path.startsWith('/') || path.split('/').some(x => !x || x === '.' || x === '..') || /[\\\0]/.test(path)) return;
    paths.add(canonicalSource(repository, path));
  };
  const plain = String(text ?? '').replace(/https:\/\/github\.com\/[^/\s]+\/blob\/[^\s`<>#?)]+/g, '')
    .replace(/https?:\/\/[^\s`<>]+/g, '');
  for (const m of plain.matchAll(/(?:^|[\s`('"\[])([\w.-]+(?:\/[\w.%+-]+)*\.[a-zA-Z][a-zA-Z0-9]*)(?=$|[\s`)'"\]:,;.])/g)) {
    if (m[1].includes('/') || /\.(?:[cm]?[jt]sx?|py|md|json|toml|ya?ml|sql|html|css|sh|rs|go|java|rb|c|h|cpp|hpp|proto|txt|svg)$/i.test(m[1])) add(m[1]);
  }
  return [...paths].sort();
}
export function tracksReviewInput(issue, key) {
  return !Array.isArray(issue?.namedSources) || !source(key) || issue.namedSources.includes(key);
}
// Stale records can help retrieval, but never authorize a route or start.
function savedSort(issue) {
  const records = (issue?.sorts ?? []).filter(x => x.authority === 'trusted' && x.intact && x.record);
  const superseded = new Set(records.flatMap(x => x.record.base ?? []));
  const heads = records.filter(x => !superseded.has(x.id));
  return heads.length === 1 ? heads[0].record : null;
}
function summary(issue, snapshot) {
  const r = savedSort(issue);
  return { summary: (r?.summary || issue.title || '').slice(0, 600), area: r?.belongs.area ?? '',
    owner: snapshot.sortContext?.areas?.find(a => a.name === r?.belongs.area)?.owner || r?.belongs.repository || r?.belongs.area || '', status: r?.status.state ?? '',
    duplicate: r?.genuine.duplicateOf ?? '', rootCause: r?.rootCause ?? '', paths: r?.paths ?? [] };
}
const matchingPaths = (issue, saved) => new Set([...(issue.namedSources ?? []), ...saved.paths].map(path => {
  if (!source(path)) return path;
  try { return decodeURIComponent(path.split('/blob/HEAD/')[1]); } catch { return path; }
}));
const words = text => new Set(String(text).toLowerCase().match(/[a-z0-9_]{3,}/g) ?? []);
export function reviewPacket(snapshot, subjects, { limit = 20 } = {}) {
  const all = new Map(snapshot.issues.map(i => [i.key, i])), selected = new Set(subjects), requested = new Set(subjects);
  const summaries = new Map(snapshot.issues.map(i => [i.key, summary(i, snapshot)]));
  for (const key of subjects) {
    const a = all.get(key), sa = summaries.get(key); if (!a) continue;
    const wa = words(`${a.title} ${a.sortText ?? ''} ${sa.summary}`), paths = matchingPaths(a, sa);
    const ranked = snapshot.issues.filter(i => i.key !== key && i.authority === 'trusted' && i.state === 'open').map(i => {
      const b = summaries.get(i.key), wb = words(`${i.title} ${b.summary}`);
      return { key: i.key, score: [Number(!!sa.rootCause && sa.rootCause === b.rootCause), Number(!!sa.area && sa.area === b.area),
        [...matchingPaths(i, b)].filter(p => paths.has(p)).length, [...wa].filter(w => wb.has(w)).length / Math.max(1, wa.size + wb.size)] };
    });
    ranked.sort((a,b) => { for (let i = 0; i < a.score.length; i++) if (a.score[i] !== b.score[i]) return b.score[i] - a.score[i]; return a.key.localeCompare(b.key); });
    for (const i of ranked.slice(0, limit)) selected.add(i.key);
    for (const named of a.namedIssues ?? []) selected.add(named.toLowerCase());
    if (sa.duplicate) selected.add(sa.duplicate);
    for (const edge of snapshot.edges) if (edge.dependent === key || edge.blocker === key) { selected.add(edge.dependent); selected.add(edge.blocker); }
    for (const r of snapshot.reviews.filter(r => r.issue === key && r.authority === 'trusted' && r.intact)) {
      for (const d of r.dependencies) selected.add(d.key);
      // Issue revisions live in issues, not inputs. Keep observations used by
      // retained reviews even when no prerequisite was declared.
      for (const row of r.inputs) if (all.has(row.key)) selected.add(row.key);
    }
    for (const g of snapshot.sortContext?.groups ?? []) if (g.members.includes(key) && g.umbrella) selected.add(g.umbrella);
  }
  // Native prerequisite closure is mandatory, including closed/cross-repo endpoints.
  let changed = true;
  while (changed) { changed = false; for (const e of snapshot.edges) if (selected.has(e.dependent) && !selected.has(e.blocker)) { selected.add(e.blocker); changed = true; } }
  const copy = structuredClone(snapshot);
  copy.issues = copy.issues.filter(i => selected.has(i.key)).map(i => {
    if (requested.has(i.key)) return i;
    const { sortText, sorts, ...rest } = i;
    return { ...rest, title: i.title.slice(0, 240), reviewSummary: summaries.get(i.key) };
  });
  copy.edges = copy.edges.filter(e => selected.has(e.dependent) && selected.has(e.blocker));
  copy.reviews = copy.reviews.filter(r => selected.has(r.issue) || r.authority === 'trusted' && r.intact
    && ['pending', 'confirmed'].includes(r.effects) && r.dependencies.some(d => requested.has(d.key))).map(r => requested.has(r.issue) ? r : {
    ...r, analysis: '', inputs: [], candidates: [], questions: [],
    // Incoming removed links still contribute to the subject's link row, even
    // when their host has no current edge and is outside retrieval.
    dependencies: selected.has(r.issue) ? r.dependencies : r.dependencies.filter(d => requested.has(d.key)),
  }).map(r => ({ ...r, candidates: r.candidates.filter(c => r.dependencies.some(d => d.key === c.key)) }));
  copy.impacts = copy.impacts.filter(i => i.reviews.some(id => copy.reviews.some(r => r.id === id)));
  const used = new Set(copy.reviews.flatMap(r => r.inputs.map(x => x.key)));
  for (const i of copy.issues.filter(i => requested.has(i.key))) for (const r of i.sorts ?? []) for (const row of r.record?.inputs ?? []) used.add(row.key);
  copy.inputs = copy.inputs.filter(row => used.has(row.key) || row.key === copy.sortContext?.key || [...requested].some(k => row.key.startsWith(`${k}#`)) || copy.issues.some(i => i.namedSources?.includes(row.key)));
  if (copy.coverage) copy.coverage.issues = copy.coverage.issues.filter(i => selected.has(i.key));
  if (copy.sortContext) copy.sortContext.groups = copy.sortContext.groups.filter(g => requested.has(g.umbrella) || g.members.some(k => requested.has(k))).map(g => ({ ...g, members: g.members.filter(k => selected.has(k)), notified: (g.notified ?? []).filter(k => selected.has(k)), ...(g.recheck ? { recheck: g.recheck.filter(x => selected.has(x.issue)) } : {}) }));
  copy.warnings = [];
  return copy;
}
export function reviewConsistency(snapshot) {
  const all = new Map(snapshot.issues.map(i => [i.key, i])), findings = new Set();
  for (const g of snapshot.sortContext?.groups ?? []) {
    if (g.merged) continue;
    if (g.umbrella && !all.has(g.umbrella)) findings.add(g.umbrella);
    for (const key of g.members) if (!all.has(key) || savedSort(all.get(key))?.rootCause !== g.rootCause) findings.add(key);
  }
  for (const e of snapshot.edges) for (const key of [e.dependent, e.blocker]) if (!all.has(key)) findings.add(key);
  return [...findings].sort();
}
