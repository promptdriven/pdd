// Source: prompts/cli/autopilot-pr-limit.prompt.md.
// Counts review backlog only. Claims, workflow capacity and approval stay with their owners.
export function ownerAreas(labels = []) {
  const areas = [...new Set(labels.map(label => typeof label === 'string' ? label : label?.name)
    .filter(name => typeof name === 'string' && /^area:\s*\S/i.test(name))
    .map(name => `area:${name.slice(5).trim().toLowerCase()}`))].sort();
  return areas.length ? areas : ['repository'];
}
export const maxOpenPrs = value => Number.isSafeInteger(value) && value > 0 ? value : 5;
export function reviewWait(labels, counts, limit) {
  limit = maxOpenPrs(limit);
  for (const area of ownerAreas(labels)) if ((counts[area] ?? 0) >= limit) return { area, count: counts[area], limit };
  return null;
}
const isAutomatic = (body, labels) => labels.some(label => (typeof label === 'string' ? label : label?.name)?.toLowerCase() === 'pdd:autopilot')
  || /<!--\s*pdd:autopilot-pr\s*-->/.test(body ?? '')
  || /pdd-workflow:[A-Za-z0-9_.-]+:[A-Za-z0-9_.-]+/.test(body ?? '') && /Autopilot `(?:auto|observe)`/.test(body ?? '');
const query = `query($owner:String!,$name:String!,$cursor:String) {
  repository(owner:$owner,name:$name) {
    pullRequests(states:OPEN,first:25,after:$cursor) {
      nodes { number state body reviewDecision reviewRequests(first:1) { totalCount }
        labels(first:100) { totalCount nodes { name } }
        closingIssuesReferences(first:100) { totalCount nodes { labels(first:100) { totalCount nodes { name } } } }
      }
      pageInfo { hasNextPage endCursor }
    }
  }
}`;
const unavailable = () => { throw Error('PR review observations unavailable; retry next tick.'); };
function complete(connection) {
  if (!connection || !Array.isArray(connection.nodes) || !Number.isSafeInteger(connection.totalCount)
    || connection.totalCount !== connection.nodes.length || connection.nodes.some(node => !node || typeof node !== 'object')) unavailable();
  return connection.nodes;
}
export async function readReviewQueue({ repository, rows }, { request }) {
  if (!Array.isArray(rows)) unavailable();
  if (!rows.some(row => row.pull_request && isAutomatic(row.body, row.labels ?? []))) return {};
  const [owner, name] = repository.split('/'), counts = {}, seen = new Set(), cursors = new Set();
  let cursor = null;
  do {
    const reply = await request(query, { owner, name, cursor });
    const page = reply?.data?.repository?.pullRequests;
    if (reply?.errors?.length || !Array.isArray(page?.nodes) || typeof page.pageInfo?.hasNextPage !== 'boolean') unavailable();
    for (const pr of page.nodes) {
      if (!pr || !Number.isSafeInteger(pr.number) || pr.number < 1 || seen.has(pr.number)
        || !['OPEN', 'CLOSED', 'MERGED'].includes(pr.state) || typeof pr.body !== 'string') unavailable();
      seen.add(pr.number);
      const labels = complete(pr.labels);
      if (labels.some(label => typeof label.name !== 'string')) unavailable();
      const automatic = isAutomatic(pr.body, labels);
      if (!automatic || pr.state !== 'OPEN') continue;
      if (!['APPROVED', 'REVIEW_REQUIRED', 'CHANGES_REQUESTED', null].includes(pr.reviewDecision)
        || !Number.isSafeInteger(pr.reviewRequests?.totalCount) || pr.reviewRequests.totalCount < 0) unavailable();
      if (!['REVIEW_REQUIRED', 'CHANGES_REQUESTED'].includes(pr.reviewDecision) && pr.reviewRequests.totalCount === 0) continue;
      let areas = ownerAreas(labels);
      if (areas[0] === 'repository') {
        const linked = complete(pr.closingIssuesReferences).flatMap(issue => complete(issue.labels));
        if (linked.some(label => typeof label.name !== 'string')) unavailable();
        areas = ownerAreas(linked);
      }
      for (const area of areas) counts[area] = (counts[area] ?? 0) + 1;
    }
    if (!page.pageInfo.hasNextPage) break;
    cursor = page.pageInfo.endCursor;
    if (typeof cursor !== 'string' || !cursor || cursors.has(cursor)) unavailable();
    cursors.add(cursor);
  } while (true);
  return counts;
}
