// A fake GitHub for one repository, answered through a fake `gh`. It counts each call, keeps the REST and GraphQL
// limits with their headers, answers conditional requests with a body ETag (gh exits 1 for a 304 and prints the
// headers), lists issues with `since` and `sort=updated`, and moves an issue's update time on each change, as GitHub
// does. No network and no real gh.
import { createHash } from 'node:crypto';

const endpointOf = args => args.find((word, index) => index > 0 && !String(word).startsWith('-') && !['GET', 'POST', 'PATCH', 'PUT', 'DELETE'].includes(word)
  && !/^[A-Z][A-Za-z-]+: /.test(word) && args[index - 1] !== '--input' && args[index - 1] !== '-H' && args[index - 1] !== '--method');
const iso = ms => new Date(ms).toISOString().replace(/\.\d{3}Z$/, 'Z');

export function createGithubRepoFake({ repository = 'acme/widgets', owner = 'acme', issues = 200, now = () => Date.parse('2026-11-07T12:00:00Z'), limit = 5000 } = {}) {
  const repo = repository.toLowerCase();
  const f = { repo, owner, now, limit, remaining: limit, graphqlRemaining: limit, resetAt: Math.floor(now() / 1000) + 3600,
    branches: new Map([['main', 'base-head']]), contents: new Map(), calls: [], issues: new Map(), nextComment: 900000, nextEvent: 700000, linkBumpsUpdate: false, failRest: null, failRead: null };
  const url = n => `https://github.com/${repo}/issues/${n}`;
  const touch = issue => { issue.updated = Math.max(f.now(), issue.updated + 1000); };
  f.add = (n, extra = {}) => {
    const at = f.now() - (issues - n + 10) * 60 * 1000;
    const issue = { id: String(5000000 + n), number: n, title: `Issue ${n}`, body: `Make part ${n} work.`, state: 'open', state_reason: null, user: owner,
      labels: [], created: at, updated: at, comments: [], blockedBy: [], timeline: [], deleted: false, movedTo: null, ...extra };
    f.issues.set(n, issue);
    return issue;
  };
  for (let n = 1; n <= issues; n++) f.add(n);
  const live = () => [...f.issues.values()].filter(issue => !issue.deleted && !issue.movedTo);
  const summary = issue => {
    const blocking = live().filter(other => other.blockedBy.includes(issue.number)).length;
    return { blocked_by: issue.blockedBy.length, total_blocked_by: issue.blockedBy.length, blocking, total_blocking: blocking };
  };
  const row = issue => ({ id: Number(issue.id), node_id: `I_${issue.id}`, number: issue.number, html_url: issue.movedTo ? `https://github.com/${issue.movedTo}/issues/${issue.number}` : url(issue.number),
    title: issue.title, body: issue.body, state: issue.state, state_reason: issue.state_reason, user: { login: issue.user }, labels: issue.labels.map(name => ({ name })),
    assignees: [], assignee: null, comments: issue.comments.length, created_at: iso(issue.created), updated_at: iso(issue.updated), closed_at: null,
    author_association: 'OWNER', issue_dependencies_summary: summary(issue) });
  const comment = (issue, c) => ({ id: Number(c.id), html_url: `${url(issue.number)}#issuecomment-${c.id}`, body: c.body, user: { login: c.user }, created_at: iso(c.created), updated_at: iso(c.updated), author_association: 'OWNER' });
  const events = issue => [...issue.timeline.map(e => ({ id: Number(e.id), event: e.event, actor: { login: e.actor }, created_at: iso(e.created), ...(e.label ? { label: { name: e.label } } : {}) })),
    ...issue.comments.map(c => ({ id: Number(c.id), event: 'commented', actor: { login: c.user }, created_at: iso(c.created), updated_at: iso(c.updated), body: c.body }))]
    .sort((a, b) => Date.parse(a.created_at) - Date.parse(b.created_at) || a.id - b.id);
  // Changes, as people and other machines make them.
  f.comment = (n, body, user = owner) => { const issue = f.issues.get(n), c = { id: String(f.nextComment++), body, user, created: f.now(), updated: f.now() }; issue.comments.push(c); touch(issue); return c; };
  f.editComment = (n, id, body) => { const issue = f.issues.get(n), c = issue.comments.find(x => x.id === String(id)); c.body = body; c.updated = f.now(); touch(issue); };
  f.label = (n, name, actor = owner) => { const issue = f.issues.get(n); issue.labels.push(name); const e = { id: String(f.nextEvent++), event: 'labeled', label: name, actor, created: f.now() }; issue.timeline.push(e); touch(issue); return e; };
  f.unlabel = (n, name, actor = owner) => { const issue = f.issues.get(n); issue.labels = issue.labels.filter(x => x !== name); issue.timeline.push({ id: String(f.nextEvent++), event: 'unlabeled', label: name, actor, created: f.now() }); touch(issue); };
  f.link = (dependent, blocker) => { const issue = f.issues.get(dependent); issue.blockedBy.push(blocker); if (f.linkBumpsUpdate) touch(issue); };
  f.close = n => { const issue = f.issues.get(n); issue.state = 'closed'; issue.state_reason = 'completed'; touch(issue); };
  f.edit = (n, body) => { const issue = f.issues.get(n); issue.body = body; touch(issue); };
  // GitHub drops a deleted or transferred issue from the lists without a change that `since` shows.
  f.remove = n => { f.issues.get(n).deleted = true; };
  f.move = (n, target) => { f.issues.get(n).movedTo = target; };
  f.reviewComments = n => f.issues.get(n).comments.filter(c => c.body.includes('<!-- pdd-dependency-review:v1 -->'));
  // A claim by another coordinator, as its chat writes it: the label, then one claim comment that names the label event.
  f.claim = (n, { coordinatorId = 'coordinator-b', machine = 'machine-b', actor = owner } = {}) => {
    const event = f.label(n, 'pdd:working', actor);
    return f.comment(n, `Autopilot claim.\n\n\`\`\`json\n${JSON.stringify({ repository: repo, coordinatorId, machine, labelEventId: event.id, lastSeen: '' })}\n\`\`\``, actor);
  };
  // The shape of a busy repository: trusted requirement comments on 3 of 4 issues, issues claimed by another machine,
  // and open issues blocked by closed ones.
  f.busy = ({ claims = [10, 20, 30, 40, 50], closed = 5 } = {}) => {
    for (let n = 1; n <= issues; n++) if (n % 4) f.comment(n, `Also keep part ${n} small.`);
    for (const n of claims) f.claim(n);
    for (let i = 1; i <= closed; i++) { const n = issues + i; f.add(n, { state: 'closed', state_reason: 'completed' }); f.issues.get(60 + i).blockedBy.push(n); }
  };

  const headers = (status, { etag, link, resource = 'core' } = {}) => [`HTTP/2.0 ${status} ${status === 304 ? 'Not Modified' : status === 403 ? 'Forbidden' : 'OK'}`, ...(etag ? [`Etag: ${etag}`] : []), ...(link ? [`Link: ${link}`] : []),
    `X-Ratelimit-Limit: ${f.limit}`, `X-Ratelimit-Remaining: ${resource === 'graphql' ? f.graphqlRemaining : f.remaining}`, `X-Ratelimit-Reset: ${f.resetAt}`, `X-Ratelimit-Resource: ${resource}`];
  const page = (endpoint, all) => {
    const [path, query = ''] = endpoint.split('?'), params = new URLSearchParams(query), number = Number(params.get('page') ?? 1), size = Number(params.get('per_page') ?? 30);
    const body = all.slice((number - 1) * size, number * size);
    if (all.length <= number * size) return { body };
    params.set('page', String(number + 1));
    return { body, link: `<https://api.github.com/${path}?${params}>; rel="next"` };
  };
  function rest(method, endpoint, input) {
    const [path, query = ''] = endpoint.split('?'), params = new URLSearchParams(query);
    const route = path.startsWith(`repos/${repo}`) ? path.slice(`repos/${repo}`.length) : null;
    if (route === null) return { status: 404, body: { message: 'Not Found' } };
    if (route === '' && method === 'GET') return { status: 200, body: { default_branch: 'main', full_name: repo, owner: { login: owner } } };
    if (route?.startsWith('/git/ref/heads/') && method === 'GET') {
      const branch = decodeURIComponent(route.slice('/git/ref/heads/'.length));
      return f.branches.has(branch) ? { status: 200, body: { object: { sha: f.branches.get(branch) } } } : { status: 404, body: {} };
    }
    if (route === '/git/refs' && method === 'POST') {
      const data = JSON.parse(input), branch = data.ref.replace('refs/heads/', '');
      if (f.branches.has(branch)) return { status: 422, body: {} };
      f.branches.set(branch, data.sha); return { status: 201, body: { ref: data.ref } };
    }
    if (route === '/contents/.pdd-reviewer.json') {
      const data = input ? JSON.parse(input) : {}, branch = data.branch ?? params.get('ref');
      if (!f.branches.has(branch)) return { status: 404, body: {} };
      const file = f.contents.get(branch);
      if (method === 'GET') return file ? { status: 200, body: file } : { status: 404, body: {} };
      if (method === 'PUT') {
        if ((file?.sha ?? undefined) !== data.sha) return { status: 409, body: {} };
        const saved = { sha: createHash('sha256').update(data.content).digest('hex'), encoding: 'base64', content: data.content };
        f.contents.set(branch, saved); return { status: file ? 200 : 201, body: { content: saved } };
      }
    }
    if (route === '/collaborators' && method === 'GET') return { status: 200, ...page(endpoint, [{ login: owner, permissions: { admin: true, maintain: true, push: true } }]) };
    let m = /^\/collaborators\/([^/]+)\/permission$/.exec(route);
    if (m) return { status: 200, body: { permission: decodeURIComponent(m[1]).toLowerCase() === owner ? 'admin' : 'read' } };
    if (route === '/issues' && method === 'GET') {
      let list = live();
      if (params.get('state') !== 'all') list = list.filter(issue => issue.state === 'open');
      if (params.get('since')) list = list.filter(issue => issue.updated >= Date.parse(params.get('since')));
      list = params.get('sort') === 'updated' ? list.sort((a, b) => b.updated - a.updated || b.number - a.number) : list.sort((a, b) => b.number - a.number);
      return { status: 200, ...page(endpoint, list.map(row)) };
    }
    m = /^\/issues\/comments\/([0-9]+)$/.exec(route);
    if (m) {
      for (const issue of live()) {
        const c = issue.comments.find(x => x.id === m[1]);
        if (!c) continue;
        if (method === 'PATCH') { c.body = JSON.parse(input).body; c.updated = f.now(); touch(issue); }
        return { status: 200, body: comment(issue, c) };
      }
      return { status: 404, body: { message: 'Not Found' } };
    }
    m = /^\/issues\/([0-9]+)(\/.*)?$/.exec(route);
    if (!m) return { status: 404, body: { message: 'Not Found' } };
    const issue = f.issues.get(Number(m[1]));
    if (!issue || issue.deleted) return { status: 404, body: { message: 'Not Found' } };
    const sub = m[2] ?? '';
    if (sub === '' && method === 'GET') return { status: 200, body: row(issue) };
    if (sub === '/comments' && method === 'POST') { const c = f.comment(issue.number, JSON.parse(input).body, owner); return { status: 201, body: comment(issue, c) }; }
    if (sub === '/comments') return { status: 200, ...page(endpoint, issue.comments.map(c => comment(issue, c))) };
    if (sub === '/dependencies/blocked_by' && method === 'POST') {
      const blocker = live().find(other => other.id === String(JSON.parse(input).issue_id));
      if (!blocker) return { status: 422, body: { message: 'Validation Failed' } };
      f.link(issue.number, blocker.number); return { status: 201, body: row(blocker) };
    }
    if (sub === '/dependencies/blocked_by') return { status: 200, ...page(endpoint, issue.blockedBy.map(n => row(f.issues.get(n)))) };
    if (sub === '/dependencies/blocking') return { status: 200, ...page(endpoint, live().filter(other => other.blockedBy.includes(issue.number)).map(row)) };
    if (sub === '/timeline') return { status: 200, ...page(endpoint, events(issue)) };
    return { status: 404, body: { message: 'Not Found' } };
  }
  function graphql(input) {
    const { variables } = JSON.parse(input), data = {};
    for (const [name, value] of Object.entries(variables)) {
      const m = /^n([0-9]+)$/.exec(name); if (!m) continue;
      const issue = f.issues.get(value);
      if (!issue || issue.deleted || issue.movedTo) { data[`i${m[1]}`] = null; continue; }
      const done = nodes => ({ nodes, pageInfo: { hasNextPage: false } });
      data[`i${m[1]}`] = { url: url(issue.number), number: issue.number, fullDatabaseId: issue.id, title: issue.title, body: issue.body, state: issue.state === 'open' ? 'OPEN' : 'CLOSED', stateReason: null,
        author: { login: issue.user }, labels: done(issue.labels.map(name => ({ name }))), assignees: done([]),
        comments: done(issue.comments.map(c => ({ fullDatabaseId: c.id, body: c.body, createdAt: iso(c.created), updatedAt: iso(c.updated), author: { login: c.user } }))),
        blockedBy: done(issue.blockedBy.map(n => ({ url: url(n) }))), blocking: done(live().filter(other => other.blockedBy.includes(issue.number)).map(other => ({ url: url(other.number) }))),
        timelineItems: done([]) };
    }
    return { data: { repository: data } };
  }
  // The fake gh: `gh api --include …`, `gh repo view`, `gh auth status`.
  f.gh = async (args, options = {}) => {
    if (args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
    if (args[0] === 'repo') return { code: 0, stdout: JSON.stringify({ nameWithOwner: repo, url: `https://github.com/${repo}`, defaultBranchRef: { name: 'main' }, owner: { login: owner } }), stderr: '' };
    if (args[0] !== 'api') return { code: 1, stdout: '', stderr: `unsupported gh ${args[0]}` };
    const endpoint = endpointOf(args), method = (args.includes('--method') ? args[args.indexOf('--method') + 1] : args.includes('--input') || args.includes('-f') ? 'POST' : 'GET').toUpperCase();
    const sent = args.find(word => /^If-None-Match: /.test(word))?.slice(15);
    const input = options.input ?? (args.includes('-f') ? JSON.stringify({ body: args[args.indexOf('-f') + 1].replace(/^body=/, '') }) : undefined);
    if (f.now() >= f.resetAt * 1000) { f.resetAt = Math.floor(f.now() / 1000) + 3600; f.remaining = f.limit; f.graphqlRemaining = f.limit; }
    const call = { method, endpoint, conditional: !!sent, api: endpoint === 'graphql' ? 'graphql' : 'rest', at: f.now() };
    f.calls.push(call);
    if (endpoint === 'graphql') {
      call.query = JSON.parse(input).query;
      if (f.graphqlRemaining <= 0) { call.status = 403; return { code: 1, stdout: [...headers(403, { resource: 'graphql' }), '', JSON.stringify({ message: 'API rate limit exceeded' })].join('\r\n'), stderr: 'gh: HTTP 403\n' }; }
      f.graphqlRemaining--; call.status = 200;
      return { code: 0, stdout: [...headers(200, { resource: 'graphql' }), '', JSON.stringify(graphql(input))].join('\r\n'), stderr: '' };
    }
    if (f.remaining <= 0 || f.failRest?.(call)) {
      if (f.remaining > 0) f.remaining = 0;
      call.status = 403;
      return { code: 1, stdout: [...headers(403), '', JSON.stringify({ message: 'API rate limit exceeded for user.' })].join('\r\n'), stderr: 'gh: API rate limit exceeded (HTTP 403)\n' };
    }
    if (method === 'GET' && f.failRead?.(call)) {
      f.remaining--; call.status = 500;
      return { code: 1, stdout: [...headers(500), '', JSON.stringify({ message: 'Unavailable' })].join('\r\n'), stderr: 'gh: HTTP 500\n' };
    }
    if (f.beforeRest) await f.beforeRest(call, input);
    const reply = endpoint === 'user' ? { status: 200, body: { login: owner } } : rest(method, endpoint, input), text = JSON.stringify(reply.body);
    const etag = method === 'GET' && reply.status === 200 ? `W/"${createHash('sha256').update(text).digest('hex').slice(0, 16)}"` : undefined;
    if (etag && sent === etag) { call.status = 304; return { code: 1, stdout: [...headers(304, { etag }), '', ''].join('\r\n'), stderr: 'gh: HTTP 304\n' }; }
    f.remaining--; call.status = reply.status;
    return { code: reply.status < 300 ? 0 : 1, stdout: [...headers(reply.status, { etag, link: reply.link }), '', text].join('\r\n'), stderr: reply.status < 300 ? '' : `gh: HTTP ${reply.status}\n` };
  };
  // REST calls since a mark: all requests, and the counted ones (a 304 does not count against the limit).
  f.mark = () => f.calls.length;
  f.since = mark => { const rest = f.calls.slice(mark).filter(call => call.api === 'rest'); return { rest: rest.length, counted: rest.filter(call => call.status !== 304).length, graphql: f.calls.slice(mark).filter(call => call.api === 'graphql').length, calls: f.calls.slice(mark) }; };
  return f;
}
