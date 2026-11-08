// Generated from prompts/cli/issue-dependencies-github.prompt.md (sha256: 260f780d5f448c584ed824b4cc9bbb49453a3b83561e8c22ecceec3b994224b1).
import { execFile as execCallback } from 'node:child_process';
import { createHash } from 'node:crypto';
import { lstatSync, readFileSync, readdirSync, realpathSync } from 'node:fs';
import { join, resolve, relative, isAbsolute } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { runAutopilot } from './autopilot.mjs';
import { resolveWorkflowRepository } from './workflow-github.mjs';
import { gitContext, currentChat, stateDirFor } from './workflow-runs.mjs';
import { chatLifecycle, chatSession, observeLifecycle, sessionEvidenceDue, observedSession, ownSession, launchAnchor, validSessionId } from './workflow-chat.mjs';
import { dependencyLinks, projectIssueGraph, validateDependencyChange } from './issue-dependencies.mjs';
import { githubFullLastPage, nativeGithubCounter } from './github-calls.mjs';

const REVIEW = 'pdd-dependency-review:v1', IMPACT = 'pdd-dependency-impact:v1';
const NATIVE_GITHUB = Symbol('native github'), NATIVE_OWNERS = Symbol('native owners');
const NATIVE_READ_SCOPE = Symbol('native dependency read scope'), NATIVE_AUTHORITY = Symbol('native authority');
const NATIVE_CONTEXT = Symbol('native context'), NATIVE_EVIDENCE = Symbol('native evidence'), NATIVE_SETTINGS = Symbol('native settings');
const nativeReadScope = () => ({ repositories: new Map(), checkouts: new Map(), authorityData: new Map(), authorityResults: new Map() });
const repositoryName = x => typeof x === 'string' && /^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*$/.test(x);
const sameRepo = (a, b) => typeof a === 'string' && typeof b === 'string' && a.toLowerCase() === b.toLowerCase();
const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const hash = text => createHash('sha256').update(text).digest('hex');
const fail = code => { throw Object.assign(Error(code), { code }); };
const parse = json => JSON.parse(json, (key, value, context) => (key === 'id' || key === 'fullDatabaseId') && typeof value === 'number'
  ? context?.source ?? (Number.isSafeInteger(value) ? String(value) : '') : value);
const readJson = (file, fallback = null) => { try { return JSON.parse(readFileSync(file, 'utf8')); } catch (e) { if (e.code === 'ENOENT') return fallback; throw e; } };
const info = key => {
  const m = /^https:\/\/github\.com\/([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)\/issues\/([1-9][0-9]*)(?:#issuecomment-([1-9][0-9]*))?$/.exec(key ?? '');
  return m && Number.isSafeInteger(Number(m[2])) ? { repository: m[1].toLowerCase(), issue: Number(m[2]), key: `https://github.com/${m[1].toLowerCase()}/issues/${m[2]}`, comment: m[3] } : null;
};
const canonical = key => { const i = info(key); return i ? i.key + (i.comment ? `#issuecomment-${i.comment}` : '') : key; };
// A review's link row (issue URL + #dependencies) comes from native links, not a read.
const linkRow = key => /^https:\/\/github\.com\/[^/#]+\/[^/#]+\/issues\/[1-9][0-9]*#dependencies$/i.test(key ?? '');
const nonIssueRows = rows => (rows ?? []).filter(r => (!info(r.key) || info(r.key).comment) && !linkRow(r.key));
// A native "blocked by" removal in the subject's own history names the blocker
// that a person removed. Undefined: the event is not such a removal (a
// "blocking" removal is about another issue's links). Null: the blocker is unknown.
const REMOVAL = /(?:block|depend).*(?:remov|delet)|(?:remov|delet).*(?:block|depend)/i;
const eventIssue = value => {
  if (!object(value)) return null;
  const direct = info(value.html_url)?.key, repo = value.repository?.full_name;
  if (direct) return direct;
  return repositoryName(repo) && Number.isSafeInteger(value.number) && value.number > 0 ? `https://github.com/${repo.toLowerCase()}/issues/${value.number}` : null;
};
const blockedByRemoval = event => {
  const name = String(event?.event ?? '');
  if (!REMOVAL.test(name) || /^blocking(?:[_-]|$)/i.test(name)) return undefined;
  return eventIssue(event.blocked_by);
};
// A pdd command outside the Autopilot tick records its gh calls in the ledger of the repository that each call names.
const execute = nativeGithubCounter(spawnRead, { purpose: 'dependencies' });
const uniqueRows = rows => [...new Map(rows.map(r => [canonical(r.key), { key: canonical(r.key), revision: r.revision }])).values()];
const bookkeeping = body => /<!--\s*pdd(?:-dependency-(?:review|impact)|[: -](?:autopilot|claim|working|sync))/i.test(body ?? '')
  || /"coordinatorId"\s*:/.test(body ?? '') && /"labelEventId"\s*:/.test(body ?? '');

function spawnRead(file, args, options = {}) {
  return new Promise((resolveResult, reject) => {
    const { input, ...rest } = options;
    const child = execCallback(file, args, { ...rest, encoding: 'utf8', shell: false, maxBuffer: 32 * 1024 * 1024 }, (error, stdout, stderr) => {
      if (error) reject(Object.assign(error, { stdout, stderr })); else resolveResult({ stdout, stderr, code: 0 });
    });
    if (input !== undefined) { child.stdin.on('error', () => {}); child.stdin.end(input); }
  });
}

// gh exits with 1 for a 304 reply and prints its headers; a conditional request reads them from the failed command.
const notModified = text => /^HTTP\/\S+\s+304\b/.test(String(text ?? ''));

function service(cwd, ports) {
  const exec = ports.execFile ?? execute;
  async function run(file, args, input, purpose, conditional = false, repository) {
    let r;
    try { r = await exec(file, args, { ...(cwd ? { cwd } : {}), ...(input === undefined ? {} : { input }), ...(purpose ? { purpose } : {}), ...(repository ? { repository } : {}) }); }
    catch (error) { if (conditional && notModified(error?.stdout)) return String(error.stdout); throw error; }
    if (r.code !== undefined && r.code !== 0 && !(conditional && notModified(r.stdout))) throw Object.assign(Error('Service read failed'), { status: r.code });
    return String(r.stdout ?? '');
  }
  // purpose names what the read is for in the GitHub call ledger, repository the ledger of a GraphQL call. With a githubCache
  // port, a GET sends the saved ETag; a 304 reply returns the saved body and next page and does not count against the limit.
  // A saved full last page, or a saved body that does not parse, sends no ETag: a 304 cannot show a new next page.
  async function api(endpoint, method = 'GET', input, purpose, repository) {
    const cache = method === 'GET' ? ports.githubCache : null;
    let saved = cache?.get(endpoint);
    if (saved) {
      try { saved = { ...saved, value: parse(saved.body) }; if (githubFullLastPage(endpoint, saved.value, saved.next)) saved = undefined; }
      catch { saved = undefined; }
    }
    const executeRequest = () => run('gh', ['api', '--include', '--method', method, endpoint, '-H', 'Accept: application/vnd.github+json',
      ...(saved ? ['-H', `If-None-Match: ${saved.etag}`] : []), ...(input === undefined ? [] : ['--input', '-'])], input, purpose, !!saved, repository);
    const mutation = method === 'POST' && /^repos\/[^/]+\/[^/]+\/issues\/[1-9][0-9]*\/(?:comments|dependencies\/blocked_by)$/.test(endpoint)
      || method === 'PATCH' && /^repos\/[^/]+\/[^/]+\/issues\/comments\/[1-9][0-9]*$/.test(endpoint);
    const raw = mutation && ports.admitMutation ? await ports.admitMutation(executeRequest) : await executeRequest();
    const boundary = raw.search(/\r?\n\r?\n/), header = boundary >= 0 ? raw.slice(0, boundary) : '';
    const body = boundary >= 0 ? raw.slice(boundary).trim() : raw;
    const status = Number(header.match(/^HTTP\/\S+\s+(\d+)/m)?.[1] ?? 200);
    if (status === 304 && saved) return { value: saved.value, next: saved.next ?? '' };
    if (status < 200 || status >= 300) throw Object.assign(Error('GitHub observation unavailable'), { status });
    const link = header.match(/^link:\s*(.*)$/im)?.[1] ?? '';
    const nextRelation = link.match(/<([^>]+)>\s*;\s*rel=(?:"next"|next)\s*(?:,|$)/i)?.[1];
    const next = nextRelation?.match(/^https:\/\/api\.github\.com\/([^#]+)$/i)?.[1] ?? '';
    if (nextRelation && !next) throw Error('Unsupported GitHub pagination link');
    const etag = header.match(/^etag:[ \t]*(.*?)[ \t]*\r?$/im)?.[1];
    const value = parse(body);
    if (cache && status === 200 && etag) cache.set(endpoint, { etag, body, next });
    return { value, next };
  }
  return { run, api };
}

// Batch direct current observations only. Incomplete or unsupported responses
// fall back to the normal per-issue REST reader, never to a saved projection.
async function bulkRoots(cwd, repository, roots, ports) {
  const s = service(cwd, ports), result = new Map();
  const eligible = roots.filter(row => !row.pull_request && Number.isSafeInteger(row.number) && row.number > 0
    && Array.isArray(row.labels) && !row.labels.some(label => (typeof label === 'string' ? label : label.name) === 'pdd:working'));
  const selection = `url number fullDatabaseId title body state stateReason author { login }
    labels(first:100) { nodes { name } pageInfo { hasNextPage } }
    assignees(first:100) { nodes { login } pageInfo { hasNextPage } }
    comments(first:100) { nodes { fullDatabaseId body createdAt updatedAt author { login } } pageInfo { hasNextPage } }
    blockedBy(first:100) { nodes { url } pageInfo { hasNextPage } }
    blocking(first:100) { nodes { url } pageInfo { hasNextPage } }
    timelineItems(first:100,itemTypes:[CROSS_REFERENCED_EVENT]) { nodes { ... on CrossReferencedEvent { source { __typename ... on PullRequest { state } } } } pageInfo { hasNextPage } }`;
  for (let offset = 0; offset < eligible.length; offset += 25) {
    const batch = eligible.slice(offset, offset + 25), [owner, name] = repository.split('/');
    const query = `query($owner:String!,$name:String!${batch.map((_, index) => `,$n${index}:Int!`).join('')}) { repository(owner:$owner,name:$name) { ${batch.map((_, index) => `i${index}:issue(number:$n${index}) { ${selection} }`).join(' ')} } }`;
    const variables = { owner, name, ...Object.fromEntries(batch.map((row, index) => [`n${index}`, row.number])) };
    let response;
    try { response = (await s.api('graphql', 'POST', JSON.stringify({ query, variables }), undefined, repository)).value; if (response.errors?.length || !object(response.data?.repository)) throw Error('Incomplete batch'); }
    catch { continue; }
    batch.forEach((root, index) => {
      const row = response.data.repository[`i${index}`], fields = ['labels','assignees','comments','blockedBy','blocking','timelineItems'];
      const complete = value => object(value) && Array.isArray(value.nodes) && value.pageInfo?.hasNextPage === false;
      if (!object(row) || info(row.url)?.key !== info(root.html_url)?.key || row.number !== root.number
        || !/^[1-9][0-9]*$/.test(String(row.fullDatabaseId ?? '')) || String(root.id ?? '') !== String(row.fullDatabaseId) || typeof row.title !== 'string' || typeof row.body !== 'string'
        || row.state !== 'OPEN' || !object(row.author) || typeof row.author.login !== 'string' || !fields.every(k => complete(row[k]))) return;
      if (row.labels.nodes.some(x => !object(x) || typeof x.name !== 'string') || row.labels.nodes.some(x => x.name === 'pdd:working')) return;
      if (row.assignees.nodes.some(x => !object(x) || typeof x.login !== 'string' || !x.login.trim())) return;
      if (row.comments.nodes.some(x => !object(x) || !/^[1-9][0-9]*$/.test(String(x.fullDatabaseId ?? '')) || typeof x.body !== 'string'
        || typeof x.createdAt !== 'string' || typeof x.updatedAt !== 'string' || !object(x.author) || typeof x.author.login !== 'string')) return;
      if ([...row.blockedBy.nodes, ...row.blocking.nodes].some(x => !object(x) || !info(x.url))) return;
      if (row.timelineItems.nodes.some(x => !object(x) || !object(x.source) || typeof x.source.__typename !== 'string'
        || x.source.__typename === 'PullRequest' && !['OPEN','CLOSED','MERGED'].includes(x.source.state))) return;
      const raw = { id: String(row.fullDatabaseId), number: row.number, html_url: row.url, title: row.title, body: row.body,
        state: 'open', state_reason: row.stateReason, user: {login:row.author.login}, labels: row.labels.nodes, assignees: row.assignees.nodes };
      const pages = {
        comments: row.comments.nodes.map(x => ({id:String(x.fullDatabaseId),body:x.body,created_at:x.createdAt,updated_at:x.updatedAt,user:{login:x.author.login}})),
        blockedBy: row.blockedBy.nodes.map(x => ({html_url:x.url})), blocking: row.blocking.nodes.map(x => ({html_url:x.url})),
        timeline: row.timelineItems.nodes.filter(x => x.source.__typename === 'PullRequest').map(x => ({event:'cross-referenced',source:{issue:{pull_request:{},state:x.source.state === 'OPEN' ? 'open' : 'closed'}}})),
      };
      result.set(info(row.url).key, {raw,pages});
    });
  }
  return result;
}

async function allPages(github, repository, kind, issue, purpose) {
  const items = [], cursors = new Set(); let cursor = '';
  do {
    try {
      if (cursors.has(cursor)) throw Error('Repeated GitHub cursor');
      cursors.add(cursor);
      const value = parse((await github.page({ repository, kind, issue, cursor, ...(purpose ? { purpose } : {}) })).json);
      if (value.error || !Array.isArray(value.items) || typeof value.next !== 'string') throw Error(`Incomplete ${kind} observation`);
      items.push(...value.items); cursor = value.next;
    } catch (error) { error.partialItems = items; throw error; }
  } while (cursor);
  return items;
}

function rawGithub(cwd, ports) {
  const s = service(cwd, ports);
  const github = {
    page: async ({ repository, kind, issue, cursor, purpose }) => {
      const suffix = { issues: '?state=open&per_page=100', comments: `/${issue}/comments?per_page=100`,
        blockedBy: `/${issue}/dependencies/blocked_by?per_page=100`, blocking: `/${issue}/dependencies/blocking?per_page=100`, timeline: `/${issue}/timeline?per_page=100` }[kind];
      if (!repositoryName(repository) || suffix === undefined) return { json: JSON.stringify({ error: 'Invalid GitHub scope', status: 400 }) };
      try {
        const route = { issues: 'issues', comments: `issues/${issue}/comments`, blockedBy: `issues/${issue}/dependencies/blocked_by`,
          blocking: `issues/${issue}/dependencies/blocking`, timeline: `issues/${issue}/timeline` }[kind];
        const path = cursor.split(/[?#]/, 1)[0];
        const canonical = /^repositories\/[1-9][0-9]*\/(.+)$/.exec(path);
        if (cursor && path !== `repos/${repository}/${route}` && canonical?.[1] !== route) throw Error('Foreign pagination cursor');
        const r = await s.api(cursor || `repos/${repository}/issues${suffix}`, 'GET', undefined, purpose);
        return { json: JSON.stringify({ items: r.value, next: r.next }) };
      } catch (e) { return { json: JSON.stringify({ error: 'GitHub read unavailable', status: e.status ?? 0 }) }; }
    },
    issue: async ({ repository, issue, purpose }) => {
      try { return { json: JSON.stringify((await s.api(`repos/${repository}/issues/${issue}`, 'GET', undefined, purpose)).value) }; }
      catch (e) { return { json: JSON.stringify({ error: 'GitHub issue unavailable', status: e.status ?? 0 }) }; }
    },
    appendComment: async ({ repository, issue, body }) => {
      // Recover an uncertain previous append by immutable record identity before another POST.
      const record = parseRecord(body);
      const existing = await allPages(github, repository, 'comments', issue);
      const equal = row => {
        const other = parseRecord(row.body);
        return record && other && record.type === other.type && JSON.stringify(record.value) === JSON.stringify(other.value);
      };
      let row = existing.find(equal);
      if (!row) {
        try { row = (await s.api(`repos/${repository}/issues/${issue}/comments`, 'POST', JSON.stringify({ body }))).value; }
        catch (error) {
          const observed = (await allPages(github, repository, 'comments', issue)).filter(equal);
          if (observed.length !== 1) throw error;
          [row] = observed;
        }
      }
      if (!/^[1-9][0-9]*$/.test(String(row?.id))) throw Error('Append has no native comment identity');
      const readback = (await s.api(`repos/${repository}/issues/comments/${row.id}`)).value;
      if (readback.id !== row.id || !equal(readback)) throw Error('Comment append readback is unresolved');
      return { json: JSON.stringify(readback) };
    },
    addBlocker: async ({ repository, issue, blockerId }) => {
      if (!/^[1-9][0-9]*$/.test(blockerId)) throw Error('Invalid REST issue identity');
      // Decimal digits become one JSON number token. Never pass through a JS Number.
      await s.api(`repos/${repository}/issues/${issue}/dependencies/blocked_by`, 'POST', `{"issue_id":${blockerId}}`);
      return { ok: true };
    },
  };
  Object.defineProperty(github, NATIVE_GITHUB, { value: true });
  return github;
}

async function selectedCheckout(cwd, repository, ports) {
  if (!cwd) return null;
  const scope = ports[NATIVE_READ_SCOPE];
  if (!scope) return null;
  const at = resolve(cwd), key = `${at}\n${repository.toLowerCase()}`;
  if (!scope.checkouts.has(key)) scope.checkouts.set(key, (async () => {
    try {
      let selected = scope.repositories.get(at);
      if (!selected) { selected = await resolveWorkflowRepository({ cwd }, ports); scope.repositories.set(at, selected); }
      if (!sameRepo(selected.repository, repository)) return null;
      return (await gitContext(cwd, ports))?.toplevel ?? null;
    } catch { return null; }
  })());
  return scope.checkouts.get(key);
}

function nativeAuthority(cwd, ports) {
  const s = service(cwd, ports), scope = ports[NATIVE_READ_SCOPE];
  const dataFor = repository => {
    const key = repository.toLowerCase();
    if (!scope.authorityData.has(key)) scope.authorityData.set(key, (async () => {
      // Another repository (or no checkout at all) has no local extra trust: apply the
      // default policy (owner and write collaborators) to its own GitHub data.
      const root = await selectedCheckout(cwd, repository, ports), selected = cwd ? scope.repositories.get(resolve(cwd)) : null;
      let configKnown = !!root || !cwd || !!selected && !sameRepo(selected.repository, repository), raw = null;
      if (root) {
        try { const setting = readJson(join(root, 'pdd.json'), {}); raw = Object.hasOwn(setting, 'autopilot') ? JSON.stringify(setting.autopilot) : null; }
        catch { configKnown = false; }
      }
      let lookup;
      try {
        const repo = (await s.api(`repos/${repository}`)).value;
        const pages = []; let endpoint = `repos/${repository}/collaborators?per_page=100`;
        while (endpoint) { const r = await s.api(endpoint); pages.push(...r.value); endpoint = r.next; }
        lookup = { owner: repo.owner?.login ?? '', writers: pages.filter(p => p.permissions?.push || p.permissions?.maintain || p.permissions?.admin).map(p => p.login), complete: !!repo.owner?.login };
      } catch { lookup = { owner: repository.split('/')[0], writers: [], complete: false }; }
      return { root, configKnown, raw, lookup };
    })());
    return scope.authorityData.get(key);
  };
  const authority = { read: async ({ repository, author }) => {
    const key = `${repository.toLowerCase()}\n${String(author ?? '').toLowerCase()}`;
    if (!scope.authorityResults.has(key)) scope.authorityResults.set(key, (async () => {
      const { root, configKnown, raw, lookup } = await dataFor(repository);
      const result = await runAutopilot({ action: 'isTrusted', author }, { cwd: root ?? cwd,
        config: { read: async () => ({ raw }), save: async () => { throw Error('Read-only authority'); } },
        github: { lookup: async () => ({ ...lookup, writers: [...lookup.writers] }) } });
      if (!lookup.complete || !configKnown || result.exitCode !== 0) return { authority: 'unverified' };
      return { authority: result.trusted ? 'trusted' : 'outsider' };
    })());
    return scope.authorityResults.get(key);
  } };
  Object.defineProperty(authority, NATIVE_AUTHORITY, { value: true });
  return authority;
}

async function readLocator(row, cwd, repository, ports, checkout = () => selectedCheckout(cwd, repository, ports)) {
  const key = canonical(row.key), s = service(cwd, ports), i = info(key);
  if (i?.comment) {
    const comment = (await s.api(`repos/${i.repository}/issues/comments/${i.comment}`)).value;
    if (canonical(comment.html_url) !== key || bookkeeping(comment.body)) throw Error('Unavailable requirement comment');
    const authority = await ports.authority.read({ repository: i.repository, author: comment.user?.login ?? '' });
    if (authority.authority !== 'trusted') throw Error('Requirement authority is unknown');
    return { key, revision: hash(comment.body ?? ''), text: comment.body ?? '', issue: i.key };
  }
  const m = /^https:\/\/github\.com\/([^/]+\/[^/]+)\/blob\/HEAD\/(.+)$/.exec(key);
  if (!m || !sameRepo(m[1], repository)) throw Error('Unsupported source locator');
  let path;
  try { path = m[2].split('/').map(decodeURIComponent).join('/'); } catch { throw Error('Invalid source locator'); }
  if (isAbsolute(path) || path.split('/').some(p => !p || p === '.' || p === '..') || /[\0\\]/.test(path)) throw Error('Invalid source path');
  const root = await checkout(); let bytes;
  if (root) {
    const target = realpathSync(resolve(root, path)), rel = relative(realpathSync(root), target);
    if (rel.startsWith('..') || isAbsolute(rel)) throw Error('Source leaves selected checkout');
    bytes = readFileSync(target);
  } else {
    const file = (await s.api(`repos/${repository}/contents/${path.split('/').map(encodeURIComponent).join('/')}`)).value;
    if (file.type !== 'file' || file.encoding !== 'base64' || typeof file.content !== 'string') throw Error('Source content unavailable');
    bytes = Buffer.from(file.content, 'base64');
  }
  return { key, revision: hash(bytes), path, text: new TextDecoder('utf-8', { fatal: true }).decode(bytes) };
}

function nativeContext(cwd, ports) {
  const context = { read: async ({ cwd: at = cwd, repository, inputs = [], [NATIVE_READ_SCOPE]: sharedScope }) => {
    const readPorts = createDependencyReadPorts({ cwd: at }, ports, sharedScope ?? nativeReadScope());
    const observed = []; let checkoutPromise;
    const checkout = () => checkoutPromise ??= selectedCheckout(at, repository, readPorts);
    for (const row of uniqueRows(inputs)) try { const item = await readLocator(row, at, repository, readPorts, checkout); observed.push({ key: item.key, revision: item.revision }); } catch { /* Missing is stale, never the carried revision. */ }
    // Semantic questions are carried by the durable reviews. Execution is
    // observed separately after the native issue identities have been read.
    return { json: JSON.stringify({ inputs: observed, conditions: [], execution: [], nativeExecution: true }) };
  } };
  Object.defineProperty(context, NATIVE_CONTEXT, { value: true });
  return context;
}

function nativeEvidence(cwd, ports) {
  const evidence = { read: async ({ cwd: at = cwd, repository, issues }) => {
    const readPorts = createDependencyReadPorts({ cwd: at }, ports, nativeReadScope());
    const source = [], requirements = [], required = new Map();
    for (const key of issues) {
      const i = info(key); if (!i || !sameRepo(i.repository, repository)) continue;
      const raw = parse((await ports.github.issue({ repository, issue: i.issue })).json);
      const authority = await readPorts.authority.read({ repository, author: raw.user?.login ?? '' });
      if (authority.authority === 'trusted') requirements.push({ issue: i.key, key: i.key,
        revision: hash(JSON.stringify({ title: raw.title ?? '', body: raw.body ?? '' })), text: `${raw.title ?? ''}\n\n${raw.body ?? ''}`, authority: 'trusted' });
      const comments = await allPages(ports.github, repository, 'comments', i.issue);
      for (const c of comments) {
        const record = parseRecord(c.body);
        if (record?.type === 'review') for (const row of nonIssueRows(record.value.inputs)) {
          const existing = required.get(row.key) ?? new Set(); existing.add(i.key); required.set(row.key, existing);
        }
        if (bookkeeping(c.body)) continue;
        if ((await readPorts.authority.read({ repository, author: c.user?.login ?? '' })).authority === 'trusted') requirements.push({
          issue: i.key, key: `${i.key}#issuecomment-${c.id}`, revision: hash(c.body ?? ''), text: c.body ?? '', authority: 'trusted',
        });
      }
    }
    // Explicit source paths in trusted requirements retain subject scope. Other
    // repository files remain optional context for the coordinator to examine.
    for (const r of requirements) for (const m of r.text.matchAll(/(?:https:\/\/github\.com\/[^/]+\/[^/]+\/blob\/HEAD\/)?\b((?:src|lib|docs|plans?|user_stories|prompts|test|tests)\/[A-Za-z0-9_./% -]+\.[A-Za-z0-9]+)\b/g)) {
      const path = m[1].trim(), key = `https://github.com/${repository.toLowerCase()}/blob/HEAD/${path.split('/').map(encodeURIComponent).join('/')}`;
      const targets = required.get(key) ?? new Set(); targets.add(r.issue); required.set(key, targets);
    }
    const root = await selectedCheckout(at, repository, readPorts);
    if (root) {
      const files = (await service(root, readPorts).run('git', ['ls-files', '-z'])).split('\0').filter(Boolean);
      for (const path of files) if (/\.(?:[cm]?[jt]sx?|py|md|json|toml|ya?ml|sql|html|css|sh)$/.test(path) && !/(?:^|\/)(?:node_modules|\.git|package-lock\.json)(?:\/|$)/.test(path)) {
        const key = `https://github.com/${repository.toLowerCase()}/blob/HEAD/${path.split('/').map(encodeURIComponent).join('/')}`;
        if (!required.has(key)) required.set(key, new Set());
      }
    }
    for (const [key, targets] of required) try {
      const item = await readLocator({ key }, at, repository, readPorts);
      if (item.path) source.push({ ...item, issues: [...targets] });
    } catch { /* Unavailable required rows stay absent on completion. */ }
    return { json: JSON.stringify({ source, requirements }) };
  } };
  Object.defineProperty(evidence, NATIVE_EVIDENCE, { value: true });
  return evidence;
}

async function launcherState(cwd, repository, ports) {
  const root = await selectedCheckout(cwd, repository, ports);
  if (!root) return null;
  const folder = ports.autopilotStateRoot ?? join(stateDirFor(ports), 'autopilot');
  const state = readJson(join(folder, `${hash(root).slice(0, 20)}.json`));
  return state && sameRepo(state.repo, repository) && state.cwd === root ? state : null;
}

// A claim comment carries one JSON record. `text` is its exact source so a
// heartbeat changes only the lastSeen value and keeps the rest of the comment.
function claimRecord(body) {
  const source = String(body ?? ''), blocks = [...source.matchAll(/```(?:json)?\s*\n([\s\S]*?)\n```/g)].map(m => m[1]);
  blocks.push(source.trim());
  for (const text of blocks) try {
    const value = JSON.parse(text);
    if (object(value) && ['repository', 'coordinatorId', 'machine', 'labelEventId'].every(k => typeof value[k] === 'string' && value[k])) return { value, text };
  } catch { /* Legacy prose claims have unknown coordinator identity. */ }
  return null;
}
const claimMetadata = body => claimRecord(body)?.value ?? null;
const CLAIM_EXPIRES_AFTER = 4 * 60 * 60 * 1000, LEGACY_CLAIM_EXPIRES_AFTER = 24 * 60 * 60 * 1000;
// Takeover ceiling (#3041): after 3 takeovers, an expired claim is not taken over a 4th
// time, and a 4th takeover made anyway does not admit a start.
// A takeover adds the label again at once: within 10 minutes of the removal, by its actor.
const TAKEOVER_LIMIT = 3, TAKEOVER_GAP = 10 * 60 * 1000;
// `self` ({coordinatorId, machine}) is the reader's own coordinator: taking back its own
// expired claim is a re-claim, not a takeover, so it is not limited.
export const takeoverLimited = (claim, self) => {
  const retake = claim?.expired === true && Boolean(self?.coordinatorId) && claim.coordinatorId === self.coordinatorId && claim.machine === self.machine;
  return (Number.isSafeInteger(claim?.takeovers) ? claim.takeovers : 0) + (claim?.expired === true && !retake ? 1 : 0) > TAKEOVER_LIMIT;
};
// A "lastSeen" member with a JSON scalar value, anywhere in the record text.
const LAST_SEEN = /(,\s*)?"lastSeen"\s*:\s*(?:"(?:[^"\\]|\\.)*"|-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?|true|false|null)(\s*,)?/g;
// The same for another member that only the tick writes: the 24-hour alert time (#3041).
const memberPattern = member => member === 'lastSeen' ? LAST_SEEN : new RegExp(LAST_SEEN.source.replace('"lastSeen"', `"${member}"`), 'g');
const TICK_MEMBERS = ['lastSeen', 'longRunningAlertedAt'];
const time = value => typeof value === 'string' ? Date.parse(value) : NaN;
const iso = at => new Date(at).toISOString();

// Set or remove only one top-level member (lastSeen unless named) and keep every other
// byte. Each place where the member can be is tried; an edit counts only when the new
// body parses to exactly the expected record, so a nested member is never changed.
// Return null when no such edit exists.
function editClaimRecord(body, record, expected, name = 'lastSeen') {
  const accept = text => { const next = String(body).replace(record.text, () => text); return isDeepStrictEqual(claimRecord(next)?.value, expected) ? next : null; };
  const set = Object.hasOwn(expected, name), value = JSON.stringify(expected[name]);
  if (set && !Object.hasOwn(record.value, name)) return accept(record.text.replace(/\}\s*$/, `,"${name}":${value}}`));
  for (const match of record.text.matchAll(memberPattern(name))) {
    const [whole, before = '', after = ''] = match, member = set ? `${before}"${name}":${value}${after}` : before && after ? ',' : '';
    const next = accept(record.text.slice(0, match.index) + member + record.text.slice(match.index + whole.length));
    if (next !== null) return next;
  }
  return null;
}

// The claim comment body without its top-level lastSeen member. A heartbeat alone
// must not look like new trusted work to the tick.
// The 24-hour alert time is removed the same way: it is also a tick write.
export function withoutClaimHeartbeat(body) {
  let text = body;
  for (const name of TICK_MEMBERS) {
    const record = claimRecord(text);
    if (!record || !Object.hasOwn(record.value, name)) continue;
    const { [name]: removed, ...rest } = record.value;
    text = editClaimRecord(text, record, rest, name) ?? text;
  }
  return text;
}

async function winningClaim(repository, key, github, authority, now = NaN) {
  // Claim checks are their own purpose in the GitHub call ledger.
  const i = info(key), raw = parse((await github.issue({ repository, issue: i.issue, purpose: 'claims' })).json);
  if (raw.error) throw Error('Current claim issue unavailable');
  const labels = raw.labels?.map(l => typeof l === 'string' ? l : l.name) ?? [];
  if (!labels.includes('pdd:working')) return null;
  const timeline = await allPages(github, repository, 'timeline', i.issue, 'claims'), comments = await allPages(github, repository, 'comments', i.issue, 'claims');
  let candidates = [], stuck = null;
  // Claim eras in order ({winner, start, end, index}; the current era has no end) and the
  // removals of pdd:stuck, for the takeover count below.
  const eras = [], stuckRemovals = [];
  // Events arrive in service order. Only a native removal ends the active claim era.
  for (const [index, event] of timeline.entries()) {
    if (event.label?.name === 'pdd:working') {
      if (event.event === 'unlabeled') { if (candidates.length) eras.at(-1).end = { event, index }; candidates = []; }
      if (event.event === 'labeled') { if (!candidates.length) eras.push({ winner: event, start: index, end: null }); candidates.push(event); }
    }
    if (event.label?.name === 'pdd:stuck') {
      if (event.event === 'unlabeled' && stuck) stuckRemovals.push({ at: time(event.created_at), index });
      stuck = event.event === 'labeled' ? event : event.event === 'unlabeled' ? null : stuck;
    }
  }
  // The one trusted claim comment of an era: by the winning label event's actor, naming that event.
  const recordOf = async winner => {
    if (!winner?.id || !winner.actor?.login) return null;
    const matching = [];
    for (const comment of comments) {
      const metadata = claimMetadata(comment.body);
      if (metadata && sameRepo(metadata.repository, repository) && metadata.labelEventId === String(winner.id)
        && comment.user?.login?.toLowerCase() === winner.actor.login.toLowerCase()
        && (await authority.read({ repository, author: comment.user.login })).authority === 'trusted') matching.push({ comment, metadata });
    }
    return matching.length === 1 ? matching[0] : null;
  };
  // The heartbeat time of a matched claim record. The current era and the takeover count
  // below use this one rule. A top-level lastSeen member, with any value ("" in a new
  // record), makes the comment a heartbeat claim; a record without it (older pdd) keeps
  // the legacy rule (NaN here). The time is only the comment's GitHub server time:
  // updated_at, else created_at. A recorded lastSeen never extends the claim, so no
  // writer clock or written value keeps a dead claim live. With no server time, the
  // legacy rule applies.
  const heartbeatTime = ({ comment, metadata }) => !Object.hasOwn(metadata, 'lastSeen') ? NaN
    : Number.isFinite(time(comment.updated_at)) ? time(comment.updated_at) : time(comment.created_at);
  // Takeovers (#3041), from GitHub data only. An era ends in one of three ways:
  // - a takeover: its claim was already expired at the removal (the same expiry rules at
  //   that time, with only earlier facts), and the removal's actor added the label again
  //   at once (within 10 minutes) for another coordinator or machine;
  // - a re-claim: the same, but the new claim names the same coordinator and machine;
  // - else a release: a normal end of a live claim, or a person's removal of an expired
  //   label. It ends the claim chain and the count starts again at 0.
  // A takeover and a re-claim continue the chain; claimedAt is the chain start. A removal
  // of pdd:stuck while the claim is takeover-limited also starts the count again at 0.
  for (const era of eras) era.record = await recordOf(era.winner);
  const expiredAt = (era, at, index) => {
    const server = era.record ? heartbeatTime(era.record) : NaN;
    const seen = Number.isFinite(server) ? Math.min(server, at) : [...comments.flatMap(c => [time(c.created_at), time(c.updated_at)]), ...timeline.slice(0, index).map(e => time(e.created_at))]
      .filter(value => Number.isFinite(value) && value < at).reduce((latest, value) => Math.max(latest, value), -Infinity);
    return Number.isFinite(at) && Number.isFinite(seen) && at - seen >= (Number.isFinite(server) ? CLAIM_EXPIRES_AFTER : LEGACY_CLAIM_EXPIRES_AFTER);
  };
  const owner = era => era?.record ? `${era.record.metadata.coordinatorId}\n${era.record.metadata.machine}` : null;
  const login = event => String(event?.actor?.login ?? '').toLowerCase();
  let takeovers = 0, chainStart = 0;
  const points = [...eras.flatMap((era, k) => era.end ? [{ index: era.end.index, k }] : []), ...stuckRemovals].sort((a, b) => a.index - b.index);
  for (const point of points) {
    if (point.k === undefined) {
      const held = eras.find(era => era.start < point.index && (!era.end || era.end.index > point.index));
      if (takeovers + (held && expiredAt(held, point.at, point.index) ? 1 : 0) > TAKEOVER_LIMIT) takeovers = 0;
      continue;
    }
    const era = eras[point.k], next = eras[point.k + 1], at = time(era.end.event.created_at);
    const again = next && login(next.winner) && login(next.winner) === login(era.end.event) && time(next.winner.created_at) - at <= TAKEOVER_GAP;
    if (again && expiredAt(era, at, era.end.index)) { if (!owner(era) || owner(era) !== owner(next)) takeovers++; }
    else { takeovers = 0; chainStart = point.k + 1; }
  }
  const chain = eras.slice(chainStart), current = candidates.length ? eras.at(-1) : null;
  const claimedAt = current ? time(chain[0].winner.created_at) : NaN;
  // The coordinator that held the claim last before the current owner in this chain.
  const previous = current && chain.slice(0, -1).reverse().find(era => owner(era) && owner(era) !== owner(current));
  // The 24-hour alert is sent once per chain: any claim record of the chain may carry it.
  const alerted = current ? chain.map(era => time(era.record?.metadata.longRunningAlertedAt)).filter(Number.isFinite).sort((a, b) => a - b)[0] : NaN;
  // Expiry: a heartbeat claim is expired 4 hours after its last-seen time. A legacy
  // claim (a record with no top-level lastSeen, no unique matching claim record, a bare
  // label, or a claim comment with no server time) is expired after 24 hours with no
  // issue activity. An unknown time or clock never expires a claim.
  const facts = (claim, lastSeen) => {
    const heartbeat = Number.isFinite(lastSeen);
    const seen = heartbeat ? lastSeen : [time(raw.updated_at), ...comments.flatMap(c => [time(c.created_at), time(c.updated_at)]),
      ...timeline.map(e => time(e.created_at))].filter(Number.isFinite).reduce((latest, at) => Math.max(latest, at), -Infinity);
    const expired = Number.isFinite(now) && Number.isFinite(seen) && now - seen >= (heartbeat ? CLAIM_EXPIRES_AFTER : LEGACY_CLAIM_EXPIRES_AFTER);
    const stuckSince = labels.includes('pdd:stuck') ? time(stuck?.created_at) : NaN;
    return { ...claim, active: !expired, ...(Number.isFinite(seen) ? { lastSeen: iso(seen) } : {}), ...(expired ? { expired: true } : {}),
      ...(Number.isFinite(stuckSince) ? { stuckSince: iso(stuckSince) } : {}), ...(Number.isFinite(claimedAt) ? { claimedAt: iso(claimedAt) } : {}),
      ...(takeovers ? { takeovers } : {}),
      ...(takeovers && previous ? { previousOwner: { coordinatorId: previous.record.metadata.coordinatorId, machine: previous.record.metadata.machine } } : {}),
      ...(Number.isFinite(alerted) ? { longRunningAlertedAt: iso(alerted) } : {}) };
  };
  const winner = candidates[0];
  if (!winner?.id || !winner.actor?.login) return facts({ issue: key, owner: '', coordinatorId: '', machine: '', commentId: '', labelEventId: '' });
  const match = current?.record;
  if (!match) return facts({ issue: key, owner: '', coordinatorId: '', machine: '', commentId: '', labelEventId: String(winner.id) });
  const { comment, metadata } = match;
  // The last-seen time of the current claim comes from heartbeatTime above: a heartbeat
  // claim (a top-level lastSeen member) uses only the comment's GitHub server time, at
  // most now; a record without lastSeen (older pdd) keeps the legacy rule.
  const server = heartbeatTime(match);
  const lastSeen = Number.isFinite(server) && Number.isFinite(now) ? Math.min(server, now) : server;
  return facts({ issue: key, owner: metadata.coordinatorId, coordinatorId: metadata.coordinatorId, machine: metadata.machine,
    commentId: String(comment.id), labelEventId: String(winner.id) }, lastSeen);
}

// The owning coordinator sets one top-level tick member (a time) of its own winning
// claim comment. It edits nothing else and no other comment.
async function setOwnClaimTime(name, { cwd = '', repository, claim, coordinatorId, machine, at }, ports) {
  const i = info(claim?.issue), s = service(cwd, ports);
  if (!repositoryName(repository) || !i || !sameRepo(i.repository, repository) || !/^[1-9][0-9]*$/.test(String(claim.commentId ?? ''))
    || !claim.labelEventId || claim.active !== true || claim.coordinatorId !== coordinatorId || claim.machine !== machine || !Number.isFinite(time(at))) return null;
  const endpoint = `repos/${repository}/issues/comments/${claim.commentId}`, comment = (await s.api(endpoint)).value;
  const record = claimRecord(comment?.body);
  if (String(comment?.id) !== String(claim.commentId) || !record || !sameRepo(record.value.repository, repository) || record.value.coordinatorId !== coordinatorId
    || record.value.machine !== machine || record.value.labelEventId !== String(claim.labelEventId)) return null;
  const value = iso(time(at)), body = editClaimRecord(comment.body, record, { ...record.value, [name]: value }, name);
  if (body === null) throw Error(`Claim record cannot take ${name === 'lastSeen' ? 'a heartbeat' : name} without other changes`);
  const saved = (await s.api(endpoint, 'PATCH', JSON.stringify({ body }))).value;
  if (String(saved?.id) !== String(claim.commentId) || claimRecord(saved.body)?.value[name] !== value) throw Error(name === 'lastSeen' ? 'Claim heartbeat readback is unresolved' : 'Claim record readback is unresolved');
  return value;
}

// Heartbeat: the owning coordinator writes the current time as the top-level lastSeen
// of its own winning claim comment.
export async function refreshClaimHeartbeat(args, ports = {}) {
  const lastSeen = await setOwnClaimTime('lastSeen', args, ports);
  return lastSeen === null ? { state: 'skipped' } : { state: 'refreshed', lastSeen };
}

// The 24-hour alert (#3041): after delivering it, the owning coordinator writes the time
// as the top-level longRunningAlertedAt of its own claim comment, so that no coordinator
// of the same claim chain sends it again.
export async function recordLongRunningAlert(args, ports = {}) {
  const longRunningAlertedAt = await setOwnClaimTime('longRunningAlertedAt', args, ports);
  return longRunningAlertedAt === null ? { state: 'skipped' } : { state: 'recorded', longRunningAlertedAt };
}

// One current custody observation for both dependency reconciliation and admission.
async function readLocalOccupied({ cwd, repository }, ports = {}) {
  const context = await gitContext(cwd, ports);
  if (!context || !await selectedCheckout(cwd, repository, ports)) return { runs: [], runsKnown: false };
  const runs = [], seen = new Set(); let runsKnown = true, names = [];
  const directory = join(context.commonDir, 'pdd', 'runs');
  try { names = readdirSync(directory); } catch (e) { if (e.code !== 'ENOENT') runsKnown = false; }
  for (const name of names.filter(n => /^[1-9][0-9]*(?:-cancelled-[0-9a-f]+)?$/.test(n))) {
    let run;
    try {
      run = readJson(join(directory, name, 'status.json'));
      if (!object(run) || run.v !== 1 || !Number.isSafeInteger(run.number) || run.number < 1
        || typeof run.repo !== 'string' || !repositoryName(run.repo) || typeof run.state !== 'string'
        || !Array.isArray(run.areas) || !Array.isArray(run.chats)) throw Error('Invalid run');
    } catch { runsKnown = false; continue; }
    if (!sameRepo(run.repo, repository) || ['completed', 'cancelled'].includes(run.state)) continue;
    const runId = run.runId || run.runDir;
    if (typeof runId !== 'string' || !runId) { runsKnown = false; continue; }
    seen.add(runId);
    const chat = currentChat(run), state = chatLifecycle(chat); let finishedTurn = false;
    if (['paused', 'stuck', 'question', 'waiting'].includes(run.state) && chat && !chat.startUnconfirmed && !run.chatFailure
      && !(run.chatReplacement && !['launched', 'rolledBack', 'ended'].includes(run.chatReplacement.phase))) {
      const live = await chatSession(chat, ports), now = (ports.now ?? Date.now)();
      const own = sessionEvidenceDue(chat, live, now) && !observedSession(chat, chat.agent ?? run.agent)
        ? await ownSession({ run, chat, since: launchAnchor(chat), ports }) : null;
      const observed = observeLifecycle(chat, live, now, chat.agent ?? run.agent, own?.kind === 'match' ? own.id : null);
      finishedTurn = live.alive && live.status === 'done' && validSessionId(chat.session?.id) && validSessionId(live.sessionId) && chat.session.id === live.sessionId && observed.exact;
      // A saved end alone cannot establish current custody; Herdr must also confirm absence.
      if (!live.alive && ['agent_not_found', 'server_not_running'].includes(live.code)
        && ['ended', 'failed'].includes(observed.state)) continue;
    }
    runs.push({ issue: `https://github.com/${repository.toLowerCase()}/issues/${run.number}`, runId,
      state: chat?.startUnconfirmed || (state === 'starting' && !finishedTurn) ? 'starting' : ['running', 'waiting', 'paused', 'stuck', 'question'].includes(run.state) ? run.state : 'unknown', ...(finishedTurn ? { occupied: false } : {}),
      ...(run.state === 'paused' && run.runtimeWait ? { waiting: 'runtime' } : {}) });
  }
  const index = join(context.commonDir, 'pdd', 'worktree-assignments');
  let indexExists = false;
  try { readdirSync(index); indexExists = true; } catch (e) { if (e.code !== 'ENOENT') runsKnown = false; }
  if (indexExists) try {
    const runFolder = join(index, 'runs'), issueFolder = join(index, 'issues');
    const runFiles = new Set(readdirSync(runFolder));
    const issueFiles = readdirSync(issueFolder);
    const allocated = new Set();
    for (const file of issueFiles) {
      const match = /^([1-9][0-9]*)\.json$/.exec(file), issueNumber = Number(match?.[1]);
      if (!match || !Number.isSafeInteger(issueNumber)) { runsKnown = false; continue; }
      try {
        const issuePath = join(issueFolder, file);
        const assignment = readJson(issuePath), runId = assignment?.runId;
        if (!object(assignment) || typeof runId !== 'string' || !runId || !repositoryName(assignment.repository)
          || !sameRepo(assignment.repository, repository) || assignment.commonDir !== context.commonDir
          || assignment.issueNumber !== issueNumber) throw Error('Invalid current allocation identity');
        const runFile = `${runId}.json`;
        if (!runFiles.has(runFile)) throw Error('Missing current allocation record');
        const runPath = join(runFolder, runFile), runStat = lstatSync(runPath), issueStat = lstatSync(issuePath);
        if (!runStat.isFile() || !issueStat.isFile() || runStat.dev !== issueStat.dev || runStat.ino !== issueStat.ino
          || runStat.nlink !== 2 || issueStat.nlink !== 2) throw Error('Unmatched allocation record');
        if (allocated.has(runId)) throw Error('Duplicate allocation run');
        allocated.add(runId);
        const issueKey = `https://github.com/${repository.toLowerCase()}/issues/${issueNumber}`;
        const prior = runs.find(run => run.runId === runId);
        if (prior) { if (prior.issue !== issueKey) runsKnown = false; continue; }
        if (seen.has(runId)) continue;
        runs.push({ issue: issueKey, runId, state: 'starting' });
      } catch { runsKnown = false; }
    }
  } catch { runsKnown = false; }
  return { runs, runsKnown };
}

function nativeOwners(cwd, ports) {
  const owner = { read: async ({ repository, issues }) => {
    const state = await launcherState(cwd, repository, ports), claims = [];
    let now = NaN; try { now = time((await ports.clock.now({})).iso); } catch { /* An unknown clock expires no claim. */ }
    for (const key of issues) { const claim = await winningClaim(repository, key, ports.github, ports.authority, now); if (claim) claims.push(claim); }
    return { json: JSON.stringify({ localOwner: state?.coordinatorId ?? '', localMachine: state?.machine ?? '', claims, ...await readLocalOccupied({ cwd, repository }, ports) }) };
  } };
  Object.defineProperty(owner, NATIVE_OWNERS, { value: true });
  return owner;
}

export function createDependencyReadPorts({ cwd = '' } = {}, supplied = {}, scope = nativeReadScope()) {
  const ports = { ...supplied };
  Object.defineProperty(ports, NATIVE_READ_SCOPE, { value: scope });
  ports.github ??= rawGithub(cwd, ports);
  ports.authority = supplied.authority?.[NATIVE_AUTHORITY] ? nativeAuthority(cwd, ports) : supplied.authority ?? nativeAuthority(cwd, ports);
  ports.context = supplied.context?.[NATIVE_CONTEXT] ? nativeContext(cwd, ports) : supplied.context ?? nativeContext(cwd, ports);
  ports.evidence = supplied.evidence?.[NATIVE_EVIDENCE] ? nativeEvidence(cwd, ports) : supplied.evidence ?? nativeEvidence(cwd, ports);
  // The default clock follows the caller's injected `now` (milliseconds) when present.
  ports.clock ??= { now: async () => ({ iso: new Date(typeof supplied.now === 'function' ? supplied.now() : Date.now()).toISOString() }) };
  ports.owners = supplied.owners?.[NATIVE_OWNERS] ? nativeOwners(cwd, ports) : supplied.owners ?? nativeOwners(cwd, ports);
  const settings = { read: async ({ cwd: at = cwd, repository }) => {
    const state = await launcherState(at, repository, ports), root = await selectedCheckout(at, repository, ports);
    if (!root) throw Error('Current repository settings unavailable');
    const result = await runAutopilot({ action: 'setup', interactive: false, inRepo: true }, { cwd: root, execFile: ports.execFile });
    if (result.exitCode !== 0 || !state || typeof state.enabled !== 'boolean') throw Error('Current activation unavailable');
    return { mode: state.enabled ? result.mode : 'off', activation: state.activatedAt ?? '', ...(state.runs === undefined ? {} : { runs: state.runs }) };
  } };
  Object.defineProperty(settings, NATIVE_SETTINGS, { value: true });
  ports.settings = supplied.settings?.[NATIVE_SETTINGS] ? settings : supplied.settings ?? settings;
  return ports;
}

function parseRecord(body) {
  const marker = String(body ?? '').match(/<!--\s*pdd-dependency-(review|impact):v([^\s]+)\s*-->/);
  if (!marker) return null;
  const type = marker[1]; let value;
  try {
    const block = String(body).slice(marker.index).match(/```json\s*\n([\s\S]*?)\n```/);
    const envelope = JSON.parse(block?.[1] ?? ''); value = envelope[type];
    if (marker[2] !== '1' || envelope.schema_version !== `pdd.dependency-${type}.v1` || !object(value)) return { type, value: value ?? {}, valid: false };
    return { type, value, valid: true };
  } catch { return { type, value: value ?? {}, valid: false }; }
}

function normalizedRecord(comment, issue, authority) {
  const record = parseRecord(comment.body);
  if (!record) return null;
  const intact = record.valid && typeof comment.created_at === 'string' && comment.created_at === comment.updated_at;
  // Invalid records must remain visible, but must not inject malformed fields
  // into the model or hide a later, unresolved review.
  if (record.type === 'review' && !validReview(record.value)) record.valid = false;
  if (record.type === 'impact' && (!validRows(record.value.inputs) || !Array.isArray(record.value.reviews)
    || !Array.isArray(record.value.affected) || typeof record.value.complete !== 'boolean')) record.valid = false;
  const value = record.valid ? record.value : {};
  if (record.type === 'review') return { type: 'review', value: { analysis: '', base: [], continuation: '', issue, inputs: [], candidates: [], outcome: 'pending',
    dependencies: [], questions: [], effects: 'pending', ...value, id: String(comment.id), issue,
    authority, intact: intact && record.valid && info(record.value.issue)?.key === issue } };
  return { type: 'impact', value: { inputs: [], reviews: [], affected: [], complete: false, ...value,
    id: String(comment.id), host: issue, authority, trusted: authority === 'trusted', intact: intact && record.valid } };
}

export async function readDependencySnapshot({ cwd = '', repository, inputs = [] } = {}, supplied = {}) {
  const scope = nativeReadScope(), ports = createDependencyReadPorts({ cwd }, supplied, scope);
  const readContext = args => ports.context[NATIVE_CONTEXT] ? ports.context.read({ ...args, [NATIVE_READ_SCOPE]: scope }) : ports.context.read(args);
  if (!repository) {
    const selected = await resolveWorkflowRepository({ cwd }, ports);
    repository = selected.repository;
    if (cwd) scope.repositories.set(resolve(cwd), selected);
  }
  if (!repositoryName(repository)) fail('invalid-repository');
  repository = repository.toLowerCase();
  const warnings = [], issues = [], edges = [], reviews = [], impacts = [], known = new Set();
  const authorities = new Map();
  const authorityFor = (repository, author) => {
    const key = `${repository.toLowerCase()}\n${author.toLowerCase()}`;
    if (!authorities.has(key)) authorities.set(key, ports.authority.read({ repository, author }).catch(() => ({ authority: 'unverified' })));
    return authorities.get(key);
  };
  let complete = true, contextKnown = true, context = { inputs: [], conditions: [], execution: [] };
  const coverage = { scope: true, issues: [] }, coverageByKey = new Map(), rootIndex = new Map();
  const warn = text => { complete = false; warnings.push(text); };
  try { context = parse((await readContext({ cwd, repository, ...(inputs.length ? { inputs } : {}) })).json); }
  catch { contextKnown = false; warn('Required context is unavailable'); }
  let roots = [];
  try { roots = await allPages(ports.github, repository, 'issues', 0); } catch (e) { roots = e.partialItems ?? []; coverage.scope = false; warn('Open issue pages are incomplete'); }
  let invalidIndex = false;
  for (const raw of roots.filter(r => !r.pull_request)) {
    const key = info(raw.html_url)?.key;
    if (!key || info(key).repository !== repository || !/^[1-9][0-9]*$/.test(String(raw.id)) || typeof raw.title !== 'string' || !(raw.body === null || typeof raw.body === 'string') || rootIndex.has(key)) { coverage.scope = false; invalidIndex = true; continue; }
    rootIndex.set(key, raw);
  }
  if (invalidIndex) warn('Open issue index is incomplete');
  const queue = [...rootIndex.keys()];
  // Supplied GitHub ports retain the exact existing contract and call behavior.
  if (ports.github[NATIVE_GITHUB] && roots.length) {
    const bulk = await bulkRoots(cwd, repository, roots, ports), github = ports.github;
    ports.github = { ...github,
      issue: async args => { const hit = bulk.get(`https://github.com/${args.repository.toLowerCase()}/issues/${args.issue}`); return hit ? {json:JSON.stringify(hit.raw)} : github.issue(args); },
      page: async args => { const hit = bulk.get(`https://github.com/${args.repository.toLowerCase()}/issues/${args.issue}`); return hit && !args.cursor && hit.pages[args.kind] ? {json:JSON.stringify({items:hit.pages[args.kind],next:''})} : github.page(args); },
    };
    if (ports.owners[NATIVE_OWNERS]) ports.owners = nativeOwners(cwd, ports);
  }
  async function read(key) {
    if (known.has(key)) return; known.add(key);
    const i = info(key); let raw, detailKnown = true;
    const observed = { key, issue: true, authority: true, comments: true, blockedBy: true, blocking: true, timeline: true, context: contextKnown, execution: true, reviewImpact: true, missing: [] };
    coverage.issues.push(observed); coverageByKey.set(key, observed);
    const missing = (field, text) => { observed[field] = false; observed.missing.push(text); warn(text); };
    try { raw = parse((await ports.github.issue({ repository: i.repository, issue: i.issue })).json); if (raw.error || info(raw.html_url)?.key !== key) throw Error(); }
    catch { detailKnown = false; missing('issue', `Issue unavailable: ${key}`); raw = rootIndex.get(key); if (!raw) { for (const field of ['authority','comments','blockedBy','blocking','timeline','context','execution']) observed[field] = false; observed.missing.push('Linked issue observations unavailable'); issues.push({ key, nodeId: '', title: key, revision: '', state: 'unknown', authority: 'unknown', conditions: [], execution: 'unknown', holds: [] }); return; } }
    const indexed = rootIndex.get(key);
    if (detailKnown && indexed && (String(raw.id) !== String(indexed.id) || raw.title !== indexed.title || raw.body !== indexed.body)) {
      coverage.scope = false; warn(`Open issue index changed during observation: ${key}`);
    }
    const authority = await authorityFor(i.repository, raw.user?.login ?? '');
    if (!['trusted','outsider'].includes(authority.authority)) missing('authority', `Issue authority unavailable: ${key}`);
    const requirementRevision = hash(JSON.stringify({ title: raw.title ?? '', body: raw.body ?? '' }));
    const conditionRows = (context.conditions ?? []).filter(c => canonical(c.issue ?? c.key) === key), execution = (context.execution ?? []).find(c => canonical(c.issue ?? c.key) === key);
    const labels = raw.labels?.map(l => typeof l === 'string' ? l : l.name) ?? [], holds = [...(execution?.holds ?? [])];
    const assignees = Array.isArray(raw.assignees) && raw.assignees.every(a => object(a) && typeof a.login === 'string' && a.login.trim())
      ? raw.assignees.map(a => a.login) : undefined;
    if (labels.includes('pdd:working')) holds.push('Claimed');
    if (labels.includes('pdd:stuck')) holds.push('Stuck');
    if (labels.includes('pdd:code-pending')) holds.push('Code pending');
    const issue = { key, nodeId: /^[1-9][0-9]*$/.test(String(raw.id)) ? String(raw.id) : '', title: raw.title ?? '', revision: requirementRevision,
      state: !detailKnown ? 'unknown' : raw.state === 'open' ? 'open' : raw.state === 'closed' ? raw.state_reason === 'not_planned' ? 'not_planned' : 'completed' : 'unknown',
      authority: authority.authority === 'trusted' ? 'trusted' : authority.authority === 'outsider' ? 'untrusted' : 'unknown',
      conditions: conditionRows.map(c => c.text ?? c.condition).filter(Boolean), execution: execution?.execution ?? execution?.state ?? (labels.includes('pdd:working') ? 'running' : context.nativeExecution ? 'unknown' : 'idle'), holds: [...new Set(holds)],
      ...(assignees ? { assignees } : {}),
      ...(conditionRows.length ? { conditionSources: conditionRows.filter(c => c.source).map(c => ({ text: c.text ?? c.condition, source: c.source, inputs: c.inputs ?? [{ key, revision: requirementRevision }] })) } : {}),
      ...(execution?.executionClaim ? { executionClaim: execution.executionClaim } : {}), ...(execution?.runIds ? { runIds: execution.runIds } : {}) };
    issues.push(issue);
    for (const kind of ['comments', 'blockedBy', 'blocking', 'timeline']) {
      let items;
      try { items = await allPages(ports.github, i.repository, kind, i.issue); } catch (e) { items = e.partialItems ?? []; missing(kind, `Incomplete ${kind}: ${key}`); }
      if (kind === 'comments') for (const comment of items) {
        const current = await authorityFor(i.repository, comment.user?.login ?? '');
        if (!['trusted','outsider'].includes(current.authority)) missing('comments', `Comment authority unavailable: ${key}`);
        const record = normalizedRecord(comment, key, current.authority);
        if (record) {
          if (record.type === 'review') { reviews.push(record.value); for (const d of record.value.dependencies) if (info(d.key)) queue.push(info(d.key).key); }
          else impacts.push(record.value);
        } else if (!bookkeeping(comment.body) && current.authority === 'trusted') {
          context.inputs ??= []; context.inputs.push({ key: `${key}#issuecomment-${comment.id}`, revision: hash(comment.body ?? '') });
        }
      }
      if (kind === 'blockedBy' || kind === 'blocking') for (const linked of items) {
        const other = info(linked.html_url)?.key;
        if (!other) { missing(kind, `Relationship identity unavailable: ${key}`); continue; }
        const edge = kind === 'blockedBy' ? { dependent: key, blocker: other } : { dependent: other, blocker: key };
        edges.push(edge); queue.push(other);
      }
    }
  }
  for (let at = 0; at < queue.length; at++) await read(queue[at]);
  if (context.nativeExecution) {
    const local = issues.filter(i => info(i.key)?.repository === repository && i.state !== 'unknown');
    try {
      const observation = parse((await ports.owners.read({ repository, issues: local.map(i => i.key) })).json);
      if (!Array.isArray(observation.claims) || !Array.isArray(observation.runs) || typeof observation.runsKnown !== 'boolean') throw Error('Incomplete execution observation');
      for (const issue of local) {
        const claims = observation.claims.filter(c => canonical(c.issue) === issue.key && c.active);
        const expired = !claims.length && observation.claims.find(c => canonical(c.issue) === issue.key && c.active === false && c.expired === true && c.lastSeen);
        if (expired) issue.holds = [...issue.holds.filter(hold => hold !== 'Claimed'), `Expired claim, last seen ${expired.lastSeen}`];
        const limited = observation.claims.find(c => canonical(c.issue) === issue.key && takeoverLimited(c, { coordinatorId: observation.localOwner, machine: observation.localMachine }));
        if (limited) issue.holds.push(`Taken over ${limited.takeovers} times; take the stuck path, not another takeover`);
        const runs = observation.runs.filter(r => canonical(r.issue) === issue.key);
        if (observation.runsKnown) issue.runIds = runs.map(r => r.runId).filter(Boolean);
        if (runs.some(r => r.waiting === 'runtime') && !issue.holds.includes('Waiting for the interpreter')) issue.holds.push('Waiting for the interpreter');
        if (claims.length === 1 && claims[0].coordinatorId && claims[0].commentId && claims[0].labelEventId) {
          const { coordinatorId, commentId, labelEventId } = claims[0];
          issue.executionClaim = { coordinatorId, commentId, labelEventId };
        }
        issue.execution = claims.length || issue.holds.includes('Claimed') ? 'running' : observation.runsKnown ? 'idle' : 'unknown';
      }
    } catch { warn('Execution observations are unavailable'); }
    for (const issue of local) if (issue.execution === 'unknown') { const row = coverageByKey.get(issue.key); row.execution = false; row.missing.push('Execution observation unavailable'); }
  }
  const required = uniqueRows([...inputs, ...reviews.flatMap(r => nonIssueRows(r.inputs)), ...impacts.flatMap(i => nonIssueRows(i.inputs))]);
  if (required.length) {
    try {
      const extra = parse((await readContext({ cwd, repository, inputs: required })).json);
      context.inputs = uniqueRows([...(context.inputs ?? []).filter(r => !required.some(x => x.key === r.key)), ...(extra.inputs ?? [])]);
    } catch { context.inputs = (context.inputs ?? []).filter(row => !required.some(input => input.key === row.key)); warn('Saved source inputs are unavailable'); }
  }
  const currentInputs = new Map((context.inputs ?? []).map(row => [row.key, row.revision]));
  for (const row of coverage.issues) {
    // This row records whether this candidate's own issue and comment source
    // can support impact discovery. The graph checks the row for each actual
    // revision deficit, then still requires a trusted complete impact record.
    row.reviewImpact = row.issue && row.authority && row.comments;
    if (!row.reviewImpact) row.missing.push('Relevant impact discovery unavailable');
    const requiredForIssue = (issues.find(issue => issue.key === row.key)?.conditionSources ?? []).flatMap(condition => nonIssueRows(condition.inputs));
    if (!contextKnown || requiredForIssue.some(input => !currentInputs.has(input.key))) { row.context = false; row.missing.push('Required context unavailable'); }
    // Execution is observed only for root issues. A linked issue in another
    // repository matters only as a prerequisite, where its native state decides.
    if (info(row.key)?.repository === repository && issues.find(issue => issue.key === row.key)?.execution === 'unknown') { row.execution = false; if (!row.missing.includes('Execution observation unavailable')) row.missing.push('Execution observation unavailable'); }
  }
  const dedupEdges = [...new Map(edges.map(e => [`${e.dependent}\n${e.blocker}`, e])).values()];
  const capturedAt = (await ports.clock.now({})).iso;
  return { snapshot: { repository, capturedAt, complete, issues, edges: dedupEdges, reviews, impacts, inputs: uniqueRows(context.inputs ?? []), coverage, warnings }, warnings };
}

function validRows(rows) { return Array.isArray(rows) && rows.every(r => object(r) && typeof r.key === 'string' && typeof r.revision === 'string' && r.revision); }
function validReview(review) {
  const fields = ['analysis', 'base', 'continuation', 'issue', 'inputs', 'candidates', 'outcome', 'dependencies', 'questions', 'effects'];
  return object(review) && Object.keys(review).length === fields.length && fields.every(k => Object.hasOwn(review, k))
    && typeof review.analysis === 'string' && !!review.analysis && Array.isArray(review.base) && review.base.every(x => typeof x === 'string')
    && typeof review.continuation === 'string' && info(review.issue) && validRows(review.inputs) && validRows(review.candidates)
    && ['complete', 'question', 'pending'].includes(review.outcome) && ['none', 'pending', 'confirmed'].includes(review.effects)
    && Array.isArray(review.dependencies) && review.dependencies.every(d => info(d.key) && typeof d.reason === 'string' && d.reason.trim() && Array.isArray(d.evidence) && d.evidence.length && d.evidence.every(x => typeof x === 'string'))
    && Array.isArray(review.questions) && review.questions.every(x => typeof x === 'string' && x.trim())
    && (review.outcome !== 'complete' || !review.questions.length) && (review.outcome !== 'question' || review.questions.length > 0);
}

async function saveRecord({ repository, issue, value, type }, supplied) {
  const i = info(issue);
  if (!repositoryName(repository) || !i || i.comment || !sameRepo(i.repository, repository)) fail('invalid-review');
  const ports = createDependencyReadPorts({}, supplied), title = type === 'review' ? 'Dependency review' : 'Dependency impact';
  const readable = type === 'review' ? [value.outcome === 'complete' && !value.dependencies.length ? 'Dependencies checked: none.' : `Review: ${value.outcome}.`,
    ...value.dependencies.map(d => `- ${d.key}: ${d.reason}`), ...value.questions.map(q => `Question: ${q}`)].join('\n') : `Impact checked: ${value.complete ? 'complete' : 'pending'}.\n${value.affected.map(k => `- ${k}`).join('\n')}`;
  const marker = type === 'review' ? REVIEW : IMPACT;
  const body = `${readable}\n\n<!-- ${marker} -->\n<details><summary>${title}</summary>\n\n\`\`\`json\n${JSON.stringify({ schema_version: `pdd.dependency-${type}.v1`, [type]: value })}\n\`\`\`\n</details>`;
  try {
    const raw = parse((await ports.github.appendComment({ repository, issue: i.issue, body })).json);
    if (!raw.id) throw Error('No native comment confirmation');
    return { id: String(raw.id), state: 'saved', warnings: [] };
  } catch { return { id: '', state: 'pending', warnings: ['The comment append is unresolved; reread this analysis before retry.'] }; }
}

export async function saveDependencyReview({ repository, issue, review }, ports = {}) {
  if (!validReview(review) || info(review.issue)?.key !== info(issue)?.key) fail('invalid-review');
  return saveRecord({ repository, issue, value: review, type: 'review' }, ports);
}

export async function saveDependencyImpact({ repository, issue, impact }, ports = {}) {
  if (!object(impact) || Object.keys(impact).sort().join(',') !== 'affected,complete,inputs,reviews' || !validRows(impact.inputs)
    || !Array.isArray(impact.reviews) || !impact.reviews.every(x => typeof x === 'string') || !Array.isArray(impact.affected)
    || !impact.affected.every(x => info(x)) || typeof impact.complete !== 'boolean') fail('invalid-review');
  return saveRecord({ repository, issue, value: impact, type: 'impact' }, ports);
}

export async function applyDependencyChanges({ cwd = '', repository, issue, reviewId }, supplied = {}) {
  const target = info(issue);
  if (!target || !sameRepo(target.repository, repository)) fail('invalid-review');
  const ports = createDependencyReadPorts({ cwd }, supplied), added = [], warnings = [];
  const pending = text => ({ state: 'pending', added, warnings: [...warnings, text] });
  const read = async inputs => (await (ports.snapshots?.read ?? (args => readDependencySnapshot(args, ports)))({ repository, cwd, ...(inputs?.length ? { inputs } : {}) })).snapshot;
  let snapshot;
  try { snapshot = await read(); } catch { return pending('Current dependency observations are unavailable'); }
  const intent = snapshot.reviews.find(r => r.id === reviewId && info(r.issue)?.key === target.key);
  if (!intent || intent.outcome !== 'pending' || intent.effects !== 'pending') return pending('No current pending intent');
  const inputs = nonIssueRows(intent.inputs);
  const accepted = current => {
    const node = projectIssueGraph({ snapshot: current }).nodes.find(n => n.key === target.key);
    return node?.review === reviewId && node.reviewState === 'pending' && !node.reasons.includes('Incomplete relevant observations');
  };
  if (!accepted(snapshot)) return pending('The intent is stale, conflicting or unverified');
  // A person's change wins. A named blocker is refused when a person removed that
  // link (a confirmed review named it, or the subject's history has a "blocked by"
  // removal of it; a removal with an unknown blocker refuses every addition), or
  // when adding it would close a cycle. A refused addition ends as one question.
  const absent = current => [...new Set(intent.dependencies.map(d => info(d.key)?.key).filter(k => k
    && !current.edges.some(e => info(e.dependent)?.key === target.key && info(e.blocker)?.key === k)))];
  const refusal = async current => {
    const missing = absent(current);
    if (!missing.length) return { blockers: [] };
    let history;
    try { history = await allPages(ports.github, repository, 'timeline', target.issue); } catch { return null; }
    const { removed } = dependencyLinks({ snapshot: current, issue: target.key }), byPerson = new Set(); let unknown = false;
    for (const event of history) { const blocker = blockedByRemoval(event); if (blocker === undefined) continue; if (blocker) byPerson.add(blocker); else unknown = true; }
    if (unknown) return { blockers: missing, why: 'unknown' };
    const human = missing.filter(b => removed.includes(b) || byPerson.has(b));
    if (human.length) return { blockers: human, why: 'removed' };
    return { blockers: missing.filter(b => validateDependencyChange({ snapshot: current, dependent: target.key, blocker: b }).reason === 'cycle'), why: 'cycle' };
  };
  const ask = async (current, { blockers, why }) => {
    const subject = target.key, list = blockers.join(', ');
    const text = why === 'cycle' ? `The link "${subject} blocked by ${list}" would close a dependency cycle, so PDD did not add it. Which issue must go first?`
      : why === 'unknown' ? `A person removed a "blocked by" link of ${subject}, and PDD cannot tell which one. PDD did not add "${subject} blocked by ${list}". If ${subject} needs it first, add the link in GitHub or answer here.`
      : `A person removed the GitHub link "${subject} blocked by ${list}". PDD does not add it back. If ${subject} still needs it first, add the link in GitHub or answer here.`;
    const { id, authority, intact, ...raw } = intent;
    const question = { ...raw, base: [reviewId], continuation: '', outcome: 'question', dependencies: [], questions: [text], effects: 'none',
      inputs: [...raw.inputs.filter(r => !linkRow(r.key)), dependencyLinks({ snapshot: current, issue: subject }).row] };
    if (ports.admitEffect && !await ports.admitEffect()) return pending('Automatic control changed before the question');
    const saved = await saveDependencyReview({ repository, issue: subject, review: question }, ports);
    return saved.state === 'saved' ? { state: 'question', added, warnings: [...warnings, why === 'cycle' ? 'Dependency cycle' : 'Human dependency change'], questions: [text], reviewId: saved.id }
      : pending('The question is not yet observed');
  };
  const first = await refusal(snapshot);
  if (!first) return pending('Relationship history is unknown');
  if (first.blockers.length) return ask(snapshot, first);
  let lastWasWrite = false;
  for (const dependency of intent.dependencies) {
    try { snapshot = await read(inputs); } catch { return pending('Cannot revalidate the pending intent'); }
    if (!accepted(snapshot)) return pending('The intent changed before its remaining effects');
    const present = snapshot.edges.some(e => info(e.dependent)?.key === target.key && info(e.blocker)?.key === info(dependency.key)?.key);
    lastWasWrite = false;
    if (present) continue;
    const validation = validateDependencyChange({ snapshot, dependent: target.key, blocker: dependency.key });
    if (!validation.allowed && validation.reason !== 'cycle') return pending(`Dependency addition waits: ${validation.reason}`);
    // Check the history again before each write: a person may change a link at any time.
    const refused = await refusal(snapshot);
    if (!refused) return pending('Relationship history is unknown');
    if (refused.blockers.length) return ask(snapshot, refused);
    const blocker = snapshot.issues.find(i => info(i.key)?.key === info(dependency.key)?.key);
    if (!/^[1-9][0-9]*$/.test(blocker?.nodeId ?? '')) return pending('REST blocker identity is unavailable');
    if (ports.admitEffect && !await ports.admitEffect()) return pending('Automatic control changed before dependency effect');
    try { await ports.github.addBlocker({ repository, issue: target.issue, blockerId: blocker.nodeId }); }
    catch { /* An unclear reply is resolved only by observing the native edge. */ }
    try { snapshot = await read(inputs); } catch { return pending('Dependency effect readback is unknown'); }
    if (!snapshot.edges.some(e => info(e.dependent)?.key === target.key && info(e.blocker)?.key === info(dependency.key)?.key)) return pending('Dependency effect remains unobserved');
    added.push(info(dependency.key).key); lastWasWrite = true;
    if (!accepted(snapshot)) return pending('Inputs changed after a native effect');
  }
  if (!lastWasWrite) try { snapshot = await read(inputs); } catch { return pending('Cannot confirm current effects'); }
  if (!accepted(snapshot) || intent.dependencies.some(d => !snapshot.edges.some(e => info(e.dependent)?.key === target.key && info(e.blocker)?.key === info(d.key)?.key))) return pending('The intent cannot yet be confirmed');
  const { id, authority, intact, ...raw } = intent;
  if (ports.admitEffect && !await ports.admitEffect()) return pending('Automatic control changed before confirmation');
  const saved = await saveDependencyReview({ repository, issue: target.key, review: { ...raw, continuation: reviewId, outcome: 'complete', effects: 'confirmed' } }, ports);
  return saved.state === 'saved' ? { state: 'confirmed', added, warnings } : pending('The confirmed continuation is not yet observed');
}
