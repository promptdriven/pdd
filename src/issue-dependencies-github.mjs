// Implements prompts/cli/issue-dependencies-github.prompt.md.
import { execFile as execCallback } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { lstatSync, readFileSync, readdirSync, realpathSync } from 'node:fs';
import { dirname, join, resolve, relative, isAbsolute } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { runAutopilot } from './autopilot.mjs';
import { resolveWorkflowRepository } from './workflow-github.mjs';
import { gitContext, currentChat, stateDirFor } from './workflow-runs.mjs';
import { chatLifecycle, chatSession, observeLifecycle, sessionEvidenceDue, observedSession, ownSession, launchAnchor, validSessionId } from './workflow-chat.mjs';
import { dependencyLinks, projectIssueGraph, validateDependencyChange } from './issue-dependencies.mjs';
import { githubBudgetSettings, githubEtagCache, githubFloorGuard, githubFullLastPage, githubLedger, githubMachineEntries, githubReply, nativeGithubCounter } from './github-calls.mjs';

const REVIEW = 'pdd-dependency-review:v1', IMPACT = 'pdd-dependency-impact:v1';
const NATIVE_GITHUB = Symbol('native github'), NATIVE_OWNERS = Symbol('native owners'), LIVE_GITHUB = Symbol('live github');
const DEFAULT_CACHE = Symbol('default etag cache');
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
  const guard = ports.githubFloor;
  async function run(file, args, input, purpose, conditional = false, repository) {
    let r;
    try { r = await exec(file, args, { ...(cwd ? { cwd } : {}), ...(input === undefined ? {} : { input }), ...(purpose ? { purpose } : {}), ...(repository ? { repository } : {}) }); }
    catch (error) { guard?.observe(githubReply(error?.stdout)); if (conditional && notModified(error?.stdout)) return String(error.stdout); throw error; }
    guard?.observe(githubReply(r.stdout));
    if (r.code !== undefined && r.code !== 0 && !(conditional && notModified(r.stdout))) throw Object.assign(Error('Service read failed'), { status: r.code });
    return String(r.stdout ?? '');
  }
  // purpose names what the read is for in the GitHub call ledger, repository the ledger of a GraphQL call. With a githubCache
  // port, a GET sends the saved ETag; a 304 reply returns the saved body and next page and does not count against the limit.
  // A saved full last page, or a saved body that does not parse, sends no ETag: a 304 cannot show a new next page.
  // With a githubFloor port, a read that is not a safety read stops while fewer calls than the floor are left.
  async function api(endpoint, method = 'GET', input, purpose, repository, safety = false) {
    const write = method !== 'GET' && endpoint !== 'graphql';
    // The batch GraphQL read also stops when REST is below the floor: without REST reads the snapshot is not complete.
    if (guard && !write && !safety && !(ports.dependencyReads?.safety > 0) && (guard.blocked('core') || endpoint === 'graphql' && guard.blocked('graphql')))
      throw Object.assign(Error('GitHub limit is below the floor'), { status: 0, floor: true });
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

async function allPages(github, repository, kind, issue, purpose, safety = false) {
  const items = [], cursors = new Set(); let cursor = '';
  do {
    let value;
    try {
      if (cursors.has(cursor)) throw Error('Repeated GitHub cursor');
      cursors.add(cursor);
      value = parse((await github.page({ repository, kind, issue, cursor, ...(purpose ? { purpose } : {}), ...(safety ? { safety } : {}) })).json);
      if (value.error || !Array.isArray(value.items) || typeof value.next !== 'string') throw Error(`Incomplete ${kind} observation`);
      items.push(...value.items); cursor = value.next;
    } catch (error) { error.partialItems = [...items, ...(Array.isArray(value?.partialItems) ? value.partialItems : [])]; throw error; }
  } while (cursor);
  return items;
}

function rawGithub(cwd, ports) {
  const s = service(cwd, ports);
  // The live claim checks, the history and comments that a write depends on, and readbacks are safety reads: the
  // floor never stops them. The claim scan inside a snapshot is not one.
  const safe = (purpose, safety) => safety === true;
  const github = {
    page: async ({ repository, kind, issue, cursor, purpose, safety }) => {
      const suffix = { issues: '?state=open&per_page=100', comments: `/${issue}/comments?per_page=100`,
        blockedBy: `/${issue}/dependencies/blocked_by?per_page=100`, blocking: `/${issue}/dependencies/blocking?per_page=100`, timeline: `/${issue}/timeline?per_page=100` }[kind];
      if (!repositoryName(repository) || suffix === undefined) return { json: JSON.stringify({ error: 'Invalid GitHub scope', status: 400 }) };
      try {
        const route = { issues: 'issues', comments: `issues/${issue}/comments`, blockedBy: `issues/${issue}/dependencies/blocked_by`,
          blocking: `issues/${issue}/dependencies/blocking`, timeline: `issues/${issue}/timeline` }[kind];
        const path = cursor.split(/[?#]/, 1)[0];
        const canonical = /^repositories\/[1-9][0-9]*\/(.+)$/.exec(path);
        if (cursor && path !== `repos/${repository}/${route}` && canonical?.[1] !== route) throw Error('Foreign pagination cursor');
        const r = await s.api(cursor || `repos/${repository}/issues${suffix}`, 'GET', undefined, purpose, undefined, safe(purpose, safety));
        return { json: JSON.stringify({ items: r.value, next: r.next }) };
      } catch (e) { return { json: JSON.stringify({ error: 'GitHub read unavailable', status: e.status ?? 0 }) }; }
    },
    issue: async ({ repository, issue, purpose, safety }) => {
      try { return { json: JSON.stringify((await s.api(`repos/${repository}/issues/${issue}`, 'GET', undefined, purpose, undefined, safe(purpose, safety))).value) }; }
      catch (e) { return { json: JSON.stringify({ error: 'GitHub issue unavailable', status: e.status ?? 0 }) }; }
    },
    appendComment: async ({ repository, issue, body }) => {
      // Recover an uncertain previous append by immutable record identity before another POST. The search and the
      // readback belong to the write: they are safety reads.
      const record = parseRecord(body);
      const existing = await allPages(github, repository, 'comments', issue, undefined, true);
      const equal = row => {
        const other = parseRecord(row.body);
        return record && other && record.type === other.type && JSON.stringify(record.value) === JSON.stringify(other.value);
      };
      let row = existing.find(equal);
      if (!row) {
        try { row = (await s.api(`repos/${repository}/issues/${issue}/comments`, 'POST', JSON.stringify({ body }))).value; }
        catch (error) {
          const observed = (await allPages(github, repository, 'comments', issue, undefined, true)).filter(equal);
          if (observed.length !== 1) throw error;
          [row] = observed;
        }
      }
      if (!/^[1-9][0-9]*$/.test(String(row?.id))) throw Error('Append has no native comment identity');
      const readback = (await s.api(`repos/${repository}/issues/comments/${row.id}`, 'GET', undefined, undefined, undefined, true)).value;
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
  Object.defineProperty(github, LIVE_GITHUB, { value: github });
  return github;
}

// ---- The saved dependency snapshot (prompt section "Saved dependency snapshot") ----
const STORE_VERSION = 1, FULL_REFRESH = 24 * 60 * 60 * 1000, SINCE_OVERLAP = 5 * 60 * 1000, HOUR = 60 * 60 * 1000;
const STORE_BYTES = 64 * 1024 * 1024, STORE_ISSUES = 10000, KINDS = ['comments', 'blockedBy', 'blocking', 'timeline'];
const short = text => hash(text).slice(0, 20);
// The change facts of one GitHub issue row. A row without a valid update time has none, so its reads are never reused.
export function issueRowVersion(row) {
  return typeof row?.updated_at === 'string' && Number.isFinite(Date.parse(row.updated_at))
    ? JSON.stringify([row.updated_at, row.comments ?? null, row.state ?? null, row.issue_dependencies_summary ?? null]) : null;
}
const login = user => object(user) ? { login: user.login } : user ?? null;
const trimRow = row => ({ id: row.id, number: row.number, html_url: row.html_url, title: row.title, body: row.body ?? null, state: row.state,
  state_reason: row.state_reason ?? null, user: login(row.user), labels: Array.isArray(row.labels) ? row.labels.map(l => typeof l === 'string' ? l : { name: l?.name }) : row.labels,
  assignees: Array.isArray(row.assignees) ? row.assignees.map(a => object(a) ? { login: a.login } : a) : row.assignees, assignee: login(row.assignee),
  created_at: row.created_at, updated_at: row.updated_at, comments: row.comments,
  ...(row.issue_dependencies_summary !== undefined ? { issue_dependencies_summary: row.issue_dependencies_summary } : {}) });
const linkedIssue = value => object(value) ? { html_url: value.html_url, number: value.number, ...(object(value.repository) ? { repository: { full_name: value.repository.full_name } } : {}) } : value;
const trimItems = {
  comments: items => items.map(c => ({ id: c.id, body: c.body, user: login(c.user), created_at: c.created_at, updated_at: c.updated_at, ...(c.html_url ? { html_url: c.html_url } : {}) })),
  blockedBy: items => items.map(x => ({ html_url: x.html_url })), blocking: items => items.map(x => ({ html_url: x.html_url })),
  timeline: items => items.map(e => ({ id: e.id, event: e.event, actor: login(e.actor), created_at: e.created_at, ...(e.label ? { label: { name: e.label.name } } : {}),
    ...(e.blocked_by ? { blocked_by: linkedIssue(e.blocked_by) } : {}), ...(e.blocking ? { blocking: linkedIssue(e.blocking) } : {}),
    ...(object(e.source) ? { source: { issue: object(e.source.issue) ? { ...(e.source.issue.pull_request ? { pull_request: {} } : {}), state: e.source.issue.state } : e.source.issue } } : {}) })),
};

// One private, versioned, bounded file for each repository: the issue rows of the last list read and the full reads of
// each issue, keyed by the change facts of its row. A save merges with the file as it is then: the newer list read
// wins with its watermark, each issue keeps its newer observation, and an issue that a process wrote stays invalid.
export function dependencySnapshotStore({ root, repository, fs = nativeFs }) {
  const repo = String(repository).toLowerCase(), file = join(root, 'github', `${short(repo)}.snapshot.json`);
  const valid = data => object(data) && data.v === STORE_VERSION && data.repository === repo && Number.isFinite(data.refreshedAt)
    && object(data.list) && object(data.list.rows) && typeof data.list.since === 'string' && Number.isFinite(data.list.readAt) && object(data.issues);
  const load = () => { try { const data = JSON.parse(fs.readFileSync(file, 'utf8')); return valid(data) ? data : null; } catch { return null; } };
  const completionFile = join(root, 'github', `${short(repo)}.completion.json`);
  const completion = {
    file: completionFile,
    read: () => { try { const value = JSON.parse(fs.readFileSync(completionFile, 'utf8')); return object(value) && value.v === STORE_VERSION ? value : null; } catch { return null; } },
    save: value => {
      const text = JSON.stringify({ v: STORE_VERSION, ...value });
      if (Buffer.byteLength(text) > STORE_BYTES) return false;
      fs.mkdirSync(dirname(completionFile), { recursive: true, mode: 0o700 });
      const temp = `${completionFile}.${randomUUID()}.tmp`;
      fs.writeFileSync(temp, text, { mode: 0o600 }); fs.renameSync(temp, completionFile);
      return true;
    },
    clear: () => { try { fs.unlinkSync(completionFile); } catch (error) { if (error.code !== 'ENOENT') throw error; } },
  };
  return {
    file, repository: repo, load, completion,
    save(data) {
      try {
        const current = load(), epoch = Math.max(data.refreshedAt, current?.refreshedAt ?? -Infinity);
        const sides = [current, data].filter(side => side && side.refreshedAt === epoch);
        // On a tie the list of this save wins: it was read after the saved one.
        const list = sides.length === 2 && current.list.readAt > data.list.readAt ? current.list : sides.at(-1).list;
        const invalid = Object.assign({}, ...sides.map(side => side.invalid ?? {}));
        const issues = {};
        for (const side of sides) for (const [n, entry] of Object.entries(side.issues)) {
          if (!object(entry) || !(entry.observedAt >= epoch) || invalid[n] > entry.observedAt) continue;
          if (!issues[n] || entry.observedAt >= issues[n].observedAt) issues[n] = entry;
        }
        const pending = sides.map(side => side.pendingList).filter(value => object(value) && object(value.rows) && value.at >= list.readAt)
          .sort((a, b) => b.at - a.at)[0];
        const next = { v: STORE_VERSION, repository: repo, refreshedAt: epoch, list, issues, invalid,
          ...(pending && (data.pendingList || pending.at > list.readAt) ? { pendingList: pending } : {}) };
        let text = JSON.stringify(next);
        // Bounded: the oldest issue reads go first; a list that is too large alone is not saved.
        const ordered = Object.entries(issues).sort((a, b) => a[1].observedAt - b[1].observedAt);
        while ((Buffer.byteLength(text) > STORE_BYTES || ordered.length > STORE_ISSUES) && ordered.length) {
          const drop = ordered.splice(0, Math.max(1, Math.ceil(ordered.length / 10)));
          for (const [n] of drop) delete issues[n];
          text = JSON.stringify(next);
        }
        if (Buffer.byteLength(text) > STORE_BYTES) return null;
        fs.mkdirSync(dirname(file), { recursive: true, mode: 0o700 });
        const temp = `${file}.${randomUUID()}.tmp`;
        fs.writeFileSync(temp, text, { mode: 0o600 });
        fs.renameSync(temp, file);
        return next;
      } catch { return null; /* A lost save only costs reads. */ }
    },
  };
}

// The pdd command default: the saved snapshot and the ETag cache of a repository where Autopilot runs on this machine,
// that is, where its call ledger exists in the state root.
const autopilotRoot = ports => ports.autopilotStateRoot ?? join(stateDirFor(ports), 'autopilot');
const autopilotRepository = (root, repository, fs = nativeFs) => { try { return fs.existsSync(githubLedger({ root, repository }).file); } catch { return false; } };
function defaultStores(ports) {
  if (ports.snapshotStore === null) return () => null;
  if (ports.snapshotStore) return repository => sameRepo(ports.snapshotStore.repository, repository) ? ports.snapshotStore : null;
  const root = autopilotRoot(ports);
  return repository => autopilotRepository(root, repository) ? dependencySnapshotStore({ root, repository }) : null;
}
function defaultEtagCache(ports) {
  const root = autopilotRoot(ports), caches = new Map();
  const cacheFor = endpoint => {
    const repo = /^repos\/([^/?#]+\/[^/?#]+)/.exec(String(endpoint))?.[1]?.toLowerCase();
    if (!repo || !repositoryName(repo)) return null;
    if (!caches.has(repo)) caches.set(repo, autopilotRepository(root, repo) ? githubEtagCache({ root, repository: repo }) : null);
    return caches.get(repo);
  };
  const cache = { get: endpoint => cacheFor(endpoint)?.get(endpoint), set: (endpoint, entry) => cacheFor(endpoint)?.set(endpoint, entry),
    save: () => { for (const each of caches.values()) each?.save(); } };
  Object.defineProperty(cache, DEFAULT_CACHE, { value: true });
  return cache;
}
const flushCache = ports => { try { if (ports.githubCache?.[DEFAULT_CACHE]) ports.githubCache.save(); } catch { /* best effort */ } };

// The floor guard of a pdd dependency command for an Autopilot repository: the floor of `autopilot.github` in the
// checkout's pdd.json (default 1,000) and the newest limit in the ledgers of this machine. Null for other repositories.
export async function commandGithubFloor({ cwd = '', repository }, ports = {}) {
  if (ports.githubFloor !== undefined || ports.github || !repositoryName(repository)) return ports.githubFloor ?? null;
  const root = autopilotRoot(ports);
  if (!autopilotRepository(root, repository)) return null;
  let setting;
  try { const top = cwd ? (await gitContext(cwd, ports.execFile ? { execFile: ports.execFile } : {}))?.toplevel : null; if (top) setting = readJson(join(top, 'pdd.json'), {})?.autopilot?.github; } catch { /* The default floor applies. */ }
  const now = typeof ports.now === 'function' ? ports.now : Date.now;
  return githubFloorGuard({ floor: githubBudgetSettings(setting).floor, entries: githubMachineEntries({ root }), now });
}

// The reads of one pdd process (one tick, one command): the issue list and the issue reads of this process, the saved
// snapshot, the comment bodies of the comment pages read, the claims of the last snapshot and the trust lookups.
function readSession(storeFor, now) {
  const repos = new Map();
  const state = repository => {
    const repo = String(repository).toLowerCase();
    if (!repos.has(repo)) {
      let store = null; try { store = storeFor(repo) ?? null; } catch { store = null; }
      repos.set(repo, { repo, store, data: undefined, list: null, entries: new Map(), blocked: new Set(), invalid: {}, rawVersion: new Map(), live: false, liveIssues: new Set() });
    }
    return repos.get(repo);
  };
  const saved = s => { if (s.data === undefined) s.data = s.store?.load() ?? null; return s.data; };
  const usable = (s, at) => { const d = saved(s); return d && at >= d.refreshedAt && at - d.refreshedAt < FULL_REFRESH ? d : null; };
  // The current read of one issue: this process's own read, else a saved read whose change facts match the current row.
  const fresh = (s, n) => {
    const row = s.list?.rows.get(n), version = row ? issueRowVersion(row) : undefined;
    const own = s.entries.get(n);
    if (own) return !row || version !== null && own.version === version ? own : null;
    if (s.blocked.has(n) || !s.list?.complete) return null;
    const d = saved(s), entry = d?.issues?.[n];
    if (!entry || d.refreshedAt !== s.list.refreshedAt || !(entry.observedAt >= d.refreshedAt) || d.invalid?.[n] > entry.observedAt) return null;
    if (row) return version !== null && entry.version === version ? entry : null;
    // An issue outside the open list is current while since reads cover its changes; it needs its saved issue.
    return s.list.mode !== 'refresh' && object(entry.raw) ? entry : null;
  };
  const entryFor = (s, n) => {
    const row = s.list?.rows.get(n), version = row ? issueRowVersion(row) : s.rawVersion.get(n) ?? null;
    let entry = s.entries.get(n);
    if (!entry || entry.version !== version) { entry = { version, observedAt: now(), kinds: {}, ...(entry?.raw && !row ? { raw: entry.raw } : {}) }; s.entries.set(n, entry); }
    return entry;
  };
  return {
    comments: new Map(), commentIssues: new Set(), lookups: new Map(), owners: null, savedList: false, safety: 0,
    stored: repository => !!state(repository).store,
    // The kept completion beside the saved snapshot of this repository, or null.
    completions: repository => state(repository).store?.completion ?? null,
    // This process reads the issue live: its saved reads and the saved list are not used.
    live(repository, n) { const s = state(repository); if (!Number.isSafeInteger(n)) return; s.entries.delete(n); s.blocked.add(n); s.live = true; s.liveIssues.add(n); },
    liveIssue: (repository, n) => state(repository).liveIssues.has(n),
    // True when the saved list was read within `within` milliseconds and its full refresh is still current.
    recentList(repository, within) { const s = state(repository), at = now(), d = usable(s, at); return !!d && !d.pendingList && at >= d.list.readAt && at - d.list.readAt < within; },
    // The open issues of the repository: a full read at the first read and once a day, else the changed issues since
    // the watermark applied to the saved rows. An incomplete list never advances complete coverage; partial rows can be staged.
    async readList(repository, api) {
      const s = state(repository), at = now(), d = usable(s, at), repo = s.repo;
      const rows = new Map(d ? Object.entries(d.list.rows).map(([n, row]) => [Number(n), row]) : []);
      if (d && d.pendingList?.at >= d.list.readAt && object(d.pendingList.rows)) {
        rows.clear(); for (const [n, row] of Object.entries(d.pendingList.rows)) rows.set(Number(n), row);
      }
      if (d && this.savedList && !s.live && !d.pendingList) {
        s.list = { rows, complete: true, readAt: d.list.readAt, since: d.list.since, refreshedAt: d.refreshedAt, mode: 'saved' };
        return [...rows.values()].sort((a, b) => b.number - a.number);
      }
      const mode = d ? 'since' : 'refresh', refreshedAt = d ? d.refreshedAt : at;
      if (!d) rows.clear();
      s.list = { rows, complete: false, readAt: at, since: d?.list.since, refreshedAt, mode };
      const items = [], cursors = new Set();
      let cursor = d ? `repos/${repo}/issues?state=all&sort=updated&direction=desc&since=${encodeURIComponent(d.list.since)}&per_page=100` : `repos/${repo}/issues?state=open&per_page=100`;
      try {
        while (cursor) {
          const path = cursor.split(/[?#]/, 1)[0];
          if (cursors.has(cursor) || path !== `repos/${repo}/issues` && !/^repositories\/[1-9][0-9]*\/issues$/.test(path)) throw Error('Foreign pagination cursor');
          cursors.add(cursor);
          const r = await api(cursor);
          if (!Array.isArray(r.value)) throw Error('GitHub returned no issue list');
          items.push(...r.value); cursor = r.next;
        }
      } catch (error) { apply(s, rows, items, d); error.partialItems = [...rows.values()].sort((a, b) => b.number - a.number); throw error; }
      let newest = apply(s, rows, items, d);
      try { if (d) {
        // Links need not move updated_at. Revalidate only the open index metadata, so change facts outside
        // `since` still invalidate the corresponding detail reads. Removals remain the daily refresh's job.
        cursor = `repos/${repo}/issues?state=open&per_page=100`;
        const seen = new Set();
        while (cursor) {
          if (seen.has(cursor)) throw Error('Repeated GitHub cursor');
          seen.add(cursor);
          const r = await api(cursor);
          if (!Array.isArray(r.value)) throw Error('GitHub returned no issue list');
          newest = Math.max(newest, apply(s, rows, r.value, d)); cursor = r.next;
        }
      } } catch (error) { error.partialItems = [...rows.values()].sort((a, b) => b.number - a.number); throw error; }
      const since = Number.isFinite(newest) ? new Date(Math.max(newest - SINCE_OVERLAP, d ? Date.parse(d.list.since) : -Infinity)).toISOString() : d?.list.since ?? new Date(at - HOUR).toISOString();
      s.list = { rows, complete: true, readAt: at, since, refreshedAt, mode };
      s.live = false;
      return [...rows.values()].sort((a, b) => b.number - a.number);
    },
    row: (repository, n) => state(repository).list?.rows.get(n) ?? null,
    // True when every kind of this issue has a current read.
    current(repository, n) { const s = state(repository); if (!s.store) return false; const entry = fresh(s, n); return !!entry && KINDS.every(kind => Array.isArray(entry.kinds?.[kind])); },
    noteComments(issueKey, items, complete) {
      for (const comment of items) if (/^[1-9][0-9]*$/.test(String(comment?.id ?? ''))) this.comments.set(`${issueKey}#issuecomment-${comment.id}`, comment);
      if (complete) this.commentIssues.add(issueKey); else this.commentIssues.delete(issueKey);
    },
    // A saved full read of one issue for this kind, or null. A history from the batch read has only its PR references,
    // so a claim check never takes it.
    served(repository, n, kind, purpose) {
      const s = state(repository); if (!s.store) return null;
      const entry = fresh(s, n), items = entry?.kinds?.[kind];
      if (!Array.isArray(items) || kind === 'timeline' && purpose === 'claims' && entry.partialTimeline) return null;
      return items;
    },
    savedIssue(repository, n) { const s = state(repository); if (!s.store || s.list?.rows.has(n)) return null; return fresh(s, n)?.raw ?? null; },
    record(repository, n, kind, items, partial = false) {
      const s = state(repository); if (!s.store || !Number.isSafeInteger(n) || !KINDS.includes(kind)) return items;
      const entry = entryFor(s, n), trimmed = trimItems[kind](items);
      entry.kinds[kind] = trimmed;
      if (kind === 'timeline') { if (partial) entry.partialTimeline = true; else delete entry.partialTimeline; }
      return trimmed;
    },
    recordIssue(repository, n, raw) {
      const s = state(repository); if (!s.store || s.list?.rows.has(n)) return;
      s.rawVersion.set(n, issueRowVersion(raw));
      entryFor(s, n).raw = trimRow(raw);
    },
    // A write to an issue: this process reads it live again, and no saved read of it before now is used again.
    invalidate(repository, n) {
      const s = state(repository); if (!Number.isSafeInteger(n)) return;
      this.commentIssues.delete(`https://github.com/${s.repo}/issues/${n}`);
      s.entries.delete(n); s.blocked.add(n); s.invalid[n] = now(); s.live = true;
      s.list?.rows.delete(n);
    },
    // Save complete list coverage and full issue reads, or stage partial rows against the last complete list.
    commit(repository) {
      const s = state(repository); if (!s.store || !s.list) return;
      const d = saved(s), issues = {};
      if (!s.list.complete && (!d || d.refreshedAt !== s.list.refreshedAt)) return;
      if (d && d.refreshedAt === s.list.refreshedAt) for (const [n, entry] of Object.entries(d.issues)) {
        const number = Number(n), row = s.list.rows.get(number);
        if (!s.blocked.has(number) && (row ? entry.version === issueRowVersion(row) : s.list.mode !== 'refresh' && object(entry.raw))) issues[n] = entry;
      }
      for (const [n, entry] of s.entries) if (KINDS.every(kind => Array.isArray(entry.kinds[kind])) && (s.list.rows.has(n) || object(entry.raw)) && entry.version !== null) issues[n] = entry;
      const data = { v: STORE_VERSION, repository: s.repo, refreshedAt: s.list.refreshedAt,
        list: s.list.complete ? { readAt: s.list.readAt, since: s.list.since, rows: Object.fromEntries(s.list.rows) } : d.list, issues,
        ...(!s.list.complete ? { pendingList: { at: s.list.readAt, rows: Object.fromEntries(s.list.rows) } } : {}),
        invalid: { ...(d && d.refreshedAt === s.list.refreshedAt ? d.invalid : {}), ...s.invalid } };
      const merged = s.store.save(data);
      if (merged) s.data = merged;
    },
  };
  // Rows of an issue list read applied to the open rows: an open issue replaces its row, any other leaves the list,
  // and a changed issue outside the list loses its saved read. Pull requests are not dependency subjects.
  function apply(s, rows, items, d) {
    let newest = -Infinity;
    for (const row of items) {
      const at = Date.parse(row?.updated_at); if (Number.isFinite(at)) newest = Math.max(newest, at);
      if (!object(row) || row.pull_request || !Number.isSafeInteger(row.number) || row.number < 1) continue;
      if (row.state === 'open') rows.set(row.number, trimRow(row));
      else {
        rows.delete(row.number);
        const entry = d?.issues?.[row.number];
        if (entry && entry.version !== issueRowVersion(row)) { s.blocked.add(row.number); s.invalid[row.number] = now(); }
      }
    }
    return newest;
  }
}

// The GitHub port of a process with a saved snapshot: an open root issue is its current list row, and a current saved
// or own read of an issue serves its pages. Every other read goes to GitHub; each read in full is recorded. Writes go
// to GitHub and make the issue live again in this process.
function sessionGithub(raw, session) {
  const numberOf = value => Number(value);
  const github = {
    page: async args => {
      const { repository, kind, issue, cursor, purpose } = args;
      if (cursor || kind === 'issues' || !session.stored(repository)) return raw.page(args);
      if (session.liveIssue(repository, numberOf(issue))) return raw.page({ ...args, safety: true });
      const hit = session.served(repository, numberOf(issue), kind, purpose);
      if (hit) return { json: JSON.stringify({ items: hit, next: '' }) };
      let items;
      try { items = await allPages(raw, repository, kind, issue, purpose, args.safety); }
      catch (error) { return { json: JSON.stringify({ error: 'GitHub read unavailable', status: error.status ?? 0, partialItems: error.partialItems ?? [] }) }; }
      return { json: JSON.stringify({ items: session.record(repository, numberOf(issue), kind, items), next: '' }) };
    },
    issue: async args => {
      if (session.liveIssue(args.repository, numberOf(args.issue))) return raw.issue({ ...args, safety: true });
      if (!session.stored(args.repository)) return raw.issue(args);
      const row = session.row(args.repository, numberOf(args.issue)) ?? session.savedIssue(args.repository, numberOf(args.issue));
      if (row) return { json: JSON.stringify(row) };
      const reply = await raw.issue(args);
      try { const value = parse(reply.json); if (!value.error && info(value.html_url)?.key === `https://github.com/${args.repository.toLowerCase()}/issues/${args.issue}`) session.recordIssue(args.repository, numberOf(args.issue), value); } catch { /* not recorded */ }
      return reply;
    },
    appendComment: async args => { session.invalidate(args.repository, numberOf(args.issue)); try { return await raw.appendComment(args); } finally { session.invalidate(args.repository, numberOf(args.issue)); } },
    addBlocker: async args => { session.invalidate(args.repository, numberOf(args.issue)); try { return await raw.addBlocker(args); } finally { session.invalidate(args.repository, numberOf(args.issue)); } },
  };
  Object.defineProperty(github, NATIVE_GITHUB, { value: true });
  Object.defineProperty(github, LIVE_GITHUB, { value: raw });
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
      // Trust is a safety read: the floor never stops it. One process reads it once for each repository.
      const lookups = ports.dependencyReads?.lookups, lookupKey = repository.toLowerCase();
      const read = async () => {
        try {
          const repo = (await s.api(`repos/${repository}`, 'GET', undefined, undefined, undefined, true)).value;
          const pages = []; let endpoint = `repos/${repository}/collaborators?per_page=100`;
          while (endpoint) { const r = await s.api(endpoint, 'GET', undefined, undefined, undefined, true); pages.push(...r.value); endpoint = r.next; }
          return { owner: repo.owner?.login ?? '', writers: pages.filter(p => p.permissions?.push || p.permissions?.maintain || p.permissions?.admin).map(p => p.login), complete: !!repo.owner?.login };
        } catch { return { owner: repository.split('/')[0], writers: [], complete: false }; }
      };
      if (lookups && !lookups.has(lookupKey)) lookups.set(lookupKey, read().then(value => { if (!value.complete) lookups.delete(lookupKey); return value; }));
      const lookup = await (lookups ? lookups.get(lookupKey) : read());
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
    // The body comes from the comment pages that this process read in full. A comment that is not on its issue's
    // complete pages is gone. Only a comment of an issue that this process did not read is one more read.
    const reads = ports.dependencyReads;
    let comment = reads?.comments.get(key);
    if (!comment && reads?.commentIssues.has(i.key)) throw Error('Unavailable requirement comment');
    if (!comment) {
      comment = (await s.api(`repos/${i.repository}/issues/comments/${i.comment}`)).value;
      if (canonical(comment.html_url) !== key) throw Error('Unavailable requirement comment');
    }
    if (bookkeeping(comment.body)) throw Error('Unavailable requirement comment');
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
  const evidence = { read: async args => { try { return await readEvidence(args); } finally { flushCache(ports); } } };
  const readEvidence = async ({ cwd: at = cwd, repository, issues }) => {
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
  };
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
// A "lastSeen" member with a JSON scalar value, anywhere in the record text.
const LAST_SEEN = /(,\s*)?"lastSeen"\s*:\s*(?:"(?:[^"\\]|\\.)*"|-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?|true|false|null)(\s*,)?/g;
const time = value => typeof value === 'string' ? Date.parse(value) : NaN;
const iso = at => new Date(at).toISOString();

// Set or remove only the top-level lastSeen member and keep every other byte. Each
// place where the member can be is tried; an edit counts only when the new body
// parses to exactly the expected record, so a nested lastSeen is never changed.
// Return null when no such edit exists.
function editClaimRecord(body, record, expected) {
  const accept = text => { const next = String(body).replace(record.text, () => text); return isDeepStrictEqual(claimRecord(next)?.value, expected) ? next : null; };
  const set = Object.hasOwn(expected, 'lastSeen'), value = JSON.stringify(expected.lastSeen);
  if (set && !Object.hasOwn(record.value, 'lastSeen')) return accept(record.text.replace(/\}\s*$/, `,"lastSeen":${value}}`));
  for (const match of record.text.matchAll(LAST_SEEN)) {
    const [whole, before = '', after = ''] = match, member = set ? `${before}"lastSeen":${value}${after}` : before && after ? ',' : '';
    const next = accept(record.text.slice(0, match.index) + member + record.text.slice(match.index + whole.length));
    if (next !== null) return next;
  }
  return null;
}

// The claim comment body without its top-level lastSeen member. A heartbeat alone
// must not look like new trusted work to the tick.
export function withoutClaimHeartbeat(body) {
  const record = claimRecord(body);
  if (!record || !Object.hasOwn(record.value, 'lastSeen')) return body;
  const { lastSeen, ...rest } = record.value;
  return editClaimRecord(body, record, rest) ?? body;
}

async function winningClaim(repository, key, github, authority, now = NaN, safety = false) {
  // Claim checks are their own purpose in the GitHub call ledger; a live claim check is a safety read.
  const i = info(key), raw = parse((await github.issue({ repository, issue: i.issue, purpose: 'claims', ...(safety ? { safety } : {}) })).json);
  if (raw.error) throw Error('Current claim issue unavailable');
  const labels = raw.labels?.map(l => typeof l === 'string' ? l : l.name) ?? [];
  if (!labels.includes('pdd:working')) return null;
  const timeline = await allPages(github, repository, 'timeline', i.issue, 'claims', safety), comments = await allPages(github, repository, 'comments', i.issue, 'claims', safety);
  let candidates = [], stuck = null;
  // Events arrive in service order. Only a native removal ends the active claim era.
  for (const event of timeline) {
    if (event.label?.name === 'pdd:working') {
      if (event.event === 'unlabeled') candidates = [];
      if (event.event === 'labeled') candidates.push(event);
    }
    if (event.label?.name === 'pdd:stuck') stuck = event.event === 'labeled' ? event : event.event === 'unlabeled' ? null : stuck;
  }
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
      ...(Number.isFinite(stuckSince) ? { stuckSince: iso(stuckSince) } : {}) };
  };
  const winner = candidates[0];
  if (!winner?.id || !winner.actor?.login) return facts({ issue: key, owner: '', coordinatorId: '', machine: '', commentId: '', labelEventId: '' });
  const matching = [];
  for (const comment of comments) {
    const metadata = claimMetadata(comment.body);
    if (metadata && sameRepo(metadata.repository, repository) && metadata.labelEventId === String(winner.id)
      && comment.user?.login?.toLowerCase() === winner.actor.login.toLowerCase()
      && (await authority.read({ repository, author: comment.user.login })).authority === 'trusted') matching.push({ comment, metadata });
  }
  if (matching.length !== 1) return facts({ issue: key, owner: '', coordinatorId: '', machine: '', commentId: '', labelEventId: String(winner.id) });
  const { comment, metadata } = matching[0];
  // A top-level lastSeen member, with any value ("" in a new record), makes the comment a
  // heartbeat claim; a record without it (older pdd) keeps the legacy rule. The last-seen
  // time is only the comment's GitHub server time: updated_at, else created_at, at most
  // now. A recorded lastSeen never extends the claim, so no writer clock or written
  // value keeps a dead claim live. With no server time, the legacy rule applies.
  const server = !Object.hasOwn(metadata, 'lastSeen') ? NaN
    : Number.isFinite(time(comment.updated_at)) ? time(comment.updated_at) : time(comment.created_at);
  const lastSeen = Number.isFinite(server) && Number.isFinite(now) ? Math.min(server, now) : server;
  return facts({ issue: key, owner: metadata.coordinatorId, coordinatorId: metadata.coordinatorId, machine: metadata.machine,
    commentId: String(comment.id), labelEventId: String(winner.id) }, lastSeen);
}

// Heartbeat: the owning coordinator writes the current time as the top-level lastSeen
// of its own winning claim comment. It edits nothing else and no other comment.
export async function refreshClaimHeartbeat({ cwd = '', repository, claim, coordinatorId, machine, at }, ports = {}) {
  const i = info(claim?.issue), s = service(cwd, ports);
  if (!repositoryName(repository) || !i || !sameRepo(i.repository, repository) || !/^[1-9][0-9]*$/.test(String(claim.commentId ?? ''))
    || !claim.labelEventId || claim.active !== true || claim.coordinatorId !== coordinatorId || claim.machine !== machine || !Number.isFinite(time(at))) return { state: 'skipped' };
  const endpoint = `repos/${repository}/issues/comments/${claim.commentId}`, comment = (await s.api(endpoint)).value;
  const record = claimRecord(comment?.body);
  if (String(comment?.id) !== String(claim.commentId) || !record || !sameRepo(record.value.repository, repository) || record.value.coordinatorId !== coordinatorId
    || record.value.machine !== machine || record.value.labelEventId !== String(claim.labelEventId)) return { state: 'skipped' };
  const lastSeen = iso(time(at)), body = editClaimRecord(comment.body, record, { ...record.value, lastSeen });
  if (body === null) throw Error('Claim record cannot take a heartbeat without other changes');
  const saved = (await s.api(endpoint, 'PATCH', JSON.stringify({ body }))).value;
  if (String(saved?.id) !== String(claim.commentId) || claimRecord(saved.body)?.value.lastSeen !== lastSeen) throw Error('Claim heartbeat readback is unresolved');
  return { state: 'refreshed', lastSeen };
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
      state: chat?.startUnconfirmed || (state === 'starting' && !finishedTurn) ? 'starting' : ['running', 'waiting', 'paused', 'stuck', 'question'].includes(run.state) ? run.state : 'unknown', ...(finishedTurn ? { occupied: false } : {}) });
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

// The default owners port is live: each claim check asks GitHub (a 304 is a live answer). Only the claim scan inside one
// snapshot (live false) reads through that snapshot's reads.
function nativeOwners(cwd, ports, { live = true } = {}) {
  const owner = { read: async ({ repository, issues }) => {
    try {
      const github = live ? ports.github[LIVE_GITHUB] ?? ports.github : ports.github;
      const state = await launcherState(cwd, repository, ports), claims = [];
      let now = NaN; try { now = time((await ports.clock.now({})).iso); } catch { /* An unknown clock expires no claim. */ }
      for (const key of issues) { const claim = await winningClaim(repository, key, github, ports.authority, now, live && !!ports.github[LIVE_GITHUB]); if (claim) claims.push(claim); }
      return { json: JSON.stringify({ localOwner: state?.coordinatorId ?? '', claims, ...await readLocalOccupied({ cwd, repository }, ports) }) };
    } finally { if (live) flushCache(ports); }
  } };
  Object.defineProperty(owner, NATIVE_OWNERS, { value: true });
  return owner;
}

export function createDependencyReadPorts({ cwd = '' } = {}, supplied = {}, scope = nativeReadScope()) {
  const ports = { ...supplied };
  Object.defineProperty(ports, NATIVE_READ_SCOPE, { value: scope });
  if (!supplied.github) {
    // The native reader of one process: its reads, the saved snapshot of an Autopilot repository, and the ETag cache.
    ports.dependencyReads ??= readSession(defaultStores(ports), typeof supplied.now === 'function' ? supplied.now : Date.now);
    if (ports.githubCache === undefined) ports.githubCache = defaultEtagCache(ports);
  }
  ports.github ??= ports.dependencyReads ? sessionGithub(rawGithub(cwd, ports), ports.dependencyReads) : rawGithub(cwd, ports);
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

export async function readDependencySnapshot(input = {}, supplied = {}) {
  const scope = nativeReadScope(), ports = createDependencyReadPorts({ cwd: input?.cwd ?? '' }, supplied, scope);
  try { return await observeSnapshot(input ?? {}, ports, scope); } finally { flushCache(ports); }
}

async function observeSnapshot({ cwd = '', repository, inputs = [] }, ports, scope) {
  const reads = ports.dependencyReads;
  // The claim scan of one snapshot reads through the snapshot's own reads; the default owners port stays live.
  if (ports.owners[NATIVE_OWNERS]) ports.owners = nativeOwners(cwd, ports, { live: false });
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
  // The native context reads the supplied inputs once, with the saved review rows at the end, from the comment
  // pages of this snapshot; a supplied context port keeps its first read with the inputs.
  try { context = parse((await readContext({ cwd, repository, ...(inputs.length && !ports.context[NATIVE_CONTEXT] ? { inputs } : {}) })).json); }
  catch { contextKnown = false; warn('Required context is unavailable'); }
  let roots = [];
  const stored = !!reads?.stored(repository) && !!ports.github[NATIVE_GITHUB];
  try {
    roots = stored ? await reads.readList(repository, endpoint => service(cwd, ports).api(endpoint, 'GET', undefined, 'dependencies'))
      : await allPages(ports.github, repository, 'issues', 0);
  } catch (e) { roots = e.partialItems ?? []; coverage.scope = false; warn('Open issue pages are incomplete'); }
  let invalidIndex = false;
  for (const raw of roots.filter(r => !r.pull_request)) {
    const key = info(raw.html_url)?.key;
    if (!key || info(key).repository !== repository || !/^[1-9][0-9]*$/.test(String(raw.id)) || typeof raw.title !== 'string' || !(raw.body === null || typeof raw.body === 'string') || rootIndex.has(key)) { coverage.scope = false; invalidIndex = true; continue; }
    rootIndex.set(key, raw);
  }
  if (invalidIndex) warn('Open issue index is incomplete');
  const queue = [...rootIndex.keys()];
  // Supplied GitHub ports retain the exact existing contract and call behavior.
  // With a saved snapshot, the batch reads only the roots whose saved reads are not current.
  const batched = stored ? roots.filter(row => !reads.liveIssue(repository, row.number) && !reads.current(repository, row.number)) : roots;
  if (ports.github[NATIVE_GITHUB] && batched.length) {
    const bulk = await bulkRoots(cwd, repository, batched, ports), github = ports.github;
    ports.github = { ...github,
      issue: async args => { const hit = bulk.get(`https://github.com/${args.repository.toLowerCase()}/issues/${args.issue}`); return hit ? {json:JSON.stringify(hit.raw)} : github.issue(args); },
      page: async args => {
        const hit = bulk.get(`https://github.com/${args.repository.toLowerCase()}/issues/${args.issue}`);
        if (!hit || args.cursor || !hit.pages[args.kind]) return github.page(args);
        // The batch history has only its PR references: a claim check never takes it from the saved snapshot.
        const items = stored ? reads.record(args.repository, Number(args.issue), args.kind, hit.pages[args.kind], args.kind === 'timeline') : hit.pages[args.kind];
        return {json:JSON.stringify({items,next:''})};
      },
    };
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
      let read = true;
      try { items = await allPages(ports.github, i.repository, kind, i.issue); } catch (e) { read = false; items = e.partialItems ?? []; missing(kind, `Incomplete ${kind}: ${key}`); }
      // The comment bodies of these pages serve the review rows that name them: no read for each comment.
      if (kind === 'comments') reads?.noteComments(key, items, read);
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
    if (reads && ports.owners[NATIVE_OWNERS]) reads.owners = { repository, issues: local.map(i => i.key), json: null };
    try {
      const observation = parse((await ports.owners.read({ repository, issues: local.map(i => i.key) })).json);
      if (!Array.isArray(observation.claims) || !Array.isArray(observation.runs) || typeof observation.runsKnown !== 'boolean') throw Error('Incomplete execution observation');
      // The claims of this scan serve the tick and prepare: they need not read the same claims again.
      if (reads && ports.owners[NATIVE_OWNERS]) reads.owners = { repository, issues: local.map(i => i.key), json: JSON.stringify(observation) };
      for (const issue of local) {
        const claims = observation.claims.filter(c => canonical(c.issue) === issue.key && c.active);
        const expired = !claims.length && observation.claims.find(c => canonical(c.issue) === issue.key && c.active === false && c.expired === true && c.lastSeen);
        if (expired) issue.holds = [...issue.holds.filter(hold => hold !== 'Claimed'), `Expired claim, last seen ${expired.lastSeen}`];
        const runs = observation.runs.filter(r => canonical(r.issue) === issue.key);
        if (observation.runsKnown) issue.runIds = runs.map(r => r.runId).filter(Boolean);
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
  if (stored) reads.commit(repository);
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
  finally { flushCache(ports); }
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
    // The history that a write depends on is a live safety read, never a saved one.
    let history; const live = ports.github[LIVE_GITHUB];
    try { history = await allPages(live ?? ports.github, repository, 'timeline', target.issue, undefined, !!live); } catch { return null; }
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
    // The readback after a write is a safety read: the floor does not stop it.
    if (ports.dependencyReads) ports.dependencyReads.safety++;
    try { snapshot = await read(inputs); } catch { return pending('Dependency effect readback is unknown'); }
    finally { if (ports.dependencyReads) ports.dependencyReads.safety--; }
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
