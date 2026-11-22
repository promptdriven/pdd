// Generated from prompts/cli/autopilot-claims.prompt.md
import { execFile as execCallback } from 'node:child_process';
import * as nativeFs from 'node:fs';
import { join } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { githubFullLastPage, githubReply, nativeGithubCounter } from '../github-calls.mjs';

export const CLAIM_EXPIRES_AFTER = 4 * 60 * 60 * 1000;
const LEGACY_CLAIM_EXPIRES_AFTER = 24 * 60 * 60 * 1000;
const TAKEOVER_LIMIT = 3;
const TAKEOVER_GAP = 10 * 60 * 1000;
const LAST_SEEN = /(,\s*)?"lastSeen"\s*:\s*(?:"(?:[^"\\]|\\.)*"|-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?|true|false|null)(\s*,)?/g;
const TICK_MEMBERS = ['lastSeen', 'longRunningAlertedAt'];
const NATIVE_GITHUB = Symbol('native claims github');

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const repositoryName = x => typeof x === 'string' && /^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*$/.test(x);
const sameRepo = (a, b) => typeof a === 'string' && typeof b === 'string' && a.toLowerCase() === b.toLowerCase();
const time = value => typeof value === 'string' ? Date.parse(value) : NaN;
const iso = at => new Date(at).toISOString();
const notModified = text => /^HTTP\/\S+\s+304\b/.test(String(text ?? ''));
export const heartbeatTimeForComment = comment => Number.isFinite(time(comment?.updated_at)) ? time(comment.updated_at) : time(comment?.created_at);
const memberPattern = member => member === 'lastSeen' ? LAST_SEEN : new RegExp(LAST_SEEN.source.replace('"lastSeen"', `"${member}"`), 'g');

const parse = json => JSON.parse(json, (key, value, context) => (key === 'id' || key === 'fullDatabaseId') && typeof value === 'number'
  ? context?.source ?? (Number.isSafeInteger(value) ? String(value) : '') : value);

function info(key) {
  const m = /^https:\/\/github\.com\/([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)\/issues\/([1-9][0-9]*)(?:#issuecomment-([1-9][0-9]*))?$/.exec(key ?? '');
  return m && Number.isSafeInteger(Number(m[2]))
    ? { repository: m[1].toLowerCase(), issue: Number(m[2]), key: `https://github.com/${m[1].toLowerCase()}/issues/${m[2]}`, comment: m[3] }
    : null;
}
const canonical = key => { const i = info(key); return i ? i.key + (i.comment ? `#issuecomment-${i.comment}` : '') : key; };

function spawnRead(file, args, options = {}) {
  return new Promise((resolveResult, reject) => {
    const { input, ...rest } = options;
    const child = execCallback(file, args, { ...rest, encoding: 'utf8', shell: false, maxBuffer: 32 * 1024 * 1024 }, (error, stdout, stderr) => {
      if (error) reject(Object.assign(error, { stdout, stderr })); else resolveResult({ stdout, stderr, code: 0 });
    });
    if (input !== undefined) { child.stdin.on('error', () => {}); child.stdin.end(input); }
  });
}
const execute = nativeGithubCounter(spawnRead, { purpose: 'claims' });

function service(cwd, ports) {
  const exec = ports.execFile ?? execute;
  async function run(file, args, input, purpose, conditional = false, repository, guard = ports.githubFloor) {
    let r;
    try {
      r = await exec(file, args, {
        ...(cwd ? { cwd } : {}),
        ...(input === undefined ? {} : { input }),
        ...(purpose ? { purpose } : {}),
        ...(repository ? { repository } : {}),
      });
    } catch (error) {
      guard?.observe(githubReply(error?.stdout));
      if (conditional && notModified(error?.stdout)) return String(error.stdout);
      throw error;
    }
    guard?.observe(githubReply(r.stdout));
    if (r.code !== undefined && r.code !== 0 && !(conditional && notModified(r.stdout))) {
      throw Object.assign(Error('Service read failed'), { status: r.code });
    }
    return String(r.stdout ?? '');
  }

  async function api(endpoint, method = 'GET', input, purpose = 'claims', repository, safety = false) {
    const guard = ports.githubFloor;
    const write = method !== 'GET' && endpoint !== 'graphql';
    if (guard && !write && !safety && (guard.blocked('core') || endpoint === 'graphql' && guard.blocked('graphql'))) {
      throw Object.assign(Error('GitHub limit is below the floor'), { status: 0, floor: true });
    }
    const cache = method === 'GET' ? ports.githubCache : null;
    let saved = cache?.get(endpoint);
    if (saved) {
      try {
        saved = { ...saved, value: parse(saved.body) };
        if (githubFullLastPage(endpoint, saved.value, saved.next)) saved = undefined;
      } catch { saved = undefined; }
    }
    const raw = await run('gh', [
      'api', '--include', '--method', method, endpoint,
      '-H', 'Accept: application/vnd.github+json',
      ...(saved ? ['-H', `If-None-Match: ${saved.etag}`] : []),
      ...(input === undefined ? [] : ['--input', '-']),
    ], input, purpose, !!saved, repository, guard);
    const boundary = raw.search(/\r?\n\r?\n/);
    const header = boundary >= 0 ? raw.slice(0, boundary) : '';
    const body = boundary >= 0 ? raw.slice(boundary).trim() : raw;
    const status = Number(header.match(/^HTTP\/\S+\s+(\d+)/m)?.[1] ?? 200);
    if (status === 304 && saved) return { value: saved.value, next: saved.next ?? '' };
    if (status < 200 || status >= 300) throw Object.assign(Error('GitHub observation unavailable'), { status });
    const link = header.match(/^link:\s*(.*)$/im)?.[1] ?? '';
    const nextRelation = link.match(/<([^>]+)>\s*;\s*rel=(?:"next"|next)\s*(?:,|$)/i)?.[1];
    const next = nextRelation?.match(/^https:\/\/api\.github\.com\/([^#]+)$/i)?.[1] ?? '';
    if (nextRelation && !next) throw Error('Unsupported GitHub pagination link');
    const etag = header.match(/^etag:[ \t]*(.*?)[ \t]*\r?$/im)?.[1];
    const value = status === 204 ? null : parse(body);
    if (cache && status === 200 && etag) cache.set(endpoint, { etag, body, next });
    return { value, next };
  }
  return { api };
}

async function allPages(github, repository, kind, issue, purpose, safety = false) {
  const items = [], cursors = new Set();
  let cursor = '';
  do {
    if (cursors.has(cursor)) throw Error('Repeated GitHub cursor');
    cursors.add(cursor);
    const value = parse((await github.page({ repository, kind, issue, cursor, ...(purpose ? { purpose } : {}), ...(safety ? { safety } : {}) })).json);
    if (value.error || !Array.isArray(value.items) || typeof value.next !== 'string') throw Error(`Incomplete ${kind} observation`);
    items.push(...value.items);
    cursor = value.next;
  } while (cursor);
  return items;
}

function rawGithub(cwd, ports) {
  const s = service(cwd, ports);
  const github = {
    page: async ({ repository, kind, issue, cursor, purpose, safety }) => {
      const suffix = { comments: `/${issue}/comments?per_page=100`, timeline: `/${issue}/timeline?per_page=100` }[kind];
      if (!repositoryName(repository) || suffix === undefined) return { json: JSON.stringify({ error: 'Invalid GitHub scope', status: 400 }) };
      try {
        const route = { comments: `issues/${issue}/comments`, timeline: `issues/${issue}/timeline` }[kind];
        const path = String(cursor ?? '').split(/[?#]/, 1)[0];
        const canonicalPath = /^repositories\/[1-9][0-9]*\/(.+)$/.exec(path);
        if (cursor && path !== `repos/${repository}/${route}` && canonicalPath?.[1] !== route) throw Error('Foreign pagination cursor');
        const r = await s.api(cursor || `repos/${repository}/issues${suffix}`, 'GET', undefined, purpose ?? 'claims', repository, safety === true);
        return { json: JSON.stringify({ items: r.value, next: r.next }) };
      } catch (e) { return { json: JSON.stringify({ error: 'GitHub read unavailable', status: e.status ?? 0 }) }; }
    },
    issue: async ({ repository, issue, purpose, safety }) => {
      try {
        return { json: JSON.stringify((await s.api(`repos/${repository}/issues/${issue}`, 'GET', undefined, purpose ?? 'claims', repository, safety === true)).value) };
      } catch (e) { return { json: JSON.stringify({ error: 'GitHub issue unavailable', status: e.status ?? 0 }) }; }
    },
  };
  Object.defineProperty(github, NATIVE_GITHUB, { value: true });
  return github;
}

export function claimRecord(body) {
  const source = String(body ?? '');
  const blocks = [...source.matchAll(/```(?:json)?\s*\n([\s\S]*?)\n```/g)].map(m => m[1]);
  blocks.push(source.trim());
  for (const text of blocks) {
    try {
      const value = JSON.parse(text);
      if (object(value) && ['repository', 'coordinatorId', 'machine', 'labelEventId'].every(k => typeof value[k] === 'string' && value[k])) {
        return { value, text };
      }
    } catch { /* Legacy prose claims have unknown coordinator identity. */ }
  }
  return null;
}

export function editClaimRecord(body, record, expected, name = 'lastSeen') {
  const accept = text => {
    const next = String(body).replace(record.text, () => text);
    return isDeepStrictEqual(claimRecord(next)?.value, expected) ? next : null;
  };
  const set = Object.hasOwn(expected, name), value = JSON.stringify(expected[name]);
  if (set && !Object.hasOwn(record.value, name)) return accept(record.text.replace(/\}\s*$/, `,"${name}":${value}}`));
  for (const match of record.text.matchAll(memberPattern(name))) {
    const [whole, before = '', after = ''] = match;
    const member = set ? `${before}"${name}":${value}${after}` : before && after ? ',' : '';
    const next = accept(record.text.slice(0, match.index) + member + record.text.slice(match.index + whole.length));
    if (next !== null) return next;
  }
  return null;
}

export const takeoverLimited = (claim, self) => {
  const retake = claim?.expired === true && Boolean(self?.coordinatorId)
    && claim.coordinatorId === self.coordinatorId && claim.machine === self.machine;
  return (Number.isSafeInteger(claim?.takeovers) ? claim.takeovers : 0) + (claim?.expired === true && !retake ? 1 : 0) > TAKEOVER_LIMIT;
};

export function withoutClaimHeartbeat(body) {
  let text = body;
  for (const name of TICK_MEMBERS) {
    const record = claimRecord(text);
    if (!record || !Object.hasOwn(record.value, name)) continue;
    const { [name]: _removed, ...rest } = record.value;
    text = editClaimRecord(text, record, rest, name) ?? text;
  }
  return text;
}

export async function winningClaim(repository, key, github, authority, now = NaN, safety = false, observedIssue = null) {
  const i = info(key);
  const raw = observedIssue ?? parse((await github.issue({ repository, issue: i.issue, purpose: 'claims', ...(safety ? { safety } : {}) })).json);
  if (raw.error) throw Error('Current claim issue unavailable');
  const labels = raw.labels?.map(l => typeof l === 'string' ? l : l.name) ?? [];
  if (!labels.includes('pdd:working')) return null;
  const timeline = await allPages(github, repository, 'timeline', i.issue, 'claims', safety);
  const comments = await allPages(github, repository, 'comments', i.issue, 'claims', safety);
  let candidates = [], stuck = null;
  const eras = [], stuckRemovals = [];
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
  const recordOf = async winner => {
    if (!winner?.id || !winner.actor?.login) return null;
    const matching = [];
    for (const comment of comments) {
      const metadata = claimRecord(comment.body)?.value ?? null;
      if (metadata && sameRepo(metadata.repository, repository) && metadata.labelEventId === String(winner.id)
        && comment.user?.login?.toLowerCase() === winner.actor.login.toLowerCase()
        && (await authority.read({ repository, author: comment.user.login })).authority === 'trusted') {
        matching.push({ comment, metadata });
      }
    }
    return matching.length === 1 ? matching[0] : null;
  };
  const heartbeatTime = ({ comment, metadata }) => (!Object.hasOwn(metadata, 'lastSeen') ? NaN : heartbeatTimeForComment(comment));
  for (const era of eras) era.record = await recordOf(era.winner);
  const expiredAt = (era, at, index) => {
    let server = era.record ? heartbeatTime(era.record) : NaN;
    let expiresAfter = Number.isFinite(server) ? CLAIM_EXPIRES_AFTER : LEGACY_CLAIM_EXPIRES_AFTER;
    const proof = era.record?.metadata.coordinatorRecovery;
    const beforeRecovery = time(proof?.lastSeenBeforeRecovery);
    if (server >= at && Number.isFinite(beforeRecovery)) {
      server = beforeRecovery;
      expiresAfter = proof.heartbeatBeforeRecovery === false ? LEGACY_CLAIM_EXPIRES_AFTER : CLAIM_EXPIRES_AFTER;
    }
    const seen = Number.isFinite(server)
      ? Math.min(server, at)
      : [...comments.flatMap(c => [time(c.created_at), time(c.updated_at)]), ...timeline.slice(0, index).map(e => time(e.created_at))]
        .filter(value => Number.isFinite(value) && value < at).reduce((latest, value) => Math.max(latest, value), -Infinity);
    return Number.isFinite(at) && Number.isFinite(seen) && at - seen >= expiresAfter;
  };
  const owner = era => (era?.record ? `${era.record.metadata.coordinatorId}\n${era.record.metadata.machine}` : null);
  const initialOwner = era => (era?.record ? `${era.record.metadata.coordinatorRecovery?.originalCoordinatorId ?? era.record.metadata.coordinatorId}\n${era.record.metadata.machine}` : null);
  const login = event => String(event?.actor?.login ?? '').toLowerCase();
  let takeovers = 0, chainStart = 0;
  const points = [...eras.flatMap((era, k) => (era.end ? [{ index: era.end.index, k }] : [])), ...stuckRemovals].sort((a, b) => a.index - b.index);
  for (const point of points) {
    if (point.k === undefined) {
      const held = eras.find(era => era.start < point.index && (!era.end || era.end.index > point.index));
      if (takeovers + (held && expiredAt(held, point.at, point.index) ? 1 : 0) > TAKEOVER_LIMIT) takeovers = 0;
      continue;
    }
    const era = eras[point.k], next = eras[point.k + 1], at = time(era.end.event.created_at);
    const again = next && login(next.winner) && login(next.winner) === login(era.end.event) && time(next.winner.created_at) - at <= TAKEOVER_GAP;
    if (again && expiredAt(era, at, era.end.index)) { if (!owner(era) || owner(era) !== initialOwner(next)) takeovers++; }
    else { takeovers = 0; chainStart = point.k + 1; }
  }
  const chain = eras.slice(chainStart), current = candidates.length ? eras.at(-1) : null;
  const claimedAt = current ? time(chain[0].winner.created_at) : NaN;
  const previous = current && chain.slice(0, -1).reverse().find(era => owner(era) && owner(era) !== owner(current));
  const alerted = current ? chain.map(era => time(era.record?.metadata.longRunningAlertedAt)).filter(Number.isFinite).sort((a, b) => a - b)[0] : NaN;
  const facts = (claim, lastSeen) => {
    const heartbeat = Number.isFinite(lastSeen);
    const seen = heartbeat ? lastSeen : [time(raw.updated_at), ...comments.flatMap(c => [time(c.created_at), time(c.updated_at)]),
      ...timeline.map(e => time(e.created_at))].filter(Number.isFinite).reduce((latest, at) => Math.max(latest, at), -Infinity);
    const expired = Number.isFinite(now) && Number.isFinite(seen) && now - seen >= (heartbeat ? CLAIM_EXPIRES_AFTER : LEGACY_CLAIM_EXPIRES_AFTER);
    const stuckSince = labels.includes('pdd:stuck') ? time(stuck?.created_at) : NaN;
    return {
      ...claim,
      active: !expired,
      ...(Number.isFinite(seen) ? { lastSeen: iso(seen) } : {}),
      ...(expired ? { expired: true } : {}),
      ...(Number.isFinite(stuckSince) ? { stuckSince: iso(stuckSince) } : {}),
      ...(Number.isFinite(claimedAt) ? { claimedAt: iso(claimedAt) } : {}),
      ...(takeovers ? { takeovers } : {}),
      ...(takeovers && previous ? { previousOwner: { coordinatorId: previous.record.metadata.coordinatorId, machine: previous.record.metadata.machine } } : {}),
      ...(Number.isFinite(alerted) ? { longRunningAlertedAt: iso(alerted) } : {}),
    };
  };
  const winner = candidates[0];
  if (!winner?.id || !winner.actor?.login) return facts({ issue: key, owner: '', coordinatorId: '', machine: '', commentId: '', labelEventId: '' });
  const match = current?.record;
  if (!match) return facts({ issue: key, owner: '', coordinatorId: '', machine: '', commentId: '', labelEventId: String(winner.id) });
  const { comment, metadata } = match;
  const server = heartbeatTime(match);
  const lastSeen = Number.isFinite(server) && Number.isFinite(now) ? Math.min(server, now) : server;
  return facts({
    issue: key,
    owner: metadata.coordinatorId,
    coordinatorId: metadata.coordinatorId,
    machine: metadata.machine,
    commentId: String(comment.id),
    labelEventId: String(winner.id),
  }, lastSeen);
}

export async function setOwnClaimTime(name, { cwd = '', repository, claim, coordinatorId, machine, at }, ports = {}) {
  const i = info(claim?.issue), s = service(cwd, ports);
  if (!repositoryName(repository) || !i || !sameRepo(i.repository, repository) || !/^[1-9][0-9]*$/.test(String(claim.commentId ?? ''))
    || !claim.labelEventId || claim.active !== true || claim.coordinatorId !== coordinatorId || claim.machine !== machine || !Number.isFinite(time(at))) {
    return null;
  }
  const endpoint = `repos/${repository}/issues/comments/${claim.commentId}`;
  const comment = (await s.api(endpoint, 'GET', undefined, 'claims', repository, true)).value;
  const record = claimRecord(comment?.body);
  if (String(comment?.id) !== String(claim.commentId) || !record || !sameRepo(record.value.repository, repository)
    || record.value.coordinatorId !== coordinatorId || record.value.machine !== machine || record.value.labelEventId !== String(claim.labelEventId)) {
    return null;
  }
  const value = iso(time(at));
  const body = editClaimRecord(comment.body, record, { ...record.value, [name]: value }, name);
  if (body === null) throw Error(`Claim record cannot take ${name === 'lastSeen' ? 'a heartbeat' : name} without other changes`);
  const saved = (await s.api(endpoint, 'PATCH', JSON.stringify({ body }), 'claims', repository)).value;
  if (String(saved?.id) !== String(claim.commentId) || claimRecord(saved.body)?.value[name] !== value) {
    throw Error(name === 'lastSeen' ? 'Claim heartbeat readback is unresolved' : 'Claim record readback is unresolved');
  }
  return value;
}

export async function refreshClaimHeartbeat(args, ports = {}) {
  const lastSeen = await setOwnClaimTime('lastSeen', args, ports);
  return lastSeen === null ? { state: 'skipped' } : { state: 'refreshed', lastSeen };
}

function nativeAuthority(cwd, ports) {
  const s = service(cwd, ports), fs = ports.fs ?? nativeFs;
  const repoCache = new Map();
  const readExtraTrust = () => {
    if (!cwd) return { ok: true, trust: [] };
    try {
      const parsed = JSON.parse(fs.readFileSync(join(cwd, 'pdd.json'), 'utf8'));
      const list = Array.isArray(parsed?.autopilot?.trust) ? parsed.autopilot.trust.filter(v => typeof v === 'string' && v.trim()) : [];
      return { ok: true, trust: list };
    } catch (error) {
      return error?.code === 'ENOENT' ? { ok: true, trust: [] } : { ok: false, trust: [] };
    }
  };
  const loadRepo = repository => {
    const key = repository.toLowerCase();
    if (!repoCache.has(key)) {
      repoCache.set(key, (async () => {
        const extra = readExtraTrust();
        try {
          const repo = (await s.api(`repos/${repository}`, 'GET', undefined, 'claims', repository, true)).value;
          const pages = [];
          let endpoint = `repos/${repository}/collaborators?per_page=100`;
          while (endpoint) {
            const r = await s.api(endpoint, 'GET', undefined, 'claims', repository, true);
            if (Array.isArray(r.value)) pages.push(...r.value);
            endpoint = r.next;
          }
          const writers = pages.filter(p => p?.permissions?.push || p?.permissions?.maintain || p?.permissions?.admin).map(p => p.login).filter(Boolean);
          const owner = repo?.owner?.login ?? '';
          return { complete: Boolean(owner) && extra.ok, trusted: new Set([owner, ...writers, ...extra.trust].filter(Boolean).map(v => v.toLowerCase())) };
        } catch {
          return { complete: false, trusted: new Set() };
        }
      })());
    }
    return repoCache.get(key);
  };
  return {
    read: async ({ repository, author }) => {
      if (!repositoryName(repository) || typeof author !== 'string' || !author.trim()) return { authority: 'unverified' };
      const data = await loadRepo(repository);
      if (!data.complete) return { authority: 'unverified' };
      return { authority: data.trusted.has(author.trim().toLowerCase()) ? 'trusted' : 'outsider' };
    },
  };
}

async function liveUnclaimed(cwd, repository, issues, ports) {
  const unclaimed = new Set(), s = service(cwd, ports), [owner, name] = repository.split('/');
  for (let offset = 0; offset < issues.length; offset += 25) {
    const batch = issues.slice(offset, offset + 25);
    const query = `query($owner:String!,$name:String!${batch.map((_, i) => `,$n${i}:Int!`).join('')}) { repository(owner:$owner,name:$name) { ${batch.map((_, i) => `i${i}:issue(number:$n${i}) { url labels(first:100) { nodes { name } pageInfo { hasNextPage } } }`).join(' ')} } }`;
    try {
      const reply = (await s.api('graphql', 'POST', JSON.stringify({
        query,
        variables: { owner, name, ...Object.fromEntries(batch.map((key, i) => [`n${i}`, info(key).issue])) },
      }), 'claims', repository, true)).value;
      if (reply.errors?.length || !object(reply.data?.repository)) continue;
      batch.forEach((key, i) => {
        const row = reply.data.repository[`i${i}`], labels = row?.labels;
        if (canonical(row?.url) === canonical(key) && Array.isArray(labels?.nodes) && labels.pageInfo?.hasNextPage === false
          && labels.nodes.every(label => object(label) && typeof label.name === 'string' && label.name)
          && !labels.nodes.some(label => label.name === 'pdd:working')) unclaimed.add(key);
      });
    } catch { /* Ordinary live winner read supplies the fallback. */ }
  }
  return unclaimed;
}

export function createDependencyReadPorts({ cwd = '' } = {}, supplied = {}) {
  const ports = { ...supplied, cwd: supplied.cwd ?? cwd };
  ports.github ??= rawGithub(ports.cwd, ports);
  ports.authority ??= nativeAuthority(ports.cwd, ports);
  ports.clock ??= { now: async () => ({ iso: new Date(typeof supplied.now === 'function' ? supplied.now() : Date.now()).toISOString() }) };
  ports.owners ??= {
    read: async ({ repository, issues = [] }) => {
      try {
        const claims = [];
        let now = NaN;
        try { now = time((await ports.clock.now({})).iso); } catch { /* Unknown clock expires no claim. */ }
        const unclaimed = issues.length > 1 && ports.github[NATIVE_GITHUB]
          ? await liveUnclaimed(ports.cwd, repository, issues, ports) : new Set();
        for (const key of issues) {
          if (unclaimed.has(key)) continue;
          const claim = await winningClaim(repository, key, ports.github, ports.authority, now, true);
          if (claim) claims.push(claim);
        }
        return { json: JSON.stringify({ claims }) };
      } finally {
        try { ports.githubCache?.flush?.(); } catch { /* cache flush is best-effort */ }
      }
    },
  };
  return ports;
}
