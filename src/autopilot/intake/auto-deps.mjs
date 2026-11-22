// Layer-2 conservative directed native `blocked_by` auto-dependency discovery + expiring local file-claim reservations.
import { createHash } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { join, resolve } from 'node:path';
import { issueKey, wouldCreateCycle } from '../graph/dag.mjs';
import { assertSafePrivateDir, isPathAtOrInside, readJsonObjectQuiet, writeAtomicPrivate } from '../../shared/atomic-fs.mjs';
import { redactSecrets } from '../../secret-redaction.mjs';

export const AUTO_DEPS_MARKER_PREFIX = '<!-- pdd:autopilot-deps:v1:';
export const DEPENDENCY_EVIDENCE_KINDS = Object.freeze(['explicit-prerequisite', 'confirmed-contract']);
export const DEPENDENCY_ACTIONS = Object.freeze([
  'add', 'remove-stale', 'hold-unknown', 're-triage-not-planned',
  'noop-exists', 'skip-human-removed', 'skip-human-owned', 'skip-cycle', 'skip-overlap-only',
]);
export const DEFAULT_FILE_CLAIM_TTL_MS = 30 * 60 * 1000;

const REPO_RE = /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/;
const REF_ITEM = '(?:issue\\s+)?(?:#[1-9]\\d*|[A-Za-z0-9_.-]+\\/[A-Za-z0-9_.-]+#[1-9]\\d*|https:\\/\\/github\\.com\\/[A-Za-z0-9_.-]+\\/[A-Za-z0-9_.-]+\\/issues\\/[1-9]\\d*)';
const REF_LIST = `(${REF_ITEM}(?:\\s*(?:,|\\band\\b|&)\\s*${REF_ITEM})*)`;
const INCOMING_RE = new RegExp(`\\b(?:blocked\\s+by|depends\\s+on|requires|prerequisites?\\s*:|must\\s+wait\\s+for|wait(?:s|ing)?\\s+(?:on|for))\\s+${REF_LIST}`, 'gi');
const OUTGOING_RE = new RegExp(`\\b(?:blocks|unblocks|is\\s+a\\s+prerequisite\\s+for|prerequisite\\s+for|must\\s+land\\s+before)\\s+${REF_LIST}`, 'gi');
const NEGATION_RE = /\b(?:not|no\s+longer|never|doesn't|does\s+not|isn't|is\s+not|without|don't|do\s+not)\s+$/i;
const SINGLE_REF_RE = /https:\/\/github\.com\/([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)\/issues\/([1-9]\d*)|\b([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)#([1-9]\d*)\b|#([1-9]\d*)\b/gi;
const ADDED_EVENTS = new Set(['blocked_by_added', 'added_blocked_by', 'blockedbyaddedevent']);
const REMOVED_EVENTS = new Set(['blocked_by_removed', 'removed_blocked_by', 'blockedbyremovedevent']);

const isObj = v => v !== null && typeof v === 'object' && !Array.isArray(v);
const asText = v => (typeof v === 'string' ? v : '');
const posInt = v => Number.isSafeInteger(v) && v > 0;
const sha16 = v => createHash('sha256').update(String(v)).digest('hex').slice(0, 16);
const keyOf = (repo, n) => issueKey(`https://github.com/${repo}/issues/${n}`);
const edgeId = (d, b) => `${d}->${b}`;
const statusOf = x => Number(x?.status ?? x?.statusCode ?? x?.response?.status ?? 0);
const parseMs = v => (typeof v === 'number' && Number.isFinite(v) ? v : (typeof v === 'string' && Number.isFinite(Date.parse(v)) ? Date.parse(v) : 0));
const nowMsOf = now => (typeof now === 'function' ? now() : now);
const cleanLine = (v, max = 240, secrets = []) => redactSecrets(asText(v), secrets).replace(/[\x00-\x1f\x7f-\x9f]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, max);

export const issueContentHash = issue => sha16(JSON.stringify({ title: asText(issue?.title).trim(), body: asText(issue?.body).trim() }));

function stripNonProse(raw) {
  const out = [];
  let fence = null;
  for (const line of asText(raw).replace(/<!--[\s\S]*?-->/g, ' ').split(/\r?\n/)) {
    const fm = /^\s*(`{3,}|~{3,})/.exec(line);
    if (fm) { fence = !fence ? fm[1][0] : (line.trim().startsWith(fence.repeat(3)) ? null : fence); continue; }
    if (!fence && !/^\s*>/.test(line)) out.push(line);
  }
  return out.join('\n');
}

/** Parse ONLY explicit directed prerequisite semantics (never temporary file overlap). */
export function parseExplicitDependencies(issue, { repo = '' } = {}) {
  const selfNum = posInt(issue?.number) ? issue.number : null;
  const repoLower = REPO_RE.test(asText(repo).trim()) ? repo.trim().toLowerCase() : '';
  const source = `${asText(issue?.title)}\n${stripNonProse(issue?.body)}`;
  const scan = regex => {
    const byTarget = new Map();
    for (const m of source.matchAll(regex)) {
      if (NEGATION_RE.test(source.slice(Math.max(0, m.index - 24), m.index))) continue;
      const evidence = cleanLine(m[0], 180);
      for (const ref of m[1].matchAll(SINGLE_REF_RE)) {
        const refRepo = (ref[1] ?? ref[3] ?? '').toLowerCase();
        if (refRepo && repoLower && refRepo !== repoLower) continue;
        const target = Number(ref[2] ?? ref[4] ?? ref[5]);
        if (posInt(target) && target !== selfNum && !byTarget.has(target)) byTarget.set(target, { target, kind: 'explicit-prerequisite', evidence });
      }
    }
    return [...byTarget.values()].sort((a, b) => a.target - b.target);
  };
  return { blockedBy: scan(INCOMING_RE), blocking: scan(OUTGOING_RE) };
}

/** Inspect timeline events to guarantee humans always win over Autopilot edges. */
export function inspectEdgeTimeline(timeline, blockerNumber, { autopilotLogins = [], managedEdge = null, autopilotRemovedAt = 0, existsInLive = false } = {}) {
  const botLogins = new Set((autopilotLogins ?? []).map(s => asText(s).trim().toLowerCase()).filter(Boolean));
  const managedAtMs = parseMs(managedEdge?.addedAt), removedAtMs = parseMs(autopilotRemovedAt);
  const events = (Array.isArray(timeline) ? timeline : [])
    .filter(ev => isObj(ev) && Number(ev.blocker ?? ev.blocking_issue?.number ?? ev.blockingIssue?.number ?? ev.issue?.number ?? ev.subject?.number ?? ev.target) === blockerNumber)
    .map((ev, idx) => ({ ev, idx, ts: parseMs(ev.created_at ?? ev.createdAt ?? ev.at) }))
    .sort((a, b) => a.ts - b.ts || a.idx - b.idx);

  let lastEvent = null, lastActorKind = null, humanRemovedBlocksReadd = false, humanAddedAfterManaged = false;
  for (const { ev, ts } of events) {
    const kind = asText(ev.event ?? ev.type).trim().toLowerCase();
    const isAdd = ADDED_EVENTS.has(kind), isRem = REMOVED_EVENTS.has(kind);
    if (!isAdd && !isRem) continue;
    const login = asText(ev.actor?.login ?? ev.actor).trim().toLowerCase(), refMs = isAdd ? managedAtMs : removedAtMs;
    const actorKind = (ev.actorKind === 'autopilot' || ev.actorKind === 'human') ? ev.actorKind
      : (botLogins.size > 0 ? (botLogins.has(login) ? 'autopilot' : 'human')
        : (refMs > 0 && ts > 0 && Math.abs(ts - refMs) <= 5000 ? 'autopilot' : 'human'));
    lastEvent = isAdd ? 'added' : 'removed';
    lastActorKind = actorKind;
    if (isRem && actorKind === 'human') humanRemovedBlocksReadd = true;
    if (isAdd && actorKind === 'human') { humanRemovedBlocksReadd = false; if (!managedEdge || ts === 0 || ts >= managedAtMs) humanAddedAfterManaged = true; }
  }
  if (managedEdge && !existsInLive && removedAtMs === 0 && !humanAddedAfterManaged) humanRemovedBlocksReadd = true;
  const humanOwned = existsInLive && (!managedEdge || humanAddedAfterManaged || (lastEvent === 'added' && lastActorKind === 'human'));
  return { lastEvent, lastActorKind, humanRemovedBlocksReadd, humanOwned };
}

function safeStateFile(fs, stateDir, filename) {
  const dir = assertSafePrivateDir(fs, stateDir, { label: 'autopilot dependency state' });
  const target = resolve(join(dir, filename));
  if (!isPathAtOrInside(target, dir, fs)) throw Object.assign(new Error(`Refusing state path outside "${dir}": "${filename}"`), { code: 'unsafe_state_path' });
  try {
    const st = (fs.lstatSync ?? nativeFs.lstatSync).call(fs, target);
    if (st.isSymbolicLink() || !st.isFile()) throw Object.assign(new Error(`Refusing symlink or non-file state target "${target}".`), { code: 'unsafe_state_path' });
  } catch (err) { if (err?.code !== 'ENOENT') throw err; }
  return target;
}

function loadAutoDepsState(fs, stateDir) {
  const file = stateDir ? safeStateFile(fs, stateDir, 'auto-deps-state.json') : null;
  const raw = file ? readJsonObjectQuiet(fs, file) : null;
  const pick = key => (isObj(raw?.[key]) ? { ...raw[key] } : {});
  return { file, state: { contentHashes: pick('contentHashes'), managedEdges: pick('managedEdges'), autopilotRemovals: pick('autopilotRemovals'), humanRemovedEdges: pick('humanRemovedEdges'), postedMarkers: pick('postedMarkers') } };
}

async function collectPaginated(fetcher, maxPages = 50) {
  if (typeof fetcher !== 'function') return [];
  const items = [], seen = new Set();
  for (let i = 0, page = 1, cursor = null; i < maxPages; i++) {
    const token = cursor ?? `p:${page}`;
    if (seen.has(token)) break;
    seen.add(token);
    const res = await fetcher({ page, perPage: 100, cursor });
    if (isObj(res) && statusOf(res) === 404) throw Object.assign(new Error('GitHub resource not found (404).'), { status: 404 });
    if (Array.isArray(res)) { items.push(...res); if (res.length < 100) break; page += 1; }
    else if (isObj(res) && Array.isArray(res.items)) { items.push(...res.items); if (!res.hasNext && !res.nextCursor) break; if (res.nextCursor) cursor = res.nextCursor; else page += 1; }
    else break;
  }
  return items;
}

async function postIdempotentComment({ gh, dependent, actionKind, lines, details, state, dryRun, secrets }) {
  const marker = `${AUTO_DEPS_MARKER_PREFIX}${dependent}:${actionKind}:${sha16(JSON.stringify(details))} -->`;
  const existing = typeof gh?.listComments === 'function' ? await collectPaginated(p => gh.listComments(dependent, p)) : [];
  if (state.postedMarkers[marker] || existing.some(c => asText(c?.body).includes(marker))) return false;
  if (dryRun || typeof gh?.createComment !== 'function') return false;
  await gh.createComment(dependent, `${lines.map(l => redactSecrets(l, secrets)).join('\n')}\n\n${marker}`);
  state.postedMarkers[marker] = true;
  return true;
}

function collectBidirectionalCandidates({ cleanRepo, subjectIssue, issueMap, contractDependencies, actions, secrets }) {
  const subjectNum = subjectIssue.number, candidates = new Map();
  const add = (dep, blk, kind, ev) => { if (posInt(dep) && posInt(blk) && !candidates.has(edgeId(dep, blk))) candidates.set(edgeId(dep, blk), { dependent: dep, blocker: blk, kind, evidence: cleanLine(ev, 180, secrets) }); };
  const sp = parseExplicitDependencies(subjectIssue, { repo: cleanRepo });
  for (const x of sp.blockedBy) add(subjectNum, x.target, x.kind, x.evidence);
  for (const x of sp.blocking) add(x.target, subjectNum, x.kind, x.evidence);
  for (const other of issueMap.values()) {
    if (other.number === subjectNum) continue;
    const op = parseExplicitDependencies(other, { repo: cleanRepo });
    for (const x of op.blockedBy) if (x.target === subjectNum) add(other.number, subjectNum, x.kind, x.evidence);
    for (const x of op.blocking) if (x.target === subjectNum) add(subjectNum, other.number, x.kind, x.evidence);
  }
  for (const dep of Array.isArray(contractDependencies) ? contractDependencies : []) {
    if (!isObj(dep)) continue;
    const dependent = Number(dep.dependent ?? dep.from), blocker = Number(dep.blocker ?? dep.to);
    if (!posInt(dependent) || !posInt(blocker) || (dependent !== subjectNum && blocker !== subjectNum)) continue;
    if (dep.kind === 'file-overlap' || dep.confirmed !== true || !asText(dep.contract).trim()) {
      actions.push({ action: 'skip-overlap-only', dependent, blocker, reason: 'Temporary file overlap or unconfirmed contract must use local file claims, not GitHub blocked_by.' });
      continue;
    }
    add(dependent, blocker, 'confirmed-contract', dep.evidence ?? dep.contract);
  }
  return candidates;
}

/** Reconcile conservative native GitHub `blocked_by` edges bidirectionally for a created/edited issue. */
export async function reconcileAutoDependencies({
  repo, subjectIssue, openIssues = null, contractDependencies = [], gh = {}, stateDir = null,
  autopilotLogins = [], dryRun = false, force = false, fs = nativeFs, now = Date.now, secrets = [],
} = {}) {
  if (!REPO_RE.test(asText(repo).trim()) || !isObj(subjectIssue) || !posInt(subjectIssue.number)) {
    throw Object.assign(new Error('reconcileAutoDependencies requires a valid repo and subjectIssue.number.'), { code: 'invalid_input' });
  }
  const cleanRepo = repo.trim(), subjectNum = subjectIssue.number, nowIso = new Date(nowMsOf(now)).toISOString();
  const { file: stateFile, state } = loadAutoDepsState(fs, stateDir), hash = issueContentHash(subjectIssue);
  const stateKey = `${hash}:${asText(subjectIssue.state)}:${asText(subjectIssue.state_reason)}`;
  if (!force && state.contentHashes[String(subjectNum)] === stateKey) {
    return { skipped: true, reason: 'unchanged-content-hash', contentHash: hash, actions: [], holds: [], retriage: [], commentsPosted: 0 };
  }

  const fetchedOpen = Array.isArray(openIssues) ? openIssues : await collectPaginated(gh.listOpenIssues);
  const issueMap = new Map();
  for (const row of [...fetchedOpen, subjectIssue]) if (isObj(row) && posInt(row.number)) issueMap.set(row.number, row);

  const actions = [], holds = [], retriage = [];
  const recordHold = (dep, blk, reason) => {
    holds.push({ issue: dep, blocker: blk, dispatchable: false, reason });
    actions.push({ action: 'hold-unknown', dependent: dep, blocker: blk, status: 404, dispatchable: false, reason });
  };
  const candidates = collectBidirectionalCandidates({ cleanRepo, subjectIssue, issueMap, contractDependencies, actions, secrets });
  const touched = new Set([subjectNum, ...issueMap.keys(), ...[...candidates.values()].map(c => c.dependent)]);
  for (const m of Object.values(state.managedEdges)) if (m?.dependent === subjectNum || m?.blocker === subjectNum) touched.add(m.dependent);

  const liveBlockedBy = new Map(), workingEdges = [], seenWorking = new Set();
  for (const depNum of [...touched].sort((a, b) => a - b)) {
    let rows = [];
    if (typeof gh.listBlockedBy === 'function') {
      try { rows = await collectPaginated(p => gh.listBlockedBy(depNum, p)); }
      catch (err) { if (statusOf(err) === 404) { recordHold(depNum, null, 'issue-unavailable-404'); continue; } throw err; }
    }
    const blkMap = new Map();
    for (const blk of rows) {
      const bNum = posInt(blk) ? blk : (posInt(blk?.number) ? blk.number : null);
      if (!bNum) continue;
      blkMap.set(bNum, isObj(blk) ? blk : (issueMap.get(bNum) ?? { number: bNum }));
      if (!seenWorking.has(edgeId(depNum, bNum))) { seenWorking.add(edgeId(depNum, bNum)); workingEdges.push({ dependent: keyOf(cleanRepo, depNum), blocker: keyOf(cleanRepo, bNum) }); }
    }
    liveBlockedBy.set(depNum, blkMap);
  }

  const timelineCache = new Map();
  const getTimeline = async n => (timelineCache.has(n) ? timelineCache.get(n)
    : (timelineCache.set(n, typeof gh.listTimeline === 'function' ? await collectPaginated(p => gh.listTimeline(n, p)) : []), timelineCache.get(n)));
  const resolveIssue = async n => {
    if (issueMap.has(n)) return { ok: true, issue: issueMap.get(n) };
    if (typeof gh.getIssue !== 'function') return { ok: true, issue: { number: n } };
    try {
      const res = await gh.getIssue(n);
      if (!res || (isObj(res) && statusOf(res) === 404)) return { ok: false, status: 404 };
      issueMap.set(n, res);
      return { ok: true, issue: res };
    } catch (err) { if (statusOf(err) === 404) return { ok: false, status: 404 }; throw err; }
  };

  let commentsPosted = 0;

  // Check existing blockers for `not_planned` closures or 404s (never silently unblock).
  for (const [depNum, blkMap] of liveBlockedBy.entries()) {
    if (depNum !== subjectNum && !blkMap.has(subjectNum)) continue;
    for (const [bNum, blkObj] of blkMap.entries()) {
      const resolved = (blkObj?.state || blkObj?.state_reason) ? { ok: true, issue: blkObj } : await resolveIssue(bNum);
      if (!resolved.ok && resolved.status === 404) { recordHold(depNum, bNum, 'blocker-unavailable-404'); continue; }
      const blk = resolved.issue;
      if (blk?.state === 'not_planned' || (blk?.state === 'closed' && blk?.state_reason === 'not_planned')) {
        retriage.push({ issue: depNum, blocker: bNum, dispatchable: false, needsRetriage: true, reason: 'blocker-closed-not-planned' });
        actions.push({ action: 're-triage-not-planned', dependent: depNum, blocker: bNum, dispatchable: false, needsRetriage: true });
        if (await postIdempotentComment({
          gh, dependent: depNum, actionKind: 'not-planned', details: { depNum, bNum, stateReason: 'not_planned' }, state, dryRun, secrets,
          lines: [`Autopilot paused dispatch for #${depNum}: prerequisite #${bNum} closed as \`not_planned\`.`, `- Action required: re-triage #${depNum} or remove the native \`blocked_by\` link if it is still valid.`],
        })) commentsPosted += 1;
      }
    }
  }

  // Evaluate candidate additions in deterministic order with dag.mjs cycle validation.
  const addedByDep = new Map();
  for (const { dependent, blocker, kind, evidence } of [...candidates.values()].sort((a, b) => a.dependent - b.dependent || a.blocker - b.blocker)) {
    const depKey = keyOf(cleanRepo, dependent), blkKey = keyOf(cleanRepo, blocker), eKey = edgeId(dependent, blocker);
    if (wouldCreateCycle(workingEdges, depKey, blkKey)) { actions.push({ action: 'skip-cycle', dependent, blocker, kind }); continue; }
    const blkMap = liveBlockedBy.get(dependent) ?? new Map();
    if (blkMap.has(blocker)) { actions.push({ action: 'noop-exists', dependent, blocker, kind, idempotent: true }); continue; }
    const tl = inspectEdgeTimeline(await getTimeline(dependent), blocker, { autopilotLogins, managedEdge: state.managedEdges[eKey] ?? null, autopilotRemovedAt: state.autopilotRemovals[eKey] ?? 0, existsInLive: false });
    if (tl.lastEvent === 'added' && tl.lastActorKind === 'human') delete state.humanRemovedEdges[eKey];
    if (tl.humanRemovedBlocksReadd || state.humanRemovedEdges[eKey]) {
      if (!dryRun) state.humanRemovedEdges[eKey] = state.humanRemovedEdges[eKey] ?? nowIso;
      actions.push({ action: 'skip-human-removed', dependent, blocker, kind });
      continue;
    }
    const resolved = await resolveIssue(blocker);
    if (!resolved.ok && resolved.status === 404) { recordHold(dependent, blocker, 'blocker-unavailable-404'); continue; }
    if (dryRun) { workingEdges.push({ dependent: depKey, blocker: blkKey }); actions.push({ action: 'add', dependent, blocker, kind, evidence, dryRun: true }); continue; }
    let writeStatus = 201;
    try { writeStatus = statusOf(typeof gh.addBlockedBy === 'function' ? await gh.addBlockedBy(dependent, resolved.issue) : { status: 201 }) || 201; }
    catch (err) { writeStatus = statusOf(err); if (writeStatus !== 404 && writeStatus !== 422) throw err; }
    if (writeStatus === 404) { recordHold(dependent, blocker, 'blocker-unavailable-404'); continue; }
    if (writeStatus === 422) { actions.push({ action: 'noop-exists', dependent, blocker, kind, status: 422, idempotent: true }); continue; }
    if (writeStatus >= 400) throw Object.assign(new Error(`GitHub addBlockedBy failed with status ${writeStatus}`), { status: writeStatus });
    workingEdges.push({ dependent: depKey, blocker: blkKey });
    blkMap.set(blocker, resolved.issue);
    liveBlockedBy.set(dependent, blkMap);
    state.managedEdges[eKey] = { dependent, blocker, kind, evidence, addedAt: nowIso, contentHash: hash };
    delete state.autopilotRemovals[eKey];
    actions.push({ action: 'add', dependent, blocker, kind, evidence });
    addedByDep.set(dependent, [...(addedByDep.get(dependent) ?? []), { blocker, kind, evidence }]);
  }

  // Remove stale Autopilot-added edges when scope changes; NEVER remove human-owned edges.
  const removedByDep = new Map();
  for (const [eKey, managed] of Object.entries({ ...state.managedEdges })) {
    if (!isObj(managed) || (managed.dependent !== subjectNum && managed.blocker !== subjectNum) || candidates.has(eKey)) continue;
    const { dependent, blocker } = managed, blkMap = liveBlockedBy.get(dependent) ?? new Map();
    if (!blkMap.has(blocker)) {
      if (!dryRun && !state.autopilotRemovals[eKey]) state.humanRemovedEdges[eKey] = nowIso;
      delete state.managedEdges[eKey];
      continue;
    }
    const tl = inspectEdgeTimeline(await getTimeline(dependent), blocker, { autopilotLogins, managedEdge: managed, autopilotRemovedAt: state.autopilotRemovals[eKey] ?? 0, existsInLive: true });
    if (tl.humanOwned) { actions.push({ action: 'skip-human-owned', dependent, blocker }); continue; }
    if (!dryRun && typeof gh.removeBlockedBy === 'function') await gh.removeBlockedBy(dependent, blkMap.get(blocker) ?? { number: blocker });
    if (!dryRun) { delete state.managedEdges[eKey]; state.autopilotRemovals[eKey] = nowIso; }
    actions.push({ action: 'remove-stale', dependent, blocker, ...(dryRun ? { dryRun: true } : {}) });
    removedByDep.set(dependent, [...(removedByDep.get(dependent) ?? []), blocker]);
  }
  for (const bNum of (liveBlockedBy.get(subjectNum) ?? new Map()).keys()) {
    const eKey = edgeId(subjectNum, bNum);
    if (!candidates.has(eKey) && !state.managedEdges[eKey]) actions.push({ action: 'skip-human-owned', dependent: subjectNum, blocker: bNum });
  }

  for (const [depNum, items] of addedByDep.entries()) {
    if (await postIdempotentComment({
      gh, dependent: depNum, actionKind: 'added', details: { depNum, blockers: items.map(i => i.blocker).sort((a, b) => a - b) }, state, dryRun, secrets,
      lines: [`Autopilot linked native \`blocked_by\` prerequisite(s) on #${depNum}:`, ...items.map(i => `- #${i.blocker} (\`${i.kind}\`): ${i.evidence}`), '- Remove any link manually if it does not apply; Autopilot will respect your removal.'],
    })) commentsPosted += 1;
  }
  for (const [depNum, blockers] of removedByDep.entries()) {
    const sorted = [...blockers].sort((a, b) => a - b);
    if (await postIdempotentComment({
      gh, dependent: depNum, actionKind: 'removed-stale', details: { depNum, blockers: sorted, hash }, state, dryRun, secrets,
      lines: [`Autopilot removed stale Autopilot-added \`blocked_by\` link(s) on #${depNum} after scope changed: ${sorted.map(b => `#${b}`).join(', ')}.`],
    })) commentsPosted += 1;
  }

  if (stateFile && !dryRun) { state.contentHashes[String(subjectNum)] = stateKey; writeAtomicPrivate(fs, stateFile, `${JSON.stringify(state, null, 2)}\n`); }
  return { skipped: false, contentHash: hash, actions, holds, retriage, commentsPosted };
}

// ---- Separate Local File-Claim Reservations (atomic temp+rename, TTL expiry, never touches GitHub) ----

function normalizeClaimFiles(files) {
  const out = new Set();
  for (const raw of Array.isArray(files) ? files : []) {
    if (typeof raw !== 'string') continue;
    const c = raw.trim().replaceAll('\\', '/').replace(/^(?:\.\/|\/)+/, '').replace(/\/+/g, '/').replace(/\/+$/, '');
    if (c && c !== '.' && c !== '..' && !c.startsWith('../') && !c.includes('/../') && !c.endsWith('/..') && !/[\x00-\x1f\x7f]/.test(c)) out.add(c);
  }
  return [...out].sort();
}
const pathsOverlap = (a, b) => a === b || a.startsWith(`${b}/`) || b.startsWith(`${a}/`);
const saveClaims = (fs, file, claims) => writeAtomicPrivate(fs, file, `${JSON.stringify({ version: 1, claims }, null, 2)}\n`);

function loadClaimsStore(fs, stateDir) {
  const file = safeStateFile(fs, stateDir, 'file-claims.json');
  const raw = readJsonObjectQuiet(fs, file);
  const claims = Array.isArray(raw?.claims) ? raw.claims.filter(c => isObj(c) && asText(c.owner).trim() && posInt(c.issue) && asText(c.leaseId).trim() && Array.isArray(c.files) && parseMs(c.expiresAt) > 0) : [];
  return { file, claims };
}

function findOverlaps(claims, normFiles, nowMs, { excludeOwner = null, excludeIssue = null, excludeLeaseId = null } = {}) {
  const conflicts = [];
  for (const c of claims) {
    if (parseMs(c.expiresAt) <= nowMs || (excludeLeaseId && c.leaseId === excludeLeaseId)) continue;
    if (excludeOwner && excludeIssue && c.owner === excludeOwner && c.issue === excludeIssue) continue;
    const overlappingFiles = normFiles.filter(f => c.files.some(cf => pathsOverlap(f, cf)));
    if (overlappingFiles.length > 0) conflicts.push({ owner: c.owner, issue: c.issue, leaseId: c.leaseId, overlappingFiles, acquiredAt: c.acquiredAt, expiresAt: c.expiresAt });
  }
  return conflicts;
}

export function sweepExpiredClaims(stateDir, { now = Date.now, fs = nativeFs } = {}) {
  const nowMs = nowMsOf(now), { file, claims } = loadClaimsStore(fs, stateDir);
  const active = claims.filter(c => parseMs(c.expiresAt) > nowMs), expired = claims.filter(c => parseMs(c.expiresAt) <= nowMs);
  if (expired.length > 0) saveClaims(fs, file, active);
  return { active, expired, sweptCount: expired.length };
}

export function activeFileConflicts(stateDir, { files = [], excludeOwner = null, excludeIssue = null, excludeLeaseId = null, now = Date.now, fs = nativeFs } = {}) {
  const conflicts = findOverlaps(loadClaimsStore(fs, stateDir).claims, normalizeClaimFiles(files), nowMsOf(now), { excludeOwner, excludeIssue, excludeLeaseId });
  return { hasConflict: conflicts.length > 0, conflicts };
}

export function acquireFileClaim(stateDir, { owner, issue, leaseId, files = [], ttlMs = DEFAULT_FILE_CLAIM_TTL_MS, now = Date.now, fs = nativeFs } = {}) {
  const cleanOwner = asText(owner).trim(), cleanLease = asText(leaseId).trim(), normFiles = normalizeClaimFiles(files);
  if (!cleanOwner || !posInt(issue) || !cleanLease || normFiles.length === 0 || !(typeof ttlMs === 'number' && Number.isFinite(ttlMs) && ttlMs > 0)) {
    throw Object.assign(new Error('acquireFileClaim requires owner, positive issue, leaseId, non-empty valid files, and positive ttlMs.'), { code: 'invalid_claim' });
  }
  const nowMs = nowMsOf(now), { file, claims } = loadClaimsStore(fs, stateDir), active = claims.filter(c => parseMs(c.expiresAt) > nowMs);
  const conflicts = findOverlaps(active, normFiles, nowMs, { excludeLeaseId: cleanLease });
  if (conflicts.length > 0) return { acquired: false, conflict: true, conflicts, claim: null };
  const record = { owner: cleanOwner, issue, leaseId: cleanLease, files: normFiles, acquiredAt: new Date(nowMs).toISOString(), expiresAt: new Date(nowMs + ttlMs).toISOString() };
  saveClaims(fs, file, [...active.filter(c => c.leaseId !== cleanLease), record]);
  return { acquired: true, conflict: false, conflicts: [], claim: record };
}

export function releaseFileClaim(stateDir, { owner = null, issue = null, leaseId = null, now = Date.now, fs = nativeFs } = {}) {
  const nowMs = nowMsOf(now), { file, claims } = loadClaimsStore(fs, stateDir), kept = [], released = [];
  for (const c of claims) {
    if (parseMs(c.expiresAt) <= nowMs) continue;
    const hit = (leaseId && c.leaseId === leaseId) || (!leaseId && owner && posInt(issue) && c.owner === owner && c.issue === issue) || (!leaseId && !owner && posInt(issue) && c.issue === issue);
    (hit ? released : kept).push(c);
  }
  saveClaims(fs, file, kept);
  return { releasedCount: released.length, released, remaining: kept };
}
