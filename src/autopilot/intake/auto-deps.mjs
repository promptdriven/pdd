// Layer-2 conservative directed native `blocked_by` auto-dependency discovery + locked expiring local file-claim reservations.
import { createHash } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { join, resolve } from 'node:path';
import { issueKey, wouldCreateCycle } from '../graph/dag.mjs';
import { assertSafePrivateDir, isPathAtOrInside, readJsonObjectQuiet, writeAtomicPrivate } from '../../shared/atomic-fs.mjs';
import { acquireRunLock } from '../../shared/file-lock.mjs';
import { redactSecrets } from '../../secret-redaction.mjs';

export const AUTO_DEPS_MARKER_PREFIX = '<!-- pdd:autopilot-deps:v1:';
export const DEPENDENCY_EVIDENCE_KINDS = Object.freeze(['explicit-prerequisite', 'confirmed-contract']);
export const DEPENDENCY_ACTIONS = Object.freeze(['add', 'remove-stale', 'hold-unknown', 're-triage-not-planned', 'noop-exists', 'skip-human-removed', 'skip-human-owned', 'skip-cycle', 'skip-overlap-only']);
export const DEFAULT_FILE_CLAIM_TTL_MS = 30 * 60 * 1000;

const REPO_RE = /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/;
const REF_ITEM = '(?:issue\\s+)?(?:#[1-9]\\d*|[A-Za-z0-9_.-]+\\/[A-Za-z0-9_.-]+#[1-9]\\d*|https:\\/\\/github\\.com\\/[A-Za-z0-9_.-]+\\/[A-Za-z0-9_.-]+\\/issues\\/[1-9]\\d*)';
const REF_LIST = `(${REF_ITEM}(?:\\s*(?:,|\\band\\b|&)\\s*${REF_ITEM})*)`;
const INCOMING_RE = new RegExp(`(?<![a-z-])(?:blocked\\s+by|depends\\s+on|prerequisites?\\s*:|must\\s+wait\\s+for|wait(?:s|ing)?\\s+(?:on|for))\\s+${REF_LIST}`, 'gi');
const OUTGOING_RE = new RegExp(`(?<![a-z-])(?:blocks|unblocks|is\\s+a\\s+prerequisite\\s+for|prerequisite\\s+for|must\\s+land\\s+before)\\s+${REF_LIST}`, 'gi');
const NEGATION_RE = /(?:\b(?:not|no\s+longer|never|doesn't|does\s+not|isn't|is\s+not|aren't|are\s+not|wasn't|was\s+not|without|don't|do\s+not)(?:\s+[a-z]+){0,2}\s+|\b(?:un|non)[-\s]*)$/i;
const SINGLE_REF_RE = /https:\/\/github\.com\/([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)\/issues\/([1-9]\d*)|\b([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)#([1-9]\d*)\b|#([1-9]\d*)\b/gi;
const ADDED_EVENTS = new Set(['blocked_by_added', 'added_blocked_by', 'blockedbyaddedevent']);
const REMOVED_EVENTS = new Set(['blocked_by_removed', 'removed_blocked_by', 'blockedbyremovedevent']);
const DUP_422_RE = /\b(?:already[\s_-]?exists?|duplicate|already[\s_-]?blocked|already[\s_-]?linked)\b/i;
const CLOCK_SKEW_MS = 5 * 60 * 1000, WAIT_BUF = new Int32Array(new SharedArrayBuffer(4));
const isObj = v => v !== null && typeof v === 'object' && !Array.isArray(v), asText = v => (typeof v === 'string' ? v : ''), posInt = v => Number.isSafeInteger(v) && v > 0;
const sha16 = v => createHash('sha256').update(String(v)).digest('hex').slice(0, 16), keyOf = (r, n) => issueKey(`https://github.com/${r}/issues/${n}`), edgeId = (d, b) => `${d}->${b}`;
const statusOf = x => Number(x?.status ?? x?.statusCode ?? x?.response?.status ?? 0), nowMsOf = now => (typeof now === 'function' ? now() : now);
const parseMs = v => (typeof v === 'number' && Number.isFinite(v) ? v : (typeof v === 'string' && Number.isFinite(Date.parse(v)) ? Date.parse(v) : 0));
const cleanLine = (v, max = 240, secrets = []) => redactSecrets(asText(v), secrets).replace(/[\x00-\x1f\x7f-\x9f]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, max);
const isNotPlanned = issue => issue?.state === 'not_planned' || (issue?.state === 'closed' && issue?.state_reason === 'not_planned');
const isPullRequest = row => Boolean(row?.pull_request) || /\/pull\/\d+(?:$|[?#])/.test(asText(row?.html_url));
const errWith = (msg, extra) => Object.assign(new Error(msg), extra), pathsOverlap = (a, b) => a === b || a.startsWith(`${b}/`) || b.startsWith(`${a}/`);

function canonicalBlockerKey(blk, defaultRepo) {
  if (posInt(blk)) return keyOf(defaultRepo, blk);
  if (!isObj(blk)) return null;
  const fromUrl = issueKey(asText(blk.html_url ?? blk.url));
  if (fromUrl) return fromUrl;
  const apiRepo = /\/repos\/([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)$/.exec(asText(blk.repository_url))?.[1];
  const repo = REPO_RE.test(asText(blk.repo ?? apiRepo).trim()) ? asText(blk.repo ?? apiRepo).trim() : defaultRepo;
  return posInt(Number(blk.number)) ? keyOf(repo, Number(blk.number)) : null;
}
export const issueContentHash = issue => sha16(JSON.stringify({ title: asText(issue?.title).trim(), body: asText(issue?.body).trim() }));
function stripNonProse(raw) {
  const out = [];
  let fence = null;
  for (const line of asText(raw).replace(/<!--[\s\S]*?-->/g, ' ').split(/\r?\n/)) {
    const fm = /^\s*(`{3,}|~{3,})/.exec(line);
    if (fm) { fence = !fence ? fm[1][0] : (line.trim().startsWith(fence.repeat(3)) ? null : fence); continue; }
    if (!fence && !/^\s*>/.test(line)) out.push(line.replace(/`+[^`]*`+/g, ' '));
  }
  return out.join('\n');
}
/** Parse ONLY explicit directed prerequisite semantics (never file overlap, inline code, or negated prose). */
export function parseExplicitDependencies(issue, { repo = '' } = {}) {
  const selfNum = posInt(issue?.number) ? issue.number : null, repoLower = REPO_RE.test(asText(repo).trim()) ? repo.trim().toLowerCase() : '';
  const source = `${stripNonProse(issue?.title)}\n${stripNonProse(issue?.body)}`;
  const scan = regex => {
    const byTarget = new Map();
    for (const m of source.matchAll(regex)) {
      if (NEGATION_RE.test(source.slice(Math.max(0, m.index - 40), m.index))) continue;
      for (const ref of m[1].matchAll(SINGLE_REF_RE)) {
        const refRepo = (ref[1] ?? ref[3] ?? '').toLowerCase(), target = Number(ref[2] ?? ref[4] ?? ref[5]);
        if ((!refRepo || !repoLower || refRepo === repoLower) && posInt(target) && target !== selfNum && !byTarget.has(target)) byTarget.set(target, { target, kind: 'explicit-prerequisite', evidence: cleanLine(m[0], 180) });
      }
    }
    return [...byTarget.values()].sort((a, b) => a.target - b.target);
  };
  return { blockedBy: scan(INCOMING_RE), blocking: scan(OUTGOING_RE) };
}

/** Inspect timeline events to guarantee humans always win over Autopilot edges. */
export function inspectEdgeTimeline(timeline, blockerNumber, {
  repo = 'owner/repo', autopilotLogins = [], managedEdge = null, autopilotRemoval = null, existsInLive = false,
} = {}) {
  const botLogins = new Set((autopilotLogins ?? []).map(s => asText(s).trim().toLowerCase()).filter(Boolean));
  const remObj = isObj(autopilotRemoval) ? autopilotRemoval : (autopilotRemoval ? { at: autopilotRemoval } : null);
  const mStart = parseMs(managedEdge?.windowStartMs ?? managedEdge?.addedAt), mEnd = parseMs(managedEdge?.windowEndMs ?? managedEdge?.addedAt);
  const rStart = parseMs(remObj?.windowStartMs ?? remObj?.at), rEnd = parseMs(remObj?.windowEndMs ?? remObj?.at), targetKey = keyOf(repo, blockerNumber);
  const hit = ev => { const raw = ev.blocking_issue ?? ev.blockingIssue ?? ev.issue ?? ev.subject; return isObj(raw) ? canonicalBlockerKey(raw, repo) === targetKey : Number(ev.blocker ?? ev.target) === blockerNumber; };
  const events = (Array.isArray(timeline) ? timeline : []).filter(ev => isObj(ev) && hit(ev))
    .map((ev, idx) => ({ ev, idx, ts: parseMs(ev.created_at ?? ev.createdAt ?? ev.at) })).sort((a, b) => a.ts - b.ts || a.idx - b.idx);
  let lastEvent = null, lastActorKind = null, humanRemovedBlocksReadd = false, humanAddedAfterManaged = false, matchedManagedAdd = false;
  for (const { ev, ts } of events) {
    const kind = asText(ev.event ?? ev.type).trim().toLowerCase(), isAdd = ADDED_EVENTS.has(kind), isRem = REMOVED_EVENTS.has(kind);
    if (!isAdd && !isRem) continue;
    const login = asText(ev.actor?.login ?? ev.actor).trim().toLowerCase(), evId = ev.id != null ? String(ev.id) : null;
    let actorKind = 'human';
    if (ev.actorKind === 'autopilot' || ev.actorKind === 'human') actorKind = ev.actorKind;
    else if (isAdd && managedEdge?.eventId && evId === String(managedEdge.eventId)) actorKind = 'autopilot';
    else if (isRem && remObj?.eventId && evId === String(remObj.eventId)) actorKind = 'autopilot';
    else if (botLogins.size > 0) actorKind = botLogins.has(login) ? 'autopilot' : 'human';
    else if (isAdd && managedEdge && !matchedManagedAdd && !humanRemovedBlocksReadd && (ts === 0 || (ts >= mStart - CLOCK_SKEW_MS && ts <= mEnd + CLOCK_SKEW_MS))) { actorKind = 'autopilot'; matchedManagedAdd = true; }
    else if (isRem && remObj && (ts === 0 || (ts >= rStart - CLOCK_SKEW_MS && ts <= rEnd + CLOCK_SKEW_MS))) actorKind = 'autopilot';
    lastEvent = isAdd ? 'added' : 'removed'; lastActorKind = actorKind;
    if (isRem && actorKind === 'human') humanRemovedBlocksReadd = true;
    if (isAdd && actorKind === 'human') { humanRemovedBlocksReadd = false; if (!managedEdge || ts === 0 || ts >= mStart) humanAddedAfterManaged = true; }
  }
  if (managedEdge && !existsInLive && !remObj && !humanAddedAfterManaged) humanRemovedBlocksReadd = true;
  return { lastEvent, lastActorKind, humanRemovedBlocksReadd, humanOwned: existsInLive && (!managedEdge || humanAddedAfterManaged || (lastEvent === 'added' && lastActorKind === 'human')) };
}

function safeStateFile(fs, stateDir, filename) {
  const dir = assertSafePrivateDir(fs, stateDir, { label: 'autopilot dependency state' }), target = resolve(join(dir, filename));
  if (!isPathAtOrInside(target, dir, fs)) throw errWith(`Refusing state path outside "${dir}": "${filename}"`, { code: 'unsafe_state_path' });
  try { const st = (fs.lstatSync ?? nativeFs.lstatSync).call(fs, target); if (st.isSymbolicLink() || !st.isFile()) throw errWith(`Refusing symlink or non-file state target "${target}".`, { code: 'unsafe_state_path' }); }
  catch (err) { if (err?.code !== 'ENOENT') throw err; }
  return { dir, target };
}
async function collectPaginated(fetcher, maxPages = 50) {
  if (typeof fetcher !== 'function') return [];
  const items = [], seen = new Set();
  for (let i = 0, page = 1, cursor = null; i < maxPages; i++) {
    const token = cursor ?? `p:${page}`;
    if (seen.has(token)) break;
    seen.add(token);
    const res = await fetcher({ page, perPage: 100, cursor });
    if (isObj(res) && statusOf(res) >= 400) throw errWith(`GitHub API error (status ${statusOf(res)}).`, { status: statusOf(res), body: res });
    if (Array.isArray(res)) { items.push(...res); if (res.length < 100) break; page += 1; }
    else if (isObj(res) && Array.isArray(res.items)) { items.push(...res.items); if (!res.hasNext && !res.nextCursor) break; if (res.nextCursor) cursor = res.nextCursor; else page += 1; }
    else break;
  }
  return items;
}
async function postIdempotentComment({ gh, dependent, actionKind, lines, details, state, dryRun, secrets, persist }) {
  const marker = `${AUTO_DEPS_MARKER_PREFIX}${dependent}:${actionKind}:${sha16(JSON.stringify(details))} -->`;
  const existing = typeof gh?.listComments === 'function' ? await collectPaginated(p => gh.listComments(dependent, p)) : [];
  if (state.postedMarkers[marker] || existing.some(c => asText(c?.body).includes(marker)) || dryRun || typeof gh?.createComment !== 'function') return false;
  await gh.createComment(dependent, `${lines.map(l => redactSecrets(l, secrets)).join('\n')}\n\n${marker}`);
  state.postedMarkers[marker] = true; persist();
  return true;
}
function collectBidirectionalCandidates({ cleanRepo, subjectIssue, issueMap, contractDependencies, actions, secrets }) {
  const subjectNum = subjectIssue.number, candidates = new Map();
  const add = (dep, blk, kind, ev, declaredBy) => { if (posInt(dep) && posInt(blk) && !candidates.has(edgeId(dep, blk))) candidates.set(edgeId(dep, blk), { dependent: dep, blocker: blk, kind, evidence: cleanLine(ev, 180, secrets), declaredBy }); };
  const sp = parseExplicitDependencies(subjectIssue, { repo: cleanRepo });
  for (const x of sp.blockedBy) add(subjectNum, x.target, x.kind, x.evidence, 'dependent');
  for (const x of sp.blocking) add(x.target, subjectNum, x.kind, x.evidence, 'blocker');
  for (const other of issueMap.values()) if (other.number !== subjectNum) {
    const op = parseExplicitDependencies(other, { repo: cleanRepo });
    for (const x of op.blockedBy) if (x.target === subjectNum) add(other.number, subjectNum, x.kind, x.evidence, 'dependent');
    for (const x of op.blocking) if (x.target === subjectNum) add(subjectNum, other.number, x.kind, x.evidence, 'blocker');
  }
  for (const dep of Array.isArray(contractDependencies) ? contractDependencies : []) if (isObj(dep)) {
    const dependent = Number(dep.dependent ?? dep.from), blocker = Number(dep.blocker ?? dep.to);
    if (!posInt(dependent) || !posInt(blocker) || (dependent !== subjectNum && blocker !== subjectNum)) continue;
    if (dep.kind === 'file-overlap' || dep.confirmed !== true || !asText(dep.contract).trim()) actions.push({ action: 'skip-overlap-only', dependent, blocker, reason: 'Temporary file overlap or unconfirmed contract must use local file claims, not GitHub blocked_by.' });
    else add(dependent, blocker, 'confirmed-contract', dep.evidence ?? dep.contract, 'contract');
  }
  return candidates;
}

/** Reconcile conservative native GitHub `blocked_by` edges bidirectionally for a created/edited issue. */
export async function reconcileAutoDependencies({
  repo, subjectIssue, openIssues = null, contractDependencies = null, gh = {}, stateDir = null,
  autopilotLogins = [], dryRun = false, force = false, fs = nativeFs, now = Date.now, secrets = [],
} = {}) {
  if (!REPO_RE.test(asText(repo).trim()) || !isObj(subjectIssue) || !posInt(subjectIssue.number)) throw errWith('reconcileAutoDependencies requires a valid repo and subjectIssue.number.', { code: 'invalid_input' });
  const cleanRepo = repo.trim(), subjectNum = subjectIssue.number;
  const stateFile = stateDir ? safeStateFile(fs, stateDir, 'auto-deps-state.json').target : null;
  const rawState = stateFile ? readJsonObjectQuiet(fs, stateFile) : null, pick = k => (isObj(rawState?.[k]) ? { ...rawState[k] } : {});
  const state = { contentHashes: pick('contentHashes'), managedEdges: pick('managedEdges'), autopilotRemovals: pick('autopilotRemovals'), humanRemovedEdges: pick('humanRemovedEdges'), postedMarkers: pick('postedMarkers') };
  const persist = () => { if (stateFile && !dryRun) writeAtomicPrivate(fs, stateFile, `${JSON.stringify(state, null, 2)}\n`); };
  const hash = issueContentHash(subjectIssue);
  const cDigest = sha16(JSON.stringify((Array.isArray(contractDependencies) ? contractDependencies : []).filter(isObj).map(d => [Number(d.dependent ?? d.from), Number(d.blocker ?? d.to), Boolean(d.confirmed), asText(d.kind), asText(d.contract).trim()]).filter(([d, b]) => d === subjectNum || b === subjectNum).sort()));
  const stateKey = `${hash}:${asText(subjectIssue.state)}:${asText(subjectIssue.state_reason)}:${cDigest}`;
  if (!force && state.contentHashes[String(subjectNum)] === stateKey) return { skipped: true, reason: 'unchanged-content-hash', contentHash: hash, actions: [], holds: [], retriage: [], commentsPosted: 0 };

  const actions = [], holds = [], retriage = [];
  const recordHold = (dep, blk, reason, status = 404) => { holds.push({ issue: dep, blocker: blk, dispatchable: false, reason }); actions.push({ action: 'hold-unknown', dependent: dep, blocker: blk, status, dispatchable: false, reason }); };
  let fetchedOpen = [], openIndexComplete = false;
  if (Array.isArray(openIssues)) { fetchedOpen = openIssues; openIndexComplete = openIssues.length > 0; }
  else if (typeof gh.listOpenIssues === 'function') { try { fetchedOpen = await collectPaginated(p => gh.listOpenIssues(p)); openIndexComplete = true; } catch (err) { recordHold(subjectNum, null, `open-issues-unavailable-${statusOf(err) || 'error'}`, statusOf(err) || 500); } }
  const issueMap = new Map();
  for (const row of fetchedOpen) if (isObj(row) && posInt(row.number) && !isPullRequest(row)) issueMap.set(row.number, row);
  if (!isPullRequest(subjectIssue)) issueMap.set(subjectNum, subjectIssue);
  const candidates = collectBidirectionalCandidates({ cleanRepo, subjectIssue, issueMap, contractDependencies, actions, secrets });
  const seed = new Set([subjectNum, ...[...candidates.values()].flatMap(c => [c.dependent, c.blocker])]);
  for (const m of Object.values(state.managedEdges)) if (m?.dependent === subjectNum || m?.blocker === subjectNum) seed.add(m.dependent);
  const liveBlockedBy = new Map(), unknownBlockedBy = new Set(), workingEdges = [], seenWorking = new Set();
  for (const q = [...seed].sort((a, b) => a - b), visited = new Set(); q.length > 0 && visited.size < 200;) {
    const depNum = q.shift();
    if (visited.has(depNum)) continue;
    visited.add(depNum);
    let rows = [];
    if (typeof gh.listBlockedBy === 'function') {
      try { rows = await collectPaginated(p => gh.listBlockedBy(depNum, p)); }
      catch (err) { unknownBlockedBy.add(depNum); recordHold(depNum, null, `issue-unavailable-${statusOf(err) || 'error'}`, statusOf(err) || 500); continue; }
    }
    const blkMap = new Map();
    for (const blk of rows) {
      const bKey = canonicalBlockerKey(blk, cleanRepo);
      if (!bKey) continue;
      const item = isObj(blk) ? blk : (issueMap.get(blk) ?? { number: blk }), num = Number(item?.number);
      blkMap.set(bKey, item);
      if (!seenWorking.has(`${keyOf(cleanRepo, depNum)}->${bKey}`)) { seenWorking.add(`${keyOf(cleanRepo, depNum)}->${bKey}`); workingEdges.push({ dependent: keyOf(cleanRepo, depNum), blocker: bKey }); }
      if (bKey === keyOf(cleanRepo, num) && posInt(num) && !visited.has(num)) q.push(num);
    }
    liveBlockedBy.set(depNum, blkMap);
  }
  const reachesUnknown = start => {
    for (const seen = new Set(), q = [start]; q.length;) {
      const n = q.shift();
      if (unknownBlockedBy.has(n)) return true;
      if (seen.has(n)) continue;
      seen.add(n);
      for (const [bKey, blk] of (liveBlockedBy.get(n) ?? new Map()).entries()) if (bKey === keyOf(cleanRepo, Number(blk?.number)) && posInt(Number(blk?.number))) q.push(Number(blk.number));
    }
    return false;
  };
  const tlCache = new Map();
  const getTimeline = async n => (tlCache.has(n) ? tlCache.get(n) : (tlCache.set(n, typeof gh.listTimeline === 'function' ? await collectPaginated(p => gh.listTimeline(n, p)) : []), tlCache.get(n)));
  const resolveIssue = async n => {
    if (issueMap.has(n)) return { ok: true, issue: issueMap.get(n) };
    if (typeof gh.getIssue !== 'function') return { ok: true, issue: { number: n } };
    try { const res = await gh.getIssue(n); if (!res || (isObj(res) && statusOf(res) >= 400)) return { ok: false, status: statusOf(res) || 404 }; issueMap.set(n, res); return { ok: true, issue: res }; }
    catch (err) { return { ok: false, status: statusOf(err) || 500 }; }
  };
  let commentsPosted = 0;
  const flagNotPlanned = async (depNum, bNum) => {
    if (retriage.some(r => r.issue === depNum && r.blocker === bNum)) return;
    retriage.push({ issue: depNum, blocker: bNum, dispatchable: false, needsRetriage: true, reason: 'blocker-closed-not-planned' });
    actions.push({ action: 're-triage-not-planned', dependent: depNum, blocker: bNum, dispatchable: false, needsRetriage: true });
    if (await postIdempotentComment({ gh, dependent: depNum, actionKind: 'not-planned', details: { depNum, bNum, stateReason: 'not_planned' }, state, dryRun, secrets, persist,
      lines: [`Autopilot paused dispatch for #${depNum}: prerequisite #${bNum} closed as \`not_planned\`.`, `- Action required: re-triage #${depNum} or remove the native \`blocked_by\` link if it is still valid.`] })) commentsPosted += 1;
  };
  for (const [depNum, blkMap] of liveBlockedBy.entries()) if (depNum === subjectNum || blkMap.has(keyOf(cleanRepo, subjectNum))) {
    for (const [bKey, blkObj] of blkMap.entries()) {
      const bNum = Number(blkObj?.number);
      if (bKey !== keyOf(cleanRepo, bNum)) continue;
      const resolved = (blkObj?.state || blkObj?.state_reason) ? { ok: true, issue: blkObj } : await resolveIssue(bNum);
      if (!resolved.ok) recordHold(depNum, bNum, `blocker-unavailable-${resolved.status}`, resolved.status);
      else if (isNotPlanned(resolved.issue)) await flagNotPlanned(depNum, bNum);
    }
  }

  const addedByDep = new Map();
  for (const { dependent, blocker, kind, evidence, declaredBy } of [...candidates.values()].sort((a, b) => a.dependent - b.dependent || a.blocker - b.blocker)) {
    if (unknownBlockedBy.has(dependent)) continue;
    const depKey = keyOf(cleanRepo, dependent), blkKey = keyOf(cleanRepo, blocker), eKey = edgeId(dependent, blocker);
    if (wouldCreateCycle(workingEdges, depKey, blkKey)) { actions.push({ action: 'skip-cycle', dependent, blocker, kind }); continue; }
    if (reachesUnknown(blocker)) { recordHold(dependent, blocker, 'cycle-check-incomplete', 404); continue; }
    const blkMap = liveBlockedBy.get(dependent) ?? new Map();
    if (blkMap.has(blkKey)) { actions.push({ action: 'noop-exists', dependent, blocker, kind, idempotent: true }); continue; }
    const tl = inspectEdgeTimeline(await getTimeline(dependent), blocker, { repo: cleanRepo, autopilotLogins, managedEdge: state.managedEdges[eKey] ?? null, autopilotRemoval: state.autopilotRemovals[eKey] ?? null, existsInLive: false });
    if (tl.lastEvent === 'added' && tl.lastActorKind === 'human') delete state.humanRemovedEdges[eKey];
    if (tl.humanRemovedBlocksReadd || state.humanRemovedEdges[eKey]) {
      if (!dryRun) { state.humanRemovedEdges[eKey] = state.humanRemovedEdges[eKey] ?? new Date(nowMsOf(now)).toISOString(); persist(); }
      actions.push({ action: 'skip-human-removed', dependent, blocker, kind }); continue;
    }
    const resolved = await resolveIssue(blocker);
    if (!resolved.ok) { recordHold(dependent, blocker, `blocker-unavailable-${resolved.status}`, resolved.status); continue; }
    if (isNotPlanned(resolved.issue)) { await flagNotPlanned(dependent, blocker); continue; }
    if (dryRun) { workingEdges.push({ dependent: depKey, blocker: blkKey }); actions.push({ action: 'add', dependent, blocker, kind, evidence, dryRun: true }); continue; }
    if (typeof gh.addBlockedBy !== 'function') { recordHold(dependent, blocker, 'missing-add-blocked-by-writer', 0); continue; }
    const beforeMs = nowMsOf(now);
    let writeStatus = 201, writeBody = null, writeErrMsg = '';
    try { writeBody = await gh.addBlockedBy(dependent, resolved.issue); writeStatus = statusOf(writeBody) || 201; }
    catch (err) { writeStatus = statusOf(err); writeErrMsg = asText(err?.message); writeBody = err?.body ?? err; if (writeStatus !== 404 && writeStatus !== 422) throw err; }
    const afterMs = nowMsOf(now);
    if (writeStatus === 404) { recordHold(dependent, blocker, 'blocker-unavailable-404', 404); continue; }
    if (writeStatus === 422) {
      let dup = DUP_422_RE.test(`${writeErrMsg} ${asText(writeBody?.message)} ${JSON.stringify(writeBody?.errors ?? '')}`);
      if (!dup && typeof gh.listBlockedBy === 'function') { try { dup = (await collectPaginated(p => gh.listBlockedBy(dependent, p))).some(x => canonicalBlockerKey(x, cleanRepo) === blkKey); } catch {} }
      if (!dup) { recordHold(dependent, blocker, 'blocker-write-rejected-422', 422); continue; }
      workingEdges.push({ dependent: depKey, blocker: blkKey }); blkMap.set(blkKey, resolved.issue); liveBlockedBy.set(dependent, blkMap);
      actions.push({ action: 'noop-exists', dependent, blocker, kind, status: 422, idempotent: true }); continue;
    }
    if (writeStatus >= 400) throw errWith(`GitHub addBlockedBy failed with status ${writeStatus}`, { status: writeStatus });
    workingEdges.push({ dependent: depKey, blocker: blkKey }); blkMap.set(blkKey, resolved.issue); liveBlockedBy.set(dependent, blkMap);
    state.managedEdges[eKey] = { dependent, blocker, kind, evidence, declaredBy, addedAt: new Date(afterMs).toISOString(), windowStartMs: beforeMs, windowEndMs: afterMs, eventId: writeBody?.id ?? null, contentHash: hash };
    delete state.autopilotRemovals[eKey]; persist();
    actions.push({ action: 'add', dependent, blocker, kind, evidence });
    addedByDep.set(dependent, [...(addedByDep.get(dependent) ?? []), { blocker, kind, evidence }]);
  }

  const removedByDep = new Map();
  for (const [eKey, managed] of Object.entries({ ...state.managedEdges })) {
    if (!isObj(managed) || (managed.dependent !== subjectNum && managed.blocker !== subjectNum) || candidates.has(eKey)) continue;
    const { dependent, blocker, declaredBy = 'dependent' } = managed, declaringNum = declaredBy === 'blocker' ? blocker : dependent;
    if (unknownBlockedBy.has(dependent)) continue;
    const observed = declaredBy === 'contract' ? Array.isArray(contractDependencies)
      : (declaringNum === subjectNum || (openIndexComplete && issueMap.has(declaringNum) && issueMap.get(declaringNum)?.state !== 'closed'));
    if (!observed) continue;
    const blkMap = liveBlockedBy.get(dependent) ?? new Map(), blkKey = keyOf(cleanRepo, blocker);
    if (!blkMap.has(blkKey)) { if (!dryRun && !state.autopilotRemovals[eKey]) state.humanRemovedEdges[eKey] = new Date(nowMsOf(now)).toISOString(); delete state.managedEdges[eKey]; persist(); continue; }
    const tl = inspectEdgeTimeline(await getTimeline(dependent), blocker, { repo: cleanRepo, autopilotLogins, managedEdge: managed, autopilotRemoval: state.autopilotRemovals[eKey] ?? null, existsInLive: true });
    if (tl.humanOwned) { actions.push({ action: 'skip-human-owned', dependent, blocker }); continue; }
    const beforeMs = nowMsOf(now);
    let remRes = null;
    if (!dryRun && typeof gh.removeBlockedBy === 'function') {
      try { remRes = await gh.removeBlockedBy(dependent, blkMap.get(blkKey) ?? { number: blocker }); const st = statusOf(remRes); if (st >= 400 && st !== 404) throw errWith(`removeBlockedBy failed (${st})`, { status: st }); }
      catch (err) { if (statusOf(err) !== 404) throw err; }
    }
    const afterMs = nowMsOf(now);
    blkMap.delete(blkKey);
    if (!dryRun) { delete state.managedEdges[eKey]; state.autopilotRemovals[eKey] = { at: new Date(afterMs).toISOString(), windowStartMs: beforeMs, windowEndMs: afterMs, eventId: remRes?.id ?? null }; persist(); }
    actions.push({ action: 'remove-stale', dependent, blocker, ...(dryRun ? { dryRun: true } : {}) });
    removedByDep.set(dependent, [...(removedByDep.get(dependent) ?? []), blocker]);
  }
  if (!unknownBlockedBy.has(subjectNum)) {
    for (const [bKey, blk] of (liveBlockedBy.get(subjectNum) ?? new Map()).entries()) {
      const bNum = Number(blk?.number);
      if (bKey === keyOf(cleanRepo, bNum) && !candidates.has(edgeId(subjectNum, bNum)) && !state.managedEdges[edgeId(subjectNum, bNum)]) actions.push({ action: 'skip-human-owned', dependent: subjectNum, blocker: bNum });
    }
  }
  for (const [depNum, items] of addedByDep.entries()) if (await postIdempotentComment({ gh, dependent: depNum, actionKind: 'added', details: { depNum, blockers: items.map(i => i.blocker).sort((a, b) => a - b) }, state, dryRun, secrets, persist,
    lines: [`Autopilot linked native \`blocked_by\` prerequisite(s) on #${depNum}:`, ...items.map(i => `- #${i.blocker} (\`${i.kind}\`): ${i.evidence}`), '- Remove any link manually if it does not apply; Autopilot will respect your removal.'] })) commentsPosted += 1;
  for (const [depNum, blockers] of removedByDep.entries()) {
    const sorted = [...blockers].sort((a, b) => a - b);
    if (await postIdempotentComment({ gh, dependent: depNum, actionKind: 'removed-stale', details: { depNum, blockers: sorted, hash }, state, dryRun, secrets, persist,
      lines: [`Autopilot removed stale Autopilot-added \`blocked_by\` link(s) on #${depNum} after scope changed: ${sorted.map(b => `#${b}`).join(', ')}.`] })) commentsPosted += 1;
  }
  if (stateFile && !dryRun) { if (holds.length === 0 && retriage.length === 0) state.contentHashes[String(subjectNum)] = stateKey; else delete state.contentHashes[String(subjectNum)]; persist(); }
  return { skipped: false, contentHash: hash, actions, holds, retriage, commentsPosted };
}

// ---- Separate Local File-Claim Reservations (cross-process locked, atomic temp+rename, fail-closed, TTL expiry) ----
function normalizeClaimFiles(files) {
  const out = new Set();
  for (const raw of Array.isArray(files) ? files : []) {
    if (typeof raw !== 'string') continue;
    const c = raw.trim().replaceAll('\\', '/').replace(/^(?:\.\/|\/)+/, '').replace(/\/+/g, '/').replace(/\/+$/, '');
    if (c && c !== '.' && c !== '..' && !c.startsWith('../') && !c.includes('/../') && !c.endsWith('/..') && !/[\x00-\x1f\x7f]/.test(c)) out.add(c);
  }
  return [...out].sort();
}
const saveClaims = (fs, file, claims) => writeAtomicPrivate(fs, file, `${JSON.stringify({ version: 1, claims }, null, 2)}\n`);
function loadClaimsStore(fs, stateDir) {
  const { dir, target: file } = safeStateFile(fs, stateDir, 'file-claims.json');
  let rawText, parsed;
  try { rawText = fs.readFileSync(file, 'utf8'); } catch (err) { if (err?.code === 'ENOENT') return { dir, file, claims: [], corrupt: false }; throw err; }
  try { parsed = JSON.parse(rawText); } catch { return { dir, file, claims: [], corrupt: true }; }
  if (!isObj(parsed) || !Array.isArray(parsed.claims)) return { dir, file, claims: [], corrupt: true };
  const valid = parsed.claims.filter(c => isObj(c) && asText(c.owner).trim() && posInt(c.issue) && asText(c.leaseId).trim() && Array.isArray(c.files) && parseMs(c.expiresAt) > 0);
  return { dir, file, claims: valid.length === parsed.claims.length ? valid : [], corrupt: valid.length !== parsed.claims.length };
}
function withLockedClaims(fs, stateDir, now, fn) {
  const { dir } = safeStateFile(fs, stateDir, 'file-claims.json');
  let release = null;
  if (typeof fs?.openSync === 'function') for (let i = 0; i < 300; i++) {
    try { release = acquireRunLock(dir, 'file-claims.lock', { fs }); break; }
    catch (err) { if (err?.code !== 'run_busy' || i === 299) throw err; Atomics.wait(WAIT_BUF, 0, 0, 5); }
  }
  try { return fn(loadClaimsStore(fs, stateDir), nowMsOf(now)); } finally { release?.(); }
}
function findOverlaps(claims, normFiles, nowMs, { excludeOwner = null, excludeIssue = null, excludeLeaseId = null } = {}) {
  const conflicts = [];
  for (const c of claims) {
    if (parseMs(c.expiresAt) <= nowMs) continue;
    if (excludeLeaseId && c.leaseId === excludeLeaseId && (!excludeOwner || c.owner === excludeOwner) && (!excludeIssue || c.issue === excludeIssue)) continue;
    if (!excludeLeaseId && excludeOwner && excludeIssue && c.owner === excludeOwner && c.issue === excludeIssue) continue;
    const overlappingFiles = normFiles.filter(f => c.files.some(cf => pathsOverlap(f, cf)));
    if (overlappingFiles.length > 0) conflicts.push({ owner: c.owner, issue: c.issue, leaseId: c.leaseId, overlappingFiles, acquiredAt: c.acquiredAt, expiresAt: c.expiresAt });
  }
  return conflicts;
}
export function sweepExpiredClaims(stateDir, { now = Date.now, fs = nativeFs } = {}) {
  return withLockedClaims(fs, stateDir, now, ({ file, claims, corrupt }, nowMs) => {
    if (corrupt) throw errWith('Refusing to sweep corrupt file-claims store.', { code: 'corrupt_claims_store' });
    const active = claims.filter(c => parseMs(c.expiresAt) > nowMs), expired = claims.filter(c => parseMs(c.expiresAt) <= nowMs);
    if (expired.length > 0) saveClaims(fs, file, active);
    return { active, expired, sweptCount: expired.length };
  });
}
export function activeFileConflicts(stateDir, { files = [], excludeOwner = null, excludeIssue = null, excludeLeaseId = null, now = Date.now, fs = nativeFs } = {}) {
  const { claims, corrupt } = loadClaimsStore(fs, stateDir);
  if (corrupt) return { hasConflict: true, error: 'corrupt-claims-store', conflicts: [] };
  const conflicts = findOverlaps(claims, normalizeClaimFiles(files), nowMsOf(now), { excludeOwner, excludeIssue, excludeLeaseId });
  return { hasConflict: conflicts.length > 0, conflicts };
}
export function acquireFileClaim(stateDir, { owner, issue, leaseId, files = [], ttlMs = DEFAULT_FILE_CLAIM_TTL_MS, now = Date.now, fs = nativeFs } = {}) {
  const cleanOwner = asText(owner).trim(), cleanLease = asText(leaseId).trim(), normFiles = normalizeClaimFiles(files);
  if (!cleanOwner || !posInt(issue) || !cleanLease || normFiles.length === 0 || !(typeof ttlMs === 'number' && Number.isFinite(ttlMs) && ttlMs > 0)) throw errWith('acquireFileClaim requires owner, positive issue, leaseId, non-empty valid files, and positive ttlMs.', { code: 'invalid_claim' });
  return withLockedClaims(fs, stateDir, now, ({ file, claims, corrupt }, nowMs) => {
    if (corrupt) return { acquired: false, conflict: false, error: 'corrupt-claims-store', conflicts: [], claim: null };
    const active = claims.filter(c => parseMs(c.expiresAt) > nowMs);
    const foreign = active.find(c => c.leaseId === cleanLease && (c.owner !== cleanOwner || c.issue !== issue));
    if (foreign) return { acquired: false, conflict: true, error: 'lease-owner-mismatch', conflicts: [foreign], claim: null };
    const conflicts = findOverlaps(active, normFiles, nowMs, { excludeOwner: cleanOwner, excludeIssue: issue, excludeLeaseId: cleanLease });
    if (conflicts.length > 0) return { acquired: false, conflict: true, conflicts, claim: null };
    const record = { owner: cleanOwner, issue, leaseId: cleanLease, files: normFiles, acquiredAt: new Date(nowMs).toISOString(), expiresAt: new Date(nowMs + ttlMs).toISOString() };
    saveClaims(fs, file, [...active.filter(c => c.leaseId !== cleanLease), record]);
    return { acquired: true, conflict: false, conflicts: [], claim: record };
  });
}
export function releaseFileClaim(stateDir, { owner = null, issue = null, leaseId = null, now = Date.now, fs = nativeFs } = {}) {
  return withLockedClaims(fs, stateDir, now, ({ file, claims, corrupt }, nowMs) => {
    if (corrupt) throw errWith('Refusing to modify corrupt file-claims store.', { code: 'corrupt_claims_store' });
    const kept = [], released = [];
    for (const c of claims) {
      if (parseMs(c.expiresAt) <= nowMs) continue;
      const hit = (leaseId && c.leaseId === leaseId && (!owner || c.owner === owner)) || (!leaseId && owner && posInt(issue) && c.owner === owner && c.issue === issue) || (!leaseId && !owner && posInt(issue) && c.issue === issue);
      (hit ? released : kept).push(c);
    }
    saveClaims(fs, file, kept);
    return { releasedCount: released.length, released, remaining: kept };
  });
}
