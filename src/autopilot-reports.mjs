// Generated from prompts/cli/autopilot-reports.prompt.md (sha256: 6407a130a495b1708a4dc9c7b5a92a22918dc92c3ec513821ddc3c2641c7aa83).
import * as nativeFs from 'node:fs';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { redactSecrets } from './secret-redaction.mjs';

export const REPORT_REPOSITORY = 'promptdriven/pdd';
export const DEFAULT_RUNTIME_REPORT_REPOSITORY = 'promptdriven/prompt-runtime';
export const DEFAULT_DAILY_REPORT_LIMIT = 3;

const DAY = 24 * 60 * 60 * 1000, RECENT = 14 * DAY;
const LOGIN = /^[a-z\d](?:[a-z\d]|-(?=[a-z\d])){0,38}$/i;
const SAFE_VERSION = /^[\w.+-]{1,40}$/;
const SAFE_ID = /^[a-z0-9_.:-]{1,80}$/i;
const LABELS = { runtime: 'pdd:runtime', pdd: 'pdd:autopilot-report' };
const REJECTED_LABEL = /^(?:invalid|wontfix|won't fix)$/i;
const DROP_OWNERS = ['pdd', 'runtime', 'content', 'quota_or_service', 'operator', 'person_decision'];

const slug = value => String(value ?? '').toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '').slice(0, 40);
const longSlug = value => String(value ?? '').toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '').slice(0, 120);
const minor = version => /^(\d+)\.(\d+)/.exec(String(version ?? ''))?.slice(1, 3).join('.') ?? 'unknown';
const known = value => SAFE_VERSION.test(String(value ?? '')) ? String(value) : 'unknown';
const readJson = (fs, file, fallback) => { try { return JSON.parse(fs.readFileSync(file, 'utf8')); } catch { return fallback; } };

function save(fs, file, value) {
  fs.mkdirSync(join(file, '..'), { recursive: true, mode: 0o700 });
  const temp = `${file}.${process.pid}.tmp`;
  fs.writeFileSync(temp, JSON.stringify(value, null, 2) + '\n', { mode: 0o600 });
  fs.renameSync(temp, file);
}

export function reportFingerprint({ kind, component, code, version }) {
  return [slug(kind), slug(component) || 'unknown', slug(code) || 'unknown', minor(version)].join('.');
}
export const reportMarker = fingerprint => `<!-- pdd:autopilot-report:${fingerprint} -->`;

function scrubInline(text, words = []) {
  let value = redactSecrets(String(text ?? ''));
  value = value
    .replace(/\b[A-Z][A-Z0-9_]*(?:TOKEN|KEY|SECRET|PASSWORD|PASS|AUTH|BEARER|COOKIE)\s*=\s*\S+/gi, '[REDACTED]')
    .replace(/(--(?:token|api-key|apikey|secret|password|auth|authorization)(?:=|\s+))\S+/gi, '$1[REDACTED]')
    .replace(/https?:\/\/\S+/gi, '[url]')
    .replace(/[A-Za-z]:\\[\w.\\@+-]+/g, '[path]')
    .replace(/(?:~|\.{0,2})?(?:\/[\w.@+-]+){2,}\/?/g, '[path]');
  for (const word of words.filter(w => typeof w === 'string' && w.length > 2)) value = value.split(word).join('[repository]');
  return value;
}

// Safe text: versions, step, error code, counts and a short redacted tail. Paths, URLs and repository names go.
function safeTail(text, words = []) {
  return scrubInline(text, words).split(/\r?\n/).map(line => line.slice(0, 200)).filter(line => line.trim()).slice(-20).join('\n');
}

function scrubCommand(command, words = []) {
  if (typeof command !== 'string' || !command.trim()) return null;
  const clean = scrubInline(command, words).replace(/\s+/g, ' ').trim().slice(0, 120);
  return clean || null;
}

function scrubSafeId(id, words = []) {
  if (typeof id !== 'string' || !id.trim()) return null;
  const clean = scrubInline(id, words).trim();
  if (!SAFE_ID.test(clean) || /\[(?:REDACTED|url|path|repository)\]/i.test(clean)) return null;
  return clean;
}

function draftFields(draft) {
  const [fpKind = 'unknown', fpComponent = 'unknown', fpCode = 'unknown'] = String(draft?.fingerprint ?? '').split('.');
  return {
    kind: draft?.kind === 'runtime' ? 'runtime' : 'pdd',
    component: slug(draft?.component ?? fpComponent) || 'unknown',
    code: slug(draft?.code ?? fpCode) || 'unknown',
    step: slug(draft?.step) || 'unknown',
    versions: draft?.versions && typeof draft.versions === 'object' ? draft.versions : {},
  };
}

// Rule 1: Real defect filter. Never auto-file quota/credit, auth/login expiry, operator/caller stops,
// maintenance/provider capacity, transient network blips, or repository content / allowed "not run" causes.
const NON_DEFECT_RULES = [
  {
    category: 'quota_or_service',
    owner: 'quota_or_service',
    reason: 'quota-or-credit',
    slugTest: /(?:^|-)(?:quota|rate-limit|ratelimit|usage-limit|billing|credit|credits|out-of-quota|insufficient-quota|429)(?:-|$)/,
    textTest: /\b(?:out of quota|quota exceeded|insufficient[ _-]quota|rate[ _-]limit(?:ed| exceeded)?|usage[ _-]limit|credit balance|out of credits|billing hard limit)\b/i,
  },
  {
    category: 'auth',
    owner: 'quota_or_service',
    reason: 'auth-expiry',
    slugTest: /(?:^|-)(?:auth|authentication|token-expired|expired-token|unauthorized|unauthenticated|login|relogin|401)(?:-|$)/,
    textTest: /\b(?:token expired|authentication failed|401 unauthorized|please log in|login expired|not logged in)\b/i,
  },
  {
    category: 'operator',
    owner: 'operator',
    reason: 'operator-stop',
    slugTest: /(?:^|-)(?:operator-stop|operator|cancelled|canceled|user-stop|caller|caller-stop|aborted|sigint|sigterm)(?:-|$)/,
    textTest: /\b(?:stopped by operator|cancelled by user|canceled by user|operator stop|caller cancelled)\b/i,
  },
  {
    category: 'maintenance',
    owner: 'quota_or_service',
    reason: 'maintenance-or-capacity',
    slugTest: /(?:^|-)(?:maintenance|capacity|overloaded|provider-capacity|model-overloaded)(?:-|$)/,
    textTest: /\b(?:in maintenance|under maintenance|overloaded_error|at capacity|model is overloaded)\b/i,
  },
  {
    category: 'network_blip',
    owner: 'quota_or_service',
    reason: 'transient-network-blip',
    slugTest: /(?:^|-)(?:econnreset|etimedout|enotfound|econnrefused|ehostunreach|enetunreach|eai-again|network-blip|socket-hang-up)(?:-|$)/,
    textTest: /\b(?:ECONNRESET|ETIMEDOUT|ENOTFOUND|EAI_AGAIN|socket hang up)\b/,
  },
  {
    category: 'content',
    owner: 'content',
    reason: 'content-or-not-run',
    slugTest: /(?:^|-)(?:no-story|not-run|unchecked-criteria|story-criterion-mismatch|content|missing-story|repo-content|native-only|no-prompt)(?:-|$)/,
    textTest: null,
  },
];

export function classifyNonDefect(causeOrDraft) {
  if (!causeOrDraft || typeof causeOrDraft !== 'object') return null;
  if (causeOrDraft.operatorStop === true) return { reason: 'operator-stop', category: 'operator', owner: 'operator' };
  const codeTokens = [causeOrDraft.rawCode, causeOrDraft.code, causeOrDraft.reason].map(longSlug).filter(Boolean);
  const sampleText = String(causeOrDraft.text ?? '');
  for (const rule of NON_DEFECT_RULES) {
    const matchedSlug = codeTokens.find(token => rule.slugTest.test(token));
    if (matchedSlug) {
      const reason = rule.category === 'content' ? matchedSlug : rule.reason;
      return { reason, category: rule.category, owner: rule.owner };
    }
    if (rule.textTest && sampleText && rule.textTest.test(sampleText)) {
      return { reason: rule.reason, category: rule.category, owner: rule.owner };
    }
  }
  return null;
}

// Rule 2: Verified owner and scrubbed proof check before auto-filing to GitHub.
export function validateReportDraft(draft, { runtimeRepo = DEFAULT_RUNTIME_REPORT_REPOSITORY, dailyFiledCount = 0, dailyLimit = DEFAULT_DAILY_REPORT_LIMIT } = {}) {
  if (!draft || typeof draft !== 'object') return { ok: false, state: 'draft', reason: 'invalid-draft', targetRepository: REPORT_REPOSITORY };
  const f = draftFields(draft);
  const destination = f.kind === 'runtime' ? (draft.runtimeRepo ?? runtimeRepo ?? DEFAULT_RUNTIME_REPORT_REPOSITORY) : REPORT_REPOSITORY;
  const targetRepository = f.kind === 'runtime' && /^[\w.-]+\/[\w.-]+$/.test(String(destination ?? '')) ? destination : REPORT_REPOSITORY;

  const nonDefect = classifyNonDefect(draft);
  if (nonDefect) return { ok: false, state: 'filtered', ...nonDefect, targetRepository };

  const command = scrubCommand(draft.command, draft.words ?? []);
  const hasConcreteStep = f.step !== 'unknown';
  const isOther = /^other-[0-9a-f]{8}$/.test(f.code);
  if (!hasConcreteStep && !command) {
    return { ok: false, state: 'draft', reason: 'missing-concrete-proof', owner: f.kind, targetRepository };
  }

  const count = Number.isSafeInteger(draft.count) && draft.count > 0 ? draft.count : 1;
  const distinctIssues = Array.isArray(draft.issues) ? new Set(draft.issues).size : 0;
  const distinctHeads = Array.isArray(draft.heads) ? new Set(draft.heads).size : 0;
  const distinctOccurrences = Array.isArray(draft.occurrences) ? draft.occurrences.length : 0;
  const reproduced = draft.reproduced === true;
  const repeated = count >= 2 || distinctIssues >= 2 || distinctHeads >= 2 || distinctOccurrences >= 2;

  if (!reproduced && !repeated) {
    return { ok: false, state: 'draft', reason: 'unverified-single-occurrence', owner: f.kind, targetRepository };
  }
  if (isOther && !reproduced && !command && !hasConcreteStep) {
    return { ok: false, state: 'draft', reason: 'unverified-other-cause', owner: f.kind, targetRepository };
  }
  if (Number.isFinite(dailyLimit) && dailyFiledCount >= dailyLimit) {
    return { ok: false, state: 'draft', reason: 'daily-cap', owner: f.kind, targetRepository };
  }
  return { ok: true, state: 'ready', owner: f.kind, targetRepository };
}

// The public text has fixed fields only (kind, component, code, step, scrubbed command/IDs, versions, count, fingerprint),
// never free-form text. A draft written earlier may lack the fields: its fingerprint KIND.COMPONENT.CODE.MINOR gives the first three.
function publicReport(draft) {
  const f = draftFields(draft);
  const words = Array.isArray(draft.words) ? draft.words : [];
  const command = scrubCommand(draft.command, words);
  const batchId = scrubSafeId(draft.batchId, words);
  const reportId = scrubSafeId(draft.reportId, words);
  const count = Number.isSafeInteger(draft.count) && draft.count > 0 ? draft.count : 1;
  const distinctIssues = Array.isArray(draft.issues) ? new Set(draft.issues).size : 0;
  const distinctHeads = Array.isArray(draft.heads) ? new Set(draft.heads).size : 0;
  const proofParts = [
    ...(draft.reproduced === true ? ['reproduced'] : []),
    ...(distinctIssues >= 2 ? [`${distinctIssues} issues`] : []),
    ...(distinctHeads >= 2 ? [`${distinctHeads} heads`] : []),
  ];
  const name = f.kind === 'runtime' ? 'Runtime' : 'PDD';
  const title = `Autopilot report: ${name} ${f.component} ${f.code} (PDD ${minor(f.versions.pdd)})`;
  const body = [f.code === 'adopt-pdd' ? 'Autopilot changed existing code that no prompt owns (path e, a direct change with a regression test). Please adopt PDD for those modules (the local draft on the Autopilot machine lists them): give each one a prompt and a binding or header.'
    : draft.shipped === true && f.code === 'vector-replay' && f.component === 'autopilot-core' ? 'Autopilot could not run the replay or formal tests of one PR. The PR went on, with that claim marked as not checked in its merge note.'
    : draft.shipped === true ? 'Autopilot shipped one PR with "Runtime: not run" because Runtime could not check it. The job did not wait for a fix.'
    : draft.stopped === true && f.code === 'stop-loop' ? 'Autopilot holds one issue: its own steps or a service stopped 3 jobs of it in 24 hours. The issue gets no strike; Autopilot takes it again after a new engine version or a person\'s comment on it.'
    : draft.stopped === true ? 'Autopilot stopped one of its own steps for one job: it made no progress. The issue gets no strike, and Autopilot tries again later.'
    : `Autopilot ended one job because of a ${name} problem. The job did not wait for a fix.`, '',
    `- Kind: ${f.kind}`, `- Component: ${f.component}`, `- Error code: ${f.code}`, `- Step: ${f.step}`,
    ...(command ? [`- Command: ${command}`] : []),
    ...(batchId ? [`- Runtime batch: ${batchId}`] : []),
    ...(reportId ? [`- Runtime report: ${reportId}`] : []),
    ...(proofParts.length ? [`- Proof: ${proofParts.join(', ')}`] : []),
    `- Versions: PDD ${known(f.versions.pdd)}, Node ${known(f.versions.node)}, ${known(f.versions.platform)}, agent ${known(f.versions.agent)}`,
    `- Seen on this machine: ${count}`,
    '', 'The detail stays in the local draft on the Autopilot machine.', '', reportMarker(draft.fingerprint)].join('\n');
  return { title, body };
}

function normalizeIssues(cause) {
  const raw = [...(Array.isArray(cause?.issues) ? cause.issues : []), ...(cause?.issue !== undefined ? [cause.issue] : [])];
  return [...new Set(raw.map(Number).filter(n => Number.isSafeInteger(n) && n > 0))];
}

function normalizeHeads(cause) {
  const raw = [...(Array.isArray(cause?.heads) ? cause.heads : []), ...(cause?.head ? [cause.head] : [])];
  return [...new Set(raw.map(h => String(h).trim().toLowerCase()).filter(h => /^[0-9a-f]{7,64}$/.test(h)))];
}

function draftFor({ cause, rawCode, versions, step, words, runtimeRepo, runtimeOwner, now }) {
  const fingerprint = reportFingerprint({ ...cause, version: versions.pdd });
  const kind = cause.kind === 'runtime' ? 'runtime' : 'pdd';
  const command = scrubCommand(cause.command, words);
  const batchId = scrubSafeId(cause.batchId, words);
  const reportId = scrubSafeId(cause.reportId, words);
  const issues = normalizeIssues(cause);
  const heads = normalizeHeads(cause);
  const initialCount = Number.isSafeInteger(cause.count) && cause.count > 0 ? cause.count : 1;
  const occurrences = Array.isArray(cause.occurrences) && cause.occurrences.length
    ? cause.occurrences.slice(-20)
    : [{ at: now, ...(issues[0] ? { issue: issues[0] } : {}), ...(heads[0] ? { head: heads[0] } : {}), ...(slug(step) ? { step: slug(step) } : {}) }];
  const draft = {
    fingerprint,
    kind,
    component: slug(cause.component) || 'unknown',
    code: slug(cause.code) || 'unknown',
    ...(rawCode ? { rawCode: longSlug(rawCode) || 'unknown' } : {}),
    step: slug(step) || 'unknown',
    ...(command ? { command } : {}),
    ...(batchId ? { batchId } : {}),
    ...(reportId ? { reportId } : {}),
    ...(cause.reproduced === true ? { reproduced: true } : {}),
    ...(issues.length ? { issues } : {}),
    ...(heads.length ? { heads } : {}),
    occurrences,
    count: initialCount,
    versions: { pdd: versions.pdd ?? null, node: versions.node ?? null, platform: versions.platform ?? null, agent: versions.agent ?? null },
    ...(cause.shipped === true ? { shipped: true } : {}),
    ...(cause.stopped === true ? { stopped: true } : {}),
    ...(runtimeRepo ? { runtimeRepo } : {}),
    ...(LOGIN.test(String(runtimeOwner ?? '')) ? { runtimeOwner } : {}),
    repository: REPORT_REPOSITORY,
    labels: [LABELS[kind]],
    detail: safeTail(cause.detail || cause.text, words) || '',
  };
  return { ...draft, ...publicReport(draft) };
}

function github(ports) {
  return async (method, endpoint, body) => {
    const args = ['api', '--include', '--method', method, endpoint, ...(body === undefined ? [] : ['--input', '-'])];
    const r = await ports.gh(args, body === undefined ? {} : { input: JSON.stringify(body) });
    const text = String(r.stdout ?? ''), cut = text.search(/\r?\n\r?\n/), status = Number(/^HTTP\/\S+\s+(\d+)/.exec(text)?.[1] ?? 0);
    if (status < 200 || status >= 300) throw Error(`GitHub ${method} returned ${status || 'no reply'}`);
    return { value: cut >= 0 && text.slice(cut).trim() ? JSON.parse(text.slice(cut).trim()) : null, next: /<https:\/\/api\.github\.com\/([^>]+)>;\s*rel="next"/.exec(text.slice(0, Math.max(cut, 0)))?.[1] };
  };
}

function isRejectedIssue(row) {
  if (String(row?.state_reason ?? '').toLowerCase() === 'not_planned') return 'closed-not-planned';
  const labels = Array.isArray(row?.labels) ? row.labels : [];
  if (labels.some(l => REJECTED_LABEL.test(typeof l === 'string' ? l : String(l?.name ?? '')))) return 'labeled-invalid';
  return null;
}

function issueMatchesCause(row, draft) {
  if (!row || row.pull_request) return false;
  const f = draftFields(draft);
  const name = f.kind === 'runtime' ? 'Runtime' : 'PDD';
  const body = String(row.body ?? '');
  const title = String(row.title ?? '');
  const exactMarker = reportMarker(draft.fingerprint);
  const crossVersionMarker = `<!-- pdd:autopilot-report:${f.kind}.${f.component}.${f.code}.`;
  const titlePrefix = `Autopilot report: ${name} ${f.component} ${f.code} (`;
  if (body.includes(exactMarker) || body.includes(crossVersionMarker)) return true;
  if (title.startsWith(titlePrefix)) return true;
  return body.includes(`- Kind: ${f.kind}`) && body.includes(`- Component: ${f.component}`) && body.includes(`- Error code: ${f.code}`);
}

// Rule 3: Live duplicate check across versions (open issues first, then rejected closures, then <14d closed issues).
async function findReport(api, draft, now) {
  let endpoint = `repos/${draft.repository}/issues?state=all&labels=${encodeURIComponent(draft.labels[0])}&per_page=100`;
  const matches = [];
  for (let page = 0; endpoint && page < 5; page++) {
    const { value, next } = await api('GET', endpoint);
    for (const row of value ?? []) if (issueMatchesCause(row, draft)) matches.push(row);
    const openMatch = matches.find(row => row.state === 'open');
    if (openMatch) return { row: openMatch, rejected: isRejectedIssue(openMatch) };
    endpoint = next;
  }
  const rejectedClosed = matches.find(row => row.state === 'closed' && isRejectedIssue(row));
  if (rejectedClosed) return { row: rejectedClosed, rejected: isRejectedIssue(rejectedClosed) };
  const recentClosed = matches.find(row => row.state === 'closed' && now - Date.parse(row.closed_at) < RECENT);
  if (recentClosed) return { row: recentClosed, rejected: null };
  return null;
}

// The owner repository: a Runtime cause goes to the configured Runtime repository when this machine can read it,
// else to promptdriven/pdd with label pdd:runtime. A PDD cause always goes to promptdriven/pdd.
async function ownerRepository(api, draft, runtimeRepo) {
  if (draft.kind !== 'runtime' || !/^[\w.-]+\/[\w.-]+$/.test(String(runtimeRepo ?? ''))) return REPORT_REPOSITORY;
  try { await api('GET', `repos/${runtimeRepo}`); return runtimeRepo; } catch { return REPORT_REPOSITORY; }
}

function seenLedgerKey(draft) {
  const f = draftFields(draft);
  const ver = known(f.versions.pdd);
  return `${f.kind}.${f.component}.${f.code}@${ver}`;
}

// Send one report through owner, rejection, cross-version dedup and daily-cap rules.
async function sendDraft(draft, { root, machine, runtimeRepo, runtimeOwner = null, limit = true, dailyLimit = Infinity }, ports) {
  const fs = ports.fs ?? nativeFs, now = (ports.now ?? Date.now)(), api = github(ports), file = join(root, 'ledger.json');
  const ledger = readJson(fs, file, { filed: [], seen: {} });
  ledger.filed = Array.isArray(ledger.filed) ? ledger.filed : [];
  ledger.seen = ledger.seen && typeof ledger.seen === 'object' ? ledger.seen : {};
  const destination = runtimeRepo ?? draft.runtimeRepo;
  const repository = await ownerRepository(api, draft, destination);
  const ownerLogin = runtimeOwner ?? draft.runtimeOwner;
  // An assignee only when the operator configured one for the Runtime repository that receives the report.
  const assignees = draft.kind === 'runtime' && repository === destination && LOGIN.test(String(ownerLogin ?? '')) ? [ownerLogin] : [];
  draft = { ...draft, repository, labels: [LABELS[draft.kind === 'runtime' ? 'runtime' : 'pdd']], assignees };
  const ref = number => `${draft.repository}#${number}`;

  const match = await findReport(api, draft, now);
  if (match) {
    const { row: found, rejected } = match;
    if (rejected) {
      return { state: 'needs-person', reason: rejected, number: found.number, id: found.id, ref: ref(found.number) };
    }
    const f = draftFields(draft);
    const versionKey = seenLedgerKey(draft);
    const ver = known(f.versions.pdd);
    const lastSeen = Math.max(
      ledger.seen[versionKey] ?? -Infinity,
      ver === 'unknown' ? (ledger.seen[draft.fingerprint] ?? -Infinity) : -Infinity,
    );
    if (now - lastSeen < DAY) return { state: 'counted', number: found.number, id: found.id, ref: ref(found.number) };
    const count = Number.isSafeInteger(draft.count) && draft.count > 0 ? draft.count : 1;
    const versionNote = ver !== 'unknown' ? ` (PDD ${ver}, count ${count})` : '';
    await api('POST', `repos/${draft.repository}/issues/${found.number}/comments`, {
      body: `Seen again on one more Autopilot machine run${versionNote} at ${new Date(now).toISOString()}.\n\n${reportMarker(draft.fingerprint)}`,
    });
    ledger.seen[versionKey] = now;
    if (ver === 'unknown') ledger.seen[draft.fingerprint] = now;
    save(fs, file, ledger);
    return { state: 'seen', number: found.number, id: found.id, ref: ref(found.number) };
  }

  const recentFiled = ledger.filed.filter(row => now - row.at < DAY);
  if (Number.isFinite(dailyLimit) && recentFiled.length >= dailyLimit) return { state: 'limit', reason: 'daily-cap' };
  // A cause with no known code ("other-…") files at most one new report per machine per day; the rest stay drafts.
  if (limit && /\.other-[0-9a-f]{8}\./.test(draft.fingerprint) && recentFiled.some(row => /\.other-/.test(row.fingerprint))) {
    return { state: 'limit', reason: 'other-daily-cap' };
  }
  const { title, body } = publicReport(draft);
  const { value } = await api('POST', `repos/${draft.repository}/issues`, { title, body, labels: draft.labels, assignees: draft.assignees });
  ledger.filed = [...recentFiled, { fingerprint: draft.fingerprint, number: value.number, at: now }];
  save(fs, file, ledger);
  return { state: 'filed', number: value.number, id: value.id, ref: ref(value.number) };
}

function mergeDraftRecord(old, draft, now) {
  const oldCount = Number.isSafeInteger(old?.count) && old.count > 0 ? old.count : 0;
  const incomingCount = Number.isSafeInteger(draft.count) && draft.count > 0 ? draft.count : 1;
  const count = old ? oldCount + 1 : incomingCount;
  const issues = [...new Set([...(Array.isArray(old?.issues) ? old.issues : []), ...(Array.isArray(draft.issues) ? draft.issues : [])])].slice(-50);
  const heads = [...new Set([...(Array.isArray(old?.heads) ? old.heads : []), ...(Array.isArray(draft.heads) ? draft.heads : [])])].slice(-50);
  const occurrences = [...(Array.isArray(old?.occurrences) ? old.occurrences : []), ...(Array.isArray(draft.occurrences) ? draft.occurrences : [])].slice(-20);
  const kept = {
    ...(old ?? {}),
    ...draft,
    rawCode: draft.rawCode && draft.rawCode !== 'unknown' ? draft.rawCode : (old?.rawCode ?? draft.code),
    ...(draft.command || old?.command ? { command: draft.command || old.command } : {}),
    ...(draft.batchId || old?.batchId ? { batchId: draft.batchId || old.batchId } : {}),
    ...(draft.reportId || old?.reportId ? { reportId: draft.reportId || old.reportId } : {}),
    ...(old?.reproduced || draft.reproduced ? { reproduced: true } : {}),
    ...(issues.length ? { issues } : {}),
    ...(heads.length ? { heads } : {}),
    ...(occurrences.length ? { occurrences } : {}),
    count,
    firstAt: old?.firstAt ?? now,
    lastAt: now,
  };
  return { ...kept, ...publicReport(kept) };
}

function keepDraft(fs, root, draft, now) {
  const file = join(root, 'drafts', `${draft.fingerprint}.json`), old = readJson(fs, file, null);
  const merged = mergeDraftRecord(old, draft, now);
  save(fs, file, merged);
  return merged;
}

function removeDraftIfPresent(fs, root, fingerprint) {
  try { fs.unlinkSync(join(root, 'drafts', `${fingerprint}.json`)); } catch { /* absent */ }
}

// The owner of a cause (Serhan's boundary): everything that goes INTO Runtime is PDD's (prompts, interface blocks,
// bindings, Stories, test vectors, tests, up to the call), so a refusal of our input (interface, binding, lint), a
// scenario value limit, a vector replay or a Runtime case is kind pdd. Kind runtime is only what happens inside Runtime
// after the call: no verdict, an interpreter error, server incompatibility, a server-side internal error.
const PDD_OWNED = /scenario|vector|replay|safe-integer|integer-out-of-range|runtime-case|test-case/;
export function reportKind(cause) {
  if (cause?.kind !== 'runtime') return cause?.kind;
  return PDD_OWNED.test(`${slug(cause.component)} ${slug(cause.code)}`) || !RUNTIME_CODES.has(stableCode(cause.code)) ? 'pdd' : 'runtime';
}
// Stable fingerprints: an agent writes the code and the component as free text, so each is mapped to a fixed word.
const CODES = [['merge-check-tool', /^merge-check-tool$/], ['suite-broken', /^suite-broken$/], ['adopt-pdd', /^adopt-pdd$/], ['no-verdict', /verdict/], ['maintenance', /maintenance/],
  ['scenario-limit', /scenario|safe-integer|integer-out-of-range|out-of-range/], ['vector-replay', /vector|replay/], ['runtime-case', /runtime-case|test-case/],
  ['lint-refusal', /lint/], ['interface-refusal', /interface/], ['binding-refusal', /binding/], ['input-refusal', /refus|reject/], ['interpreter-error', /interpreter/],
  ['server-internal', /server-internal|internal-server|server-error|(?:^|-)5\d\d(?:-|$)|unavailable|bad-gateway/], ['server-incompatible', /server|compat/], ['crash', /crash|panic|segfault|exception/], ['claim-error', /claim/], ['not-run', /not-run/],
  ['base-check', /^base-check$/], ['step-quiet', /^step-quiet$/], ['stop-loop', /^stop-loop$/], ['timeout', /timeout|timed-out/], ['cli-error', /cli|command|usage|exit|failed|error/]];
// An unknown code is other-HASH of the step and the error class (the code slug with no digits) only, never of the
// agent's text, so one cause is one report; at most one new "other" report per machine per day.
export const stableCode = (code, step = '') => CODES.find(([, test]) => test.test(slug(code)))?.[0]
  ?? `other-${createHash('sha256').update(`${slug(step)}:${slug(code).replace(/\d+/g, '')}`).digest('hex').slice(0, 8)}`;
// Runtime kind is only what happens inside Runtime; every other cause (a refusal of our input, scenario limits, test
// vectors, the pdd command, the core) is a PDD report.
export const RUNTIME_CODES = new Set(['no-verdict', 'maintenance', 'interpreter-error', 'server-incompatible', 'server-internal']);
const COMPONENTS = [['autopilot-core', /autopilot|core/], ['pdd-lint', /lint/], ['pdd-approve', /approve/], ['pdd-workflow', /workflow/],
  ['pdd-test', /test|runtime|interpreter|verdict|scenario|vector/], ['pdd', /pdd/], ['agent', /agent|codex|claude/]];
export const stableComponent = component => COMPONENTS.find(([, test]) => test.test(slug(component)))?.[0] ?? 'other';

// File, count, filter or keep one report for a Runtime or PDD cause. It never throws: a failed send keeps a local draft.
export async function fileReport(
  { cause, mode, validate = false, dailyLimit = DEFAULT_DAILY_REPORT_LIMIT, root, machine, versions = {}, step, words = [], runtimeRepo = null, runtimeOwner = null },
  ports = {},
) {
  if (!['runtime', 'pdd'].includes(cause?.kind) || mode === 'off') return { state: 'off' };
  const validated = mode === 'validated' || (mode === 'file' && validate === true);
  const rawCode = cause?.code;
  const nonDefect = classifyNonDefect(cause);
  const normalized = { ...cause, kind: reportKind(cause), code: stableCode(cause.code, step), component: stableComponent(cause.component) };
  const effectiveRuntimeRepo = validated ? (runtimeRepo ?? DEFAULT_RUNTIME_REPORT_REPOSITORY) : runtimeRepo;
  const fs = ports.fs ?? nativeFs, now = (ports.now ?? Date.now)();
  const draft = draftFor({ cause: normalized, rawCode, versions, step, words, runtimeRepo: effectiveRuntimeRepo, runtimeOwner, now });

  if (mode === 'draft') {
    keepDraft(fs, root, draft, now);
    return { state: 'draft', fingerprint: draft.fingerprint };
  }

  if (nonDefect) {
    const legacyAllowedContent = !validated && nonDefect.category === 'content' && /^(?:no-story|not-run)$/.test(longSlug(rawCode));
    if (!legacyAllowedContent) {
      return { state: 'filtered', ...nonDefect, fingerprint: draft.fingerprint };
    }
  }

  if (validated) {
    const existing = readJson(fs, join(root, 'drafts', `${draft.fingerprint}.json`), null);
    const candidate = mergeDraftRecord(existing, draft, now);
    const verdict = validateReportDraft(candidate, { runtimeRepo: effectiveRuntimeRepo, dailyFiledCount: 0, dailyLimit });
    if (verdict.state === 'filtered') return { state: 'filtered', reason: verdict.reason, category: verdict.category, owner: verdict.owner, fingerprint: draft.fingerprint };
    if (!verdict.ok) {
      save(fs, join(root, 'drafts', `${draft.fingerprint}.json`), candidate);
      return { state: 'draft', reason: verdict.reason, fingerprint: draft.fingerprint };
    }
    try {
      const sent = await sendDraft(candidate, { root, machine, runtimeRepo: effectiveRuntimeRepo, runtimeOwner, dailyLimit }, ports);
      if (sent.state === 'needs-person') {
        save(fs, join(root, 'drafts', `${draft.fingerprint}.json`), { ...candidate, status: 'needs-person', statusReason: sent.reason });
        return { ...sent, fingerprint: draft.fingerprint };
      }
      if (sent.state !== 'limit') {
        removeDraftIfPresent(fs, root, draft.fingerprint);
        return { ...sent, fingerprint: draft.fingerprint };
      }
      save(fs, join(root, 'drafts', `${draft.fingerprint}.json`), candidate);
      return { state: 'draft', reason: sent.reason ?? 'daily-cap', fingerprint: draft.fingerprint };
    } catch (error) {
      ports.warn?.(`Autopilot report kept as a local draft: ${error.message}`);
      save(fs, join(root, 'drafts', `${draft.fingerprint}.json`), candidate);
      return { state: 'draft', fingerprint: draft.fingerprint };
    }
  }

  if (mode === 'file') {
    try {
      const sent = await sendDraft(draft, { root, machine, runtimeRepo }, ports);
      if (sent.state === 'needs-person') {
        keepDraft(fs, root, { ...draft, status: 'needs-person', statusReason: sent.reason }, now);
        return { ...sent, fingerprint: draft.fingerprint };
      }
      if (sent.state !== 'limit') return { ...sent, fingerprint: draft.fingerprint };
    } catch (error) { ports.warn?.(`Autopilot report kept as a local draft: ${error.message}`); }
  }
  keepDraft(fs, root, draft, now);
  return { state: 'draft', fingerprint: draft.fingerprint };
}

export async function autoFileValidatedReports(
  { root, machine, runtimeRepo = DEFAULT_RUNTIME_REPORT_REPOSITORY, runtimeOwner = null, dailyLimit = DEFAULT_DAILY_REPORT_LIMIT },
  ports = {},
) {
  const fs = ports.fs ?? nativeFs;
  const drafts = listReportDrafts({ root }, ports);
  const results = [];
  for (const draft of drafts) {
    const verdict = validateReportDraft(draft, { runtimeRepo, dailyFiledCount: 0, dailyLimit });
    if (verdict.state === 'filtered') {
      results.push({ fingerprint: draft.fingerprint, state: 'filtered', reason: verdict.reason, category: verdict.category, owner: verdict.owner });
      continue;
    }
    if (!verdict.ok) {
      results.push({ fingerprint: draft.fingerprint, state: 'draft', reason: verdict.reason });
      continue;
    }
    try {
      const sent = await sendDraft(draft, { root, machine, runtimeRepo: draft.runtimeRepo ?? runtimeRepo, runtimeOwner: draft.runtimeOwner ?? runtimeOwner, dailyLimit }, ports);
      if (sent.state === 'needs-person') {
        save(fs, join(root, 'drafts', `${draft.fingerprint}.json`), { ...draft, status: 'needs-person', statusReason: sent.reason });
        results.push({ ...sent, fingerprint: draft.fingerprint });
      } else if (sent.state === 'limit') {
        results.push({ fingerprint: draft.fingerprint, state: 'draft', reason: sent.reason ?? 'daily-cap' });
      } else {
        removeDraftIfPresent(fs, root, draft.fingerprint);
        results.push({ ...sent, fingerprint: draft.fingerprint });
      }
    } catch (error) {
      ports.warn?.(`Autopilot report kept as a local draft: ${error.message}`);
      results.push({ fingerprint: draft.fingerprint, state: 'draft', reason: 'github-error' });
    }
  }
  return {
    results,
    filed: results.filter(r => r.state === 'filed'),
    seen: results.filter(r => r.state === 'seen'),
    counted: results.filter(r => r.state === 'counted'),
    filtered: results.filter(r => r.state === 'filtered'),
    needsPerson: results.filter(r => r.state === 'needs-person'),
    drafts: results.filter(r => r.state === 'draft'),
  };
}

export function listReportDrafts({ root }, ports = {}) {
  const fs = ports.fs ?? nativeFs, folder = join(root, 'drafts');
  let names = [];
  try { names = fs.readdirSync(folder).filter(name => name.endsWith('.json')).sort(); } catch { return []; }
  return names.map(name => readJson(fs, join(folder, name), null)).filter(Boolean);
}

export async function sendReportDraft({ root, fingerprint, machine, runtimeRepo = null }, ports = {}) {
  const fs = ports.fs ?? nativeFs, file = join(root, 'drafts', `${fingerprint}.json`), draft = readJson(fs, file, null);
  if (!draft || draft.fingerprint !== fingerprint) return { exitCode: 1, message: `No local report draft ${fingerprint}. Run pdd autopilot report to list drafts.` };
  try {
    const sent = await sendDraft(draft, { root, machine, runtimeRepo: runtimeRepo ?? draft.runtimeRepo, limit: false, dailyLimit: Infinity }, ports);
    if (sent.state === 'needs-person') {
      return { exitCode: 1, state: 'needs-person', message: `Report ${sent.ref} was closed as not planned or marked invalid; human review required. The draft stays.` };
    }
    fs.unlinkSync(file);
    return { exitCode: 0, state: sent.state, message: `${sent.state === 'filed' ? 'Filed' : 'Counted on'} ${sent.ref}.` };
  } catch (error) { return { exitCode: 1, message: `Report not sent: ${error.message}. The draft stays.` }; }
}

function stageRatio(numerator, denominator) {
  return {
    numerator,
    denominator,
    rate: denominator > 0 ? Number((numerator / denominator).toFixed(4)) : null,
  };
}

function classifyDropOwner(run) {
  if (DROP_OWNERS.includes(run?.owner)) return run.owner;
  const outcome = longSlug(run?.outcome ?? run?.status ?? '');
  const code = longSlug(run?.cause?.rawCode ?? run?.cause?.code ?? run?.reason ?? run?.code ?? outcome);
  if (
    run?.needsDecision === true
    || /^(?:question|ask|needs-decision|person-decision|human-review|awaiting-review|strict-approval|scope-choice|unclear-spec|ambiguous)$/.test(outcome)
    || /^(?:question|ask|needs-decision|person-decision|human-review|awaiting-review|strict-approval|scope-choice|unclear-spec|ambiguous)$/.test(code)
  ) {
    return 'person_decision';
  }
  const nonDefect = classifyNonDefect({
    rawCode: code,
    code: run?.cause?.code ?? run?.code,
    reason: run?.reason ?? outcome,
    text: run?.cause?.text ?? run?.text ?? '',
    operatorStop: run?.operatorStop === true,
  });
  if (nonDefect) return nonDefect.owner;
  const kind = reportKind({ kind: run?.cause?.kind ?? run?.kind ?? 'pdd', component: run?.cause?.component ?? run?.component ?? '', code });
  return kind === 'runtime' ? 'runtime' : 'pdd';
}

// Deterministic JSON summary helper for stats-branch daily conversion-drop logging (#3361).
export function summarizeConversionDrops({
  runs = [],
  backlogCount = null,
  claimableCount = null,
  claimedCount = null,
  clearSpecCount = null,
  prOpenedCount = null,
  mergedOrWouldMergeCount = null,
  drafts = [],
  filed = [],
  filtered = [],
  date = null,
} = {}) {
  const validRuns = Array.isArray(runs) ? runs.filter(r => r && typeof r === 'object') : [];
  const claimedRuns = validRuns.filter(r => r.claimed !== false);
  const hasPr = r => typeof r.prOpened === 'boolean' ? r.prOpened
    : Boolean(r.pr || r.prNumber || r.merged || r.wouldMerge || /^(?:merged|would-merge|pr-opened)$/.test(longSlug(r.outcome ?? r.status ?? '')));
  const isMergedOrWm = r => Boolean(r.merged || r.wouldMerge || /^(?:merged|would-merge)$/.test(longSlug(r.outcome ?? r.status ?? '')));
  const hasClearSpec = r => {
    if (typeof r.clearSpec === 'boolean') return r.clearSpec;
    if (hasPr(r) || isMergedOrWm(r)) return true;
    const tag = longSlug(r.reason ?? r.cause?.rawCode ?? r.cause?.code ?? r.outcome ?? r.status ?? '');
    if (r.needsDecision === true || /^(?:question|ask|needs-decision|unclear-spec|ambiguous|no-story|missing-story|story-criterion-mismatch|unchecked-criteria)$/.test(tag)) {
      return false;
    }
    return true;
  };

  const backlog = Number.isSafeInteger(backlogCount) && backlogCount >= 0 ? backlogCount : validRuns.length;
  const claimable = Number.isSafeInteger(claimableCount) && claimableCount >= 0 ? claimableCount : claimedRuns.length;
  const claimed = Number.isSafeInteger(claimedCount) && claimedCount >= 0 ? claimedCount : claimedRuns.length;
  const clearSpec = Number.isSafeInteger(clearSpecCount) && clearSpecCount >= 0 ? clearSpecCount : claimedRuns.filter(hasClearSpec).length;
  const prOpened = Number.isSafeInteger(prOpenedCount) && prOpenedCount >= 0 ? prOpenedCount : claimedRuns.filter(r => hasClearSpec(r) && hasPr(r)).length;
  const mergedOrWouldMerge = Number.isSafeInteger(mergedOrWouldMergeCount) && mergedOrWouldMergeCount >= 0
    ? mergedOrWouldMergeCount
    : claimedRuns.filter(r => hasPr(r) && isMergedOrWm(r)).length;

  const dropsByOwner = Object.fromEntries(DROP_OWNERS.map(owner => [owner, { count: 0, causes: {}, issues: [] }]));
  let dropped = 0;
  for (const run of claimedRuns) {
    if (isMergedOrWm(run)) continue;
    dropped += 1;
    const owner = classifyDropOwner(run);
    const rawCause = longSlug(run?.cause?.rawCode ?? run?.cause?.code ?? run?.reason ?? run?.code ?? run?.outcome ?? run?.status ?? '') || 'unknown';
    const bucket = dropsByOwner[owner];
    bucket.count += 1;
    bucket.causes[rawCause] = (bucket.causes[rawCause] ?? 0) + 1;
    const issueNum = Number(run?.issue);
    if (Number.isSafeInteger(issueNum) && issueNum > 0 && !bucket.issues.includes(issueNum)) bucket.issues.push(issueNum);
  }
  for (const owner of DROP_OWNERS) dropsByOwner[owner].issues.sort((a, b) => a - b);

  const reportItems = [
    ...(Array.isArray(filed) ? filed : []),
    ...(Array.isArray(filtered) ? filtered : []),
    ...(Array.isArray(drafts) ? drafts.map(d => ({ ...d, state: d.status === 'needs-person' ? 'needs-person' : (d.state ?? 'draft') })) : []),
    ...validRuns.map(r => r.report).filter(r => r && typeof r === 'object'),
  ];

  const verifiedByKey = new Map();
  const pendingByKey = new Map();
  const filteredByKey = new Map();

  for (const item of reportItems) {
    const fp = typeof item.fingerprint === 'string' && item.fingerprint ? item.fingerprint : 'unknown';
    const f = draftFields(item);
    if (item.state === 'filed' || item.state === 'seen' || item.state === 'counted') {
      verifiedByKey.set(`${fp}:${item.ref ?? ''}`, {
        fingerprint: fp,
        state: item.state,
        ref: item.ref ?? null,
        number: Number.isSafeInteger(item.number) ? item.number : null,
        kind: f.kind,
        component: f.component,
        code: f.code,
      });
      continue;
    }
    const nonDefect = item.state === 'filtered'
      ? { reason: item.reason ?? 'filtered', category: item.category ?? 'noise', owner: item.owner ?? 'quota_or_service' }
      : classifyNonDefect(item);
    if (nonDefect) {
      filteredByKey.set(`${fp}:${nonDefect.reason}`, {
        fingerprint: fp,
        reason: slug(nonDefect.reason) || 'filtered',
        category: nonDefect.category,
        owner: nonDefect.owner,
        code: slug(item.rawCode ?? f.code) || 'unknown',
      });
      continue;
    }
    pendingByKey.set(fp, {
      fingerprint: fp,
      state: item.state === 'needs-person' ? 'needs-person' : 'draft',
      reason: item.reason ?? item.statusReason ?? null,
      kind: f.kind,
      component: f.component,
      code: f.code,
      count: Number.isSafeInteger(item.count) && item.count > 0 ? item.count : 1,
    });
  }

  return {
    date: typeof date === 'string' && date ? date : null,
    totals: {
      backlog,
      claimable,
      claimed,
      clearSpec,
      prOpened,
      mergedOrWouldMerge,
      dropped,
    },
    stages: {
      backlogToClaimable: stageRatio(claimable, backlog),
      claimedToClearSpec: stageRatio(clearSpec, claimed),
      clearSpecToPrOpened: stageRatio(prOpened, clearSpec),
      prOpenedToMergedOrWouldMerge: stageRatio(mergedOrWouldMerge, prOpened),
    },
    dropsByOwner,
    reports: {
      verifiedIssues: [...verifiedByKey.values()],
      pendingDrafts: [...pendingByKey.values()],
      filteredNoise: [...filteredByKey.values()],
    },
  };
}
