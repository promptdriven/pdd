// Layer-2 Pillar 2B daily read-only 4-bucket Ladder-of-Fixes investigator.
import { createHash } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { join, resolve } from 'node:path';
import { redactSecrets } from '../../secret-redaction.mjs';
import { assertSafePrivateDir, isPathAtOrInside, readJsonObjectQuiet, writeAtomicPrivate } from '../../shared/atomic-fs.mjs';
import { DEFAULT_STANDUP_TIMEZONE, localDateParts } from '../metrics/funnel-cohort.mjs';

export const INVESTIGATOR_SCHEMA = 'pdd.autopilot.investigator.v1';
export const INVESTIGATOR_MARKER_PREFIX = '<!-- pdd:investigator:v1:';
export const INVESTIGATOR_BUCKETS = Object.freeze(['orchestrator', 'agent-quality', 'environment', 'real-hold']);
export const LADDER_OF_FIXES = Object.freeze(['architecture-api', 'lint-checker', 'runtime-proof', 'skill-prose']);
export const LADDER_RANK = Object.freeze({ 'architecture-api': 1, 'lint-checker': 2, 'runtime-proof': 3, 'skill-prose': 4 });
export const DEFAULT_MAX_ISSUES_PER_RUN = 5;

const DATE_RE = /^\d{4}-\d{2}-\d{2}$/;
const isObj = v => v !== null && typeof v === 'object' && !Array.isArray(v), asText = v => (typeof v === 'string' ? v : ''), posInt = v => Number.isSafeInteger(v) && v > 0;
const nowMsOf = now => (typeof now === 'function' ? now() : now), toSet = v => (v instanceof Set ? new Set(v) : new Set(Array.isArray(v) ? v : (isObj(v) ? Object.keys(v) : [])));
const sortFindings = (a, b) => (a.proposal?.rank ?? 9) - (b.proposal?.rank ?? 9) || b.occurrences - a.occurrences || a.fingerprint.localeCompare(b.fingerprint);
const defangMentions = text => text.replace(/(?<![\w`/])@([a-zA-Z0-9][a-zA-Z0-9_-]{0,38})\b/g, '`@$1`');
const safeSnippet = (value, { max = 360, secrets = [] } = {}) => defangMentions(redactSecrets(asText(value), secrets).replace(/[\r\n\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f]/g, ' ').replace(/\s+/g, ' ').trim()).slice(0, max);
const sanitizeCode = (raw, secrets = []) => redactSecrets(asText(raw), secrets).replace(/\[redacted\]/gi, '').toLowerCase().replace(/[_\s./]+/g, '-').replace(/[^a-z0-9-]+/g, '').replace(/-+/g, '-').replace(/^-|-$/g, '').slice(0, 64) || null;
const normalizeSignatureText = (raw, secrets = []) => safeSnippet(raw, { max: 200, secrets }).toLowerCase()
  .replace(/\b\d{4}-\d{2}-\d{2}t\d{2}:\d{2}:\d{2}(?:\.\d+)?z\b/g, '<ts>')
  .replace(/\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b/g, '<uuid>')
  .replace(/\b(?:run|job|attempt|build|trace)[_-]?(?:id)?[=:\s#]+[a-z0-9_-]+\b/g, '<run>')
  .replace(/\bpid[=:\s]+\d+\b/g, 'pid=<n>').replace(/\b[0-9a-f]{7,40}\b/g, '<sha>')
  .replace(/\b\d+(?:\.\d+)?\s*(?:ms|s|sec|secs|seconds|m|min|mins|minutes)\b/g, '<dur>')
  .replace(/(?:\b(?:pr|issue)\s+)?#[1-9]\d*\b/g, '<ref>').replace(/\/(?:tmp|var\/folders|private\/var\/folders)\/[^\s'"]+/g, '<tmp>').replace(/\s+/g, ' ').trim();
const incidentFreeText = inc => [inc?.title, inc?.reason, inc?.summary, inc?.detail, inc?.error, inc?.stderr, inc?.snippet].map(asText).filter(Boolean).join(' ').toLowerCase();

// Canonical structured code table (checked strictly BEFORE free-text heuristics).
const STRUCTURED_CODES = new Map([
  ...[['real-hold', 'real-hold'], ['protected-path', 'protected-path'], ['codeowners-hold', 'protected-path'], ['human-decision', 'human-decision'],
    ['needs-decision', 'human-decision'], ['needs-person', 'human-decision'], ['policy-decision', 'human-decision'], ['unclear-or-unsound', 'unclear-or-unsound'],
    ['cross-repo', 'cross-repo'], ['needs-other-repo', 'cross-repo'], ['unverifiable-boundary', 'unverifiable-boundary'], ['blocker-closed-not-planned', 'not-planned-retriage'],
    ['re-triage-not-planned', 'not-planned-retriage'], ['not-planned-retriage', 'not-planned-retriage'], ['blocker-unavailable-404', 'blocker-unavailable-404'],
    ['duplicate', 'duplicate'], ['assigned-to-human', 'assigned-to-human']].map(([k, v]) => [k, ['real-hold', v]]),
  ...[['environment', 'flaky-infra'], ['missing-capability', 'missing-capability'], ['missing-capacity', 'missing-capability'], ['no-worker-slot', 'missing-capability'],
    ['quota', 'quota-or-rate-limit'], ['quota-exhausted', 'quota-or-rate-limit'], ['quota-or-rate-limit', 'quota-or-rate-limit'], ['rate-limit', 'quota-or-rate-limit'],
    ['rate-limited', 'quota-or-rate-limit'], ['auth-expired', 'auth-expired'], ['token-expired', 'auth-expired'], ['login-exhausted', 'auth-expired'],
    ['sigterm', 'runner-sigterm'], ['runner-sigterm', 'runner-sigterm'], ['sigkill', 'runner-oom'], ['oom', 'runner-oom'], ['runner-oom', 'runner-oom'],
    ['flaky-infra', 'flaky-infra'], ['ci-infra', 'flaky-infra'], ['suspect-ci', 'flaky-infra'], ['flaked-then-passed', 'flaky-infra'],
    ['base-test-red', 'flaky-infra'], ['github-unavailable', 'flaky-infra'], ['network-timeout', 'flaky-infra']].map(([k, v]) => [k, ['environment', v]]),
  ...[['orchestrator', 'orchestrator-bug'], ['orchestrator-bug', 'orchestrator-bug'], ['harness', 'harness-bug'], ['harness-bug', 'harness-bug'],
    ['lease-expired', 'lease-expired'], ['lease-bug', 'lease-bug'], ['claim-collision', 'claim-collision'], ['lock-timeout', 'lock-timeout'],
    ['state-corrupt', 'state-corrupt'], ['state-corruption', 'state-corrupt'], ['worktree-leak', 'worktree-leak'], ['dispatch-bug', 'dispatch-bug'],
    ['tick-crash', 'tick-crash'], ['merge-gate-bug', 'merge-gate-bug'], ['gate-bypass', 'gate-bypass'], ['evidence-wiring', 'evidence-wiring'],
    ['autopilot-bug', 'autopilot-bug'], ['duplicate-write', 'duplicate-write']].map(([k, v]) => [k, ['orchestrator', v]]),
  ...[['missed-proof', 'missed-proof'], ['missed-ac', 'missed-ac'], ['weakened-assertion', 'weakened-assertion'], ['stale-prompt', 'stale-prompt'],
    ['prompt-drift', 'stale-prompt'], ['bad-code', 'bad-code'], ['bad-test', 'bad-test'], ['suite-fail', 'suite-fail'], ['review-fail', 'review-fail'],
    ['runtime-fail', 'runtime-fail'], ['vectors-fail', 'vectors-fail'], ['formal-fail', 'formal-fail'],
    ['reopened-regression', 'reopened-regression'], ['reverted-regression', 'reverted-regression']].map(([k, v]) => [k, ['agent-quality', v]]),
]);

const ENV_RESOURCE_CODES = new Set(['runner-sigterm', 'runner-oom', 'missing-capability', 'quota-or-rate-limit', 'auth-expired']);
const LINT_AQ_CODES = new Set(['weakened-assertion', 'stale-prompt', 'bad-test', 'schema-violation', 'private-import']);
const PROOF_AQ_CODES = new Set(['missed-proof', 'missed-ac', 'reopened-regression', 'reverted-regression', 'runtime-fail', 'vectors-fail', 'formal-fail', 'suite-fail']);

/** Deterministic non-compensatory 4-bucket classifier (structured codes strictly beat free text; zero numeric confidence). */
export function classifyIncidentBucket(incident, { secrets = [] } = {}) {
  const inc = isObj(incident) ? incident : {};
  const structuredFields = [inc.reasonCode, inc.reason_code, inc.code, inc.holdReason, inc.category, inc.kind]
    .map(v => sanitizeCode(v, secrets)).filter(Boolean);

  // 1. Exact structured code table match (takes strict precedence over any free text!).
  for (const code of structuredFields) {
    const hit = STRUCTURED_CODES.get(code);
    if (hit) return { bucket: hit[0], reasonCode: hit[1], rule: `${hit[0]}-structured-code` };
  }

  // 2. Explicit process exit signal/code or harness flags.
  const exitCode = Number(inc.exitCode), exitSignal = asText(inc.exitSignal ?? inc.signal).trim().toUpperCase();
  if (exitSignal === 'SIGTERM' || exitCode === 143) return { bucket: 'environment', reasonCode: 'runner-sigterm', rule: 'environment-signal' };
  if (exitSignal === 'SIGKILL' || exitCode === 137) return { bucket: 'environment', reasonCode: 'runner-oom', rule: 'environment-signal' };
  if (inc.harnessBug === true || inc.gateBypassed === true) return { bucket: 'orchestrator', reasonCode: inc.gateBypassed ? 'gate-bypass' : 'harness-bug', rule: 'orchestrator-flag' };

  // 3. Structured code family fallback for underscore/custom structured codes.
  for (const code of structuredFields) {
    if (/(?:^|-)(?:lease|lock|harness|orchestrator|worktree|dispatch|corrupt|gate-bypass|claim-collision)(?:-|$)/.test(code)) return { bucket: 'orchestrator', reasonCode: code, rule: 'orchestrator-code-family' };
    if (/(?:^|-)(?:oom|sigterm|sigkill|quota|rate-limit|auth|slot|capabilit|capacit|infra|flake|network|timeout)(?:-|$)/.test(code)) return { bucket: 'environment', reasonCode: code, rule: 'environment-code-family' };
    if (/(?:^|-)(?:hold|decision|protected|codeowners|cross-repo|unsound|unverifiable|not-planned)(?:-|$)/.test(code)) return { bucket: 'real-hold', reasonCode: code, rule: 'real-hold-code-family' };
  }

  // 4. Anchored free-text fallback ONLY when no structured code matched.
  const text = incidentFreeText(inc);
  if (/\b(?:protected[\s_-]+path|codeowners|human[\s_-]+decision|needs[\s_-]+decision|needs[\s_-]+person|unclear[\s_-]+or[\s_-]+unsound|cross[\s_-]+repo|unverifiable[\s_-]+boundary|not_planned|pdd:needs-decision)\b/.test(text)) {
    return { bucket: 'real-hold', reasonCode: 'human-hold', rule: 'real-hold-text' };
  }
  if (/\b(?:sigterm|sigkill|out of memory|oom|enomem|exit(?:ed)?\s+(?:with\s+)?(?:137|143)|runner\s+killed)\b/.test(text)) {
    return { bucket: 'environment', reasonCode: /\b(?:sigterm|143)\b/.test(text) ? 'runner-sigterm' : 'runner-oom', rule: 'environment-text' };
  }
  if (/\b(?:quota[\s_-]+(?:exceeded|exhausted|limit)|rate[\s_-]?limit\w*|http[\s:=]+429)\b/.test(text)) {
    return { bucket: 'environment', reasonCode: 'quota-or-rate-limit', rule: 'environment-text' };
  }
  if (/\b(?:(?:auth(?:entication)?|token|login|credential)[\s_-]+(?:expir\w*|invalid|revoked|exhaust\w*|fail\w*|denied)|http[\s:=]+401)\b/.test(text)) {
    return { bucket: 'environment', reasonCode: 'auth-expired', rule: 'environment-text' };
  }
  if (/\b(?:missing[\s_-]+capabilit\w*|missing[\s_-]+capacit\w*|no[\s_-]+worker[\s_-]+slot)\b/.test(text)) {
    return { bucket: 'environment', reasonCode: 'missing-capability', rule: 'environment-text' };
  }
  if (/\b(?:flaky[\s_-]+infra|ci[\s_-]+infra|suspect[\s_-]+ci|flaked-then-passed|base-test-red|econnreset|etimedout|(?:http|status|response|error)[\s:=]+(?:502|503|504))\b/.test(text)) {
    return { bucket: 'environment', reasonCode: 'flaky-infra', rule: 'environment-text' };
  }
  if (/\b(?:orchestrator|harness[\s_-]+bug|lease[\s_-]+(?:bug|collision|corrupt|leak|expired)|lock[\s_-]+timeout|state[\s_-]+corrupt\w*|worktree[\s_-]+leak|dispatch[\s_-]+bug|merge[\s_-]+gate[\s_-]+bug|gate[\s_-]+bypass|tick[\s_-]+lock|autopilot[\s_-]+crash|duplicate[\s_-]+comment)\b/.test(text)) {
    return { bucket: 'orchestrator', reasonCode: 'orchestrator-bug', rule: 'orchestrator-text' };
  }

  const aqCode = /\b(?:weakened[\s_-]+assertion|removed[\s_-]+assertion|mock[\s_-]+only|tautolog\w*)\b/.test(text) ? 'weakened-assertion'
    : /\b(?:stale[\s_-]+prompt|prompt[\s_-]+drift|prompt[\s_-]+mismatch)\b/.test(text) ? 'stale-prompt'
      : (inc.missedProof === true || /\b(?:missed[\s_-]+proof|without[\s_-]+(?:runtime[\s_-]+)?proof|unverified[\s_-]+merge|skipped[\s_-]+proof|missing[\s_-]+proof)\b/.test(text)) ? 'missed-proof'
        : /\b(?:missed[\s_-]+ac|acceptance[\s_-]+criteri\w*)\b/.test(text) ? 'missed-ac'
          : (inc.reverted === true || /\brevert(?:ed)?\b/.test(text)) ? 'reverted-regression'
            : (inc.reopened === true || /\breopen(?:ed)?\b/.test(text)) ? 'reopened-regression'
              : (structuredFields[0] && !['regression', 'ci-failed'].includes(structuredFields[0]) ? structuredFields[0] : 'agent-quality-defect');
  return { bucket: 'agent-quality', reasonCode: aqCode, rule: 'agent-quality-contract' };
}

/** Deterministic Ladder-of-Fixes proposal mapped strictly from canonical `(bucket, reasonCode)`. */
export function proposeRootCauseFix(classification, incident, { secrets = [] } = {}) {
  const bucket = classification.bucket, reasonCode = sanitizeCode(classification.reasonCode, secrets) ?? 'unknown-incident';
  const inc = isObj(incident) ? incident : {};
  const target = safeSnippet(inc.target ?? inc.file ?? inc.module ?? '', { max: 120, secrets });
  const make = (rung, title, action, extra = {}) => ({
    rung, rank: LADDER_RANK[rung],
    title: safeSnippet(title, { max: 180, secrets }),
    action: safeSnippet(action, { max: 360, secrets }),
    deferredRungs: LADDER_OF_FIXES.slice(LADDER_RANK[rung]),
    ...extra,
  });

  if (bucket === 'orchestrator') {
    return make('architecture-api', `Harden orchestrator boundary for ${reasonCode}`,
      `Eliminate ${reasonCode} by enforcing the invariant at the owning Autopilot state/lease/gate API boundary so invalid transitions cannot occur.`);
  }
  if (bucket === 'environment') {
    if (ENV_RESOURCE_CODES.has(reasonCode) || /(?:sigterm|oom|quota|rate-limit|auth|capabilit|capacit|slot)/.test(reasonCode)) {
      return make('architecture-api', `Enforce ${reasonCode} resource/capability boundary in harness`,
        `Prevent ${reasonCode} by enforcing worker capability preflight, bounded concurrency/memory guards, or deterministic auth/quota backoff in the harness API.`);
    }
    return make('runtime-proof', `Add isolated real-host reproduction & flake guard for ${reasonCode}`,
      `Reproduce ${reasonCode}${target ? ` (${target})` : ''} with an isolated \`pdd prove\` / real-host check and stabilize flaky external dependency boundaries.`);
  }
  if (bucket === 'agent-quality') {
    if (PROOF_AQ_CODES.has(reasonCode)) {
      return make('runtime-proof', `Add verify.paths / pdd prove runtime proof for ${reasonCode}`,
        `Require a real-host \`verify.paths\` / \`pdd prove\` verification recipe covering ${reasonCode}${target ? ` (${target})` : ''} so unproved regressions cannot merge.`);
    }
    const lintExtra = LINT_AQ_CODES.has(reasonCode) || reasonCode === 'review-fail' || reasonCode === 'agent-quality-defect' ? {
      diagnosticTemplate: {
        rule: reasonCode,
        invariant: safeSnippet(`Changes must satisfy the ${reasonCode} contract without weakening checks or drifting from prompts.`, { max: 220, secrets }),
        fix: safeSnippet(`Restore the full contract check${target ? ` in ${target}` : ''} before submitting.`, { max: 220, secrets }),
        rerun: 'npm test',
      },
    } : {};
    return make('lint-checker', `Add deterministic lint checker for ${reasonCode}`,
      `Enforce a mechanical lint rule blocking ${reasonCode}${target ? ` (${target})` : ''} with a 4-part agent-teaching diagnostic (rule, invariant, fix, rerun).`, lintExtra);
  }
  return make('skill-prose', `Clarify human-hold triage guidance for ${reasonCode}`,
    `Keep held (legitimate ${reasonCode}); optionally add lightweight triage/template guidance only if recurring ambiguity slows human decisions.`);
}

/** Deterministic root-cause fingerprint (groups same root cause across issues, ignoring SHAs/run IDs/durations/secrets). */
export function incidentFingerprint(incident, classification = null, { secrets = [] } = {}) {
  const inc = isObj(incident) ? incident : {}, cls = classification ?? classifyIncidentBucket(inc, { secrets });
  const repo = asText(inc.repo).trim().toLowerCase();
  const target = normalizeSignatureText(inc.fingerprintKey ?? inc.target ?? inc.file ?? inc.module ?? '', secrets);
  const payload = JSON.stringify({ repo, bucket: cls.bucket, reasonCode: cls.reasonCode, target });
  return createHash('sha256').update(payload).digest('hex').slice(0, 16);
}

function buildProvenance(inc, secrets) {
  const out = {};
  if (asText(inc.repo).trim()) out.repo = safeSnippet(inc.repo, { max: 120, secrets });
  if (posInt(inc.issue)) out.issue = inc.issue;
  if (posInt(inc.pr)) out.pr = inc.pr;
  if (asText(inc.stage).trim()) out.stage = safeSnippet(inc.stage, { max: 40, secrets });
  if (asText(inc.url).trim()) out.url = safeSnippet(inc.url, { max: 240, secrets });
  if (asText(inc.target).trim()) out.target = safeSnippet(inc.target, { max: 180, secrets });
  if (asText(inc.command).trim()) out.command = safeSnippet(inc.command, { max: 200, secrets });
  const snippet = safeSnippet(inc.snippet ?? inc.detail ?? inc.stderr ?? inc.error ?? inc.reason ?? inc.summary ?? '', { max: 360, secrets });
  if (snippet) out.snippet = snippet;
  return out;
}

function summarizeFindings(findings, { totalInputs, newFindings, deduplicatedCount, createdIssuesCount }) {
  const buckets = Object.fromEntries(INVESTIGATOR_BUCKETS.map(b => [b, { count: 0, occurrences: 0, fingerprints: [] }]));
  const ladder = Object.fromEntries(LADDER_OF_FIXES.map(r => [r, 0]));
  for (const f of findings) {
    if (buckets[f.bucket]) { buckets[f.bucket].count += 1; buckets[f.bucket].occurrences += f.occurrences; buckets[f.bucket].fingerprints.push(f.fingerprint); }
    if (f.proposal?.rung && Object.hasOwn(ladder, f.proposal.rung)) ladder[f.proposal.rung] += 1;
  }
  return { totalInputs, uniqueFindings: findings.length, newFindings, deduplicatedCount, createdIssuesCount, buckets, ladder };
}

async function collectExistingIssueBodies(listIssues, maxPages = 50) {
  const bodies = [], seen = new Set();
  for (let i = 0, page = 1, cursor = null; i < maxPages; i++) {
    const token = cursor ?? `p:${page}`;
    if (seen.has(token)) break;
    seen.add(token);
    const res = await listIssues({ page, perPage: 100, cursor });
    const rows = Array.isArray(res) ? res : (Array.isArray(res?.items) ? res.items : []);
    for (const row of rows) bodies.push(asText(row?.body));
    if (Array.isArray(res)) { if (res.length < 100) break; page += 1; }
    else if (isObj(res) && (res.hasNext || res.nextCursor)) { if (res.nextCursor) cursor = res.nextCursor; else page += 1; }
    else break;
  }
  return bodies;
}

function defaultStandupDate(nowMs, timezone) {
  const p = localDateParts(nowMs, timezone);
  return `${String(p.year).padStart(4, '0')}-${String(p.month).padStart(2, '0')}-${String(p.day).padStart(2, '0')}`;
}

/**
 * Pure read-only daily investigator: structured-first 4-bucket classification, Ladder-of-Fixes prioritization,
 * full secret redaction + mention defanging, and root-cause fingerprint deduplication. Writes ZERO GitHub issues by default.
 */
export async function investigateIncidents({
  incidents = [], repo = null, date = null, timezone = DEFAULT_STANDUP_TIMEZONE, now = Date.now,
  knownFingerprints = null, filedFingerprints = null, secrets = [], writeIssues = false, gh = null, maxIssuesPerRun = DEFAULT_MAX_ISSUES_PER_RUN,
} = {}) {
  const nowMs = nowMsOf(now), generatedAt = new Date(nowMs).toISOString();
  const reportDate = DATE_RE.test(asText(date).trim()) ? date.trim() : defaultStandupDate(nowMs, timezone);
  const seenSet = knownFingerprints instanceof Set ? new Set(knownFingerprints) : toSet(knownFingerprints?.seen ?? knownFingerprints);
  const filedSet = filedFingerprints !== null ? toSet(filedFingerprints) : toSet(knownFingerprints?.filed ?? []);

  const byFp = new Map();
  let totalInputs = 0, deduplicatedCount = 0;

  for (const raw of Array.isArray(incidents) ? incidents : []) {
    if (!isObj(raw)) continue;
    totalInputs += 1;
    const enriched = (!raw.repo && repo) ? { ...raw, repo } : raw;
    const cls = classifyIncidentBucket(enriched, { secrets });
    const fingerprint = incidentFingerprint(enriched, cls, { secrets });
    const provenance = buildProvenance(enriched, secrets);
    const alreadySeen = seenSet.has(fingerprint);

    if (byFp.has(fingerprint)) {
      const ex = byFp.get(fingerprint);
      ex.occurrences += 1;
      if (ex.provenance.length < 10 && !ex.provenance.some(p => p.pr === provenance.pr && p.issue === provenance.issue && p.snippet === provenance.snippet)) ex.provenance.push(provenance);
      deduplicatedCount += 1;
      continue;
    }
    if (alreadySeen) deduplicatedCount += 1;
    const proposal = proposeRootCauseFix(cls, enriched, { secrets });
    byFp.set(fingerprint, {
      fingerprint, marker: `${INVESTIGATOR_MARKER_PREFIX}${fingerprint} -->`,
      bucket: cls.bucket, reasonCode: cls.reasonCode, rule: cls.rule, isDuplicateOfPrior: alreadySeen,
      occurrences: 1, title: safeSnippet(enriched.title ?? proposal.title, { max: 180, secrets }),
      proposal, provenance: [provenance],
    });
  }

  const allFindings = [...byFp.values()].sort(sortFindings);
  const newFindings = allFindings.filter(f => !f.isDuplicateOfPrior);
  const createdIssues = [];
  const cap = Number.isSafeInteger(maxIssuesPerRun) && maxIssuesPerRun >= 0 ? maxIssuesPerRun : DEFAULT_MAX_ISSUES_PER_RUN;

  // Fail-closed opt-in issue filing: requires paginated `gh.listIssues`, tracks `filedSet` separately from `seenSet`, and enforces cap.
  if (writeIssues === true && gh && typeof gh.createIssue === 'function' && typeof gh.listIssues === 'function' && cap > 0) {
    const existingBodies = await collectExistingIssueBodies(p => gh.listIssues(p));
    for (const f of allFindings) {
      if (createdIssues.length >= cap) break;
      if (f.bucket === 'real-hold' || filedSet.has(f.fingerprint)) continue;
      if (existingBodies.some(b => b.includes(f.marker))) { deduplicatedCount += 1; continue; }
      const body = [
        `Bucket: \`${f.bucket}\` (\`${f.reasonCode}\`)`,
        `Ladder rung: \`${f.proposal.rung}\` (priority #${f.proposal.rank})`,
        `Recommended fix: ${f.proposal.action}`,
        ...(f.provenance[0]?.snippet ? ['', `Provenance: ${f.provenance[0].snippet}`] : []),
        '', f.marker,
      ].join('\n');
      const created = await gh.createIssue({
        title: safeSnippet(`[investigator:${f.proposal.rung}] ${f.proposal.title}`, { max: 180, secrets }),
        body: defangMentions(redactSecrets(body, secrets)),
        labels: ['pdd:autopilot-report'],
      });
      createdIssues.push({ fingerprint: f.fingerprint, marker: f.marker, issue: created?.number ?? null });
      existingBodies.push(f.marker);
    }
  }

  return {
    schema: INVESTIGATOR_SCHEMA, readOnly: writeIssues !== true, date: reportDate, timezone, generatedAt,
    repo: repo ? safeSnippet(repo, { max: 120, secrets }) : null,
    summary: summarizeFindings(allFindings, { totalInputs, newFindings: newFindings.length, deduplicatedCount, createdIssuesCount: createdIssues.length }),
    findings: allFindings, newFindings,
    proposals: allFindings.map(f => ({ fingerprint: f.fingerprint, bucket: f.bucket, occurrences: f.occurrences, ...f.proposal })),
    createdIssues,
  };
}

function safeInvestigationsFile(fs, stateDir, relName) {
  const root = assertSafePrivateDir(fs, stateDir, { label: 'autopilot investigator state' });
  const dir = assertSafePrivateDir(fs, join(root, 'investigations'), { label: 'autopilot investigations dir' });
  const target = resolve(join(dir, relName));
  if (!isPathAtOrInside(target, dir, fs)) throw Object.assign(new Error(`Refusing investigation file path outside "${dir}": "${relName}"`), { code: 'unsafe_state_path' });
  try { const st = (fs.lstatSync ?? nativeFs.lstatSync).call(fs, target); if (st.isSymbolicLink() || !st.isFile()) throw Object.assign(new Error(`Refusing symlink investigation target "${target}".`), { code: 'unsafe_state_path' }); }
  catch (err) { if (err?.code !== 'ENOENT') throw err; }
  return target;
}

export function loadInvestigationLedger(stateDir, { fs = nativeFs } = {}) {
  const raw = readJsonObjectQuiet(fs, safeInvestigationsFile(fs, stateDir, 'fingerprints.json'));
  const seenObj = isObj(raw?.seen) ? raw.seen : (isObj(raw?.fingerprints) ? raw.fingerprints : {});
  const filedObj = isObj(raw?.filed) ? raw.filed : {};
  return { seen: new Set(Object.keys(seenObj)), filed: new Set(Object.keys(filedObj)) };
}

export function loadKnownInvestigationFingerprints(stateDir, { fs = nativeFs } = {}) {
  const ledger = loadInvestigationLedger(stateDir, { fs });
  return Object.assign(new Set(ledger.seen), { seen: ledger.seen, filed: ledger.filed });
}

/** Atomically persist daily report + separate seen/filed ledger with consistent recomputed summaries. */
export function persistDailyInvestigationReport(stateDir, report, { fs = nativeFs, now = Date.now } = {}) {
  if (!isObj(report) || !DATE_RE.test(asText(report.date))) throw Object.assign(new Error('persistDailyInvestigationReport requires a valid report with YYYY-MM-DD date.'), { code: 'invalid_report' });
  const nowIso = new Date(nowMsOf(now)).toISOString();
  const reportPath = safeInvestigationsFile(fs, stateDir, `${report.date}.json`);
  const ledgerPath = safeInvestigationsFile(fs, stateDir, 'fingerprints.json');
  const priorLedger = readJsonObjectQuiet(fs, ledgerPath);
  const seenMap = isObj(priorLedger?.seen) ? { ...priorLedger.seen } : (isObj(priorLedger?.fingerprints) ? { ...priorLedger.fingerprints } : {});
  const filedMap = isObj(priorLedger?.filed) ? { ...priorLedger.filed } : {};
  const priorDaily = readJsonObjectQuiet(fs, reportPath);
  const mergedByFp = new Map();
  for (const item of Array.isArray(priorDaily?.findings) ? priorDaily.findings : []) if (isObj(item) && asText(item.fingerprint)) mergedByFp.set(item.fingerprint, item);

  const newFingerprints = [], duplicateFingerprints = [];
  for (const f of Array.isArray(report.findings) ? report.findings : []) {
    const fp = f.fingerprint;
    if (!fp) continue;
    const seenPrior = seenMap[fp];
    if (seenPrior || mergedByFp.has(fp)) {
      duplicateFingerprints.push(fp);
      seenMap[fp] = { ...seenPrior, lastSeenAt: nowIso };
      // Keep prior-day recurrences visible in today's daily file while avoiding same-day replay duplicates.
      if (!mergedByFp.has(fp) && seenPrior?.date && seenPrior.date !== report.date) mergedByFp.set(fp, { ...f, isDuplicateOfPrior: true });
    } else {
      newFingerprints.push(fp);
      mergedByFp.set(fp, f);
      seenMap[fp] = { firstSeenAt: nowIso, lastSeenAt: nowIso, date: report.date, bucket: f.bucket, rung: f.proposal?.rung ?? null };
    }
  }
  for (const created of Array.isArray(report.createdIssues) ? report.createdIssues : []) {
    if (created?.fingerprint) filedMap[created.fingerprint] = { filedAt: nowIso, issue: created.issue ?? null, date: report.date };
  }

  const mergedFindings = [...mergedByFp.values()].sort(sortFindings);
  const totalOccurrences = mergedFindings.reduce((acc, f) => acc + (Number(f.occurrences) || 1), 0);
  const mergedReport = {
    ...report, updatedAt: nowIso, findings: mergedFindings,
    proposals: mergedFindings.map(f => ({ fingerprint: f.fingerprint, bucket: f.bucket, occurrences: f.occurrences, ...f.proposal })),
    summary: summarizeFindings(mergedFindings, {
      totalInputs: totalOccurrences, newFindings: newFingerprints.length,
      deduplicatedCount: duplicateFingerprints.length, createdIssuesCount: (report.createdIssues ?? []).length,
    }),
  };
  writeAtomicPrivate(fs, reportPath, `${JSON.stringify(mergedReport, null, 2)}\n`);
  writeAtomicPrivate(fs, ledgerPath, `${JSON.stringify({ schema: INVESTIGATOR_SCHEMA, updatedAt: nowIso, seen: seenMap, filed: filedMap }, null, 2)}\n`);
  return { reportPath, ledgerPath, newFingerprints, duplicateFingerprints, totalUniqueFindings: mergedFindings.length };
}

export function formatInvestigationMarkdown(report, { secrets = [] } = {}) {
  const findings = Array.isArray(report?.findings) ? report.findings : [];
  const lines = [
    `# Daily Autopilot Investigation (${report?.date ?? 'unknown'})`,
    `Mode: ${report?.readOnly === false ? 'write-issues' : 'read-only'} | Unique findings: ${report?.summary?.uniqueFindings ?? 0} | New: ${report?.summary?.newFindings ?? 0} | Deduplicated: ${report?.summary?.deduplicatedCount ?? 0}`,
    '', '## 4-Bucket Breakdown',
    ...INVESTIGATOR_BUCKETS.map(b => `- \`${b}\`: ${report?.summary?.buckets?.[b]?.count ?? 0} unique (${report?.summary?.buckets?.[b]?.occurrences ?? 0} incidents)`),
    '', '## Prioritized Root-Cause Proposals (Ladder of Fixes)',
    ...(findings.length ? findings.map(f => `- [#${f.proposal.rank} \`${f.proposal.rung}\`] (\`${f.bucket}\` / \`${f.reasonCode}\`, ${f.occurrences}x, fp:\`${f.fingerprint}\`) ${f.proposal.title}: ${f.proposal.action}`) : ['- None']),
  ];
  return defangMentions(redactSecrets(lines.join('\n'), secrets));
}
