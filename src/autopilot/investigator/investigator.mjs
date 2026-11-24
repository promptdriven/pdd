// Layer-2 Pillar 2B daily read-only 4-bucket Ladder-of-Fixes investigator.
import { createHash } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { basename, join, resolve } from 'node:path';
import { redactSecrets } from '../../secret-redaction.mjs';
import { assertSafePrivateDir, isPathAtOrInside, readJsonObjectQuiet, writeAtomicPrivate } from '../../shared/atomic-fs.mjs';
import { DEFAULT_STANDUP_TIMEZONE, localDateParts } from '../metrics/funnel-cohort.mjs';

export const INVESTIGATOR_SCHEMA = 'pdd.autopilot.investigator.v1';
export const INVESTIGATOR_MARKER_PREFIX = '<!-- pdd:investigator:v1:';
export const INVESTIGATOR_BUCKETS = Object.freeze(['orchestrator', 'agent-quality', 'environment', 'real-hold']);
export const STUCK_BUCKET_LABELS = Object.freeze({
  'real-hold': 'repo/spec problem',
  'agent-quality': 'agent-quality',
  orchestrator: 'pdd/harness bug',
  environment: 'infra/quota/flake',
});
export const LADDER_OF_FIXES = Object.freeze(['architecture-api', 'lint-checker', 'runtime-proof', 'skill-prose']);
export const LADDER_RANK = Object.freeze({ 'architecture-api': 1, 'lint-checker': 2, 'runtime-proof': 3, 'skill-prose': 4 });
export const DEFAULT_MAX_ISSUES_PER_RUN = 5;
export const MAX_ISSUES_PER_RUN = 20;

const DATE_RE = /^\d{4}-\d{2}-\d{2}$/;
const HEX_SHA_RE = /^[0-9a-f]{7,40}$/i;
const SAFE_REPORT_REF_RE = /^(?:[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)?#[1-9]\d*$/;
const isObj = v => v !== null && typeof v === 'object' && !Array.isArray(v), asText = v => (typeof v === 'string' ? v : ''), posInt = v => Number.isSafeInteger(v) && v > 0;
const firstNonEmpty = (...values) => values.map(asText).find(s => s.trim().length > 0) ?? '';
const nowMsOf = now => (typeof now === 'function' ? now() : now), toSet = v => (v instanceof Set ? new Set(v) : new Set(Array.isArray(v) ? v : (isObj(v) ? Object.keys(v) : [])));
const sortFindings = (a, b) => (a.proposal?.rank ?? 9) - (b.proposal?.rank ?? 9) || b.occurrences - a.occurrences || a.fingerprint.localeCompare(b.fingerprint);
export function isValidCalendarDate(raw) {
  const text = asText(raw).trim();
  if (!DATE_RE.test(text)) return false;
  const [y, m, d] = text.split('-').map(Number);
  const dt = new Date(Date.UTC(y, m - 1, d));
  return dt.getUTCFullYear() === y && dt.getUTCMonth() === m - 1 && dt.getUTCDate() === d;
}
function defangMentions(text) {
  const input = asText(text);
  // Process outside balanced single-backtick code spans and replace any stray unmatched backticks
  // so `x`@bob or ``@bob can never break out of inline code or bypass mention defanging.
  const parts = input.split(/(`[^`\r\n]+`)/g);
  return parts.map((segment, idx) => {
    if (idx % 2 === 1) return segment;
    const clean = segment.replace(/`/g, "'");
    const prevWasCode = idx > 0 && parts[idx - 1].endsWith('`');
    return clean.replace(/(?<![\w/])@([a-zA-Z0-9][a-zA-Z0-9_-]{0,38})\b/g, (match, user, offset) => {
      const needsSpace = offset === 0 && prevWasCode;
      return `${needsSpace ? ' ' : ''}\`@${user}\``;
    });
  }).join('');
}
const scrubLocalPaths = value => asText(value)
  .replace(/(?:\/private\/(?:tmp|var\/folders)\/[^\s'"`<>)\]]+|\/(?:Users|home|root)\/[^\s'"`<>)\]]+|\/var\/folders\/[^\s'"`<>)\]]+|\/tmp\/[^\s'"`<>)\]]+|~\/[^\s'"`<>)\]]+|[A-Za-z]:[\\/]Users[\\/][^\s'"`<>)\]]+)/g, '[local-path]');
const inlineCode = value => `\`${asText(value).replace(/`/g, "'")}\``;
const safeSnippet = (value, { max = 360, secrets = [] } = {}) => defangMentions(scrubLocalPaths(redactSecrets(asText(value), secrets)).replace(/[\r\n\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f]/g, ' ').replace(/\s+/g, ' ').trim()).slice(0, max);
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
    ['needs-decision', 'human-decision'], ['needs-person', 'human-decision'], ['no-decision', 'human-decision'], ['policy-decision', 'human-decision'], ['unclear-or-unsound', 'unclear-or-unsound'],
    ['cross-repo', 'cross-repo'], ['needs-other-repo', 'cross-repo'], ['unverifiable-boundary', 'unverifiable-boundary'], ['blocker-closed-not-planned', 'not-planned-retriage'],
    ['re-triage-not-planned', 'not-planned-retriage'], ['not-planned-retriage', 'not-planned-retriage'], ['blocker-unavailable-404', 'blocker-unavailable-404'],
    ['duplicate', 'duplicate'], ['assigned-to-human', 'assigned-to-human'], ['human-stop', 'human-stop'],
    ['no-test-command', 'no-test-command'], ['base-check', 'base-check'], ['base-moving', 'base-moving'], ['pr-closed', 'pr-closed'], ['head-moved', 'head-moved']].map(([k, v]) => [k, ['real-hold', v]]),
  ...[['environment', 'flaky-infra'], ['missing-capability', 'missing-capability'], ['missing-capacity', 'missing-capability'], ['no-worker-slot', 'missing-capability'],
    ['quota', 'quota-or-rate-limit'], ['quota-exhausted', 'quota-or-rate-limit'], ['quota-or-rate-limit', 'quota-or-rate-limit'], ['rate-limit', 'quota-or-rate-limit'],
    ['rate-limited', 'quota-or-rate-limit'], ['auth-expired', 'auth-expired'], ['token-expired', 'auth-expired'], ['login-exhausted', 'auth-expired'],
    ['sigterm', 'runner-sigterm'], ['runner-sigterm', 'runner-sigterm'], ['sigkill', 'runner-oom'], ['oom', 'runner-oom'], ['runner-oom', 'runner-oom'],
    ['machine-sleep', 'machine-sleep'],
    ['flaky-infra', 'flaky-infra'], ['ci-infra', 'flaky-infra'], ['suspect-ci', 'flaky-infra'], ['flaked-then-passed', 'flaky-infra'], ['checks-stuck', 'flaky-infra'],
    ['base-test-red', 'flaky-infra'], ['github-unavailable', 'flaky-infra'], ['network-timeout', 'flaky-infra']].map(([k, v]) => [k, ['environment', v]]),
  ...[['orchestrator', 'orchestrator-bug'], ['orchestrator-bug', 'orchestrator-bug'], ['harness', 'harness-bug'], ['harness-bug', 'harness-bug'],
    ['lease-expired', 'lease-expired'], ['lease-bug', 'lease-bug'], ['claim-collision', 'claim-collision'], ['claim-expired', 'claim-expired'], ['lock-timeout', 'lock-timeout'],
    ['state-corrupt', 'state-corrupt'], ['state-corruption', 'state-corrupt'], ['worktree-leak', 'worktree-leak'], ['dispatch-bug', 'dispatch-bug'],
    ['tick-crash', 'tick-crash'], ['merge-gate-bug', 'merge-gate-bug'], ['gate-bypass', 'gate-bypass'], ['evidence-wiring', 'evidence-wiring'],
    ['autopilot-bug', 'autopilot-bug'], ['duplicate-write', 'duplicate-write'], ['suite-broken', 'suite-broken'], ['runtime-bug', 'runtime-bug']].map(([k, v]) => [k, ['orchestrator', v]]),
  ...[['missed-proof', 'missed-proof'], ['missed-ac', 'missed-ac'], ['weakened-assertion', 'weakened-assertion'], ['stale-prompt', 'stale-prompt'],
    ['prompt-drift', 'stale-prompt'], ['bad-code', 'bad-code'], ['bad-test', 'bad-test'], ['suite-fail', 'suite-fail'], ['review-fail', 'review-fail'],
    ['runtime-fail', 'runtime-fail'], ['vectors-fail', 'vectors-fail'], ['formal-fail', 'formal-fail'],
    ['checks-red', 'checks-red'], ['hung', 'hung-command'], ['hung-command', 'hung-command'],
    ['reopened-regression', 'reopened-regression'], ['post-merge-reopen', 'reopened-regression'], ['reopened', 'reopened-regression'],
    ['reverted-regression', 'reverted-regression'], ['post-merge-revert', 'reverted-regression'], ['revert', 'reverted-regression'], ['reverted', 'reverted-regression'],
    ['post-merge-ci', 'post-merge-ci-regression'], ['post-merge-ci-regression', 'post-merge-ci-regression'], ['ci-broken', 'post-merge-ci-regression']].map(([k, v]) => [k, ['agent-quality', v]]),
]);

const ENV_RESOURCE_CODES = new Set(['runner-sigterm', 'runner-oom', 'missing-capability', 'quota-or-rate-limit', 'auth-expired', 'machine-sleep']);
const LINT_AQ_CODES = new Set(['weakened-assertion', 'stale-prompt', 'bad-test', 'schema-violation', 'private-import']);
const PROOF_AQ_CODES = new Set(['missed-proof', 'missed-ac', 'reopened-regression', 'reverted-regression', 'post-merge-ci-regression', 'runtime-fail', 'vectors-fail', 'formal-fail', 'suite-fail', 'checks-red', 'hung-command']);
const NON_ACTIONABLE_FILING_CODES = new Set(['quota-or-rate-limit', 'auth-expired', 'missing-capability', 'machine-sleep', 'human-stop', 'stopped', 'released', 'abandoned', 'claim-expired']);
const GENERIC_WEAK_CODES = new Set(['unknown-incident', 'agent-quality-defect', 'ended', 'stopped', 'failed', 'released', 'abandoned', 'no-result']);

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

  // 2. Explicit process exit signal/code or structured harness/regression flags (strictly before free-text heuristics).
  const exitCode = Number(inc.exitCode), exitSignal = asText(inc.exitSignal ?? inc.signal).trim().toUpperCase();
  if (exitSignal === 'SIGTERM' || exitCode === 143) return { bucket: 'environment', reasonCode: 'runner-sigterm', rule: 'environment-signal' };
  if (exitSignal === 'SIGKILL' || exitCode === 137) return { bucket: 'environment', reasonCode: 'runner-oom', rule: 'environment-signal' };
  if (inc.harnessBug === true || inc.gateBypassed === true) return { bucket: 'orchestrator', reasonCode: inc.gateBypassed ? 'gate-bypass' : 'harness-bug', rule: 'orchestrator-flag' };
  if (inc.missedProof === true) return { bucket: 'agent-quality', reasonCode: 'missed-proof', rule: 'agent-quality-flag' };
  if (inc.reverted === true) return { bucket: 'agent-quality', reasonCode: 'reverted-regression', rule: 'agent-quality-flag' };
  if (inc.reopened === true) return { bucket: 'agent-quality', reasonCode: 'reopened-regression', rule: 'agent-quality-flag' };

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
  const rawCommit = asText(inc.mergeCommit ?? inc.commit ?? inc.head).trim();
  if (HEX_SHA_RE.test(rawCommit)) out.commit = rawCommit.toLowerCase();
  const component = safeSnippet(inc.component ?? inc.module ?? inc.file ?? '', { max: 120, secrets });
  if (component) out.component = component;
  const code = sanitizeCode(inc.code ?? inc.reasonCode ?? inc.reason_code ?? '', secrets);
  if (code) out.code = code;
  if (asText(inc.stage).trim()) out.stage = safeSnippet(inc.stage, { max: 40, secrets });
  if (asText(inc.url).trim()) out.url = safeSnippet(inc.url, { max: 240, secrets });
  if (asText(inc.target).trim()) out.target = safeSnippet(inc.target, { max: 180, secrets });
  if (asText(inc.command).trim()) out.command = safeSnippet(inc.command, { max: 200, secrets });
  const rawLog = asText(inc.log).trim();
  if (rawLog) {
    const cleanLog = safeSnippet(basename(rawLog), { max: 120, secrets });
    if (cleanLog) out.log = cleanLog;
  }
  const rawReport = asText(inc.report).trim();
  if (SAFE_REPORT_REF_RE.test(rawReport)) out.report = rawReport;
  if (typeof inc.at === 'string' && Number.isFinite(Date.parse(inc.at))) out.at = new Date(Date.parse(inc.at)).toISOString();
  else if (typeof inc.at === 'number' && Number.isFinite(inc.at)) out.at = new Date(inc.at).toISOString();
  const rawSnippet = firstNonEmpty(inc.snippet, inc.detail, inc.stderr, inc.error, inc.reason, inc.summary);
  const snippet = safeSnippet(rawSnippet, { max: 360, secrets });
  if (snippet) out.snippet = snippet;
  return out;
}

/** Deterministic strong-evidence gate preventing vague, empty, or transient quota/auth/one-off flake issue spam. */
export function hasStrongInvestigationEvidence(finding, { repo = null } = {}) {
  if (!isObj(finding)) return false;
  if (finding.bucket === 'real-hold') return false;
  const code = asText(finding.reasonCode).trim().toLowerCase();
  if (!code || NON_ACTIONABLE_FILING_CODES.has(code) || GENERIC_WEAK_CODES.has(code)) return false;
  const occurrences = posInt(finding.occurrences) ? finding.occurrences : 1;
  if (code === 'flaky-infra' && occurrences < 3) return false;
  const provList = Array.isArray(finding.provenance) ? finding.provenance.filter(isObj) : [];
  const hasRepo = Boolean(asText(repo).trim() || provList.some(p => asText(p.repo).trim()));
  if (!hasRepo) return false;
  const hasConcreteAnchor = provList.some(p =>
    posInt(p.issue) || posInt(p.pr) || Boolean(asText(p.commit).trim())
    || Boolean(asText(p.url).trim() && /^https:\/\//i.test(p.url))
    || Boolean(asText(p.target).trim()) || Boolean(asText(p.component).trim()));
  return hasConcreteAnchor;
}

/** Format a rich, secret-redacted, local-path-scrubbed structured GitHub issue body for an investigator finding. */
export function formatInvestigationIssueBody(finding, { repo = null, secrets = [] } = {}) {
  const provList = Array.isArray(finding?.provenance) ? finding.provenance.filter(isObj) : [];
  const primary = provList[0] ?? {};
  const repoLabel = safeSnippet(primary.repo ?? repo ?? 'unknown', { max: 120, secrets });
  const bucketLabel = STUCK_BUCKET_LABELS[finding?.bucket] ?? finding?.bucket ?? 'unknown';
  const component = safeSnippet(primary.component ?? primary.target ?? primary.stage ?? 'autopilot', { max: 120, secrets });
  const evidenceLines = provList.slice(0, 5).map(p => {
    const parts = [];
    if (p.repo) parts.push(`Repo: ${inlineCode(p.repo)}`);
    if (posInt(p.issue)) parts.push(`Issue: #${p.issue}`);
    if (posInt(p.pr)) parts.push(`PR: #${p.pr}`);
    if (p.commit) parts.push(`Commit: ${inlineCode(p.commit)}`);
    if (p.stage) parts.push(`Stage: ${inlineCode(p.stage)}`);
    if (p.code) parts.push(`Code: ${inlineCode(p.code)}`);
    if (p.log) parts.push(`Log: ${inlineCode(p.log)}`);
    if (p.at) parts.push(`At: ${inlineCode(p.at)}`);
    if (p.url && /^https:\/\//i.test(p.url)) parts.push(`URL: ${p.url}`);
    const head = `- ${parts.length ? parts.join(' | ') : 'Recorded incident'}`;
    return p.snippet ? `${head}\n  - Detail: ${p.snippet}` : head;
  });
  const command = provList.map(p => p.command).find(Boolean) ?? null;
  const rerun = finding?.proposal?.diagnosticTemplate?.rerun ?? 'pdd prove';
  const body = [
    '## Root-Cause Diagnosis',
    '',
    `- **Repository:** ${inlineCode(repoLabel)}`,
    `- **Root-cause bucket:** ${inlineCode(finding.bucket)} (${bucketLabel})`,
    `- **Error / reason code:** ${inlineCode(finding.reasonCode)}`,
    `- **Affected component:** ${inlineCode(component)}`,
    `- **Ladder of Fixes rung:** ${inlineCode(finding.proposal?.rung ?? 'runtime-proof')} (priority #${finding.proposal?.rank ?? '?'})`,
    `- **Occurrences observed:** ${finding.occurrences ?? 1}`,
    `- **Fingerprint:** ${inlineCode(finding.fingerprint)}`,
    '',
    '## Recommended Fix',
    '',
    finding.proposal?.action ?? 'Add a deterministic regression check before closing.',
    '',
    '## Concrete Evidence & Provenance',
    '',
    ...(evidenceLines.length ? evidenceLines : ['- No structured provenance attached.']),
    '',
    '## Reproduction & Verification Context',
    '',
    `- **Target / component:** ${inlineCode(component)}`,
    ...(command ? [`- **Command:** ${inlineCode(command)}`] : []),
    `- **Verify with:** ${inlineCode(rerun)}`,
    '',
    finding.marker,
  ].join('\n');
  return defangMentions(scrubLocalPaths(redactSecrets(body, secrets)));
}

/**
 * Fast, deterministic, zero-LLM read-only diagnosis run before labeling an issue `pdd:stuck`.
 * Reuses `classifyIncidentBucket` (4 buckets: repo/spec problem, agent-quality, pdd/harness bug, infra/quota/flake).
 */
export function diagnoseStuckCause(incident, { secrets = [], reportRef = null, logName = null } = {}) {
  const inc = isObj(incident) ? incident : {};
  const cls = classifyIncidentBucket(inc, { secrets });
  const proposal = proposeRootCauseFix(cls, inc, { secrets });
  const label = STUCK_BUCKET_LABELS[cls.bucket] ?? cls.bucket;
  const cleanLog = logName ? safeSnippet(basename(asText(logName)), { max: 120, secrets }) : null;
  const cleanRef = SAFE_REPORT_REF_RE.test(asText(reportRef).trim()) ? asText(reportRef).trim() : null;
  const rc = cls.reasonCode;

  let summary;
  let nextStep;
  if (cls.bucket === 'real-hold') {
    if (rc === 'no-test-command') {
      summary = 'Repository has no configured or auto-detected full test command.';
      nextStep = 'Configure `autopilot.testCommand` (or a repository test script) in `pdd.json`, then remove `pdd:stuck` to retry.';
    } else if (rc === 'base-check' || rc === 'base-moving') {
      summary = 'Base branch check or repeated base-branch merge conflicts blocked completion.';
      nextStep = 'Update or stabilize the repository base branch, resolve conflicts, and remove `pdd:stuck` to retry.';
    } else if (rc === 'pr-closed' || rc === 'head-moved') {
      summary = 'The PR was closed or moved outside this Autopilot job branch.';
      nextStep = 'Inspect the PR/branch state, reconcile any external commits, and remove `pdd:stuck` to retry.';
    } else {
      summary = `Issue requires a repository/specification decision or configuration fix (${rc}).`;
      nextStep = 'Clarify the issue acceptance criteria, protected-path rules, or repository config, then remove `pdd:stuck` to retry.';
    }
  } else if (cls.bucket === 'orchestrator') {
    if (rc === 'claim-expired') {
      summary = 'Autopilot claim lease expired before the job completed.';
      nextStep = 'Check why the Autopilot timer paused or missed heartbeats on this machine, then remove `pdd:stuck` to retry.';
    } else if (cleanRef) {
      summary = `PDD/harness failure (${rc}) blocked the run; tracked by ${cleanRef}.`;
      nextStep = `Wait for or resolve ${cleanRef}, then remove \`pdd:stuck\` to retry.`;
    } else {
      summary = `PDD/harness failure (${rc}) prevented the job from completing.`;
      nextStep = 'Inspect the PDD/harness report (`pdd autopilot report`) and job log, fix the harness error, then remove `pdd:stuck` to retry.';
    }
  } else if (cls.bucket === 'environment') {
    if (rc === 'quota-or-rate-limit') {
      summary = 'AI or GitHub quota/rate limit interrupted execution.';
      nextStep = 'Wait for quota reset or verify account capacity (`pdd accounts status`), then remove `pdd:stuck` to retry.';
    } else if (rc === 'auth-expired') {
      summary = 'An AI provider or GitHub login/token expired or was rejected.';
      nextStep = 'Refresh authentication (`pdd accounts status` / `gh auth status`), then remove `pdd:stuck` to retry.';
    } else if (rc === 'runner-oom' || rc === 'runner-sigterm') {
      summary = `Worker or test runner was terminated by the environment (${rc}).`;
      nextStep = 'Check machine/CI memory and reduce concurrency (`--runs` / `--share`), then remove `pdd:stuck` to retry.';
    } else {
      summary = `External infrastructure or CI flake (${rc}) interrupted the run.`;
      nextStep = 'Verify external CI/network health, rerun the flaky check, and remove `pdd:stuck` to retry.';
    }
  } else {
    if (rc === 'hung-command') {
      summary = 'A build or test command hung without output or CPU progress.';
      nextStep = `Inspect the hung command in ${cleanLog ? `\`${cleanLog}\`` : 'the job log'}, add a timeout or fix the hang, then remove \`pdd:stuck\` to retry.`;
    } else if (rc === 'checks-red' || rc === 'suite-fail' || rc === 'review-fail' || rc === 'runtime-fail' || rc === 'vectors-fail' || rc === 'formal-fail') {
      summary = `Automated verification failed (${rc}) and exhausted repair attempts.`;
      nextStep = `Inspect the failing checks, PR diff, and ${cleanLog ? `\`${cleanLog}\`` : 'job log'}, tighten the fix or scope, then remove \`pdd:stuck\` to retry.`;
    } else {
      summary = `Agent run could not produce a passing fix (${rc}).`;
      nextStep = `Inspect ${cleanLog ? `\`${cleanLog}\`` : 'the job log'} and PR diff, clarify failing checks or scope, then remove \`pdd:stuck\` to retry.`;
    }
  }

  const evidenceParts = [];
  if (posInt(inc.pr)) evidenceParts.push(`PR #${inc.pr}`);
  if (cleanLog) evidenceParts.push(`log ${inlineCode(cleanLog)}`);
  const rawSnippet = safeSnippet(firstNonEmpty(inc.detail, inc.error, inc.stderr), { max: 180, secrets });
  if (rawSnippet) evidenceParts.push(rawSnippet);
  const evidence = evidenceParts.length ? defangMentions(scrubLocalPaths(redactSecrets(evidenceParts.join(' · '), secrets))) : null;

  return {
    bucket: cls.bucket,
    label,
    reasonCode: rc,
    rule: cls.rule,
    summary: defangMentions(scrubLocalPaths(redactSecrets(summary, secrets))),
    nextStep: defangMentions(scrubLocalPaths(redactSecrets(nextStep, secrets))),
    evidence,
    proposal,
  };
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
    if (seen.has(token)) throw new Error('Cyclic GitHub issue pagination.');
    seen.add(token);
    const res = await listIssues({ page, perPage: 100, cursor });
    const rows = Array.isArray(res) ? res : (Array.isArray(res?.items) ? res.items : null);
    if (!Array.isArray(rows)) throw new Error('Malformed GitHub issue list reply.');
    for (const row of rows) bodies.push(asText(row?.body));
    const hasMore = Array.isArray(res)
      ? res.length >= 100
      : Boolean(isObj(res) && (res.hasNext || res.nextCursor));
    if (!hasMore) return bodies;
    if (i + 1 >= maxPages) throw new Error(`GitHub issue pagination exceeded ${maxPages} pages (truncated).`);
    if (isObj(res) && res.nextCursor) cursor = res.nextCursor;
    else page += 1;
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
  knownFingerprints = null, filedFingerprints = null, secrets = [], writeIssues = false, gh = null, maxIssuesPerRun = undefined,
} = {}) {
  const nowMs = nowMsOf(now), generatedAt = new Date(nowMs).toISOString();
  const reportDate = isValidCalendarDate(date) ? date.trim() : defaultStandupDate(nowMs, timezone);
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
  const alreadyFiledOnGithub = [];
  const cap = maxIssuesPerRun === undefined
    ? DEFAULT_MAX_ISSUES_PER_RUN
    : (Number.isSafeInteger(maxIssuesPerRun) && maxIssuesPerRun >= 0 ? Math.min(maxIssuesPerRun, MAX_ISSUES_PER_RUN) : 0);

  // Fail-closed opt-in issue filing: requires paginated `gh.listIssues`, strong evidence, separate `filedSet`, and strict cap.
  if (writeIssues === true && gh && typeof gh.createIssue === 'function' && typeof gh.listIssues === 'function' && cap > 0) {
    let existingBodies = null;
    try {
      existingBodies = await collectExistingIssueBodies(p => gh.listIssues(p));
    } catch {
      existingBodies = null;
    }
    if (Array.isArray(existingBodies)) {
      for (const f of allFindings) {
        if (createdIssues.length >= cap) break;
        if (filedSet.has(f.fingerprint)) continue;
        if (!hasStrongInvestigationEvidence(f, { repo })) continue;
        if (existingBodies.some(b => b.includes(f.marker))) {
          deduplicatedCount += 1;
          filedSet.add(f.fingerprint);
          alreadyFiledOnGithub.push({ fingerprint: f.fingerprint, marker: f.marker });
          continue;
        }
        const body = formatInvestigationIssueBody(f, { repo, secrets });
        const title = defangMentions(scrubLocalPaths(safeSnippet(`[investigator:${f.proposal.rung}] ${f.proposal.title}`, { max: 180, secrets })));
        try {
          const created = await gh.createIssue({
            title,
            body,
            labels: ['pdd:autopilot-report'],
          });
          createdIssues.push({
            fingerprint: f.fingerprint,
            marker: f.marker,
            issue: created?.number ?? null,
            ...(typeof created?.html_url === 'string' && /^https:\/\//i.test(created.html_url)
              ? { url: safeSnippet(created.html_url, { max: 240, secrets }) }
              : {}),
          });
          filedSet.add(f.fingerprint);
          existingBodies.push(f.marker);
        } catch {
          // Never abort remaining findings or crash caller ticks if one create call fails.
        }
      }
    }
  }

  return {
    schema: INVESTIGATOR_SCHEMA, readOnly: writeIssues !== true, date: reportDate, timezone, generatedAt,
    repo: repo ? safeSnippet(repo, { max: 120, secrets }) : null,
    summary: summarizeFindings(allFindings, { totalInputs, newFindings: newFindings.length, deduplicatedCount, createdIssuesCount: createdIssues.length }),
    findings: allFindings, newFindings,
    proposals: allFindings.map(f => ({ fingerprint: f.fingerprint, bucket: f.bucket, occurrences: f.occurrences, ...f.proposal })),
    createdIssues,
    ...(alreadyFiledOnGithub.length ? { alreadyFiledOnGithub } : {}),
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
  if (!isObj(report) || !isValidCalendarDate(report.date)) throw Object.assign(new Error('persistDailyInvestigationReport requires a valid report with YYYY-MM-DD date.'), { code: 'invalid_report' });
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
      seenMap[fp] = {
        firstSeenAt: seenPrior?.firstSeenAt ?? nowIso,
        date: seenPrior?.date ?? report.date,
        bucket: seenPrior?.bucket ?? f.bucket,
        rung: seenPrior?.rung ?? f.proposal?.rung ?? null,
        ...seenPrior,
        lastSeenAt: nowIso,
      };
      // Keep prior-day recurrences visible in today's daily file while avoiding same-day replay duplicates.
      if (!mergedByFp.has(fp) && seenPrior?.date && seenPrior.date !== report.date) mergedByFp.set(fp, { ...f, isDuplicateOfPrior: true });
    } else {
      newFingerprints.push(fp);
      mergedByFp.set(fp, f);
      seenMap[fp] = { firstSeenAt: nowIso, lastSeenAt: nowIso, date: report.date, bucket: f.bucket, rung: f.proposal?.rung ?? null };
    }
  }
  const mergedCreatedByFp = new Map();
  for (const prevCreated of Array.isArray(priorDaily?.createdIssues) ? priorDaily.createdIssues : []) {
    if (prevCreated?.fingerprint) mergedCreatedByFp.set(prevCreated.fingerprint, prevCreated);
  }
  for (const created of Array.isArray(report.createdIssues) ? report.createdIssues : []) {
    if (created?.fingerprint) {
      mergedCreatedByFp.set(created.fingerprint, created);
      filedMap[created.fingerprint] = { filedAt: nowIso, issue: created.issue ?? null, date: report.date };
    }
  }
  for (const existing of Array.isArray(report.alreadyFiledOnGithub) ? report.alreadyFiledOnGithub : []) {
    if (existing?.fingerprint && !filedMap[existing.fingerprint]) {
      filedMap[existing.fingerprint] = { filedAt: nowIso, issue: existing.issue ?? null, date: report.date, source: 'github-existing' };
    }
  }

  const mergedCreatedIssues = [...mergedCreatedByFp.values()];
  const mergedFindings = [...mergedByFp.values()].sort(sortFindings);
  const totalOccurrences = mergedFindings.reduce((acc, f) => acc + (Number(f.occurrences) || 1), 0);
  const mergedReport = {
    ...report, updatedAt: nowIso, findings: mergedFindings,
    createdIssues: mergedCreatedIssues,
    proposals: mergedFindings.map(f => ({ fingerprint: f.fingerprint, bucket: f.bucket, occurrences: f.occurrences, ...f.proposal })),
    summary: summarizeFindings(mergedFindings, {
      totalInputs: totalOccurrences, newFindings: newFingerprints.length,
      deduplicatedCount: duplicateFingerprints.length, createdIssuesCount: mergedCreatedIssues.length,
    }),
  };
  writeAtomicPrivate(fs, reportPath, `${JSON.stringify(mergedReport, null, 2)}\n`);
  writeAtomicPrivate(fs, ledgerPath, `${JSON.stringify({ schema: INVESTIGATOR_SCHEMA, updatedAt: nowIso, seen: seenMap, filed: filedMap }, null, 2)}\n`);
  return { reportPath, ledgerPath, newFingerprints, duplicateFingerprints, totalUniqueFindings: mergedFindings.length };
}

function isSymlinkQuiet(fs, targetPath) {
  try {
    return Boolean((fs.lstatSync ?? nativeFs.lstatSync).call(fs, targetPath)?.isSymbolicLink?.());
  } catch {
    return false;
  }
}

function readSafeFileQuiet(fs, filePath) {
  try {
    if (isSymlinkQuiet(fs, filePath)) return null;
    const st = (fs.lstatSync ?? nativeFs.lstatSync).call(fs, filePath);
    if (st && typeof st.isFile === 'function' && !st.isFile()) return null;
    return fs.readFileSync(filePath, 'utf8');
  } catch {
    return null;
  }
}

/**
 * Harvest local Autopilot incidents from a `<stem>-core` directory:
 * - `history.jsonl` job failures/ends AND `postMerge: true` regression rows (enriched from `post-merge.json`),
 * - `flakes.jsonl` cross-job flake entries,
 * - `reports/drafts/` local report drafts (when `listReportDrafts` is supplied).
 * Symlink-safe and fail-safe on unreadable files.
 */
export function collectCoreLocalIncidents(root, {
  repo = null,
  reportRoot = null,
  sinceMs = null,
  fs = nativeFs,
  parseFlakeLedger = null,
  listReportDrafts = null,
} = {}) {
  if (!asText(root).trim() || isSymlinkQuiet(fs, root)) return [];
  const cutoffMs = typeof sinceMs === 'number' && Number.isFinite(sinceMs) ? sinceMs : null;
  const withinCutoff = rawTs => {
    if (cutoffMs === null) return true;
    const ms = typeof rawTs === 'number' && Number.isFinite(rawTs) ? rawTs : (typeof rawTs === 'string' ? Date.parse(rawTs) : NaN);
    return !Number.isFinite(ms) || ms >= cutoffMs;
  };
  const incidents = [];

  // Optional `post-merge.json` lookup to enrich post-merge history rows with mergeCommit/mergedAt/signal URLs.
  const postMergeByPr = new Map();
  const rawPostMerge = readSafeFileQuiet(fs, join(root, 'post-merge.json'));
  if (rawPostMerge) {
    try {
      const parsed = JSON.parse(rawPostMerge);
      if (isObj(parsed?.merges)) {
        for (const entry of Object.values(parsed.merges)) {
          if (isObj(entry) && posInt(entry.pr)) postMergeByPr.set(entry.pr, entry);
        }
      }
    } catch { /* Ignore corrupt post-merge.json. */ }
  }

  const rawHistory = readSafeFileQuiet(fs, join(root, 'history.jsonl'));
  if (rawHistory) {
    for (const line of rawHistory.split('\n')) {
      if (!line.trim()) continue;
      let row;
      try { row = JSON.parse(line); } catch { continue; }
      if (!isObj(row)) continue;

      if (row.postMerge === true) {
        if (!withinCutoff(row.signalAt ?? row.at)) continue;
        const postCode = asText(row.code).trim()
          || (row.kind === 'reopened' ? 'post-merge-reopen'
            : (row.kind === 'revert' || row.kind === 'reverted') ? 'post-merge-revert'
              : 'post-merge-ci');
        const pmEntry = posInt(row.pr) ? postMergeByPr.get(row.pr) : null;
        const matchedSignal = Array.isArray(pmEntry?.signals)
          ? pmEntry.signals.find(s =>
            isObj(s) && s.level === 'proven'
            && (s.kind === row.kind || (postCode === 'post-merge-reopen' && s.kind === 'reopened')
              || (postCode === 'post-merge-revert' && s.kind === 'revert')
              || (postCode === 'post-merge-ci' && s.kind === 'ci'))
            && (!posInt(row.issue) || !posInt(s.issue) || s.issue === row.issue))
          : null;
        incidents.push({
          repo: row.repo ?? repo ?? null,
          issue: posInt(row.issue) ? row.issue : (posInt(pmEntry?.issue) ? pmEntry.issue : null),
          ...(Array.isArray(row.issues) && row.issues.length ? { issues: row.issues.filter(posInt) } : {}),
          pr: posInt(row.pr) ? row.pr : null,
          kind: row.kind ?? null,
          code: postCode,
          reopened: row.kind === 'reopened' || postCode === 'post-merge-reopen',
          reverted: row.kind === 'revert' || row.kind === 'reverted' || postCode === 'post-merge-revert',
          ...(row.mergeCommit || pmEntry?.mergeCommit ? { mergeCommit: row.mergeCommit ?? pmEntry.mergeCommit } : {}),
          ...(row.mergedAt || pmEntry?.mergedAt ? { mergedAt: row.mergedAt ?? pmEntry.mergedAt } : {}),
          ...(row.url || matchedSignal?.url ? { url: row.url ?? matchedSignal.url } : {}),
          ...(row.report ? { report: row.report } : {}),
          ...(row.signalAt || row.at ? { at: row.signalAt ?? row.at } : {}),
          component: 'post-merge',
          reason: asText(row.text),
          detail: asText(row.text),
          stage: 'post-merge',
        });
        continue;
      }

      const isIncident = ['ended', 'failed', 'stopped', 'abandoned'].includes(row.outcome)
        || row.hold === true
        || row.noResult === true
        || row.poolExhausted === true
        || (row.outcome === 'released' && asText(row.owner).trim().length > 0);
      if (!isIncident) continue;
      if (!withinCutoff(row.at)) continue;
      const rowText = asText(row.text);
      const isHumanStop = row.outcome === 'stopped' && /^stopped by a person\b/i.test(rowText);
      const isMachineSleep = row.outcome === 'released' && (row.owner === 'machine' || /\bran no tick for\b|\bwhile it slept\b/i.test(rowText));
      const diagCode = asText(row.diagnosis?.reasonCode).trim();
      const rowCode = asText(row.code).trim();
      const derivedCode = isHumanStop ? 'human-stop'
        : isMachineSleep ? 'machine-sleep'
          : (diagCode || rowCode
            || (row.poolExhausted ? 'quota-exhausted'
              : row.hold ? 'orchestrator-bug'
                : row.owner === 'pdd' ? 'harness-bug'
                  : row.outcome));
      incidents.push({
        repo: row.repo ?? repo ?? null,
        issue: posInt(row.issue) ? row.issue : null,
        pr: posInt(row.pr) ? row.pr : null,
        code: derivedCode,
        ...(row.log ? { log: row.log } : {}),
        ...(row.at ? { at: row.at } : {}),
        ...(row.target ? { target: row.target } : {}),
        ...(row.component ? { component: row.component } : {}),
        reason: rowText,
        detail: rowText,
        stage: row.outcome ?? 'ended',
      });
    }
  }

  const rawFlakes = readSafeFileQuiet(fs, join(root, 'flakes.jsonl'));
  if (rawFlakes) {
    let entries = [];
    if (typeof parseFlakeLedger === 'function') {
      try { entries = parseFlakeLedger(rawFlakes); } catch { entries = []; }
    } else {
      for (const line of rawFlakes.split(/\r?\n/)) {
        if (!line.trim()) continue;
        try {
          const parsed = JSON.parse(line);
          if (isObj(parsed) && asText(parsed.target).trim()) entries.push(parsed);
        } catch { /* Skip malformed line. */ }
      }
    }
    for (const entry of entries) {
      if (!withinCutoff(entry.ts)) continue;
      incidents.push({
        repo: entry.repo ?? repo ?? null,
        issue: posInt(entry.issue) ? entry.issue : null,
        pr: posInt(entry.pr) ? entry.pr : null,
        ...(entry.head ? { head: entry.head } : {}),
        code: entry.outcome || 'flaky-infra',
        target: entry.target ?? '',
        reason: entry.detail ?? entry.outcome ?? 'flake',
        stage: 'suite',
        ...(entry.ts ? { at: entry.ts } : {}),
      });
    }
  }

  if (typeof listReportDrafts === 'function') {
    const draftsRoot = asText(reportRoot).trim() || join(root, 'reports');
    const draftsDir = join(draftsRoot, 'drafts');
    if (!isSymlinkQuiet(fs, draftsRoot) && !isSymlinkQuiet(fs, draftsDir)) {
      try {
        const safeDraftFs = {
          ...fs,
          readdirSync: dir => (fs.readdirSync?.(dir) ?? []).filter(name => !isSymlinkQuiet(fs, join(dir, name))),
        };
        for (const draft of listReportDrafts({ root: draftsRoot }, { fs: safeDraftFs })) {
          if (!isObj(draft)) continue;
          incidents.push({
            repo: repo ?? null,
            code: draft.code ?? draft.kind ?? 'harness-bug',
            component: draft.component ?? 'autopilot',
            title: draft.title ?? '',
            reason: firstNonEmpty(draft.cause, draft.detail),
            detail: firstNonEmpty(draft.detail, draft.cause),
            stage: draft.step ?? 'report',
          });
        }
      } catch { /* No report drafts yet. */ }
    }
  }

  return incidents;
}

/** Read the newest persisted daily investigation JSON from `root/investigations/` (symlink-safe, fail-safe). */
export function readLatestDailyInvestigation(root, { fs = nativeFs } = {}) {
  if (!asText(root).trim() || isSymlinkQuiet(fs, root)) return null;
  const dir = join(root, 'investigations');
  if (isSymlinkQuiet(fs, dir)) return null;
  let names = [];
  try {
    names = fs.readdirSync(dir)
      .filter(name => /^\d{4}-\d{2}-\d{2}\.json$/.test(name))
      .sort()
      .reverse();
  } catch {
    return null;
  }
  for (const name of names) {
    const raw = readSafeFileQuiet(fs, join(dir, name));
    if (!raw) continue;
    try {
      const parsed = JSON.parse(raw);
      if (isObj(parsed) && isObj(parsed.summary)) return parsed;
    } catch { /* Skip corrupt file. */ }
  }
  return null;
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
