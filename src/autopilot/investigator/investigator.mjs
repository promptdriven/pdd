// Layer-2 Pillar 2B daily read-only 4-bucket Ladder-of-Fixes investigator.
import { createHash } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { join, resolve } from 'node:path';
import { redactSecrets } from '../../secret-redaction.mjs';
import { assertSafePrivateDir, isPathAtOrInside, readJsonObjectQuiet, writeAtomicPrivate } from '../../shared/atomic-fs.mjs';

export const INVESTIGATOR_SCHEMA = 'pdd.autopilot.investigator.v1';
export const INVESTIGATOR_MARKER_PREFIX = '<!-- pdd:investigator:v1:';
export const INVESTIGATOR_BUCKETS = Object.freeze(['orchestrator', 'agent-quality', 'environment', 'real-hold']);
export const LADDER_OF_FIXES = Object.freeze(['architecture-api', 'lint-checker', 'runtime-proof', 'skill-prose']);
export const LADDER_RANK = Object.freeze({ 'architecture-api': 1, 'lint-checker': 2, 'runtime-proof': 3, 'skill-prose': 4 });

const DATE_RE = /^\d{4}-\d{2}-\d{2}$/;
const isObj = v => v !== null && typeof v === 'object' && !Array.isArray(v);
const asText = v => (typeof v === 'string' ? v : '');
const posInt = v => Number.isSafeInteger(v) && v > 0;
const nowMsOf = now => (typeof now === 'function' ? now() : now);
const sortFindings = (a, b) => (a.proposal?.rank ?? 9) - (b.proposal?.rank ?? 9) || b.occurrences - a.occurrences || a.fingerprint.localeCompare(b.fingerprint);

function safeSnippet(value, { max = 360, secrets = [] } = {}) {
  return redactSecrets(asText(value), secrets).replace(/[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, max);
}

function normalizeSignatureText(raw, secrets = []) {
  return safeSnippet(raw, { max: 200, secrets }).toLowerCase()
    .replace(/\b\d{4}-\d{2}-\d{2}t\d{2}:\d{2}:\d{2}(?:\.\d+)?z\b/g, '<ts>')
    .replace(/\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b/g, '<uuid>')
    .replace(/\bpid[=:\s]+\d+\b/g, 'pid=<n>')
    .replace(/\/(?:tmp|var\/folders|private\/var\/folders)\/[^\s'"]+/g, '<tmp>')
    .replace(/\s+/g, ' ').trim();
}

const incidentCorpus = inc => [
  inc?.kind, inc?.code, inc?.reasonCode, inc?.reason_code, inc?.category, inc?.holdReason,
  inc?.gate, inc?.signal, inc?.exitSignal, inc?.status, inc?.outcome,
  inc?.title, inc?.reason, inc?.summary, inc?.detail, inc?.error, inc?.stderr, inc?.snippet,
].map(asText).filter(Boolean).join(' ').toLowerCase();

const REAL_HOLD_CODES = new Set([
  'real-hold', 'real_hold', 'protected-path', 'protected_path', 'codeowners-hold', 'human_decision', 'human-decision',
  'needs-decision', 'needs-person', 'policy-decision', 'unclear_or_unsound', 'unclear-or-unsound', 'cross_repo',
  'cross-repo', 'needs-other-repo', 'unverifiable_boundary', 'unverifiable-boundary', 'blocker-closed-not-planned',
  're-triage-not-planned', 'blocker-unavailable-404', 'duplicate', 'assigned-to-human',
]);
const ENV_CODES = new Set([
  'environment', 'missing-capability', 'missing-capacity', 'no-worker-slot', 'quota', 'quota-exhausted',
  'rate-limit', 'rate-limited', 'auth-expired', 'token-expired', 'login-exhausted', 'sigterm', 'sigkill', 'oom',
  'runner-oom', 'flaky-infra', 'ci-infra', 'suspect-ci', 'flaked-then-passed', 'base-test-red', 'github-unavailable', 'network-timeout',
]);
const ORCH_CODES = new Set([
  'orchestrator', 'harness', 'harness-bug', 'lease-expired', 'lease-bug', 'claim-collision', 'lock-timeout',
  'state-corrupt', 'state-corruption', 'worktree-leak', 'dispatch-bug', 'tick-crash', 'merge-gate-bug',
  'gate-bypass', 'evidence-wiring', 'autopilot-bug', 'duplicate-write',
]);

/** Deterministic non-compensatory 4-bucket classifier (zero LLM numeric confidence scores). */
export function classifyIncidentBucket(incident) {
  const inc = isObj(incident) ? incident : {};
  const codes = [inc.reasonCode, inc.reason_code, inc.code, inc.kind, inc.category, inc.holdReason].map(v => asText(v).trim().toLowerCase()).filter(Boolean);
  const corpus = incidentCorpus(inc), exitCode = Number(inc.exitCode), exitSignal = asText(inc.exitSignal ?? inc.signal).trim().toUpperCase();

  const holdCode = codes.find(c => REAL_HOLD_CODES.has(c));
  if (holdCode || /\b(?:protected[\s_-]+path|codeowners|human[\s_-]+decision|needs[\s_-]+decision|needs[\s_-]+person|unclear[\s_-]+or[\s_-]+unsound|cross[\s_-]+repo|unverifiable[\s_-]+boundary|not_planned|pdd:needs-decision)\b/.test(corpus)) {
    return { bucket: 'real-hold', reasonCode: holdCode ?? 'human-hold', rule: 'real-hold-contract' };
  }

  const envCode = codes.find(c => ENV_CODES.has(c));
  if (envCode || exitSignal === 'SIGTERM' || exitSignal === 'SIGKILL' || exitCode === 137 || exitCode === 143
    || /\b(?:sigterm|sigkill|out of memory|oom|enomem|exit(?:ed)?\s+(?:with\s+)?(?:137|143)|quota|rate[\s_-]?limit|http\s*429|auth(?:entication)?[\s_-]?expir|token[\s_-]?expir|login[\s_-]?exhaust|missing[\s_-]+capabilit|missing[\s_-]+capacit|flaky[\s_-]+infra|ci[\s_-]+infra|suspect[\s_-]+ci|flaked-then-passed|base-test-red|econnreset|etimedout|502|503|504|runner\s+killed)\b/.test(corpus)) {
    const code = envCode ?? (exitSignal === 'SIGTERM' || exitCode === 143 || /\bsigterm\b/.test(corpus) ? 'runner-sigterm'
      : (exitSignal === 'SIGKILL' || exitCode === 137 || /\boom|enomem|out of memory\b/.test(corpus) ? 'runner-oom'
        : (/\bquota|rate[\s_-]?limit|429\b/.test(corpus) ? 'quota-or-rate-limit'
          : (/\bauth|token|login\b/.test(corpus) ? 'auth-expired' : (/\bcapabilit|capacit\b/.test(corpus) ? 'missing-capability' : 'flaky-infra')))));
    return { bucket: 'environment', reasonCode: code, rule: 'environment-infra-contract' };
  }

  const orchCode = codes.find(c => ORCH_CODES.has(c));
  if (orchCode || inc.harnessBug === true || inc.gateBypassed === true
    || /\b(?:orchestrator|harness[\s_-]+bug|lease[\s_-]+(?:bug|collision|corrupt|leak)|lock[\s_-]+timeout|state[\s_-]+corrupt|worktree[\s_-]+leak|dispatch[\s_-]+bug|merge[\s_-]+gate[\s_-]+bug|gate[\s_-]+bypass|tick[\s_-]+lock|autopilot[\s_-]+crash|duplicate[\s_-]+comment)\b/.test(corpus)) {
    return { bucket: 'orchestrator', reasonCode: orchCode ?? 'orchestrator-bug', rule: 'orchestrator-harness-contract' };
  }

  const aqCode = /\b(?:weakened[\s_-]+assertion|removed[\s_-]+assertion|mock[\s_-]+only|tautolog)\b/.test(corpus) ? 'weakened-assertion'
    : /\b(?:stale[\s_-]+prompt|prompt[\s_-]+drift|prompt[\s_-]+mismatch)\b/.test(corpus) ? 'stale-prompt'
      : (inc.missedProof === true || /\b(?:missed[\s_-]+proof|without[\s_-]+(?:runtime[\s_-]+)?proof|unverified[\s_-]+merge|skipped[\s_-]+proof|missing[\s_-]+proof)\b/.test(corpus)) ? 'missed-proof'
        : /\b(?:missed[\s_-]+ac|acceptance[\s_-]+criteri)\b/.test(corpus) ? 'missed-ac'
          : (inc.reverted === true || /\brevert(?:ed)?\b/.test(corpus)) ? 'reverted-regression'
            : (inc.reopened === true || /\breopen(?:ed)?\b/.test(corpus)) ? 'reopened-regression'
              : (codes[0] || 'agent-quality-defect');
  return { bucket: 'agent-quality', reasonCode: aqCode, rule: 'agent-quality-contract' };
}

/** Map a classified incident strictly down PDD's 4-rung Ladder of Fixes. */
export function proposeRootCauseFix(classification, incident, { secrets = [] } = {}) {
  const { bucket, reasonCode } = classification, inc = isObj(incident) ? incident : {}, corpus = incidentCorpus(inc);
  const entity = posInt(inc.pr) ? `PR #${inc.pr}` : (posInt(inc.issue) ? `issue #${inc.issue}` : 'incident');
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
      `Eliminate ${reasonCode} (${entity}) by enforcing the invariant at the owning Autopilot state/lease/gate API boundary so invalid transitions cannot occur.`);
  }
  if (bucket === 'environment') {
    if (['runner-sigterm', 'runner-oom', 'missing-capability', 'missing-capacity', 'quota-or-rate-limit', 'auth-expired'].includes(reasonCode)) {
      return make('architecture-api', `Enforce ${reasonCode} resource/capability boundary in harness`,
        `Prevent ${reasonCode} (${entity}) by enforcing worker capability preflight, bounded concurrency/memory guards, or deterministic auth/quota backoff in the harness API.`);
    }
    return make('runtime-proof', `Add isolated real-host reproduction & flake guard for ${reasonCode}`,
      `Reproduce ${reasonCode}${target ? ` (${target})` : ''} with an isolated \`pdd prove\` / real-host check and stabilize flaky external dependency boundaries.`);
  }
  if (bucket === 'agent-quality') {
    if (['weakened-assertion', 'stale-prompt', 'prompt-drift'].includes(reasonCode) || /\b(?:weakened[\s_-]+assertion|stale[\s_-]+prompt|prompt[\s_-]+drift|lint|private[\s_-]+import|schema)\b/.test(corpus)) {
      return make('lint-checker', `Add deterministic lint checker for ${reasonCode}`,
        `Enforce a mechanical lint rule blocking ${reasonCode} (${entity}) with a 4-part agent-teaching diagnostic (rule, invariant, fix, rerun).`, {
          diagnosticTemplate: {
            rule: reasonCode,
            invariant: `Changes must satisfy the ${reasonCode} contract without weakening checks or drifting from prompts.`,
            fix: `Restore the full contract check${target ? ` in ${target}` : ''} before submitting.`,
            rerun: 'npm test',
          },
        });
    }
    if (['missed-proof', 'missed-ac', 'reopened-regression', 'reverted-regression'].includes(reasonCode) || inc.reopened || inc.reverted || inc.missedProof) {
      return make('runtime-proof', `Add verify.paths / pdd prove runtime proof for ${reasonCode}`,
        `Require a real-host \`verify.paths\` / \`pdd prove\` verification recipe covering ${entity}${target ? ` (${target})` : ''} so unproved regressions cannot merge.`);
    }
    return make('lint-checker', `Add mechanical verification check for ${reasonCode}`,
      `Add a deterministic check catching ${reasonCode} (${entity}) before PR merge with a 4-part agent-teaching error.`);
  }
  return make('skill-prose', `Clarify human-hold triage guidance for ${reasonCode}`,
    `Keep ${entity} held (legitimate ${reasonCode}); optionally add lightweight triage/template guidance only if recurring ambiguity slows human decisions.`);
}

/** Deterministic deduplication fingerprint ignoring volatile timestamps, PIDs, UUIDs, and secrets. */
export function incidentFingerprint(incident, classification = null, { secrets = [] } = {}) {
  const inc = isObj(incident) ? incident : {}, cls = classification ?? classifyIncidentBucket(inc);
  const repo = asText(inc.repo).trim().toLowerCase();
  const entity = posInt(inc.pr) ? `pr:${inc.pr}` : (posInt(inc.issue) ? `issue:${inc.issue}` : 'global');
  const signature = normalizeSignatureText(inc.fingerprintKey ?? inc.target ?? inc.file ?? inc.gate ?? inc.reason ?? inc.summary ?? inc.error ?? inc.detail ?? '', secrets);
  return createHash('sha256').update(JSON.stringify({ repo, bucket: cls.bucket, reasonCode: cls.reasonCode, entity, signature })).digest('hex').slice(0, 16);
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

/**
 * Pure read-only daily investigator: 4-bucket classification, Ladder-of-Fixes prioritization,
 * full secret redaction, and fingerprint deduplication. Writes ZERO GitHub issues by default.
 */
export async function investigateIncidents({
  incidents = [], repo = null, date = null, now = Date.now,
  knownFingerprints = null, secrets = [], writeIssues = false, gh = null,
} = {}) {
  const generatedAt = new Date(nowMsOf(now)).toISOString();
  const reportDate = DATE_RE.test(asText(date).trim()) ? date.trim() : generatedAt.slice(0, 10);
  const priorSet = knownFingerprints instanceof Set
    ? new Set(knownFingerprints)
    : new Set(Array.isArray(knownFingerprints) ? knownFingerprints : (isObj(knownFingerprints) ? Object.keys(knownFingerprints) : []));

  const byFp = new Map();
  let totalInputs = 0, deduplicatedCount = 0;

  for (const raw of Array.isArray(incidents) ? incidents : []) {
    if (!isObj(raw)) continue;
    totalInputs += 1;
    const enriched = (!raw.repo && repo) ? { ...raw, repo } : raw;
    const cls = classifyIncidentBucket(enriched);
    const fingerprint = incidentFingerprint(enriched, cls, { secrets });
    const provenance = buildProvenance(enriched, secrets);
    const alreadyKnown = priorSet.has(fingerprint);

    if (byFp.has(fingerprint)) {
      const ex = byFp.get(fingerprint);
      ex.occurrences += 1;
      if (ex.provenance.length < 5 && provenance.snippet && !ex.provenance.some(p => p.snippet === provenance.snippet)) ex.provenance.push(provenance);
      deduplicatedCount += 1;
      continue;
    }
    if (alreadyKnown) deduplicatedCount += 1;
    const proposal = proposeRootCauseFix(cls, enriched, { secrets });
    byFp.set(fingerprint, {
      fingerprint, marker: `${INVESTIGATOR_MARKER_PREFIX}${fingerprint} -->`,
      bucket: cls.bucket, reasonCode: cls.reasonCode, rule: cls.rule, isDuplicateOfPrior: alreadyKnown,
      occurrences: 1, title: safeSnippet(enriched.title ?? proposal.title, { max: 180, secrets }),
      proposal, provenance: [provenance],
    });
  }

  const allFindings = [...byFp.values()].sort(sortFindings);
  const newFindings = allFindings.filter(f => !f.isDuplicateOfPrior);
  const buckets = Object.fromEntries(INVESTIGATOR_BUCKETS.map(b => [b, { count: 0, occurrences: 0, fingerprints: [] }]));
  const ladder = Object.fromEntries(LADDER_OF_FIXES.map(r => [r, 0]));
  for (const f of allFindings) {
    buckets[f.bucket].count += 1;
    buckets[f.bucket].occurrences += f.occurrences;
    buckets[f.bucket].fingerprints.push(f.fingerprint);
    ladder[f.proposal.rung] += 1;
  }

  const createdIssues = [];
  if (writeIssues === true && gh && typeof gh.createIssue === 'function') {
    const existingBodies = (typeof gh.listIssues === 'function' ? await gh.listIssues() : []).map(i => asText(i?.body));
    for (const f of newFindings) {
      if (f.bucket === 'real-hold') continue;
      if (existingBodies.some(b => b.includes(f.marker))) { deduplicatedCount += 1; continue; }
      const body = [
        `Bucket: \`${f.bucket}\` (\`${f.reasonCode}\`)`,
        `Ladder rung: \`${f.proposal.rung}\` (priority #${f.proposal.rank})`,
        `Recommended fix: ${f.proposal.action}`,
        ...(f.provenance[0]?.snippet ? ['', `Provenance: ${f.provenance[0].snippet}`] : []),
        '', f.marker,
      ].join('\n');
      const created = await gh.createIssue({
        title: `[investigator:${f.proposal.rung}] ${f.proposal.title}`.slice(0, 180),
        body: redactSecrets(body, secrets),
        labels: ['pdd:autopilot-report'],
      });
      createdIssues.push({ fingerprint: f.fingerprint, marker: f.marker, issue: created?.number ?? null });
    }
  }

  return {
    schema: INVESTIGATOR_SCHEMA,
    readOnly: writeIssues !== true,
    date: reportDate,
    generatedAt,
    repo: repo ? safeSnippet(repo, { max: 120, secrets }) : null,
    summary: { totalInputs, uniqueFindings: allFindings.length, newFindings: newFindings.length, deduplicatedCount, createdIssuesCount: createdIssues.length, buckets, ladder },
    findings: allFindings,
    newFindings,
    proposals: allFindings.map(f => ({ fingerprint: f.fingerprint, bucket: f.bucket, occurrences: f.occurrences, ...f.proposal })),
    createdIssues,
  };
}

function safeInvestigationsFile(fs, stateDir, relName) {
  const root = assertSafePrivateDir(fs, stateDir, { label: 'autopilot investigator state' });
  const dir = assertSafePrivateDir(fs, join(root, 'investigations'), { label: 'autopilot investigations dir' });
  const target = resolve(join(dir, relName));
  if (!isPathAtOrInside(target, dir, fs)) throw Object.assign(new Error(`Refusing investigation file path outside "${dir}": "${relName}"`), { code: 'unsafe_state_path' });
  try {
    const st = (fs.lstatSync ?? nativeFs.lstatSync).call(fs, target);
    if (st.isSymbolicLink() || !st.isFile()) throw Object.assign(new Error(`Refusing symlink investigation target "${target}".`), { code: 'unsafe_state_path' });
  } catch (err) { if (err?.code !== 'ENOENT') throw err; }
  return target;
}

export function loadKnownInvestigationFingerprints(stateDir, { fs = nativeFs } = {}) {
  const raw = readJsonObjectQuiet(fs, safeInvestigationsFile(fs, stateDir, 'fingerprints.json'));
  return new Set(isObj(raw?.fingerprints) ? Object.keys(raw.fingerprints) : []);
}

/** Atomically persist daily report + fingerprint ledger with zero-duplicate merge semantics. */
export function persistDailyInvestigationReport(stateDir, report, { fs = nativeFs, now = Date.now } = {}) {
  if (!isObj(report) || !DATE_RE.test(asText(report.date))) {
    throw Object.assign(new Error('persistDailyInvestigationReport requires a valid report with YYYY-MM-DD date.'), { code: 'invalid_report' });
  }
  const nowIso = new Date(nowMsOf(now)).toISOString();
  const reportPath = safeInvestigationsFile(fs, stateDir, `${report.date}.json`);
  const ledgerPath = safeInvestigationsFile(fs, stateDir, 'fingerprints.json');
  const priorLedger = readJsonObjectQuiet(fs, ledgerPath);
  const fpMap = isObj(priorLedger?.fingerprints) ? { ...priorLedger.fingerprints } : {};
  const priorDaily = readJsonObjectQuiet(fs, reportPath);
  const mergedByFp = new Map();
  for (const item of Array.isArray(priorDaily?.findings) ? priorDaily.findings : []) {
    if (isObj(item) && asText(item.fingerprint)) mergedByFp.set(item.fingerprint, item);
  }

  const newFingerprints = [], duplicateFingerprints = [];
  for (const finding of Array.isArray(report.findings) ? report.findings : []) {
    const fp = finding.fingerprint;
    if (!fp) continue;
    if (fpMap[fp] || mergedByFp.has(fp)) {
      duplicateFingerprints.push(fp);
      fpMap[fp] = { ...fpMap[fp], lastSeenAt: nowIso };
    } else {
      newFingerprints.push(fp);
      mergedByFp.set(fp, finding);
      fpMap[fp] = { firstSeenAt: nowIso, lastSeenAt: nowIso, date: report.date, bucket: finding.bucket, rung: finding.proposal?.rung ?? null };
    }
  }

  const mergedFindings = [...mergedByFp.values()].sort(sortFindings);
  const mergedReport = {
    ...report, updatedAt: nowIso, findings: mergedFindings,
    proposals: mergedFindings.map(f => ({ fingerprint: f.fingerprint, bucket: f.bucket, occurrences: f.occurrences, ...f.proposal })),
    summary: { ...report.summary, uniqueFindings: mergedFindings.length, newFindings: newFingerprints.length },
  };
  writeAtomicPrivate(fs, reportPath, `${JSON.stringify(mergedReport, null, 2)}\n`);
  writeAtomicPrivate(fs, ledgerPath, `${JSON.stringify({ schema: INVESTIGATOR_SCHEMA, updatedAt: nowIso, fingerprints: fpMap }, null, 2)}\n`);
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
  return redactSecrets(lines.join('\n'), secrets);
}
