// Generated from prompts/cli/autopilot-self-report.prompt.md (sha256: 6795dd6feaec282298faca686b6a2f7bc2178d6148b4c8d26ed21ba85f61871c).
import { spawn } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { loadAgentDefinitions } from './agent-config.mjs';
import { launchProfile } from './workflow-launch-profile.mjs';
import { updateRun } from './workflow-runs.mjs';

const PACKAGE_ROOT = dirname(dirname(fileURLToPath(import.meta.url)));
const BRIEF_PATH = join(PACKAGE_ROOT, 'docs', 'autopilot-self-report.md');

export const SELF_REPORT_REPO = 'promptdriven/pdd';
export const FORBIDDEN_RUNTIME_REPO = 'promptdriven/prompt-runtime';
export const DAILY_SELF_REPORT_CAP = 5;
export const CONSENT_PROMPT = 'May Autopilot file PDD bug reports for failures in PDD itself? auto / ask each time / off';

const oneLine = value => String(value ?? '').replace(/\s+/g, ' ').trim();
const validLogin = value => typeof value === 'string' && /^[a-z0-9][a-z0-9-]{0,38}$/i.test(value.trim());
const utcDay = ms => new Date(Number.isFinite(ms) ? ms : Date.now()).toISOString().slice(0, 10);
const MAX_SELF_REPORT_FILE_ATTEMPTS = 2;
const RUNTIME_FAILURES = new Set(['no-verdict', 'runner-stopped', 'provider-error', 'server-refusal', 'timeout']);
const PDD_FAILURES = new Set(['command-crash', 'invariant-broken', 'missing-command', 'autopilot-state']);

function publicCode(value, side, cause = '') {
  const code = String(value ?? '');
  if (/^(?:ERR_[A-Z0-9_]{1,72}|RUNTIME_[A-Z0-9_]{1,72}|[A-Z][A-Za-z]+Error|INVARIANT_BROKEN|MISSING_COMMAND|AUTOPILOT_STATE_BUG)$/.test(code)) return code;
  if (side === 'runtime' && RUNTIME_FAILURES.has(cause)) return 'RUNTIME_' + cause.toUpperCase().replace(/-/g, '_');
  return side === 'runtime' ? 'RUNTIME_FAILURE' : 'ERR_PDD_INTERNAL';
}

function publicModule(value, side) {
  if (side === 'runtime') return 'runtime-service';
  const module = String(value ?? '');
  return /^src\/[a-z0-9-]+\.mjs$/i.test(module) ? module : 'src/workflow-runner.mjs';
}

function publicFunction(value, side) {
  const fn = String(value ?? '');
  return (/^[A-Za-z_$][A-Za-z0-9_$]{0,79}$/.test(fn) || fn === 'pdd-test') ? fn : (side === 'runtime' ? 'pdd-test' : 'unknown');
}

function publicVersion(value) {
  const version = String(value ?? '');
  return /^\d+\.\d+\.\d+(?:[-+][0-9A-Za-z.-]+)?$/.test(version) ? version : 'unknown';
}

function publicDiagnosisLocation(value) {
  if (!value || typeof value !== 'object' || Array.isArray(value)) return null;
  const module = String(value.module ?? '');
  const fn = String(value.fn ?? '');
  const line = Number(value.line);
  if (!/^src\/[a-z0-9-]+\.mjs$/i.test(module)
    || !/^[A-Za-z_$][A-Za-z0-9_$]{0,79}$/.test(fn)
    || !Number.isSafeInteger(line) || line < 1 || line > 1_000_000) return null;
  return { module, fn, line };
}

function readDiagnosisLocation(result, signature, { fs = nativeFs, packageRoot = PACKAGE_ROOT } = {}) {
  if (!result || result.signature !== signature || !result.rootCause || typeof result.rootCause !== 'object') return null;
  const location = publicDiagnosisLocation(result.rootCause);
  if (!location) return null;
  try {
    const lineCount = fs.readFileSync(join(packageRoot, location.module), 'utf8').split(String.fromCharCode(10)).length;
    return location.line <= lineCount ? location : null;
  } catch { return null; }
}

function safePublicReport(report = {}) {
  const side = report.side === 'runtime' ? 'runtime' : 'pdd';
  const rawKind = String(report.cause ?? report.kind ?? '');
  const cause = side === 'runtime' && RUNTIME_FAILURES.has(rawKind) ? rawKind : 'no-verdict';
  const kind = side === 'pdd' && PDD_FAILURES.has(rawKind) ? rawKind : 'command-crash';
  const code = publicCode(report.code, side, cause);
  const module = publicModule(report.module, side);
  const fn = publicFunction(report.fn, side);
  const candidateLine = Number(report.line ?? report.rootCause?.line);
  const line = Number.isSafeInteger(candidateLine) && candidateLine > 0 && candidateLine <= 1_000_000 ? candidateLine : 1;
  const fileLine = side === 'runtime' ? 'Runtime service' : module + ':' + line;
  const diagnosisLocation = side === 'pdd' ? publicDiagnosisLocation(report.diagnosisLocation) : null;
  const signature = buildSignature(code, module, fn);
  const summary = side === 'runtime'
    ? 'Runtime reported a ' + cause + ' result for a PDD check.'
    : 'Autopilot recorded a ' + kind + ' failure (' + code + ') in ' + module + ' (' + fn + ').';
  return {
    side, cause, kind, code, module, fn, line, fileLine, signature,
    title: side === 'runtime'
      ? 'Runtime report: ' + cause
      : 'PDD ' + kind + ': ' + code + ' in ' + module + ' (' + fn + ')',
    summary,
    problem: summary,
    steps: side === 'runtime'
      ? ['Run the PDD check that uses Runtime.', 'Observe the saved Runtime result: ' + cause + '.']
      : ['Run the affected PDD workflow operation in a controlled check.', 'Observe the saved ' + code + ' failure at ' + fileLine + '.'],
    expected: side === 'runtime'
      ? 'Runtime returns a check result or a clear service error.'
      : 'PDD completes the workflow operation or records a normal refusal.',
    actual: summary,
    evidence: code + ' at ' + fileLine + ' (' + fn + ').',
    rootCause: diagnosisLocation
      ? diagnosisLocation.module + ':' + diagnosisLocation.line + ' in ' + diagnosisLocation.fn + ' (' + code + ').'
      : fileLine + ' in ' + fn + ' (' + code + ').',
    diagnosisLocation,
    pddVersion: publicVersion(report.pddVersion ?? report.versions?.pdd),
    versions: {
      pdd: publicVersion(report.pddVersion ?? report.versions?.pdd),
      agent: ['codex', 'claude'].includes(report.versions?.agent ?? report.agent) ? (report.versions?.agent ?? report.agent) : 'unknown',
      node: process.version,
      os: process.platform + ' ' + process.arch,
    },
  };
}

function packageVersion(fs = nativeFs, packageRoot = PACKAGE_ROOT) {
  try {
    return JSON.parse(fs.readFileSync(join(packageRoot, 'package.json'), 'utf8')).version || 'unknown';
  } catch {
    return 'unknown';
  }
}

const bindingRow = row => ['binding-missing', 'missing-binding'].includes(row?.reason?.code)
  || (Array.isArray(row?.refusals) ? row.refusals : []).some(r => ['binding-missing', 'missing-binding'].includes(r?.code))
  || row?.compatibility?.state === 'missing-binding';

function hasAccountLimitEvidence(value) {
  let text = '';
  try { text = JSON.stringify(value); } catch { return false; }
  return /provider[-_ ]call[-_ ]cap|call[-_ ]cap[-_ ]reached|HTTP\s*429|(?:budget|quota)[-_ ](?:cap|limit|exceeded|reached)|(?:provider|account)[-_ ](?:call|budget|quota|usage)[-_ ](?:cap|limit|exceeded|reached)/i.test(text);
}

function isAccountLimitFailure(check, health, run, reason = '') {
  return ['account', 'usage-limit', 'quota'].includes(String(run?.blockedOn?.kind ?? '').toLowerCase())
    || hasAccountLimitEvidence([check, health, run?.runtimeWait, run?.runtimeFailure, run?.blockedOn, reason]);
}

export const runtimeEvidence = run => JSON.stringify([
  run?.parkReason ?? null,
  run?.runtimeWait ?? null,
  run?.gate ?? null,
  run?.done?.check ?? null,
]);

export function classifyRuntimeFailure(check, health = null) {
  if (!check || typeof check !== 'object' || hasAccountLimitEvidence([check, health])) return null;
  const rows = Array.isArray(check.states) ? check.states : Array.isArray(check.rows) ? check.rows : null;
  if (rows) {
    if (!rows.length || rows.some(row => bindingRow(row) || ['ready', 'waiting', 'sending', 'queued', 'running', 'sent'].includes(row?.state))) return null;
    const open = rows.filter(row => !['passed', 'failed'].includes(row?.state));
    if (!open.length) return null;
    const codes = open.flatMap(row => [
      row?.reason?.code,
      row?.note?.code,
      row?.provider?.code,
      row?.code,
      ...(Array.isArray(row?.refusals) ? row.refusals : []).map(r => r?.code),
    ]).filter(Boolean);
    if (codes.some(code => ['check-plan-prerequisite', 'broken-test', 'invalid-input', 'interface-missing', 'undefined-call-bound', 'recursive-call-bound', 'auth-required', 'blocked', 'expectation-failed', 'file-rule'].includes(code))) return null;
    const words = JSON.stringify(open);
    if (/\(HTTP 40[13]\)|\bgh auth login\b|\bgh auth status\b/i.test(words)) return null;
    if (/failed an expectation|file rule|schema_version/i.test(words) && !/server refusal|internal error|provider|runner-stopped|no[ -]verdict/i.test(words)) return null;
    const cause = /timeout|timed.out|time.limit|deadline/i.test(words) ? 'timeout'
      : codes.includes('runner-stopped') || /runner[ -]stopped|ECONNREFUSED|ECONNRESET|fetch failed/i.test(words) ? 'runner-stopped'
      : codes.some(code => /provider|uncertain-child-dispatch/.test(code)) || /provider[ -]error|upstream model|ai-service/i.test(words) ? 'provider-error'
      : open.some(row => row?.state === 'refused') || /server refusal|HTTP 5\d\d|internal server error|runtime_internal_error/i.test(words) ? 'server-refusal'
      : open.every(row => ['partial', 'unknown', 'not run', 'no-verdict'].includes(row?.state)) ? 'no-verdict' : null;
    if (!cause) return null;
    const offered = health?.cause?.code ?? health?.cause ?? health?.code;
    return typeof offered === 'string' && /^[a-z][a-z0-9-]{0,79}$/.test(offered) ? offered : cause;
  }
  const rawCause = String(check.cause ?? check.kind ?? '').toLowerCase();
  const rawState = String(check.state ?? '').toLowerCase();
  const text = `${check.reason ?? ''} ${check.message ?? ''} ${rawCause} ${rawState}`;
  if (['issue', 'access', 'passed', 'failed'].includes(rawCause) || ['passed', 'failed'].includes(rawState)) return null;
  if (/\(HTTP 40[13]\)|\bgh auth login\b|\bgh auth status\b|failed an expectation|file rule/i.test(text)) return null;
  if (/runner[ -]stopped|network|ECONNREFUSED|ECONNRESET|fetch failed/i.test(text)) return 'runner-stopped';
  if (/provider[ -]error|ai-service|upstream model|busy/i.test(text)) return 'provider-error';
  if (/server[ -]refusal|HTTP 5\d\d|runtime_internal_error|interpreter internal error/i.test(text)) return 'server-refusal';
  if (/timeout|timed out/i.test(text)) return 'timeout';
  if (['unknown', 'none', 'no-verdict', 'lost', 'service'].includes(rawCause) || /no[ -](?:saved[ -])?verdict|lost[ -]verdict/i.test(text)) return 'no-verdict';
  return null;
}

export function parsePddStackFrame(stack, fallbackModule = 'src/workflow-runner.mjs', fallbackFn = 'unknown') {
  const lines = String(stack ?? '').split('\n');
  for (const line of lines) {
    const match = /at\s+(?:async\s+)?(?:([A-Za-z0-9_$<>[\].]+)\s+\()?(?:file:\/\/)?([^\s():]+\/src\/([a-z0-9-]+\.mjs)):(\d+)(?::(\d+))?\)?/i.exec(line)
      || /at\s+(?:async\s+)?(?:([A-Za-z0-9_$<>[\].]+)\s+\()?(src\/([a-z0-9-]+\.mjs)):(\d+)(?::(\d+))?\)?/i.exec(line);
    if (match) {
      const fn = (match[1] || fallbackFn).split('.').at(-1) || fallbackFn;
      const module = `src/${match[3]}`;
      const lineNumber = Number(match[4]) || 1;
      return { module, fn, line: lineNumber, fileLine: `${module}:${lineNumber}` };
    }
  }
  return { module: fallbackModule, fn: fallbackFn, line: 1, fileLine: `${fallbackModule}:1` };
}

function normalizeSignaturePart(value, fallback) {
  const cleaned = String(value ?? '').trim().replace(/[^A-Za-z0-9_./:-]/g, '-').replace(/-+/g, '-').replace(/^-|-$/g, '');
  return cleaned || fallback;
}

export function buildSignature(code, module, fn) {
  return `${normalizeSignaturePart(code, 'ERR_PDD_INTERNAL')}+${normalizeSignaturePart(module, 'src/workflow-runner.mjs')}+${normalizeSignaturePart(fn, 'unknown')}`;
}

function readSavedCrash(run, fs = nativeFs) {
  if (run?.commandFailure && typeof run.commandFailure === 'object') return run.commandFailure;
  if (typeof run?.runDir === 'string') {
    try {
      const parsed = JSON.parse(fs.readFileSync(join(run.runDir, 'command-crash.json'), 'utf8'));
      if (parsed && typeof parsed === 'object' && (!run.runId || !parsed.runId || parsed.runId === run.runId)) return parsed;
    } catch { /* No saved crash file. */ }
  }
  return null;
}

export function classifyFailureCause(run = {}, { check = null, health = null, commandError = null, fs = nativeFs } = {}) {
  const none = { side: 'none', kind: 'none', reportable: false, code: null, module: null, fn: null, signature: null, summary: '', evidence: '' };
  if (!run || typeof run !== 'object') return none;

  const crash = commandError || readSavedCrash(run, fs);
  if (crash) {
    const frame = parsePddStackFrame(crash.stack, crash.module || 'src/workflow-runner.mjs', crash.fn || crash.command || 'runPdd');
    const code = String(crash.code || crash.name || 'ERR_PDD_CRASH').trim();
    const module = crash.module || frame.module;
    const fn = crash.fn || frame.fn;
    const signature = buildSignature(code, module, fn);
    const summary = oneLine(crash.message || `pdd command crashed (${code} in ${module}:${fn})`);
    return {
      side: 'pdd',
      kind: 'command-crash',
      reportable: true,
      code,
      module,
      fn,
      line: crash.line || frame.line,
      fileLine: crash.fileLine || frame.fileLine,
      signature,
      command: crash.command || 'pdd',
      summary,
      evidence: String(crash.stack || crash.message || summary),
    };
  }

  if (run.invariantFailure && typeof run.invariantFailure === 'object') {
    const inv = run.invariantFailure;
    const frame = parsePddStackFrame(inv.stack, inv.module || 'src/workflow-runner.mjs', inv.fn || 'invariant');
    const code = String(inv.code || 'INVARIANT_BROKEN');
    const module = inv.module || frame.module;
    const fn = inv.fn || frame.fn;
    return {
      side: 'pdd',
      kind: 'invariant-broken',
      reportable: true,
      code,
      module,
      fn,
      line: inv.line || frame.line,
      fileLine: inv.fileLine || frame.fileLine,
      signature: buildSignature(code, module, fn),
      summary: oneLine(inv.message || inv.reason || 'PDD contract or state invariant broken'),
      evidence: String(inv.stack || inv.evidence || inv.message || ''),
    };
  }

  if (run.autopilotBug && typeof run.autopilotBug === 'object') {
    const bug = run.autopilotBug;
    const frame = parsePddStackFrame(bug.stack, bug.module || 'src/autopilot-launcher.mjs', bug.fn || 'reconcile');
    const code = String(bug.code || 'AUTOPILOT_STATE_BUG');
    const module = bug.module || frame.module;
    const fn = bug.fn || frame.fn;
    return {
      side: 'pdd',
      kind: 'autopilot-state',
      reportable: true,
      code,
      module,
      fn,
      line: bug.line || frame.line,
      fileLine: bug.fileLine || frame.fileLine,
      signature: buildSignature(code, module, fn),
      summary: oneLine(bug.message || bug.reason || 'Autopilot state invariant failure'),
      evidence: String(bug.stack || bug.evidence || bug.message || ''),
    };
  }

  if (run.missingCommand && typeof run.missingCommand === 'object') {
    const miss = run.missingCommand;
    const code = String(miss.code || 'MISSING_COMMAND');
    const module = miss.module || 'src/command-catalog.mjs';
    const fn = miss.fn || miss.command || 'parseArgv';
    return {
      side: 'pdd',
      kind: 'missing-command',
      reportable: true,
      code,
      module,
      fn,
      line: miss.line || 1,
      fileLine: `${module}:${miss.line || 1}`,
      signature: buildSignature(code, module, fn),
      summary: oneLine(miss.message || miss.reason || 'Supported PDD command is missing or wrong'),
      evidence: String(miss.evidence || miss.message || ''),
    };
  }

  const reason = oneLine(run.parkReason ?? run.reason ?? run.message ?? run.error ?? '');
  const rawStack = String(run.stack ?? run.evidence ?? '');

  // Explicit PDD-side patterns in reason/error text:
  if (/(?:The pdd workflow command failed before it could report|pdd stopped with an internal error|pdd command crash|Uncaught\s+\w*Error|(?:TypeError|ReferenceError|RangeError)\s*:|ERR_PDD_[A-Z0-9_]+)/i.test(reason)) {
    const codeMatch = /(ERR_PDD_[A-Z0-9_]+|TypeError|ReferenceError|RangeError|SyntaxError|AssertionError)/.exec(reason);
    const code = codeMatch?.[1] || 'ERR_PDD_CRASH';
    const frame = parsePddStackFrame(rawStack || reason, run.module || 'src/workflow-runner.mjs', run.fn || 'runPdd');
    return {
      side: 'pdd',
      kind: 'command-crash',
      reportable: true,
      code,
      module: run.module || frame.module,
      fn: run.fn || frame.fn,
      line: frame.line,
      fileLine: frame.fileLine,
      signature: buildSignature(code, run.module || frame.module, run.fn || frame.fn),
      summary: reason,
      evidence: rawStack || reason,
    };
  }

  if (/(?:contract or state invariant|state invariant broken|contract invariant broken|invariant broken|Invalid (?:runner|proof|Autopilot|product|alert) reply|run ownership is missing or contradictory|corrupt run record)/i.test(reason)) {
    const code = run.code || 'INVARIANT_BROKEN';
    const frame = parsePddStackFrame(rawStack || reason, run.module || 'src/workflow-runner.mjs', run.fn || 'validateRunState');
    return {
      side: 'pdd',
      kind: 'invariant-broken',
      reportable: true,
      code,
      module: run.module || frame.module,
      fn: run.fn || frame.fn,
      line: frame.line,
      fileLine: frame.fileLine,
      signature: buildSignature(code, run.module || frame.module, run.fn || frame.fn),
      summary: reason,
      evidence: rawStack || reason,
    };
  }

  if (run.routeWait || run.blockedOn?.kind === 'pdd-route'
    || /(?:Missing (?:runner|product) export|Unsupported command in pdd|supported command (?:is )?(?:missing|wrong)|missing PDD route|unknown option .* on supported pdd command)/i.test(reason)) {
    const routeKind = run.routeWait?.kind || 'supported-command';
    const code = run.code || 'MISSING_COMMAND';
    const module = run.module || 'src/command-catalog.mjs';
    const fn = run.fn || routeKind;
    return {
      side: 'pdd',
      kind: 'missing-command',
      reportable: true,
      code,
      module,
      fn,
      line: 1,
      fileLine: `${module}:1`,
      signature: buildSignature(code, module, fn),
      summary: reason || `Supported PDD command or route is missing (${routeKind})`,
      evidence: rawStack || reason || routeKind,
    };
  }

  if (/(?:Autopilot state bug|Parking custody changed|Parking chat changed|(?:claim|parking|wake|admission) (?:state )?(?:bug|invariant|mismatch)|current coordinator ownership does not match)/i.test(reason)
    || (run.blockedOn?.kind === 'pdd' && !/^#[1-9][0-9]*$/.test(String(run.blockedOn?.until ?? '')))) {
    const code = run.code || 'AUTOPILOT_STATE_BUG';
    const frame = parsePddStackFrame(rawStack || reason, run.module || 'src/autopilot-launcher.mjs', run.fn || 'reconcileParking');
    return {
      side: 'pdd',
      kind: 'autopilot-state',
      reportable: true,
      code,
      module: run.module || frame.module,
      fn: run.fn || frame.fn,
      line: frame.line,
      fileLine: frame.fileLine,
      signature: buildSignature(code, run.module || frame.module, run.fn || frame.fn),
      summary: reason || 'Autopilot state invariant bug',
      evidence: rawStack || reason,
    };
  }

  // Provider/account budgets are external limits, not Runtime service defects.
  if (isAccountLimitFailure(check, health, run, reason)) {
    return {
      side: 'person',
      kind: 'account',
      reportable: false,
      code: null,
      module: null,
      fn: null,
      signature: null,
      summary: 'Provider or account usage limit reached',
      evidence: '',
    };
  }

  // Runtime service classification:
  const runtimeCause = classifyRuntimeFailure(check, health)
    || (run.runtimeWait ? classifyRuntimeFailure(run.runtimeWait, health) : null)
    || (run.runtimeFailure ? classifyRuntimeFailure(run.runtimeFailure, health) : null)
    || (/^(?:no-verdict|runner-stopped|provider-error|server-refusal|timeout)$/i.test(String(run.runtimeCause ?? '')) ? String(run.runtimeCause).toLowerCase() : null)
    || (/(?:Interpreter|Runtime)\b.*(?:\bno(?: saved)? verdict\b|\brunner[ -]stopped\b|\bprovider[ -]error\b|\bserver refusal\b|\bHTTP 50[0234]\b)/i.test(reason)
      && !/failed an expectation|file rule|gh auth login|HTTP 40[13]/i.test(reason)
      ? (/runner[ -]stopped/i.test(reason) ? 'runner-stopped'
        : /provider[ -]error|ai-service/i.test(reason) ? 'provider-error'
        : /server refusal|HTTP 50[0234]/i.test(reason) ? 'server-refusal'
        : /timeout|timed out/i.test(reason) ? 'timeout'
        : 'no-verdict')
      : null);

  if (runtimeCause) {
    const code = `RUNTIME_${runtimeCause.toUpperCase().replace(/[^A-Z0-9]+/g, '_')}`;
    const module = 'runtime-service';
    const fn = check?.kind ? String(check.kind).replace(/\s+/g, '-') : 'pdd-test';
    const batch = check?.batch ?? run.runtimeWait?.batch ?? null;
    const summary = reason || `Runtime service failure (${runtimeCause})${batch ? ` in batch ${batch}` : ''}`;
    return {
      side: 'runtime',
      kind: runtimeCause,
      reportable: true,
      code,
      module,
      fn,
      batch,
      signature: buildSignature(code, module, fn),
      summary,
      evidence: JSON.stringify({ cause: runtimeCause, batch, reason: summary }),
    };
  }

  // Person decisions (never file a report):
  const checkHasUserFailure = check?.cause === 'issue'
    || check?.state === 'failed'
    || (Array.isArray(check?.states) && check.states.some(r => r?.state === 'failed' || bindingRow(r)));
  if (['person', 'review', 'account', 'github'].includes(run.blockedOn?.kind)
    || (run.question && !run.question.answeredAt)
    || (run.gate && ['approve-story', 'approve-pr', 'ask-code', 'strict-approve'].includes(run.gate.kind) && !checkHasUserFailure && !run.repairLimit && !run.integrationLimit && !reason)
    || check?.cause === 'access'
    || /(?:\bgh auth (?:login|status)\b|\bcodex login\b|\bclaude auth\b|requires a person terminal|strict_approvals|waiting for (?:you|person|approval|review)|\bHTTP 40[13]\b)/i.test(reason)) {
    const kind = check?.cause === 'access' || /gh auth|codex login|claude auth|HTTP 40[13]/i.test(reason) ? 'access'
      : run.blockedOn?.kind === 'review' ? 'review'
      : (run.question && !run.question.answeredAt) ? 'question'
      : 'gate';
    return {
      side: 'person',
      kind,
      reportable: false,
      code: null,
      module: null,
      fn: null,
      signature: null,
      summary: reason || (run.question?.text ? oneLine(run.question.text) : `Waiting for person (${kind})`),
      evidence: '',
    };
  }

  // User's own code or tests (never file a report):
  if (check?.cause === 'issue' || check?.state === 'failed'
    || (Array.isArray(check?.states) && check.states.some(r => r?.state === 'failed' || bindingRow(r)))
    || run.repairLimit || run.integrationLimit
    || ['ci', 'dependency', 'binding'].includes(run.blockedOn?.kind)
    || run.stuckCause === 'environment' || run.stuckCause === 'suite' || run.environmentRetry
    || /(?:failed an expectation|file rule|binding-missing|missing-binding|unresolved binding|check-plan-prerequisite|interface-missing|test suite failed|npm test|node --test|repair ceiling|syntax error in user|compile error)/i.test(reason)
    || ['stuck', 'paused'].includes(run.state)) {
    const hasBindingMissing = (Array.isArray(check?.states) && check.states.some(bindingRow)) || run.blockedOn?.kind === 'binding' || /binding-missing|missing-binding|unresolved binding/i.test(reason);
    const hasExpectationFailed = (Array.isArray(check?.states) && check.states.some(r => r?.state === 'failed')) || check?.cause === 'issue' || /failed an expectation|file rule|interface-missing/i.test(reason);
    const kind = hasBindingMissing ? 'binding-missing'
      : hasExpectationFailed ? 'expectation-failed'
      : run.stuckCause === 'environment' || run.environmentRetry ? 'environment'
      : run.stuckCause === 'suite' || /test|suite|assertion/i.test(reason) || check?.state === 'failed' ? 'suite'
      : 'user-code';
    return {
      side: 'user',
      kind,
      reportable: false,
      code: null,
      module: null,
      fn: null,
      signature: null,
      summary: reason || `User repository failure (${kind})`,
      evidence: '',
    };
  }

  return none;
}

const SECRET_KEYS = /^(?:token|secret|password|passwd|api[_-]?key|authorization|cookie|webhook|private[_-]?key|client[_-]?secret|access[_-]?token|refresh[_-]?token)$/i;
const STRIP_FIELD_KEYS = /^(?:request[_-]?body|response[_-]?prose|response[_-]?body|user[_-]?source|source[_-]?code|prompt[_-]?prose|completion|raw[_-]?request|raw[_-]?response)$/i;

function redactHomePaths(text, homeDir) {
  const homes = new Set(
    [homeDir, '/home/[^/\\s"\'<>():;,\\]]+', '/Users/[^/\\s"\'<>():;,\\]]+']
      .filter(Boolean)
  );
  let out = String(text ?? '');
  const replaceForPrefix = prefixPattern => {
    const regex = new RegExp(`(${prefixPattern})(/\\.local/state/pdd(?:/[^\\s"'<>():;,\\]]*)?|/\\.pdd(?:/[^\\s"'<>():;,\\]]*)?|/\\.config/pdd(?:/[^\\s"'<>():;,\\]]*)?|/\\.(?:agents|claude)/skills/pdd-[^\\s"'<>():;,\\]]*|/[^\\s"'<>():;,\\]]+)?`, 'g');
    out = out.replace(regex, (full, _home, rest) => {
      if (!rest) return '~';
      if (/^\/(?:\.local\/state\/pdd|\.pdd|\.config\/pdd|\.(?:agents|claude)\/skills\/pdd-[^/]*)(?:\/|$)/.test(rest)) {
        return `~${rest}`;
      }
      return '~/<redacted>';
    });
  };
  if (homeDir && typeof homeDir === 'string' && homeDir.length > 1) {
    const escaped = homeDir.replace(/[/\\]+$/, '').replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    replaceForPrefix(escaped);
  }
  for (const pattern of homes) {
    if (pattern !== homeDir) replaceForPrefix(pattern);
  }
  return out;
}

export function redactSelfReport(value, { home, env = process.env } = {}) {
  const homeDir = home || env?.HOME || env?.USERPROFILE || homedir();
  if (value && typeof value === 'object') {
    if (Array.isArray(value)) return value.map(item => redactSelfReport(item, { home: homeDir, env }));
    const out = {};
    for (const [k, v] of Object.entries(value)) {
      if (STRIP_FIELD_KEYS.test(k)) {
        out[k] = '[REDACTED]';
      } else if (SECRET_KEYS.test(k)) {
        out[k] = '[REDACTED_SECRET]';
      } else {
        out[k] = redactSelfReport(v, { home: homeDir, env });
      }
    }
    return out;
  }
  if (typeof value !== 'string') return value;

  let text = value;
  // Strip labeled request bodies, response prose, and user source code blocks:
  text = text.replace(/(?:request[ _-]?body|response[ _-]?prose|response[ _-]?body|user[ _-]?source(?:[ _-]?code)?|source[ _-]?code)\s*:\s*(?:```[\s\S]*?```|\{[\s\S]*?\}|"[^"]*"|'[^']*'|[^\n]+)/gi, '[REDACTED]');
  text = text.replace(/```(?:js|javascript|ts|typescript|py|python|sh|bash|mjs|cjs|html|css)?\n([\s\S]*?)```/gi, (full, inner) => {
    if (/^\s*at\s+.+\(?(?:file:\/\/)?[^\n]*src\/[a-z0-9-]+\.mjs:\d+/m.test(inner)) return full;
    return '[REDACTED_CODE]';
  });

  // Strip known token and secret formats:
  text = text.replace(/\b(?:gh[pousr]_[A-Za-z0-9_]{8,}|github_pat_[A-Za-z0-9_]{8,})\b/g, '[REDACTED_TOKEN]');
  text = text.replace(/\bsk-(?:ant-|proj-|live-|test-)?[A-Za-z0-9_-]{8,}\b/g, '[REDACTED_SECRET]');
  text = text.replace(/\bxox[baprs]-[A-Za-z0-9-]{8,}\b/g, '[REDACTED_SECRET]');
  text = text.replace(/\bAIza[A-Za-z0-9_-]{16,}\b/g, '[REDACTED_SECRET]');
  text = text.replace(/\bBearer\s+[A-Za-z0-9._~+/=-]{6,}/gi, 'Bearer [REDACTED_SECRET]');
  text = text.replace(/\bBasic\s+[A-Za-z0-9+/=]{6,}/gi, 'Basic [REDACTED_SECRET]');
  text = text.replace(/https?:\/\/hooks\.slack\.com\/services\/[^\s"'<>)]+/gi, '[REDACTED_WEBHOOK]');
  text = text.replace(/https?:\/\/(?:ptb\.|canary\.)?discord(?:app)?\.com\/api\/webhooks\/[^\s"'<>)]+/gi, '[REDACTED_WEBHOOK]');
  text = text.replace(/https?:\/\/[^\s)<>\]"'`]*?\/s\/[^/\s)<>\]"'`]+(?:\/[^\s)<>\]"'`]*)?/g, '(Try link removed)');
  text = text.replace(/\b((?:[a-z0-9_]*?(?:token|secret|password|passwd|api[_-]?key|authorization|cookie|webhook[_-]?url|private[_-]?key))\s*[:=]\s*["']?)([^\s"',;}\]]+)(["']?)/gi, '$1[REDACTED_SECRET]$3');

  // Strip secret values from env:
  if (env && typeof env === 'object') {
    for (const [k, v] of Object.entries(env)) {
      if (typeof v === 'string' && v.trim().length >= 6 && /(?:TOKEN|SECRET|KEY|PASSWORD|PASSWD|AUTH|WEBHOOK|COOKIE)/i.test(k)) {
        text = text.split(v).join('[REDACTED_SECRET]');
      }
    }
  }

  // Redact paths under home except PDD's own state paths:
  text = redactHomePaths(text, homeDir);
  return text;
}

export function selfReportConsent(repo, config = {}, state = {}) {
  const configured = typeof config?.selfReport === 'string' ? config.selfReport.trim().toLowerCase() : '';
  if (['auto', 'ask', 'off'].includes(configured)) {
    return { mode: configured, source: 'config', prompt: configured === 'ask' ? CONSENT_PROMPT : null };
  }
  const saved = typeof state?.selfReportConsent === 'string' ? state.selfReportConsent.trim().toLowerCase() : '';
  if (['auto', 'ask', 'off'].includes(saved)) {
    return { mode: saved, source: 'state', prompt: saved === 'ask' ? CONSENT_PROMPT : null };
  }
  const isPromptdriven = /^promptdriven\//i.test(String(repo ?? '').trim());
  if (isPromptdriven) {
    return { mode: 'auto', source: 'org-default', prompt: null };
  }
  return { mode: 'ask-once', source: 'outside-default', prompt: CONSENT_PROMPT };
}

function normalizeConsentAnswer(answer) {
  if (typeof answer === 'boolean') return answer ? 'auto' : 'off';
  const text = String(answer ?? '').trim().toLowerCase();
  if (/^(?:auto|y|yes|always)$/.test(text)) return 'auto';
  if (/^(?:ask|ask each time|each time)$/.test(text)) return 'ask';
  if (/^(?:off|n|no|never|disable)$/.test(text)) return 'off';
  return null;
}

export async function resolveSelfReportConsent({ repo, config = {}, state = {}, ask } = {}, ports = {}) {
  const decision = selfReportConsent(repo, config, state);
  if (decision.mode === 'auto') return { allowed: true, mode: 'auto', asked: false, prompt: null };
  if (decision.mode === 'off') return { allowed: false, mode: 'off', asked: false, prompt: null, reason: 'self-report-off' };

  const askFn = ask ?? ports.askConsent ?? ports.confirm ?? null;
  if (decision.mode === 'ask-once') {
    if (state.selfReportAsked && !state.selfReportConsent && !askFn) {
      return { allowed: false, mode: 'ask-once', asked: false, prompt: CONSENT_PROMPT, reason: 'consent-pending' };
    }
    state.selfReportAsked = true;
    state.selfReportConsentPrompt = CONSENT_PROMPT;
    if (!askFn) {
      return { allowed: false, mode: 'ask-once', asked: true, prompt: CONSENT_PROMPT, reason: 'consent-pending' };
    }
    const raw = await askFn(CONSENT_PROMPT);
    const chosen = normalizeConsentAnswer(raw);
    if (chosen === 'auto') {
      state.selfReportConsent = 'auto';
      return { allowed: true, mode: 'auto', asked: true, prompt: CONSENT_PROMPT };
    }
    if (chosen === 'ask') {
      state.selfReportConsent = 'ask';
      return { allowed: true, mode: 'ask', asked: true, prompt: CONSENT_PROMPT };
    }
    state.selfReportConsent = 'off';
    return { allowed: false, mode: 'off', asked: true, prompt: CONSENT_PROMPT, reason: 'consent-declined' };
  }

  // decision.mode === 'ask' (ask each time):
  if (!askFn) {
    state.selfReportConsentPrompt = CONSENT_PROMPT;
    return { allowed: false, mode: 'ask', asked: true, prompt: CONSENT_PROMPT, reason: 'consent-pending' };
  }
  const raw = await askFn(CONSENT_PROMPT);
  const chosen = normalizeConsentAnswer(raw);
  if (chosen === 'auto' || chosen === 'ask') {
    return { allowed: true, mode: 'ask', asked: true, prompt: CONSENT_PROMPT };
  }
  return { allowed: false, mode: 'ask', asked: true, prompt: CONSENT_PROMPT, reason: 'consent-declined' };
}

export function findSourceEvidence(cause, { fs = nativeFs, packageRoot = PACKAGE_ROOT } = {}) {
  const frame = parsePddStackFrame(cause?.evidence || cause?.stack || '', cause?.module || 'src/workflow-runner.mjs', cause?.fn || 'unknown');
  const supplied = String(cause?.module ?? '');
  const framed = String(frame.module ?? '');
  const modulePath = /^src\/[a-z0-9-]+\.mjs$/i.test(supplied)
    ? supplied
    : /^src\/[a-z0-9-]+\.mjs$/i.test(framed) ? framed : 'src/workflow-runner.mjs';
  const requestedLine = Number(cause?.line || frame.line);
  const lineNumber = Number.isSafeInteger(requestedLine) && requestedLine > 0 ? requestedLine : 1;
  const fullPath = join(packageRoot, modulePath);
  try {
    const lines = fs.readFileSync(fullPath, 'utf8').split(String.fromCharCode(10));
    const clamped = Math.max(1, Math.min(lineNumber, lines.length));
    return {
      module: modulePath,
      line: clamped,
      fileLine: modulePath + ':' + clamped,
      snippet: '',
    };
  } catch {
    const clamped = Math.min(lineNumber, 1_000_000);
    return {
      module: modulePath,
      line: clamped,
      fileLine: modulePath + ':' + clamped,
      snippet: '',
    };
  }
}

const SENSITIVE_SUBAGENT_ENV = [
  'PDD_AGENT_SESSION',
  'PDD_AUTOPILOT_CONTEXT',
  'CODEX_THREAD_ID',
  'CLAUDECODE',
  'HERDR_ENV',
  'HERDR_PANE_ID',
  'HERDR_SOCKET_PATH',
  'HERDR_TAB_ID',
  'HERDR_WORKSPACE_ID',
];

function diagnoseEnv(baseEnv = {}, profileEnv = {}) {
  const env = { ...baseEnv };
  for (const key of SENSITIVE_SUBAGENT_ENV) delete env[key];
  for (const [k, v] of Object.entries(profileEnv)) {
    if (v === undefined) delete env[k];
    else env[k] = v;
  }
  return env;
}

function runAgentProcess(file, args, { cwd, env, input = '', timeoutMs = 60_000, maxBytes = 2 * 1024 * 1024 } = {}) {
  return new Promise(resolve => {
    let stdout = '', stderr = '', bytes = 0, settled = false, child;
    const finish = result => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      resolve({ ...result, stdout, stderr });
    };
    try {
      child = spawn(file, args, { cwd, env, stdio: ['pipe', 'pipe', 'pipe'] });
    } catch (error) {
      finish({ code: 1, error: error.message });
      return;
    }
    const timer = setTimeout(() => {
      try { child.kill('SIGTERM'); } catch {}
      finish({ code: 1, timedOut: true });
    }, timeoutMs);
    const collect = (chunk, isOut) => {
      const text = Buffer.from(chunk).toString('utf8');
      bytes += Buffer.byteLength(text);
      if (bytes <= maxBytes) {
        if (isOut) stdout += text;
        else stderr += text;
      }
    };
    child.stdout.on('data', chunk => collect(chunk, true));
    child.stderr.on('data', chunk => collect(chunk, false));
    child.on('error', error => finish({ code: 1, error: error.message }));
    child.on('close', code => finish({ code: code ?? 1 }));
    child.stdin.on('error', () => {});
    child.stdin.end(input);
  });
}

function parseDiagnoseOutput(kind, stdout) {
  let session = null, text = '';
  for (const rawLine of String(stdout ?? '').split('\n').map(s => s.trim()).filter(Boolean)) {
    let row;
    try { row = JSON.parse(rawLine); } catch { continue; }
    if (kind === 'codex') {
      if (row.type === 'thread.started' && typeof row.thread_id === 'string') session = row.thread_id;
      if (row.type === 'item.completed' && row.item?.type === 'agent_message' && typeof row.item.text === 'string') text = row.item.text;
    } else if (kind === 'claude') {
      if (typeof row.session_id === 'string') session = row.session_id;
      if (typeof row.result === 'string') text = row.result;
    }
  }
  if (!text && String(stdout ?? '').trim().startsWith('{')) {
    text = String(stdout).trim();
  }
  let parsed = null;
  if (text) {
    try { parsed = JSON.parse(text); } catch {
      const m = /\{[\s\S]*\}/.exec(text);
      if (m) {
        try { parsed = JSON.parse(m[0]); } catch { parsed = null; }
      }
    }
  }
  return { session, parsed };
}

export function formatSelfReportBody(report, { home, env = process.env } = {}) {
  const r = safePublicReport(report);
  const marker = '<!-- pdd:self-report:' + r.signature + ' -->';
  const runtimeMarker = r.side === 'runtime'
    ? String.fromCharCode(10) + '<!-- pdd:runtime-cause:' + r.cause + ' -->'
    : '';
  const closedNumber = Number(report?.closedMatch?.number);
  const closedRef = Number.isSafeInteger(closedNumber) && closedNumber > 0
    ? String.fromCharCode(10) + 'Previously seen in closed issue #' + closedNumber + '.'
    : '';
  const fence = String.fromCharCode(96).repeat(3) + 'text';
  const body = [
    marker + runtimeMarker,
    '',
    '## Problem',
    r.problem,
    '',
    '## Steps to reproduce',
    r.steps.map((step, index) => (index + 1) + '. ' + step).join(String.fromCharCode(10)),
    '',
    '## Expected vs. actual',
    '- **Expected:** ' + r.expected,
    '- **Actual:** ' + r.actual,
    '',
    '## Evidence',
    fence,
    r.evidence,
    String.fromCharCode(96).repeat(3),
    '',
    '## Versions',
    '- **pdd:** ' + r.versions.pdd,
    '- **Agent:** ' + r.versions.agent,
    '- **Node:** ' + r.versions.node,
    '- **OS:** ' + r.versions.os,
    '',
    '## Suspected root cause',
    r.rootCause + closedRef,
  ].join(String.fromCharCode(10));
  return redactSelfReport(body, { home, env });
}

export async function diagnosePddFailure(run = {}, cause = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const env = ports.env ?? process.env;
  const home = ports.home ?? env?.HOME ?? homedir();
  const packageRoot = ports.packageRoot ?? PACKAGE_ROOT;
  const now = typeof ports.now === 'function' ? ports.now() : Date.now();
  const pddVersion = packageVersion(fs, packageRoot);
  const sourceInfo = findSourceEvidence(cause, { fs, packageRoot });
  const code = cause.code || 'ERR_PDD_CRASH';
  const module = sourceInfo.module || cause.module || 'src/workflow-runner.mjs';
  const fn = cause.fn || 'unknown';
  const signature = cause.signature || buildSignature(code, module, fn);

  let brief = '';
  try { brief = fs.readFileSync(BRIEF_PATH, 'utf8'); } catch { brief = '# Autopilot Self-Report Diagnosis'; }

  const taskInput = redactSelfReport({
    task: 'self-report-diagnose',
    targetRepository: SELF_REPORT_REPO,
    run: { number: run.number ?? null, runId: run.runId ?? null },
    runNumber: run.number ?? null,
    runId: run.runId ?? null,
    runDir: run.runDir ?? null,
    packageRoot,
    pddVersion,
    nodeVersion: process.version,
    osVersion: `${process.platform} ${process.arch}`,
    cause: {
      side: cause.side || 'pdd',
      kind: cause.kind || 'command-crash',
      code,
      module,
      fn,
      line: sourceInfo.line,
      fileLine: sourceInfo.fileLine,
      snippet: sourceInfo.snippet,
      signature,
      command: cause.command || 'pdd',
      summary: cause.summary || '',
      evidence: cause.evidence || '',
    },
  }, { home, env });

  let sessionId = null;
  let diagnosisOutput = null;
  let agentKind = ['codex', 'claude'].includes(ports.agent ?? run.agent) ? (ports.agent ?? run.agent) : 'codex';
  let configDir = null;

  if (typeof ports.diagnose === 'function') {
    const reply = await ports.diagnose({ run, cause: taskInput.cause, brief, taskInput });
    sessionId = reply?.session?.id ?? reply?.session ?? null;
    diagnosisOutput = reply?.diagnosis ?? reply;
  } else {
    try {
      const profile = launchProfile(run);
      configDir = profile?.configDir ?? null;
      let command = ports.agentCommand || agentKind;
      let defEnv = {};
      if (ports.agentDefinitions) {
        const definitions = await ports.agentDefinitions({ cwd: run.sourceRoot || run.root || packageRoot, env });
        const def = Array.isArray(definitions) ? definitions.find(d => d.kind === agentKind) : null;
        if (def?.command) command = def.command;
        if (def?.env) defEnv = def.env;
      }
      const childEnv = diagnoseEnv(env, defEnv);
      const promptText = `${brief.trim()}\n\nTask input:\n${JSON.stringify(taskInput)}`;
      const args = agentKind === 'claude'
        ? ['-p', '--output-format', 'json', '--permission-mode', 'plan', ...(profile?.model ? ['--model', profile.model] : []), promptText]
        : ['exec', '--sandbox', 'read-only', '--skip-git-repo-check', '--json', '-C', run.root || packageRoot, ...(profile?.model ? ['-m', profile.model] : []), '-'];
      const exec = ports.runDiagnoseProcess ?? ports.execute ?? ports.execFile ?? ((file, a, o) => runAgentProcess(file, a, o));
      const reply = await exec(command, args, {
        cwd: run.root || packageRoot,
        env: childEnv,
        input: agentKind === 'codex' ? promptText : '',
        purpose: 'self-report-diagnose',
      });
      if (reply && (reply.code === undefined || reply.code === 0)) {
        const parsed = parseDiagnoseOutput(agentKind, reply.stdout);
        sessionId = parsed.session;
        diagnosisOutput = parsed.parsed;
      }
    } catch { /* Fallback to deterministic local source diagnosis below. */ }
  }

  // Persist subagent session in runDir/self-reports for cost-ledger token attribution:
  if (typeof run.runDir === 'string') {
    try {
      const folder = join(run.runDir, 'self-reports');
      fs.mkdirSync(folder, { recursive: true, mode: 0o700 });
      const recordId = createHash('sha256').update(`${run.runId ?? 'run'}:${signature}`).digest('hex').slice(0, 16);
      const recordPath = join(folder, `${recordId}.json`);
      fs.writeFileSync(recordPath, JSON.stringify({
        schema: 'pdd.self-report.v1',
        runId: run.runId ?? null,
        number: run.number ?? null,
        at: now,
        signature,
        chat: {
          agent: agentKind,
          configDir,
          startedAt: now,
          root: run.root ?? null,
          ...(sessionId ? { session: { id: sessionId } } : {}),
        },
      }, null, 2) + '\n', { mode: 0o600 });
    } catch { /* Non-fatal if runDir is read-only in a synthetic test. */ }
  }

  const report = safePublicReport({
    side: 'pdd',
    kind: cause.kind,
    code,
    module,
    fn,
    line: sourceInfo.line,
    pddVersion,
    agent: agentKind,
    diagnosisLocation: readDiagnosisLocation(diagnosisOutput, signature, { fs, packageRoot }),
  });
  report.session = typeof sessionId === 'string' ? { id: sessionId, agent: agentKind, at: now } : null;
  report.body = formatSelfReportBody(report, { home, env });
  return report;
}

function readMachineCap(stateRoot, fs = nativeFs) {
  if (!stateRoot) return { days: {} };
  try {
    const parsed = JSON.parse(fs.readFileSync(join(stateRoot, 'self-report-machine.json'), 'utf8'));
    return parsed && typeof parsed === 'object' && parsed.days && typeof parsed.days === 'object' ? parsed : { days: {} };
  } catch {
    return { days: {} };
  }
}

function writeMachineCap(stateRoot, data, fs = nativeFs) {
  if (!stateRoot) return;
  try {
    fs.mkdirSync(stateRoot, { recursive: true, mode: 0o700 });
    const file = join(stateRoot, 'self-report-machine.json');
    const tmp = `${file}.${randomUUID()}.tmp`;
    fs.writeFileSync(tmp, JSON.stringify(data, null, 2) + '\n', { mode: 0o600 });
    fs.renameSync(tmp, file);
  } catch { /* Keep in-memory state if stateRoot is unavailable. */ }
}

function ensureCounters(holder) {
  if (!holder || typeof holder !== 'object') return { filed: 0, commented: 0, skipped: 0 };
  holder.selfReports ??= { filed: 0, commented: 0, skipped: 0 };
  if (Array.isArray(holder.selfReports)) {
    let filed = 0, commented = 0, skipped = 0;
    for (const r of holder.selfReports) {
      if (r?.action === 'filed') filed++;
      else if (r?.action === 'commented') commented++;
      else if (r?.action === 'skipped') skipped++;
    }
    return { filed, commented, skipped };
  }
  holder.selfReports.filed = Number(holder.selfReports.filed) || 0;
  holder.selfReports.commented = Number(holder.selfReports.commented) || 0;
  holder.selfReports.skipped = Number(holder.selfReports.skipped) || 0;
  return holder.selfReports;
}

function recordRunSelfReport(run, entry, ports = {}) {
  if (!run || typeof run !== 'object') return;
  run.selfReports = Array.isArray(run.selfReports) ? run.selfReports : [];
  if (!run.selfReports.some(row => row?.id === entry.id)) run.selfReports.push(entry);
  if (typeof run.runDir === 'string') {
    try {
      updateRun(run.runDir, latest => {
        if (latest.runId && run.runId && latest.runId !== run.runId) return latest;
        latest.selfReports = Array.isArray(latest.selfReports) ? latest.selfReports : [];
        if (!latest.selfReports.some(r => r.id === entry.id)) latest.selfReports.push(entry);
        if (entry.blocker && !['completed', 'cancelled'].includes(latest.state)) {
          latest.blockedOn = entry.blocker;
          latest.state = 'paused';
          if (entry.parkReason) latest.parkReason = entry.parkReason;
        }
        return latest;
      }, ports);
    } catch { /* Synthetic in-memory run in unit tests. */ }
  }
}

async function hasRuntimeWriteAccess(ports = {}) {
  if (typeof ports.repoPermission === 'function') {
    try {
      const value = await ports.repoPermission(FORBIDDEN_RUNTIME_REPO);
      if (typeof value === 'boolean') return value;
      const permission = typeof value === 'string' ? value : value?.viewerPermission ?? value?.permission;
      return ['WRITE', 'MAINTAIN', 'ADMIN'].includes(String(permission ?? '').toUpperCase());
    } catch { return false; }
  }
  const exec = ports.execute ?? ports.execFile;
  if (!exec) return false;
  try {
    const result = await exec('gh', ['repo', 'view', FORBIDDEN_RUNTIME_REPO, '--json', 'viewerPermission'], { purpose: 'self-report-access' });
    if (result.code !== undefined && result.code !== 0) return false;
    const parsed = JSON.parse(result.stdout || '{}');
    return ['WRITE', 'MAINTAIN', 'ADMIN'].includes(String(parsed.viewerPermission ?? '').toUpperCase());
  } catch { return false; }
}

function nextSelfReportEntryId(run, signature, action, at) {
  const prefix = String(run?.runId ?? 'run') + ':' + signature + ':' + action + ':';
  const existing = Array.isArray(run?.selfReports) ? run.selfReports.filter(row => String(row?.id ?? '').startsWith(prefix)).length : 0;
  return prefix + at + ':' + (existing + 1);
}

export async function fileSelfReport(input = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const env = ports.env ?? process.env;
  const home = ports.home ?? env?.HOME ?? homedir();
  const now = typeof ports.now === 'function' ? ports.now() : Date.now();
  const state = input.state ?? ports.state ?? {};
  const config = input.config ?? ports.config ?? {};
  const run = input.run ?? null;
  const workingRepo = String(input.repo ?? state.repo ?? run?.repo ?? '').trim();
  const side = input.side === 'runtime' ? 'runtime' : 'pdd';
  const requestedRepo = String(input.targetRepo ?? '').trim().toLowerCase();
  if (requestedRepo && ![SELF_REPORT_REPO, FORBIDDEN_RUNTIME_REPO].includes(requestedRepo)) {
    throw Error('Refusing to file self-report in ' + input.targetRepo + '; target must be ' + SELF_REPORT_REPO + ' or ' + FORBIDDEN_RUNTIME_REPO + '.');
  }
  if (side !== 'runtime' && requestedRepo === FORBIDDEN_RUNTIME_REPO) {
    throw Error('PDD self-reports must target ' + SELF_REPORT_REPO + '.');
  }
  let targetRepo = SELF_REPORT_REPO;
  const publicReport = safePublicReport(input);
  const { code, module, fn, signature } = publicReport;
  const marker = '<!-- pdd:self-report:' + signature + ' -->';
  const runtimeMarker = side === 'runtime' ? '<!-- pdd:runtime-cause:' + publicReport.cause + ' -->' : null;

  const counters = ensureCounters(state);

  // Check consent when not already resolved:
  if (input.checkConsent !== false && (workingRepo || config?.selfReport || state?.selfReportConsent)) {
    const consent = await resolveSelfReportConsent({
      repo: workingRepo,
      config,
      state,
      ask: input.askConsent ?? ports.askConsent ?? ports.confirm,
    }, ports);
    if (!consent.allowed) {
      counters.skipped++;
      const entry = { id: nextSelfReportEntryId(run, signature, 'skipped', now), at: now, action: 'skipped', reason: consent.reason || 'consent', side, signature, issue: null };
      recordRunSelfReport(run, entry, ports);
      return { action: 'skipped', reason: consent.reason || 'consent', prompt: consent.prompt ?? null, issue: null, signature, targetRepo };
    }
  }

  targetRepo = side === 'runtime' && await hasRuntimeWriteAccess(ports) ? FORBIDDEN_RUNTIME_REPO : SELF_REPORT_REPO;
  const detectedVersion = packageVersion(fs, ports.packageRoot ?? PACKAGE_ROOT);
  const pddVersion = publicVersion(input.pddVersion) === 'unknown' ? publicVersion(detectedVersion) : publicVersion(input.pddVersion);
  const title = publicReport.side === 'runtime'
    ? 'Runtime report: ' + publicReport.cause
    : 'PDD ' + publicReport.kind + ': ' + publicReport.code + ' in ' + publicReport.module + ' (' + publicReport.fn + ')';

  const searchIssues = ports.searchIssues ?? (async () => {
    const exec = ports.execute ?? ports.execFile;
    if (!exec) return [];
    const r = await exec('gh', [
      'issue', 'list', '--repo', targetRepo, '--state', 'all',
      '--search', `"${marker}" in:body`, '--limit', '100',
      '--json', 'number,url,state,body,title,closedAt,updatedAt',
    ], { purpose: 'self-report' });
    if (r.code !== undefined && r.code !== 0) throw Error(r.stderr || 'Self-report issue search failed');
    return JSON.parse(r.stdout || '[]');
  });

  const allMatches = (await searchIssues(marker, { targetRepo, signature, runtimeMarker })) || [];
  const matching = allMatches.filter(row => {
    const b = String(row?.body ?? '');
    return b.includes(marker) || (runtimeMarker && b.includes(runtimeMarker));
  });
  const openMatch = matching.find(row => String(row?.state ?? 'open').toLowerCase() === 'open');
  const closedMatch = !openMatch ? matching.find(row => String(row?.state ?? '').toLowerCase() === 'closed') : null;

  const occurrenceComment = redactSelfReport([
    'New occurrence of ' + signature + ':',
    '- **Summary:** ' + publicReport.summary,
    '- **pdd version:** ' + pddVersion,
    '- **Observed at:** ' + new Date(now).toISOString(),
  ].join(String.fromCharCode(10)), { home, env });

  const commentOnIssue = async issue => {
    if (typeof ports.commentIssue === 'function') {
      await ports.commentIssue({ repo: targetRepo, number: issue.number, body: occurrenceComment, signature });
    } else {
      const exec = ports.execute ?? ports.execFile;
      if (exec) {
        const r = await exec('gh', ['issue', 'comment', String(issue.number), '--repo', targetRepo, '--body', occurrenceComment], { purpose: 'self-report' });
        if (r.code !== undefined && r.code !== 0) throw Error(r.stderr || 'Self-report comment failed');
      }
    }
  };

  // 1. Same cause signature open -> add one comment, no new issue.
  if (openMatch) {
    const issue = {
      number: Number(openMatch.number),
      url: openMatch.url || `https://github.com/${targetRepo}/issues/${openMatch.number}`,
    };
    await commentOnIssue(issue);
    counters.commented++;
    const blocker = side === 'runtime'
      ? { kind: 'runtime', until: String(issue.number), cause: publicReport.cause, batch: input.batch ?? null, checkKind: 'pdd test', evidence: run ? runtimeEvidence(run) : null }
      : { kind: 'pdd', until: `#${issue.number}` };
    const entry = { id: nextSelfReportEntryId(run, signature, 'commented', now), at: now, action: 'commented', side, signature, issue, blocker, parkReason: `Blocked on ${SELF_REPORT_REPO}#${issue.number} (${signature})` };
    recordRunSelfReport(run, entry, ports);
    return { action: 'commented', issue, signature, targetRepo, blocker };
  }

  // 2. Check daily machine cap (at most 5 new self-reports per machine per UTC day; more occurrences only comment).
  const stateRoot = ports.stateRoot ?? (typeof state.stateFile === 'string' ? dirname(state.stateFile) : null);
  const capData = state.selfReportMachine ?? readMachineCap(stateRoot, fs);
  const today = utcDay(now);
  capData.days ??= {};
  const createdToday = Array.isArray(capData.days[today]) ? capData.days[today] : (capData.days[today] = []);

  if (createdToday.length >= DAILY_SELF_REPORT_CAP) {
    const fallbackIssue = closedMatch
      ? { number: Number(closedMatch.number), url: closedMatch.url || `https://github.com/${targetRepo}/issues/${closedMatch.number}` }
      : createdToday.at(-1)?.issue ?? null;
    if (fallbackIssue) {
      await commentOnIssue(fallbackIssue);
      counters.commented++;
      const blocker = side === 'runtime'
        ? { kind: 'runtime', until: String(fallbackIssue.number), cause: publicReport.cause, batch: input.batch ?? null, checkKind: 'pdd test', evidence: run ? runtimeEvidence(run) : null }
        : { kind: 'pdd', until: `#${fallbackIssue.number}` };
      const entry = { id: nextSelfReportEntryId(run, signature, 'commented', now), at: now, action: 'commented', capped: true, side, signature, issue: fallbackIssue, blocker, parkReason: `Blocked on ${SELF_REPORT_REPO}#${fallbackIssue.number} (${signature})` };
      recordRunSelfReport(run, entry, ports);
      return { action: 'commented', capped: true, issue: fallbackIssue, signature, targetRepo, blocker };
    }
    counters.skipped++;
    const entry = { id: nextSelfReportEntryId(run, signature, 'skipped', now), at: now, action: 'skipped', capped: true, reason: 'daily-cap', side, signature, issue: null };
    recordRunSelfReport(run, entry, ports);
    return { action: 'skipped', capped: true, reason: 'daily-cap', issue: null, signature, targetRepo };
  }

  // 3. File one new issue in the selected target repository:
  const labels = side === 'runtime'
    ? (targetRepo === SELF_REPORT_REPO ? ['pdd:self-report', 'pdd:runtime-report'] : [])
    : ['pdd:self-report'];
  const rawMaintainer = targetRepo === FORBIDDEN_RUNTIME_REPO
    ? input.runtimeOwner ?? config?.runtimeOwner ?? null
    : input.maintainer ?? config?.maintainer ?? config?.pddMaintainer ?? config?.selfReportMaintainer ?? null;
  const assignee = validLogin(rawMaintainer) ? rawMaintainer.trim() : null;
  const body = formatSelfReportBody({
    ...publicReport,
    pddVersion,
    closedMatch,
  }, { home, env });

  let createdIssue;
  if (typeof ports.createIssue === 'function') {
    createdIssue = await ports.createIssue({
      repo: targetRepo,
      title,
      body,
      labels,
      assignee,
      signature,
      side,
    });
  } else {
    const exec = ports.execute ?? ports.execFile;
    if (!exec) throw Error('No GitHub execution port available for self-report filing');
    for (const label of labels) {
      const color = label === 'pdd:runtime-report' ? 'B60205' : 'D93F0B';
      const desc = label === 'pdd:runtime-report' ? 'Automatic Runtime self-report' : 'Automatic PDD/Autopilot self-report';
      await exec('gh', ['label', 'create', label, '--repo', targetRepo, '--color', color, '--description', desc, '--force'], { purpose: 'self-report' });
    }
    const args = ['issue', 'create', '--repo', targetRepo, '--title', title, '--body', body];
    for (const label of labels) args.push('--label', label);
    if (assignee) args.push('--assignee', assignee);
    const r = await exec('gh', args, { purpose: 'self-report' });
    if (r.code !== undefined && r.code !== 0) throw Error(r.stderr || 'Self-report issue creation failed');
    const url = String(r.stdout ?? '').trim();
    const number = Number(/\/issues\/([1-9][0-9]*)$/.exec(url)?.[1]);
    if (!number) throw Error('Self-report issue number unavailable');
    createdIssue = { number, url: `https://github.com/${targetRepo}/issues/${number}` };
  }

  const issue = {
    number: Number(createdIssue.number),
    url: createdIssue.url || `https://github.com/${targetRepo}/issues/${createdIssue.number}`,
  };
  createdToday.push({ at: now, signature, side, issue });
  state.selfReportMachine = capData;
  writeMachineCap(stateRoot, capData, fs);

  counters.filed++;
  const blocker = side === 'runtime'
    ? { kind: 'runtime', until: String(issue.number), cause: publicReport.cause, batch: input.batch ?? null, checkKind: 'pdd test', evidence: run ? runtimeEvidence(run) : null }
    : { kind: 'pdd', until: `#${issue.number}` };
  const entry = {
    id: nextSelfReportEntryId(run, signature, 'filed', now),
    at: now,
    action: 'filed',
    side,
    signature,
    issue,
    labels,
    assignee,
    blocker,
    parkReason: `Blocked on ${SELF_REPORT_REPO}#${issue.number} (${signature})`,
  };
  recordRunSelfReport(run, entry, ports);
  return { action: 'filed', issue, signature, labels, assignee, targetRepo, blocker };
}

export function recordCommandCrash({ cwd, ref, command, error, run: providedRun } = {}, ports = {}) {
  if (!error || error.code === 'workflow_run_save_failed' || error.code === 'workflow_progress_refused') return null;
  const fs = ports.fs ?? nativeFs;
  const now = typeof ports.now === 'function' ? ports.now() : Date.now();
  const frame = parsePddStackFrame(error.stack, 'src/workflow-runner.mjs', command || 'runPdd');
  const code = String(error.code || error.name || 'ERR_PDD_CRASH').trim();
  const crash = {
    at: now,
    command: String(command || 'pdd'),
    code,
    message: oneLine(error.message ?? error),
    stack: String(error.stack ?? error.message ?? error),
    module: frame.module,
    fn: frame.fn,
    line: frame.line,
    fileLine: frame.fileLine,
    signature: buildSignature(code, frame.module, frame.fn),
  };

  let targetRunDir = providedRun?.runDir ?? null;
  if (!targetRunDir && typeof cwd === 'string') {
    // Check if cwd is a run worktree or repository root:
    let dir = cwd;
    for (let depth = 0; depth < 5 && dir; depth++) {
      const gitPath = join(dir, '.git');
      try {
        const stat = fs.statSync(gitPath);
        if (stat.isFile()) {
          const gitdirText = fs.readFileSync(gitPath, 'utf8');
          const m = /gitdir:\s*(.+)/.exec(gitdirText);
          if (m) {
            const commonDir = dirname(dirname(m[1].trim()));
            const runsFolder = join(commonDir, 'pdd', 'runs');
            for (const name of fs.readdirSync(runsFolder)) {
              if (!/^[1-9][0-9]*$/.test(name)) continue;
              const candidateDir = join(runsFolder, name);
              const candidate = JSON.parse(fs.readFileSync(join(candidateDir, 'status.json'), 'utf8'));
              if (candidate?.root === dir || (ref && String(candidate?.number) === String(ref))) {
                targetRunDir = candidateDir;
                break;
              }
            }
          }
          break;
        } else if (stat.isDirectory() && ref && /^[1-9][0-9]*$/.test(String(ref))) {
          const candidateDir = join(gitPath, 'pdd', 'runs', String(ref));
          if (fs.existsSync(join(candidateDir, 'status.json'))) targetRunDir = candidateDir;
          break;
        }
      } catch {}
      const parent = dirname(dir);
      if (parent === dir) break;
      dir = parent;
    }
  }

  if (!targetRunDir) return crash;
  try {
    fs.writeFileSync(join(targetRunDir, 'command-crash.json'), JSON.stringify(crash, null, 2) + '\n', { mode: 0o600 });
  } catch {}
  try {
    updateRun(targetRunDir, latest => {
      latest.commandFailure = crash;
      latest.done = latest.done && typeof latest.done === 'object' ? latest.done : {};
      if (Array.isArray(latest.areas) && latest.areas[latest.area] && !Array.isArray(latest.areas[latest.area].steps)) {
        latest.areas[latest.area].steps = ['change', 'verify', 'check', 'review'];
      }
      if (latest.automaticOrigin && !['completed', 'cancelled'].includes(latest.state)) {
        latest.state = 'stuck';
        latest.parkReason = `pdd command crash (${crash.code} in ${crash.module}:${crash.fn}): ${crash.message}`;
      }
      return latest;
    }, ports);
  } catch {}
  return crash;
}

export async function reconcileSelfReports(state, ports = {}, config = {}, runs = [], { localOnly = false, includeRuntime = false } = {}) {
  const blockers = new Map();
  ensureCounters(state);
  const ledger = state.selfReportLedger ??= { seen: {} };
  ledger.seen ??= {};

  const save = async () => {
    if (typeof ports.save !== 'function') return true;
    try { return (await ports.save()) !== false; } catch { return false; }
  };
  const timestamp = () => typeof ports.now === 'function' ? ports.now() : Date.now();

  for (const run of runs) {
    if (!run || ['completed', 'cancelled'].includes(run.state) || ['waking', 'releasing'].includes(run.parking?.phase)) continue;
    if (run.routeWait || run.blockedOn?.kind === 'pdd-route') continue;

    let check = null;
    try { check = await ports.readCheck?.(run); } catch {}
    const cause = classifyFailureCause(run, { check, fs: ports.fs ?? nativeFs });
    if (!cause.reportable || (cause.side === 'runtime' && !includeRuntime)) continue;

    const prior = run.parking?.blocker ?? run.blockedOn;
    const existingEntry = Array.isArray(run.selfReports)
      ? run.selfReports.find(row => row?.signature === cause.signature && row?.issue?.number)
      : null;
    if (existingEntry?.issue?.number) {
      const blocker = cause.side === 'runtime'
        ? { kind: 'runtime', until: String(existingEntry.issue.number), cause: cause.kind, batch: cause.batch ?? null, checkKind: 'pdd test', evidence: runtimeEvidence(run) }
        : { kind: 'pdd', until: '#' + existingEntry.issue.number };
      blockers.set(run.number, blocker);
      continue;
    }
    if (prior && ['pdd', 'runtime'].includes(prior.kind) && /^(?:#)?[1-9][0-9]*$/.test(String(prior.until ?? ''))) {
      blockers.set(run.number, prior);
      continue;
    }
    if (localOnly) {
      blockers.set(run.number, { kind: 'pdd-pending', until: null });
      continue;
    }

    const key = String(run.runId ?? run.number) + ':' + cause.signature;
    let custody = ledger.seen[key] ?? { signature: cause.signature, filingAttempts: 0 };
    if (custody.issue?.number) {
      const blocker = cause.side === 'runtime'
        ? { kind: 'runtime', until: String(custody.issue.number), cause: cause.kind, batch: cause.batch ?? null, checkKind: 'pdd test', evidence: runtimeEvidence(run) }
        : { kind: 'pdd', until: '#' + custody.issue.number };
      blockers.set(run.number, blocker);
      continue;
    }
    if (custody.filingStatus === 'exhausted' || (custody.status === 'complete' && custody.action === 'skipped')) continue;
    if (custody.action === 'skipped' && !custody.diagnosisResult) continue;

    const consent = await resolveSelfReportConsent({
      repo: state.repo ?? run.repo,
      config,
      state,
      ask: ports.askConsent ?? ports.confirm,
    }, ports);
    if (!consent.allowed) {
      if (!custody.consentRecorded) {
        const at = timestamp();
        custody = { ...custody, at, status: 'complete', action: 'skipped', reason: consent.reason || 'consent', consentRecorded: true };
        ledger.seen[key] = custody;
        state.selfReports.skipped++;
        recordRunSelfReport(run, {
          id: key + ':skipped',
          at,
          action: 'skipped',
          reason: consent.reason || 'consent',
          side: cause.side,
          signature: cause.signature,
          issue: null,
        }, ports);
        await save();
      }
      continue;
    }

    const savedDiagnosis = Array.isArray(run.selfReports)
      ? run.selfReports.find(row => row?.action === 'diagnosed' && row?.signature === cause.signature && row?.result)
      : null;
    let report = custody.diagnosisResult
      ? safePublicReport(custody.diagnosisResult)
      : savedDiagnosis?.result ? safePublicReport(savedDiagnosis.result) : null;
    let diagnosisSession = custody.diagnosisSession ?? savedDiagnosis?.session ?? null;
    if (report && !custody.diagnosisResult) {
      custody = {
        ...custody,
        diagnosisAttempted: true,
        diagnosisStatus: 'recovered-from-run',
        diagnosisResult: report,
        ...(diagnosisSession ? { diagnosisSession } : {}),
      };
      ledger.seen[key] = custody;
      if (!await save()) continue;
    }
    if (!report && custody.diagnosisAttempted) {
      report = safePublicReport({
        side: cause.side, kind: cause.kind, cause: cause.kind, code: cause.code, module: cause.module, fn: cause.fn, line: cause.line,
      });
      custody = { ...custody, diagnosisStatus: 'recovered-from-attempt', diagnosisResult: report };
      ledger.seen[key] = custody;
      if (!await save()) continue;
    }
    if (!report) {
      const startedAt = timestamp();
      custody = {
        ...custody,
        at: custody.at ?? startedAt,
        signature: cause.signature,
        diagnosisAttempted: true,
        diagnosisStatus: 'started',
        diagnosisAt: startedAt,
        filingAttempts: Number(custody.filingAttempts) || 0,
      };
      ledger.seen[key] = custody;
      if (!await save()) continue;

      let diagnosed;
      try {
        diagnosed = cause.side === 'pdd'
          ? await diagnosePddFailure(run, cause, ports)
          : safePublicReport({
              side: 'runtime',
              cause: cause.kind,
              kind: cause.kind,
              code: cause.code,
              module: cause.module,
              fn: cause.fn,
              line: cause.line,
            });
      } catch {
        diagnosed = safePublicReport({
          side: cause.side,
          cause: cause.kind,
          kind: cause.kind,
          code: cause.code,
          module: cause.module,
          fn: cause.fn,
          line: cause.line,
        });
      }
      diagnosisSession = diagnosed?.session ?? null;
      report = safePublicReport(diagnosed ?? {
        side: cause.side, cause: cause.kind, kind: cause.kind, code: cause.code, module: cause.module, fn: cause.fn, line: cause.line,
      });
      custody = {
        ...custody,
        diagnosisStatus: 'complete',
        diagnosisResult: report,
        ...(diagnosisSession ? { diagnosisSession } : {}),
      };
      ledger.seen[key] = custody;
      recordRunSelfReport(run, {
        id: key + ':diagnosed',
        at: Number(diagnosisSession?.at) || startedAt,
        action: 'diagnosed',
        side: cause.side,
        signature: cause.signature,
        issue: null,
        result: report,
        ...(diagnosisSession?.id ? {
          session: {
            id: diagnosisSession.id,
            agent: diagnosisSession.agent ?? run.agent ?? 'codex',
            at: Number(diagnosisSession.at) || startedAt,
          },
        } : {}),
      }, ports);
      if (!await save()) continue;
    }

    const attempts = Number(custody.filingAttempts) || 0;
    if (attempts >= MAX_SELF_REPORT_FILE_ATTEMPTS) {
      ledger.seen[key] = { ...custody, filingStatus: 'exhausted' };
      await save();
      continue;
    }

    const attempt = attempts + 1;
    custody = { ...custody, filingAttempts: attempt, filingStatus: 'attempting', lastAttemptAt: timestamp() };
    ledger.seen[key] = custody;
    if (!await save()) continue;

    try {
      const filed = await fileSelfReport({
        ...report,
        run,
        state,
        config,
        repo: state.repo ?? run.repo,
        checkConsent: false,
      }, ports);
      custody = {
        ...custody,
        status: 'complete',
        action: filed.action,
        issue: filed.issue ?? null,
        targetRepo: filed.targetRepo ?? null,
        filingStatus: 'complete',
      };
      ledger.seen[key] = custody;
      if (filed.blocker && filed.issue?.number) blockers.set(run.number, filed.blocker);
      await save();
    } catch {
      const filingStatus = attempt >= MAX_SELF_REPORT_FILE_ATTEMPTS ? 'exhausted' : 'retry';
      ledger.seen[key] = { ...custody, filingStatus, lastFailure: 'github-filing' };
      await save();
      ports.warn?.('Self-report filing attempt ' + attempt + ' of ' + MAX_SELF_REPORT_FILE_ATTEMPTS + ' failed for run #' + run.number + '; the saved diagnosis is retained.');
    }
  }
  return blockers;
}
