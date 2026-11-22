// Layer-2 G3 Standard Test Report Comparator & Base-Owned Edited-Test Oracle.
// Deterministic, non-compensatory, fail-closed diff across JUnit XML, TAP v13, and go test -json.
import { spawn } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { cpSync, existsSync, lstatSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, renameSync, rmSync, unlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, isAbsolute, join, relative, sep } from 'node:path';
import { scrubReadonlyEnv } from '../../shared/readonly-agent.mjs';
import {
  normalizeRunnerKind, parseCargoReport, parseGoJsonReport, parseJunitXml, parseTapReport,
} from './test-runners.mjs';

export { parseGoJsonReport, parseJunitXml, parseTapReport };
export const CACHE_KEY_FIELDS = Object.freeze(['baseSha', 'policyDigest', 'recipeDigest', 'toolchain', 'platform', 'profile']);
const STATUS_RANK = Object.freeze({ pass: 0, skip: 1, fail: 2, error: 3 });

const canonicalRelPath = v => typeof v === 'string' && v.trim().length > 0 && v.length <= 1000
  && !isAbsolute(v) && !/[\\\x00-\x1f\x7f]/.test(v)
  && !v.split('/').some(p => !p || p === '.' || p === '..' || p.toLowerCase() === '.git');

export function parseStandardTestReport(rawReport, format = 'auto') {
  const bad = reason => ({ ok: false, complete: false, format: null, cases: [], counts: null, reason });
  if (rawReport === null || rawReport === undefined) return bad('missing_report');
  if (typeof rawReport === 'object' && !Array.isArray(rawReport)) {
    if (rawReport.ok === false || rawReport.complete === false || !Array.isArray(rawReport.cases)) {
      return bad(rawReport.reason || 'incomplete_report');
    }
    const cases = rawReport.cases
      .filter(c => c && typeof c.id === 'string' && c.id.trim() && Object.hasOwn(STATUS_RANK, c.status))
      .map(c => ({ id: c.id.trim(), status: c.status, durationMs: Number.isFinite(c.durationMs) ? c.durationMs : null }));
    if (cases.length !== rawReport.cases.length) return bad('malformed_case_entries');
    const passed = cases.filter(c => c.status === 'pass').length;
    const failed = cases.filter(c => c.status === 'fail' || c.status === 'error').length;
    const skipped = cases.filter(c => c.status === 'skip').length;
    return {
      ok: true, complete: true, format: rawReport.format ?? 'custom', cases,
      counts: rawReport.counts ?? { total: cases.length, passed, failed, skipped, format: rawReport.format ?? 'custom' },
      reason: null,
    };
  }
  const text = String(rawReport);
  if (!text.trim()) return bad('empty_report');
  const kind = format === 'auto' || !format ? null : normalizeRunnerKind(format);
  if (kind === 'junit' || (!kind && /^\s*<(?:\?xml|testsuites?|testsuite)\b/.test(text))) return parseJunitXml(text);
  if (kind === 'node:test' || (!kind && /^TAP version 13\b/m.test(text))) return parseTapReport(text);
  if (kind === 'go' || (!kind && /^\s*\{.*"Action"\s*:/.test(text))) return parseGoJsonReport(text);
  if (kind === 'cargo' || (!kind && /^test result:/m.test(text))) return parseCargoReport(text);
  return bad('unrecognized_report_format');
}

function checkCacheKeyParity(baseMeta, headMeta) {
  const mismatches = [];
  if (!baseMeta || typeof baseMeta !== 'object' || !headMeta || typeof headMeta !== 'object') {
    return { ok: false, mismatches: [...CACHE_KEY_FIELDS] };
  }
  for (const field of CACHE_KEY_FIELDS) {
    const b = baseMeta[field], h = headMeta[field];
    if (typeof b !== 'string' || !b.trim() || typeof h !== 'string' || !h.trim() || b !== h) {
      mismatches.push(field);
    }
  }
  return { ok: mismatches.length === 0, mismatches };
}

function checkShardIntegrity(baseMeta, headMeta) {
  for (const [label, meta] of [['base', baseMeta], ['head', headMeta]]) {
    if (!meta || typeof meta !== 'object') continue;
    if (meta.expectedShards !== undefined && meta.completedShards !== undefined && meta.completedShards !== meta.expectedShards) {
      return { ok: false, detail: `${label}_incomplete_shards` };
    }
    if (Array.isArray(meta.shardIds) && Number.isInteger(meta.expectedShards) && new Set(meta.shardIds).size !== meta.expectedShards) {
      return { ok: false, detail: `${label}_missing_shard_ids` };
    }
  }
  if (baseMeta?.expectedShards !== undefined && headMeta?.expectedShards !== undefined && baseMeta.expectedShards !== headMeta.expectedShards) {
    return { ok: false, detail: 'shard_count_mismatch' };
  }
  if (baseMeta?.shards !== undefined && headMeta?.shards !== undefined && baseMeta.shards !== headMeta.shards) {
    return { ok: false, detail: 'shard_count_mismatch' };
  }
  return { ok: true, detail: null };
}

function indexCases(cases) {
  const map = new Map();
  for (const c of cases) {
    const prev = map.get(c.id);
    if (!prev || STATUS_RANK[c.status] > STATUS_RANK[prev.status]) map.set(c.id, c);
  }
  return map;
}

export function compareTestReports({ baseReport, headReport, baseMeta = null, headMeta = null, approvedRemovals = [] } = {}) {
  const emptyResult = extra => ({
    status: 'unknown', verdict: 'HOLD', reason: 'unknown',
    mismatches: [], missingIds: [], approvedRemovedIds: [], newlySkippedIds: [],
    newlyFailingIds: [], preexistingFailingIds: [], addedIds: [], fixedIds: [],
    baseCounts: null, headCounts: null, ...extra,
  });

  const parity = checkCacheKeyParity(baseMeta, headMeta);
  if (!parity.ok) return emptyResult({ reason: 'cache_key_mismatch', mismatches: parity.mismatches });

  const shards = checkShardIntegrity(baseMeta, headMeta);
  if (!shards.ok) return emptyResult({ reason: 'partial_shard_mismatch', detail: shards.detail });

  if (baseMeta?.killed === true || headMeta?.killed === true || baseMeta?.signal || headMeta?.signal) {
    return emptyResult({ reason: 'runner_killed' });
  }

  const base = parseStandardTestReport(baseReport, baseMeta?.format ?? 'auto');
  const head = parseStandardTestReport(headReport, headMeta?.format ?? 'auto');
  if (!base.ok || !base.complete || !head.ok || !head.complete) {
    return emptyResult({
      reason: 'missing_or_malformed_report',
      detail: !base.ok ? `base:${base.reason}` : `head:${head.reason}`,
    });
  }

  const baseFailCount = base.cases.filter(c => c.status === 'fail' || c.status === 'error').length;
  const headFailCount = head.cases.filter(c => c.status === 'fail' || c.status === 'error').length;
  if ((typeof baseMeta?.exitCode === 'number' && baseMeta.exitCode !== 0 && baseFailCount === 0)
    || (typeof headMeta?.exitCode === 'number' && headMeta.exitCode !== 0 && headFailCount === 0)) {
    return emptyResult({ reason: 'runner_nonzero_without_failures', baseCounts: base.counts, headCounts: head.counts });
  }

  if (base.cases.length === 0 || head.cases.length === 0 || base.counts?.total === 0 || head.counts?.total === 0) {
    return emptyResult({ reason: 'zero_collected_tests', baseCounts: base.counts, headCounts: head.counts });
  }

  const baseMap = indexCases(base.cases);
  const headMap = indexCases(head.cases);
  const approvedSet = new Set((Array.isArray(approvedRemovals) ? approvedRemovals : []).map(String));
  const missingIds = [], approvedRemovedIds = [], newlySkippedIds = [];
  const newlyFailingIds = [], preexistingFailingIds = [], addedIds = [], fixedIds = [];

  for (const [id, bCase] of baseMap.entries()) {
    const hCase = headMap.get(id);
    if (!hCase) {
      if (approvedSet.has(id)) approvedRemovedIds.push(id);
      else if (bCase.status === 'pass') missingIds.push(id);
      continue;
    }
    const baseFailed = bCase.status === 'fail' || bCase.status === 'error';
    const headFailed = hCase.status === 'fail' || hCase.status === 'error';
    if (bCase.status === 'pass' && hCase.status === 'skip') newlySkippedIds.push(id);
    else if (!baseFailed && headFailed) newlyFailingIds.push(id);
    else if (baseFailed && headFailed) preexistingFailingIds.push(id);
    else if (baseFailed && hCase.status === 'pass') fixedIds.push(id);
  }
  for (const [id, hCase] of headMap.entries()) {
    if (!baseMap.has(id)) {
      addedIds.push(id);
      if (hCase.status === 'fail' || hCase.status === 'error') newlyFailingIds.push(id);
    }
  }

  for (const list of [missingIds, approvedRemovedIds, newlySkippedIds, newlyFailingIds, preexistingFailingIds, addedIds, fixedIds]) {
    list.sort();
  }

  const reasons = [
    ...(missingIds.length ? ['missing_tests'] : []),
    ...(newlySkippedIds.length ? ['newly_skipped_tests'] : []),
    ...(newlyFailingIds.length ? ['newly_failing_tests'] : []),
  ];
  const failed = reasons.length > 0;
  return emptyResult({
    status: failed ? 'fail' : 'pass',
    verdict: failed ? 'HOLD' : 'ALLOW',
    reason: failed ? reasons.join(',') : 'clean',
    missingIds, approvedRemovedIds, newlySkippedIds, newlyFailingIds,
    preexistingFailingIds, addedIds, fixedIds,
    baseCounts: base.counts, headCounts: head.counts,
  });
}

function inspectSafePathInTree(realRoot, relPath) {
  if (!canonicalRelPath(relPath)) return { status: 'unsafe', reason: 'non_canonical_path' };
  const parts = relPath.split('/');
  let cur = realRoot;
  for (let i = 0; i < parts.length; i += 1) {
    cur = join(cur, parts[i]);
    let st;
    try { st = lstatSync(cur); } catch (err) {
      return err?.code === 'ENOENT' ? { status: 'missing', fullPath: cur } : { status: 'unsafe', reason: 'stat_failed' };
    }
    if (st.isSymbolicLink()) return { status: 'unsafe', reason: 'symlink_refused' };
    if (i < parts.length - 1 && !st.isDirectory()) return { status: 'unsafe', reason: 'non_directory_parent' };
    if (i === parts.length - 1 && !st.isFile()) return { status: 'unsafe', reason: 'not_regular_file' };
  }
  return { status: 'file', fullPath: cur };
}

function writeAtomicTempFile(targetPath, data) {
  mkdirSync(dirname(targetPath), { recursive: true });
  const tmp = `${targetPath}.${randomUUID()}.tmp`;
  try {
    writeFileSync(tmp, data);
    renameSync(tmp, targetPath);
  } finally {
    try { unlinkSync(tmp); } catch {}
  }
}

function runCommandInTree(command, { cwd, env, timeoutMs = 120_000, maxBytes = 4 * 1024 * 1024 }) {
  return new Promise(resolveRun => {
    const isArray = Array.isArray(command);
    const bin = isArray ? String(command[0]) : '/bin/sh';
    const args = isArray ? command.slice(1).map(String) : ['-c', String(command)];
    const childEnv = scrubReadonlyEnv(env, { extraStrip: ['NODE_TEST_CONTEXT'] });
    const child = spawn(bin, args, {
      cwd, env: childEnv, stdio: ['ignore', 'pipe', 'pipe'],
      shell: false, detached: process.platform !== 'win32',
    });
    let stdout = '', stderr = '', size = 0, killed = false, settled = false, killTimer = null;
    const stop = () => {
      killed = true;
      try { process.kill(-child.pid, 'SIGTERM'); } catch { try { child.kill('SIGTERM'); } catch {} }
      killTimer = setTimeout(() => {
        try { process.kill(-child.pid, 'SIGKILL'); } catch { try { child.kill('SIGKILL'); } catch {} }
      }, 500);
      killTimer.unref();
    };
    const finish = payload => {
      if (settled) return;
      settled = true; clearTimeout(timer); clearTimeout(killTimer);
      resolveRun(payload);
    };
    const timer = setTimeout(stop, Math.max(100, timeoutMs));
    timer.unref();
    const capture = (kind, chunk) => {
      size += chunk.length;
      if (size > maxBytes) { stop(); return; }
      if (kind === 'stdout') stdout += chunk.toString('utf8');
      else stderr += chunk.toString('utf8');
    };
    child.stdout.on('data', c => capture('stdout', c));
    child.stderr.on('data', c => capture('stderr', c));
    child.on('error', err => finish({ exitCode: 1, signal: null, killed: true, stdout, stderr: `${stderr}\n${err.message}` }));
    child.on('close', (code, signal) => finish({ exitCode: code ?? 1, signal: signal ?? null, killed, stdout, stderr }));
  });
}

export async function runBaseOwnedTestOracle({
  baseTree, headTree, editedTestFiles = [], testCommand, intendedChanges = [],
  runner = null, format = 'auto', timeoutMs = 120_000, env = process.env,
} = {}) {
  const failClosed = (status, reason, extra = {}) => ({
    status, verdict: 'HOLD', reason, overlaidFiles: [], skippedNewFiles: [],
    regressions: [], intendedFailures: [], exitCode: null, counts: null, ...extra,
  });

  if (!baseTree || !headTree || !existsSync(baseTree) || !existsSync(headTree)) {
    return failClosed('unknown', 'missing_base_or_head_tree');
  }
  const files = [...new Set((Array.isArray(editedTestFiles) ? editedTestFiles : []).map(String))];
  if (!files.length) {
    return { status: 'pass', verdict: 'ALLOW', reason: 'no_edited_test_files', overlaidFiles: [], skippedNewFiles: [], regressions: [], intendedFailures: [], exitCode: 0, counts: null };
  }
  if (!runner && (!testCommand || (Array.isArray(testCommand) && !testCommand.length))) {
    return failClosed('unknown', 'missing_test_command');
  }

  let realBase, realHead;
  try { realBase = realpathSync(baseTree); realHead = realpathSync(headTree); }
  catch { return failClosed('unknown', 'unreadable_tree'); }

  const toOverlay = [], skippedNewFiles = [];
  for (const rel of files) {
    const baseCheck = inspectSafePathInTree(realBase, rel);
    const headCheck = inspectSafePathInTree(realHead, rel);
    if (baseCheck.status === 'unsafe' || headCheck.status === 'unsafe') {
      return failClosed('unknown', 'unsafe_test_path', { detail: `${rel}:${baseCheck.reason ?? headCheck.reason}` });
    }
    if (baseCheck.status === 'missing') { skippedNewFiles.push(rel); continue; }
    toOverlay.push({ rel, source: baseCheck.fullPath });
  }

  if (!toOverlay.length) {
    return { status: 'pass', verdict: 'ALLOW', reason: 'no_base_test_files_to_overlay', overlaidFiles: [], skippedNewFiles, regressions: [], intendedFailures: [], exitCode: 0, counts: null };
  }

  const tempDir = mkdtempSync(join(tmpdir(), 'pdd-base-oracle-'));
  try {
    cpSync(realHead, tempDir, {
      recursive: true, dereference: false,
      filter: src => {
        const rel = relative(realHead, src).split(sep).join('/');
        return rel !== '.git' && !rel.startsWith('.git/');
      },
    });
    const overlaidFiles = [];
    for (const item of toOverlay) {
      const targetCheck = inspectSafePathInTree(tempDir, item.rel);
      if (targetCheck.status === 'unsafe') return failClosed('unknown', 'unsafe_overlay_target', { detail: item.rel });
      writeAtomicTempFile(join(tempDir, item.rel), readFileSync(item.source));
      overlaidFiles.push(item.rel);
    }

    const runRes = typeof runner === 'function'
      ? await runner({ cwd: tempDir, command: testCommand, overlaidFiles, baseTree: realBase, headTree: realHead })
      : await runCommandInTree(testCommand, { cwd: tempDir, env, timeoutMs });

    if (!runRes || runRes.killed === true || runRes.signal) {
      return failClosed('unknown', 'oracle_runner_killed', { overlaidFiles, skippedNewFiles, exitCode: runRes?.exitCode ?? null });
    }

    const exitCode = Number.isInteger(runRes.exitCode) ? runRes.exitCode : (Number.isInteger(runRes.code) ? runRes.code : 1);
    const parsed = parseStandardTestReport(runRes.report ?? runRes.stdout ?? '', runRes.format ?? format);
    const intendedSet = new Set((Array.isArray(intendedChanges) ? intendedChanges : []).map(String));

    if (!parsed.ok || !parsed.complete) {
      if (exitCode !== 0) {
        return failClosed('fail', 'unlisted_base_test_regression', {
          overlaidFiles, skippedNewFiles, exitCode,
          regressions: [{ id: '<oracle-command>', status: 'error', durationMs: null }],
        });
      }
      return failClosed('unknown', 'oracle_unparseable_report', { overlaidFiles, skippedNewFiles, exitCode });
    }

    if (parsed.cases.length === 0) {
      return failClosed('unknown', 'oracle_zero_tests', { overlaidFiles, skippedNewFiles, exitCode, counts: parsed.counts });
    }

    const failing = parsed.cases.filter(c => c.status === 'fail' || c.status === 'error');
    const intendedFailures = failing.filter(c => intendedSet.has(c.id));
    const regressions = failing.filter(c => !intendedSet.has(c.id));

    if (regressions.length > 0 || (exitCode !== 0 && intendedFailures.length === 0)) {
      return failClosed('fail', 'unlisted_base_test_regression', {
        overlaidFiles, skippedNewFiles, exitCode, counts: parsed.counts,
        regressions: regressions.length ? regressions : [{ id: '<oracle-command>', status: 'error', durationMs: null }],
        intendedFailures,
      });
    }

    return {
      status: 'pass', verdict: 'ALLOW',
      reason: intendedFailures.length ? 'intended_changes_only' : 'clean',
      overlaidFiles, skippedNewFiles, regressions: [], intendedFailures, exitCode, counts: parsed.counts,
    };
  } finally {
    try { rmSync(tempDir, { recursive: true, force: true }); } catch {}
  }
}
