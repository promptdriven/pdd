// Layer-2 G3 Standard Test Report Comparator & Base-Owned Edited-Test Oracle.
// Deterministic, non-compensatory, fail-closed diff across JUnit XML, TAP v13, and go test -json.
import { spawn } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { chmodSync, cpSync, existsSync, lstatSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, renameSync, rmSync, unlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, isAbsolute, join, relative, sep } from 'node:path';
import { normalizeRunnerKind, parseCargoReport, parseGoJsonReport, parseJunitXml, parseTapReport } from './test-runners.mjs';

export { parseGoJsonReport, parseJunitXml, parseTapReport };
export const CACHE_KEY_FIELDS = Object.freeze(['baseSha', 'policyDigest', 'recipeDigest', 'toolchain', 'platform', 'profile']);
const STATUS_RANK = Object.freeze({ pass: 0, skip: 1, fail: 2, error: 3 });
const ORACLE_ENV_ALLOW_RE = /^(?:PATH|LANG|LANGUAGE|LC_[A-Z_]+|TZ|TERM|CI|SystemRoot|WINDIR|GOPATH|GOMODCACHE|CARGO_HOME|RUSTUP_HOME|VIRTUAL_ENV|UV_CACHE_DIR|PDD_TEST_ENV_[A-Z0-9_]+)$/;

const canonicalRelPath = v => typeof v === 'string' && v.trim().length > 0 && v.length <= 1000
  && !isAbsolute(v) && !/[\\\x00-\x1f\x7f]/.test(v)
  && !v.split('/').some(p => !p || p === '.' || p === '..' || p.toLowerCase() === '.git');

export function parseStandardTestReport(rawReport, format = 'auto') {
  const bad = reason => ({ ok: false, complete: false, format: null, cases: [], counts: null, reason });
  if (rawReport === null || rawReport === undefined) return bad('missing_report');
  if (typeof rawReport === 'object' && !Array.isArray(rawReport)) {
    if (rawReport.ok === false || rawReport.complete === false || !Array.isArray(rawReport.cases)) return bad(rawReport.reason || 'incomplete_report');
    const cases = rawReport.cases
      .filter(c => c && typeof c.id === 'string' && c.id.trim() && Object.hasOwn(STATUS_RANK, c.status))
      .map(c => ({ id: c.id.trim(), status: c.status, durationMs: Number.isFinite(c.durationMs) ? c.durationMs : null }));
    if (cases.length !== rawReport.cases.length) return bad('malformed_case_entries');
    const passed = cases.filter(c => c.status === 'pass').length;
    const failed = cases.filter(c => c.status === 'fail' || c.status === 'error').length;
    const skipped = cases.filter(c => c.status === 'skip').length;
    return { ok: true, complete: true, format: rawReport.format ?? 'custom', cases, counts: rawReport.counts ?? { total: cases.length, passed, failed, skipped, format: rawReport.format ?? 'custom' }, reason: null };
  }
  const text = String(rawReport);
  if (!text.trim()) return bad('empty_report');
  const kind = format === 'auto' || !format ? null : normalizeRunnerKind(format);
  const looksXml = /^\s*<(?:\?xml|testsuites?|testsuite)\b/.test(text);
  if (kind === 'junit' || ((kind === 'vitest' || kind === 'pytest' || !kind) && looksXml)) return parseJunitXml(text);
  if (kind === 'node:test' || (!kind && /^TAP version 13\b/m.test(text))) return parseTapReport(text);
  if (kind === 'go' || (!kind && /^\s*\{.*"Action"\s*:/.test(text))) return parseGoJsonReport(text);
  if (kind === 'cargo' || (!kind && /^test result:/m.test(text))) return parseCargoReport(text);
  return bad('unrecognized_report_format');
}

function checkCacheKeyParity(baseMeta, headMeta) {
  if (!baseMeta || typeof baseMeta !== 'object' || !headMeta || typeof headMeta !== 'object') return { ok: false, mismatches: [...CACHE_KEY_FIELDS] };
  const mismatches = CACHE_KEY_FIELDS.filter(f => typeof baseMeta[f] !== 'string' || !baseMeta[f].trim() || typeof headMeta[f] !== 'string' || !headMeta[f].trim() || baseMeta[f] !== headMeta[f]);
  return { ok: mismatches.length === 0, mismatches };
}

function checkShardIntegrity(baseMeta, headMeta) {
  const shardKeys = ['expectedShards', 'completedShards', 'shards', 'shardIds'];
  const hasAny = meta => Boolean(meta && typeof meta === 'object' && shardKeys.some(k => meta[k] !== undefined && meta[k] !== null));
  const baseHas = hasAny(baseMeta), headHas = hasAny(headMeta);
  if (!baseHas && !headHas) return { ok: true, detail: null };
  if (!baseHas || !headHas) return { ok: false, detail: 'one_sided_shard_metadata' };

  const parseSide = (label, meta) => {
    const expected = meta.expectedShards ?? meta.shards;
    if (!Number.isInteger(expected) || expected < 1) return { ok: false, detail: `${label}_invalid_expected_shards` };
    if (meta.shards !== undefined && meta.expectedShards !== undefined && meta.shards !== meta.expectedShards) return { ok: false, detail: `${label}_shard_field_mismatch` };
    if (!Number.isInteger(meta.completedShards) || meta.completedShards !== expected) return { ok: false, detail: `${label}_incomplete_shards` };
    if (meta.shardIds !== undefined && (!Array.isArray(meta.shardIds) || new Set(meta.shardIds).size !== expected)) return { ok: false, detail: `${label}_missing_shard_ids` };
    return { ok: true, expected };
  };
  const b = parseSide('base', baseMeta);
  if (!b.ok) return b;
  const h = parseSide('head', headMeta);
  if (!h.ok) return h;
  if (b.expected !== h.expected) return { ok: false, detail: 'shard_count_mismatch' };
  return { ok: true, detail: null };
}

function indexCaseMultiset(cases) {
  const map = new Map();
  for (const c of cases) {
    const cur = map.get(c.id) ?? { total: 0, pass: 0, skip: 0, fail: 0, error: 0 };
    cur.total += 1;
    cur[c.status] += 1;
    map.set(c.id, cur);
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

  if (baseMeta?.killed === true || headMeta?.killed === true || baseMeta?.signal || headMeta?.signal) return emptyResult({ reason: 'runner_killed' });

  const base = parseStandardTestReport(baseReport, baseMeta?.format ?? 'auto');
  const head = parseStandardTestReport(headReport, headMeta?.format ?? 'auto');
  if (!base.ok || !base.complete || !head.ok || !head.complete) {
    return emptyResult({ reason: 'missing_or_malformed_report', detail: !base.ok ? `base:${base.reason}` : `head:${head.reason}` });
  }

  const baseFailCount = base.cases.filter(c => c.status === 'fail' || c.status === 'error').length;
  const headFailCount = head.cases.filter(c => c.status === 'fail' || c.status === 'error').length;
  if ((base.counts?.failed ?? 0) > baseFailCount || (head.counts?.failed ?? 0) > headFailCount) {
    return emptyResult({ reason: 'summary_case_count_mismatch', baseCounts: base.counts, headCounts: head.counts });
  }
  if ((typeof baseMeta?.exitCode === 'number' && baseMeta.exitCode !== 0 && baseFailCount === 0)
    || (typeof headMeta?.exitCode === 'number' && headMeta.exitCode !== 0 && headFailCount === 0)) {
    return emptyResult({ reason: 'runner_nonzero_without_failures', baseCounts: base.counts, headCounts: head.counts });
  }
  if (base.cases.length === 0 || head.cases.length === 0 || base.counts?.total === 0 || head.counts?.total === 0) {
    return emptyResult({ reason: 'zero_collected_tests', baseCounts: base.counts, headCounts: head.counts });
  }

  const baseMap = indexCaseMultiset(base.cases), headMap = indexCaseMultiset(head.cases);
  const approvalQuota = new Map();
  for (const id of Array.isArray(approvedRemovals) ? approvedRemovals : []) {
    const key = String(id);
    approvalQuota.set(key, (approvalQuota.get(key) ?? 0) + 1);
  }
  const missingIds = [], approvedRemovedIds = [], newlySkippedIds = [];
  const newlyFailingIds = [], preexistingFailingIds = [], addedIds = [], fixedIds = [];

  for (const [id, b] of baseMap.entries()) {
    const h = headMap.get(id) ?? { total: 0, pass: 0, skip: 0, fail: 0, error: 0 };
    const bFail = b.fail + b.error, hFail = h.fail + h.error;
    const removed = Math.max(0, b.total - h.total);
    if (removed > 0) {
      const approved = Math.min(removed, approvalQuota.get(id) ?? 0);
      for (let k = 0; k < approved; k += 1) approvedRemovedIds.push(id);
      const unapprovedRemovedPassing = Math.min(removed - approved, Math.max(0, b.pass - h.pass));
      if (unapprovedRemovedPassing > 0) missingIds.push(id);
    }
    if (h.total > 0 && h.skip > b.skip && h.pass < b.pass) newlySkippedIds.push(id);
    if (hFail > bFail) newlyFailingIds.push(id);
    else if (bFail > 0 && hFail > 0) preexistingFailingIds.push(id);
    else if (bFail > 0 && hFail < bFail && h.pass > b.pass) fixedIds.push(id);
    if (h.total > b.total) addedIds.push(id);
  }
  for (const [id, h] of headMap.entries()) {
    if (!baseMap.has(id)) {
      addedIds.push(id);
      if (h.fail + h.error > 0) newlyFailingIds.push(id);
    }
  }
  for (const list of [missingIds, approvedRemovedIds, newlySkippedIds, newlyFailingIds, preexistingFailingIds, addedIds, fixedIds]) list.sort();

  if ((head.counts?.failed ?? 0) > 0 && newlyFailingIds.length === 0 && preexistingFailingIds.length === 0) {
    return emptyResult({ reason: 'summary_case_count_mismatch', baseCounts: base.counts, headCounts: head.counts });
  }
  const reasons = [
    ...(missingIds.length ? ['missing_tests'] : []),
    ...(newlySkippedIds.length ? ['newly_skipped_tests'] : []),
    ...(newlyFailingIds.length ? ['newly_failing_tests'] : []),
  ];
  const failed = reasons.length > 0;
  return emptyResult({
    status: failed ? 'fail' : 'pass', verdict: failed ? 'HOLD' : 'ALLOW', reason: failed ? reasons.join(',') : 'clean',
    missingIds, approvedRemovedIds, newlySkippedIds, newlyFailingIds, preexistingFailingIds, addedIds, fixedIds,
    baseCounts: base.counts, headCounts: head.counts,
  });
}

export const diffTestReports = compareTestReports;

function inspectSafePathInTree(realRoot, relPath) {
  if (!canonicalRelPath(relPath)) return { status: 'unsafe', reason: 'non_canonical_path' };
  const parts = relPath.split('/');
  let cur = realRoot, mode = 0o644;
  for (let i = 0; i < parts.length; i += 1) {
    cur = join(cur, parts[i]);
    let st;
    try { st = lstatSync(cur); } catch (err) { return err?.code === 'ENOENT' ? { status: 'missing', fullPath: cur } : { status: 'unsafe', reason: 'stat_failed' }; }
    if (st.isSymbolicLink()) return { status: 'unsafe', reason: 'symlink_refused' };
    if (i < parts.length - 1 && !st.isDirectory()) return { status: 'unsafe', reason: 'non_directory_parent' };
    if (i === parts.length - 1) {
      if (!st.isFile()) return { status: 'unsafe', reason: 'not_regular_file' };
      mode = st.mode & 0o777;
    }
  }
  return { status: 'file', fullPath: cur, mode };
}

function writeAtomicTempFile(targetPath, data, mode = 0o644) {
  mkdirSync(dirname(targetPath), { recursive: true });
  const tmp = `${targetPath}.${randomUUID()}.tmp`;
  try {
    writeFileSync(tmp, data, { mode });
    chmodSync(tmp, mode);
    renameSync(tmp, targetPath);
  } finally { try { unlinkSync(tmp); } catch {} }
}

function buildOracleEnv(env, envRoot) {
  const childEnv = Object.fromEntries(
    Object.entries(env ?? {}).filter(([k, v]) => typeof v === 'string' && ORACLE_ENV_ALLOW_RE.test(k)),
  );
  childEnv.PATH ??= '/usr/bin:/bin';
  for (const [sub, keys] of [['home', ['HOME', 'USERPROFILE']], ['config', ['XDG_CONFIG_HOME']], ['tmp', ['TMPDIR', 'TMP', 'TEMP']]]) {
    const dir = join(envRoot, sub);
    mkdirSync(dir, { recursive: true, mode: 0o700 });
    for (const k of keys) childEnv[k] = dir;
  }
  return childEnv;
}

function runCommandInTree(command, { cwd, env, envRoot, timeoutMs = 120_000, maxBytes = 4 * 1024 * 1024 }) {
  return new Promise(resolveRun => {
    const isArray = Array.isArray(command);
    const bin = isArray ? String(command[0]) : '/bin/sh';
    const args = isArray ? command.slice(1).map(String) : ['-c', String(command)];
    const childEnv = buildOracleEnv(env, envRoot);
    const child = spawn(bin, args, { cwd, env: childEnv, stdio: ['ignore', 'pipe', 'pipe'], shell: false, detached: process.platform !== 'win32' });
    let stdout = '', stderr = '', size = 0, killed = false, settled = false, killTimer = null;
    const stop = () => {
      if (killed) return;
      killed = true;
      try { process.kill(-child.pid, 'SIGTERM'); } catch { try { child.kill('SIGTERM'); } catch {} }
      killTimer = setTimeout(() => {
        try { process.kill(-child.pid, 'SIGKILL'); } catch { try { child.kill('SIGKILL'); } catch {} }
      }, 500);
      killTimer.unref();
    };
    const finish = payload => { if (settled) return; settled = true; clearTimeout(timer); clearTimeout(killTimer); resolveRun(payload); };
    const timer = setTimeout(stop, Math.max(100, timeoutMs));
    timer.unref();
    const capture = (kind, chunk) => {
      size += chunk.length;
      if (size > maxBytes) { stop(); return; }
      if (kind === 'stdout') stdout += chunk.toString('utf8'); else stderr += chunk.toString('utf8');
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

  if (!baseTree || !headTree || !existsSync(baseTree) || !existsSync(headTree)) return failClosed('unknown', 'missing_base_or_head_tree');
  const files = [...new Set((Array.isArray(editedTestFiles) ? editedTestFiles : []).map(String))];
  if (!files.length) return { status: 'pass', verdict: 'ALLOW', reason: 'no_edited_test_files', overlaidFiles: [], skippedNewFiles: [], regressions: [], intendedFailures: [], exitCode: 0, counts: null };
  if (!runner && (!testCommand || (Array.isArray(testCommand) && !testCommand.length))) return failClosed('unknown', 'missing_test_command');

  let realBase, realHead;
  try { realBase = realpathSync(baseTree); realHead = realpathSync(headTree); }
  catch { return failClosed('unknown', 'unreadable_tree'); }

  const toOverlay = [], skippedNewFiles = [];
  for (const rel of files) {
    const baseCheck = inspectSafePathInTree(realBase, rel), headCheck = inspectSafePathInTree(realHead, rel);
    if (baseCheck.status === 'unsafe' || headCheck.status === 'unsafe') return failClosed('unknown', 'unsafe_test_path', { detail: `${rel}:${baseCheck.reason ?? headCheck.reason}` });
    if (baseCheck.status === 'missing') { skippedNewFiles.push(rel); continue; }
    toOverlay.push({ rel, source: baseCheck.fullPath, mode: baseCheck.mode });
  }
  if (!toOverlay.length) return { status: 'pass', verdict: 'ALLOW', reason: 'no_base_test_files_to_overlay', overlaidFiles: [], skippedNewFiles, regressions: [], intendedFailures: [], exitCode: 0, counts: null };

  const tempRoot = mkdtempSync(join(tmpdir(), 'pdd-base-oracle-'));
  const workDir = join(tempRoot, 'work'), envRoot = join(tempRoot, 'env');
  try {
    const overlaidFiles = [];
    try {
      mkdirSync(workDir, { mode: 0o700 }); mkdirSync(envRoot, { mode: 0o700 });
      let copyGitDir = false;
      try { const gitStat = lstatSync(join(realHead, '.git')); copyGitDir = gitStat.isDirectory() && !gitStat.isSymbolicLink(); } catch {}
      cpSync(realHead, workDir, {
        recursive: true, dereference: false, verbatimSymlinks: true,
        filter: src => {
          const rel = relative(realHead, src).split(sep).join('/');
          if (rel === 'node_modules' || rel.startsWith('node_modules/')) return false;
          if (!copyGitDir && (rel === '.git' || rel.startsWith('.git/'))) return false;
          return true;
        },
      });
      for (const item of toOverlay) {
        const targetCheck = inspectSafePathInTree(workDir, item.rel);
        if (targetCheck.status === 'unsafe') return failClosed('unknown', 'unsafe_overlay_target', { detail: item.rel });
        writeAtomicTempFile(join(workDir, item.rel), readFileSync(item.source), item.mode);
        overlaidFiles.push(item.rel);
      }
    } catch (err) {
      return failClosed('unknown', 'oracle_setup_failed', { detail: String(err?.code ?? err?.message ?? 'copy_failed') });
    }

    const runRes = typeof runner === 'function'
      ? await runner({ cwd: workDir, command: testCommand, overlaidFiles, baseTree: realBase, headTree: realHead, env: buildOracleEnv(env, envRoot) })
      : await runCommandInTree(testCommand, { cwd: workDir, env, envRoot, timeoutMs });

    if (!runRes || runRes.killed === true || runRes.signal) return failClosed('unknown', 'oracle_runner_killed', { overlaidFiles, skippedNewFiles, exitCode: runRes?.exitCode ?? null });

    const exitCode = Number.isInteger(runRes.exitCode) ? runRes.exitCode : (Number.isInteger(runRes.code) ? runRes.code : 1);
    const parsed = parseStandardTestReport(runRes.report ?? runRes.stdout ?? '', runRes.format ?? format);
    const intendedSet = new Set((Array.isArray(intendedChanges) ? intendedChanges : []).map(String));

    if (!parsed.ok || !parsed.complete) {
      if (exitCode !== 0) return failClosed('fail', 'unlisted_base_test_regression', { overlaidFiles, skippedNewFiles, exitCode, regressions: [{ id: '<oracle-command>', status: 'error', durationMs: null }] });
      return failClosed('unknown', 'oracle_unparseable_report', { overlaidFiles, skippedNewFiles, exitCode });
    }
    if (parsed.cases.length === 0) return failClosed('unknown', 'oracle_zero_tests', { overlaidFiles, skippedNewFiles, exitCode, counts: parsed.counts });

    const executedCount = parsed.cases.filter(c => c.status !== 'skip').length;
    if (executedCount === 0) return failClosed('unknown', 'oracle_zero_executed_tests', { overlaidFiles, skippedNewFiles, exitCode, counts: parsed.counts });

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
      status: 'pass', verdict: 'ALLOW', reason: intendedFailures.length ? 'intended_changes_only' : 'clean',
      overlaidFiles, skippedNewFiles, regressions: [], intendedFailures, exitCode, counts: parsed.counts,
    };
  } finally { try { rmSync(tempRoot, { recursive: true, force: true }); } catch {} }
}
