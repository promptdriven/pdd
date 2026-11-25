// Prompt: prompts/cli/prove-coverage.prompt.md

// Opt-in `pdd prove --coverage` engine: diff-line extraction + per-file & diff-line coverage split across formal, vectors, and all suites.
import { spawnSync } from 'node:child_process';
import { existsSync, lstatSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, posix, relative, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import { gitFiles } from '../shared/git-context.mjs';
import { causeText } from '../shared/safe-read.mjs';
import { canonicalRepoPath, readSafeUtf8, scrubChildEnv } from './lint/diagnostics.mjs';
import {
  FORMAL_TEST_FILE_RE,
  chooseRunnerForFormalFile,
  detectSignalInterruption,
  execChildAsync,
  isProductionCodeFile,
  killProcessTree,
  lexCStyleSource,
  lexPythonSource,
  resolvePythonBinary,
} from './formal-verify.mjs';
import { buildRunnerEnv, buildRunnerInvocation } from './polyglot-runners.mjs';

export const VECTOR_TEST_FILE_RE = /(?:\.vectors?\.test\.[^/]+$|(?:^|\/)test_vectors(?:_[^/]+)?\.[^/]+$|(?:^|\/)(?:test_[^/]*vectors?[^/]*|[^/]*vectors?_test)\.py$|(?:^|\/)vectors\/(?:test_[^/]+|[^/]+_test)\.py$|_vectors?_test\.go$|(?:^|\/)tests\/[^/]*vectors?[^/]*\.rs$)/i;

const JS_FILE_RE = /\.(?:mjs|cjs|js|ts|tsx|jsx)$/i;
const PY_FILE_RE = /\.py$/i;
const GO_FILE_RE = /\.go$/i;
const SUITE_NAMES = Object.freeze(['formal', 'vectors', 'all']);
const NON_STMT_CSTYLE_LINE_RE = /^[\s{}()[\];,]*$|^(?:else|try|finally)\s*\{?\s*$|^export\s*\{?\s*$/;

const roundPct = (covered, total) => (total > 0 ? Math.round((covered * 1000) / total) / 10 : null);
const uniqSortedNums = nums => [...new Set((Array.isArray(nums) ? nums : []).filter(n => Number.isInteger(n) && n > 0))].sort((a, b) => a - b);

export function validateProveOptInFlags({ coverage = false, mutationCheck = false, test, expect } = {}) {
  const hasOptIn = coverage === true || mutationCheck === true;
  const hasBugContrast = (test !== undefined && test !== null) || (expect !== undefined && expect !== null);
  if (hasOptIn && hasBugContrast) {
    return {
      ok: false,
      exitCode: 2,
      error: 'pdd prove --coverage and --mutation-check cannot be combined with bug-contrast --test/--expect mode.',
    };
  }
  return { ok: true, exitCode: 0, error: null };
}

function unquoteGitPath(rawPath) {
  let p = String(rawPath ?? '').trim();
  if (p.startsWith('"') && p.endsWith('"')) {
    try { p = JSON.parse(p); } catch { p = p.slice(1, -1); }
  }
  if (p.startsWith('b/')) p = p.slice(2);
  return p.replace(/\\/g, '/').replace(/^(?:\.\/)+/, '');
}

/**
 * Parse unified diff (`git diff -U0`) into `{ files: { [relPath]: number[] } }` of sorted unique 1-based added/modified line numbers.
 */
export function parseUnifiedDiffAddedLines({ diffText = '' } = {}) {
  const byFile = new Map();
  let curFile = null;
  let oldRem = 0;
  let newRem = 0;
  for (const rawLine of String(diffText ?? '').split(/\r?\n/)) {
    if (oldRem > 0 || newRem > 0) {
      if (rawLine.startsWith('+')) newRem = Math.max(0, newRem - 1);
      else if (rawLine.startsWith('-')) oldRem = Math.max(0, oldRem - 1);
      else if (rawLine.startsWith(' ')) { oldRem = Math.max(0, oldRem - 1); newRem = Math.max(0, newRem - 1); }
      else if (rawLine.startsWith('\\')) { /* \ No newline at end of file */ }
      else {
        // Malformed or truncated hunk without body lines: reset hunk counters and process as header.
        oldRem = 0;
        newRem = 0;
      }
      if (oldRem > 0 || newRem > 0 || rawLine.startsWith('+') || rawLine.startsWith('-') || rawLine.startsWith(' ') || rawLine.startsWith('\\')) {
        continue;
      }
    }
    if (rawLine.startsWith('diff --git ')) {
      curFile = null;
      oldRem = 0;
      newRem = 0;
      continue;
    }
    if (rawLine.startsWith('+++ ')) {
      const target = rawLine.slice(4).trim();
      if (target === '/dev/null') {
        curFile = null;
      } else {
        const rel = unquoteGitPath(target);
        curFile = canonicalRepoPath(rel) ? rel : null;
      }
      continue;
    }
    if (!curFile || !rawLine.startsWith('@@ ')) continue;
    const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(rawLine);
    if (!m) continue;
    oldRem = m[2] === undefined ? 1 : Number(m[2]);
    const start = Number(m[3]);
    const count = m[4] === undefined ? 1 : Number(m[4]);
    newRem = Number.isInteger(count) && count >= 0 ? count : 0;
    if (!Number.isInteger(start) || start < 1 || !Number.isInteger(count) || count <= 0) continue;
    let set = byFile.get(curFile);
    if (!set) { set = new Set(); byFile.set(curFile, set); }
    for (let ln = start; ln < start + count; ln += 1) set.add(ln);
  }
  const files = {};
  for (const file of [...byFile.keys()].sort()) {
    files[file] = [...byFile.get(file)].sort((a, b) => a - b);
  }
  return { files };
}

/**
 * Estimate executable statement line numbers in a production source file when no coverage tool imported it.
 */
export function scanFallbackExecutableLines(filePath, sourceText) {
  const text = String(sourceText ?? '');
  if (!text.trim()) return [];
  const rawLines = text.split(/\r?\n/);
  if (PY_FILE_RE.test(filePath)) {
    const lexed = lexPythonSource(text);
    const codeLines = lexed.codeOnly.split(/\r?\n/);
    const out = [];
    for (let i = 0; i < rawLines.length; i += 1) {
      const code = (codeLines[i] ?? '').trim();
      if (!code) continue;
      if (/^(?:def|class|elif|else:|try:|finally:|except\b|@)/.test(code) && code.endsWith(':')) continue;
      out.push(i + 1);
    }
    return out;
  }
  const lexed = lexCStyleSource(text, { go: GO_FILE_RE.test(filePath), rust: /\.rs$/i.test(filePath) });
  const codeLines = lexed.codeOnly.split(/\r?\n/);
  const out = [];
  for (let i = 0; i < rawLines.length; i += 1) {
    const code = (codeLines[i] ?? '').trim();
    if (!code || NON_STMT_CSTYLE_LINE_RE.test(code)) continue;
    if (GO_FILE_RE.test(filePath) && /^(?:package\s+|import\s*\(?$|type\s+.*struct\s*\{$)/.test(code)) continue;
    if (JS_FILE_RE.test(filePath) && /^(?:import\s+type\b|export\s+type\b|interface\s+|type\s+\w+\s*=)/.test(code)) continue;
    out.push(i + 1);
  }
  return out;
}

export function collectDiffLines({ root, baseSha, touchedFiles: _touchedFiles = [] } = {}) {
  const diffLinesByFile = {};
  const fallbackExecutableLinesByFile = {};
  if (!root || typeof root !== 'string') return { diffLinesByFile, fallbackExecutableLinesByFile };
  let realRoot;
  try { realRoot = realpathSync(root); } catch { return { diffLinesByFile, fallbackExecutableLinesByFile }; }

  if (baseSha) {
    const diff = spawnSync('git', ['diff', '--no-ext-diff', '--no-textconv', '--no-renames', '--src-prefix=a/', '--dst-prefix=b/', '-U0', baseSha, '--'], {
      cwd: realRoot,
      encoding: 'utf8',
      maxBuffer: 32 * 1024 * 1024,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    if (diff.status === 0 && typeof diff.stdout === 'string') {
      const parsed = parseUnifiedDiffAddedLines({ diffText: diff.stdout });
      for (const [file, lines] of Object.entries(parsed.files)) {
        if (!isProductionCodeFile(file) || lines.length === 0) continue;
        const src = readSafeUtf8(realRoot, file);
        if (typeof src !== 'string') continue;
        diffLinesByFile[file] = lines;
        fallbackExecutableLinesByFile[file] = scanFallbackExecutableLines(file, src);
      }
    }
  }

  const untrackedRes = spawnSync('git', ['ls-files', '--others', '--exclude-standard', '-z'], {
    cwd: realRoot,
    encoding: 'utf8',
    maxBuffer: 16 * 1024 * 1024,
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  const untrackedList = untrackedRes.status === 0 && untrackedRes.stdout
    ? untrackedRes.stdout.split('\0').filter(Boolean)
    : [];
  for (const file of untrackedList) {
    if (!isProductionCodeFile(file) || Object.hasOwn(diffLinesByFile, file)) continue;
    const src = readSafeUtf8(realRoot, file);
    if (typeof src !== 'string') continue;
    const rawLines = src.split(/\r?\n/);
    const nonBlank = [];
    for (let i = 0; i < rawLines.length; i += 1) {
      if (rawLines[i].trim()) nonBlank.push(i + 1);
    }
    if (nonBlank.length > 0) {
      diffLinesByFile[file] = nonBlank;
      fallbackExecutableLinesByFile[file] = scanFallbackExecutableLines(file, src);
    }
  }
  return { diffLinesByFile, fallbackExecutableLinesByFile };
}

/**
 * Resolve V8 block coverage function ranges into exact per-line executed/missed sets and branch totals.
 * Inner `count: 0` ranges accurately override outer `count > 0` ranges.
 */
export function resolveV8FileCoverage({ sourceText = '', functions = [] } = {}) {
  const src = String(sourceText ?? '');
  const len = src.length;
  const lineStarts = [0];
  for (let i = 0; i < len; i += 1) if (src[i] === '\n') lineStarts.push(i + 1);

  const flatRanges = [];
  const branchRanges = new Map();
  for (const fn of Array.isArray(functions) ? functions : []) {
    const ranges = Array.isArray(fn?.ranges) ? fn.ranges : [];
    const rootRange = ranges[0] ?? null;
    for (let idx = 0; idx < ranges.length; idx += 1) {
      const r = ranges[idx];
      const start = Math.max(0, Math.min(len, Number(r?.startOffset ?? 0)));
      const end = Math.max(start, Math.min(len, Number(r?.endOffset ?? 0)));
      const count = Math.max(0, Number(r?.count ?? 0) || 0);
      if (end > start) flatRanges.push({ start, end, count, span: end - start });
      if (fn?.isBlockCoverage && idx > 0 && rootRange && (start > rootRange.startOffset || end < rootRange.endOffset)) {
        const key = `${start}:${end}`;
        branchRanges.set(key, Math.max(branchRanges.get(key) ?? 0, count));
      }
    }
  }

  // Sort outermost first, narrowest last so inner ranges override outer counts on their exact byte span.
  flatRanges.sort((a, b) => (b.span - a.span) || (a.start - b.start) || (a.count - b.count));

  const boundarySet = new Set([0, len]);
  for (const r of flatRanges) {
    boundarySet.add(r.start);
    boundarySet.add(r.end);
  }
  const boundaries = [...boundarySet].sort((a, b) => a - b);
  const segCount = Math.max(0, boundaries.length - 1);
  const segCounts = new Int32Array(segCount).fill(-1);

  const findBoundaryIdx = offset => {
    let lo = 0, hi = boundaries.length - 1;
    while (lo <= hi) {
      const mid = (lo + hi) >> 1;
      if (boundaries[mid] === offset) return mid;
      if (boundaries[mid] < offset) lo = mid + 1;
      else hi = mid - 1;
    }
    return lo;
  };

  for (const r of flatRanges) {
    const si = findBoundaryIdx(r.start);
    const ei = findBoundaryIdx(r.end);
    for (let k = si; k < ei && k < segCount; k += 1) {
      segCounts[k] = r.count;
    }
  }

  const codeOnly = lexCStyleSource(src).codeOnly;
  const executedLines = [];
  const missedLines = [];

  let segIdx = 0;
  for (let lineIdx = 0; lineIdx < lineStarts.length; lineIdx += 1) {
    const lStart = lineStarts[lineIdx];
    const lEnd = lineIdx + 1 < lineStarts.length ? lineStarts[lineIdx + 1] - 1 : len;
    const lineCode = codeOnly.slice(lStart, lEnd);
    if (!lineCode.trim() || NON_STMT_CSTYLE_LINE_RE.test(lineCode.trim())) continue;

    while (segIdx < segCount && boundaries[segIdx + 1] <= lStart) segIdx += 1;
    let hasPositive = false;
    let hasZero = false;
    for (let k = segIdx; k < segCount && boundaries[k] < lEnd; k += 1) {
      const ovStart = Math.max(lStart, boundaries[k]);
      const ovEnd = Math.min(lEnd, boundaries[k + 1]);
      if (ovEnd <= ovStart) continue;
      const piece = codeOnly.slice(ovStart, ovEnd).trim();
      if (!piece || /^[{};,()[\]]+$/.test(piece)) continue;
      const cnt = segCounts[k];
      if (cnt > 0) hasPositive = true;
      else if (cnt === 0) hasZero = true;
    }
    if (hasPositive) executedLines.push(lineIdx + 1);
    else if (hasZero) missedLines.push(lineIdx + 1);
  }

  const executableLines = [...executedLines, ...missedLines].sort((a, b) => a - b);
  const totalBranches = branchRanges.size;
  let coveredBranches = 0;
  for (const cnt of branchRanges.values()) if (cnt > 0) coveredBranches += 1;
  return { executedLines, missedLines, executableLines, totalBranches, coveredBranches, branchMap: Object.fromEntries(branchRanges) };
}

function mergeFileCoverageRecords(records) {
  const execSet = new Set();
  const allExecSet = new Set();
  let hasBranches = false;
  const branchMap = new Map();
  let maxBranches = 0;
  let maxCoveredBranches = 0;

  for (const rec of records) {
    for (const ln of rec.executedLines ?? []) { execSet.add(ln); allExecSet.add(ln); }
    for (const ln of rec.missedLines ?? []) allExecSet.add(ln);
    for (const ln of rec.executableLines ?? []) allExecSet.add(ln);
    if (rec.branchMap && typeof rec.branchMap === 'object') {
      hasBranches = true;
      for (const [k, v] of Object.entries(rec.branchMap)) {
        branchMap.set(k, Math.max(branchMap.get(k) ?? 0, Number(v) || 0));
      }
    } else if (typeof rec.totalBranches === 'number') {
      hasBranches = true;
      maxBranches = Math.max(maxBranches, rec.totalBranches);
      maxCoveredBranches = Math.max(maxCoveredBranches, Number(rec.coveredBranches) || 0);
    }
  }

  const executableLines = [...allExecSet].sort((a, b) => a - b);
  const executedLines = executableLines.filter(ln => execSet.has(ln));
  const missedLines = executableLines.filter(ln => !execSet.has(ln));
  let totalBranches = null;
  let coveredBranches = null;
  if (hasBranches) {
    if (branchMap.size > 0) {
      totalBranches = branchMap.size;
      coveredBranches = [...branchMap.values()].filter(v => v > 0).length;
    } else {
      totalBranches = maxBranches;
      coveredBranches = Math.min(maxBranches, maxCoveredBranches);
    }
  }
  return { executedLines, missedLines, executableLines, totalBranches, coveredBranches };
}

function toRepoRelPath(rawPath, realRoot) {
  let clean = String(rawPath ?? '').trim();
  if (!clean) return null;
  if (clean.startsWith('file://')) {
    try { clean = fileURLToPath(clean); } catch { return null; }
  }
  let rel;
  if (clean.startsWith('/') || /^[A-Za-z]:[\\/]/.test(clean)) {
    let resolved = clean;
    try { resolved = realpathSync(clean); } catch {}
    rel = relative(realRoot, resolved).split(sep).join('/');
  } else {
    rel = clean.replace(/\\/g, '/').replace(/^(?:\.\/)+/, '');
  }
  return canonicalRepoPath(rel) ? rel : null;
}

/**
 * Parse `coverage.py` JSON output (`coverage json`) into canonical repo-relative production file coverage records.
 */
export function parseCoveragePyJson({ jsonText = '', root = '' } = {}) {
  let parsed;
  try { parsed = JSON.parse(String(jsonText ?? '')); } catch { return {}; }
  let realRoot = root;
  if (root) {
    try { realRoot = realpathSync(root); } catch {}
  }
  const files = {};
  const rawFiles = parsed?.files && typeof parsed.files === 'object' ? parsed.files : {};
  for (const [rawKey, entry] of Object.entries(rawFiles)) {
    const rel = realRoot ? toRepoRelPath(rawKey, realRoot) : rawKey.replace(/\\/g, '/').replace(/^(?:\.\/)+/, '');
    if (!rel || !isProductionCodeFile(rel)) continue;
    const executedLines = uniqSortedNums(entry?.executed_lines);
    const missedLines = uniqSortedNums(entry?.missing_lines);
    const execSet = new Set(executedLines);
    const executableLines = uniqSortedNums([...executedLines, ...missedLines]);
    const summary = entry?.summary ?? {};
    const numBranches = typeof summary.num_branches === 'number' ? summary.num_branches : null;
    const coveredBranches = typeof summary.covered_branches === 'number'
      ? summary.covered_branches
      : (Array.isArray(entry?.executed_branches) ? entry.executed_branches.length : null);
    files[rel] = {
      executedLines: executableLines.filter(ln => execSet.has(ln)),
      missedLines: executableLines.filter(ln => !execSet.has(ln)),
      executableLines,
      totalBranches: numBranches,
      coveredBranches: numBranches !== null ? (coveredBranches ?? 0) : null,
    };
  }
  return files;
}

/**
 * Parse Go `go test -coverprofile` output into canonical repo-relative production file coverage records.
 */
export function parseGoCoverProfile({ profileText = '', modulePath = '' } = {}) {
  const perFileLines = new Map();
  const prefix = modulePath ? `${modulePath.replace(/\/+$/, '')}/` : '';
  for (const rawLine of String(profileText ?? '').split(/\r?\n/)) {
    const line = rawLine.trim();
    if (!line || line.startsWith('mode:')) continue;
    const m = /^(.+?):(\d+)\.\d+,(\d+)\.\d+\s+\d+\s+(\d+)$/.exec(line);
    if (!m) continue;
    let rel = m[1].replace(/\\/g, '/');
    if (prefix && rel.startsWith(prefix)) rel = rel.slice(prefix.length);
    rel = rel.replace(/^(?:\.\/)+/, '');
    if (!canonicalRepoPath(rel) || !isProductionCodeFile(rel)) continue;
    const startLine = Number(m[2]);
    const endLine = Number(m[3]);
    const count = Number(m[4]);
    let lineMap = perFileLines.get(rel);
    if (!lineMap) { lineMap = new Map(); perFileLines.set(rel, lineMap); }
    for (let ln = startLine; ln <= endLine; ln += 1) {
      lineMap.set(ln, Math.max(lineMap.get(ln) ?? 0, count));
    }
  }
  const files = {};
  for (const [rel, lineMap] of [...perFileLines.entries()].sort((a, b) => a[0].localeCompare(b[0]))) {
    const executableLines = [...lineMap.keys()].sort((a, b) => a - b);
    const executedLines = executableLines.filter(ln => (lineMap.get(ln) ?? 0) > 0);
    const missedLines = executableLines.filter(ln => (lineMap.get(ln) ?? 0) === 0);
    files[rel] = { executedLines, missedLines, executableLines, totalBranches: null, coveredBranches: null };
  }
  return files;
}

/**
 * Pure coverage split aggregator across `formal`, `vectors`, and `all` suites.
 */
export function aggregateCoverageSplit({ tool = null, diffLinesByFile = {}, suites = {}, fallbackExecutableLinesByFile = {} } = {}) {
  const diffMap = diffLinesByFile && typeof diffLinesByFile === 'object' ? diffLinesByFile : {};
  const fallbackMap = fallbackExecutableLinesByFile && typeof fallbackExecutableLinesByFile === 'object' ? fallbackExecutableLinesByFile : {};

  // Build canonical universe of production files and executable lines per file.
  const allFileSet = new Set(Object.keys(diffMap));
  const canonicalExecutable = new Map();
  const addExec = (file, lines) => {
    let s = canonicalExecutable.get(file);
    if (!s) { s = new Set(); canonicalExecutable.set(file, s); }
    for (const ln of uniqSortedNums(lines)) s.add(ln);
  };

  for (const name of SUITE_NAMES) {
    const suiteFiles = suites?.[name]?.files;
    if (!suiteFiles || typeof suiteFiles !== 'object') continue;
    for (const [file, rec] of Object.entries(suiteFiles)) {
      allFileSet.add(file);
      addExec(file, rec?.executableLines ?? [...(rec?.executedLines ?? []), ...(rec?.missedLines ?? [])]);
    }
  }
  for (const file of allFileSet) {
    const existing = canonicalExecutable.get(file);
    if (!existing || existing.size === 0) {
      const fb = uniqSortedNums(fallbackMap[file]);
      addExec(file, fb.length > 0 ? fb : uniqSortedNums(diffMap[file]));
    }
  }

  const sortedFiles = [...allFileSet].sort();
  const outSuites = {};

  for (const name of SUITE_NAMES) {
    const rawSuite = suites?.[name] ?? {};
    const rawFiles = rawSuite.files && typeof rawSuite.files === 'object' ? rawSuite.files : {};
    const suiteStatus = typeof rawSuite.status === 'string' ? rawSuite.status : 'not-found';
    const testFiles = Array.isArray(rawSuite.testFiles) ? [...rawSuite.testFiles] : [];
    const command = typeof rawSuite.command === 'string' ? rawSuite.command : null;

    let totalStatements = 0;
    let totalCovered = 0;
    let totalBranches = 0;
    let totalCoveredBranches = 0;
    let hasBranches = false;
    let diffTotal = 0;
    let diffCovered = 0;
    const perFileOut = {};

    for (const file of sortedFiles) {
      const canonExec = [...(canonicalExecutable.get(file) ?? [])].sort((a, b) => a - b);
      const canonSet = new Set(canonExec);
      const rec = rawFiles[file];
      const execSet = new Set(uniqSortedNums(rec?.executedLines).filter(ln => canonSet.has(ln)));
      const executedLines = canonExec.filter(ln => execSet.has(ln));
      const missedLines = canonExec.filter(ln => !execSet.has(ln));
      const fileDiffRaw = uniqSortedNums(diffMap[file]);
      const diffExecLines = fileDiffRaw.filter(ln => canonSet.has(ln));
      const diffCovLines = diffExecLines.filter(ln => execSet.has(ln));
      const diffMissLines = diffExecLines.filter(ln => !execSet.has(ln));

      const fBranches = typeof rec?.totalBranches === 'number' ? rec.totalBranches : null;
      const fCovBranches = fBranches !== null ? Math.min(fBranches, Number(rec?.coveredBranches) || 0) : null;
      if (fBranches !== null) {
        hasBranches = true;
        totalBranches += fBranches;
        totalCoveredBranches += fCovBranches;
      }

      totalStatements += canonExec.length;
      totalCovered += executedLines.length;
      diffTotal += diffExecLines.length;
      diffCovered += diffCovLines.length;

      perFileOut[file] = {
        statements: canonExec.length,
        covered: executedLines.length,
        missed: missedLines.length,
        pct: roundPct(executedLines.length, canonExec.length),
        branches: fBranches,
        coveredBranches: fCovBranches,
        branchPct: fBranches !== null ? roundPct(fCovBranches, fBranches) : null,
        executedLines,
        missedLines,
        diffLines: diffExecLines,
        diffCoveredLines: diffCovLines,
        diffMissedLines: diffMissLines,
        diffPct: roundPct(diffCovLines.length, diffExecLines.length),
      };
    }

    outSuites[name] = {
      status: suiteStatus,
      testFiles,
      command,
      total: {
        statements: totalStatements,
        covered: totalCovered,
        missed: totalStatements - totalCovered,
        pct: roundPct(totalCovered, totalStatements),
        branches: hasBranches ? totalBranches : null,
        coveredBranches: hasBranches ? totalCoveredBranches : null,
        branchPct: hasBranches ? roundPct(totalCoveredBranches, totalBranches) : null,
      },
      diff: {
        lines: diffTotal,
        covered: diffCovered,
        missed: diffTotal - diffCovered,
        pct: roundPct(diffCovered, diffTotal),
      },
      files: perFileOut,
    };
  }

  // Union of formal + vectors, plus formal-only and vectors-only counts.
  let unionStmts = 0, unionCov = 0, unionDiffLines = 0, unionDiffCov = 0;
  let formalOnlyLines = 0, vectorsOnlyLines = 0;
  const filesTable = [];
  const uncoveredDiffLines = [];

  for (const file of sortedFiles) {
    const fRec = outSuites.formal.files[file];
    const vRec = outSuites.vectors.files[file];
    const aRec = outSuites.all.files[file];
    const fSet = new Set(fRec.executedLines);
    const vSet = new Set(vRec.executedLines);
    const canonExec = [...(canonicalExecutable.get(file) ?? [])].sort((a, b) => a - b);

    for (const ln of canonExec) {
      const inF = fSet.has(ln);
      const inV = vSet.has(ln);
      if (inF || inV) unionCov += 1;
      if (inF && !inV) formalOnlyLines += 1;
      if (inV && !inF) vectorsOnlyLines += 1;
    }
    unionStmts += canonExec.length;

    const diffExecLines = aRec.diffLines;
    for (const ln of diffExecLines) {
      if (fSet.has(ln) || vSet.has(ln)) unionDiffCov += 1;
    }
    unionDiffLines += diffExecLines.length;

    const projectRow = r => ({
      covered: r.covered,
      statements: r.statements,
      pct: r.pct,
      diffCovered: r.diffCoveredLines.length,
      diffTotal: r.diffLines.length,
      diffPct: r.diffPct,
      diffMissedLines: r.diffMissedLines,
    });
    filesTable.push({
      file,
      touched: Object.hasOwn(diffMap, file),
      diffLines: diffExecLines,
      formal: projectRow(fRec),
      vectors: projectRow(vRec),
      all: projectRow(aRec),
    });

    if (diffExecLines.length > 0) {
      const missedAll = new Set(aRec.diffMissedLines);
      const missedFormal = new Set(fRec.diffMissedLines);
      const missedVectors = new Set(vRec.diffMissedLines);
      const gapLines = diffExecLines.filter(ln => missedAll.has(ln) || (missedFormal.has(ln) && missedVectors.has(ln)));
      if (gapLines.length > 0) {
        const missingIn = [];
        if (gapLines.some(ln => missedFormal.has(ln))) missingIn.push('formal');
        if (gapLines.some(ln => missedVectors.has(ln))) missingIn.push('vectors');
        if (gapLines.some(ln => missedAll.has(ln))) missingIn.push('all');
        uncoveredDiffLines.push({ file, lines: gapLines, missingIn });
      }
    }
  }

  const statuses = SUITE_NAMES.map(n => outSuites[n].status);
  let status;
  if (sortedFiles.length === 0) status = 'not-applicable';
  else if (statuses.includes('failed')) status = 'failed';
  else if (statuses.includes('ok')) status = 'ok';
  else status = 'unavailable';

  const fmtSuite = (label, s) => {
    if (s.status === 'not-found') return `${label} n/a`;
    if (s.status === 'unavailable' || s.status === 'timed-out' || s.status === 'interrupted') return `${label} ${s.status}`;
    if (s.diff.lines > 0) return `${label} ${s.diff.pct.toFixed(1)}% (${s.diff.covered}/${s.diff.lines})`;
    if (s.total.statements > 0) return `${label} ${s.total.pct.toFixed(1)}% (${s.total.covered}/${s.total.statements})`;
    return `${label} 0/0`;
  };
  const toolTag = tool ? ` (${tool})` : '';
  const summary = status === 'not-applicable'
    ? `Coverage${toolTag}: not-applicable (0 production files)`
    : `Coverage${toolTag}: diff ${fmtSuite('formal', outSuites.formal)}, ${fmtSuite('vectors', outSuites.vectors)}, ${fmtSuite('all', outSuites.all)}`;

  return {
    status,
    suites: outSuites,
    unionFormalVectors: {
      total: {
        statements: unionStmts,
        covered: unionCov,
        missed: unionStmts - unionCov,
        pct: roundPct(unionCov, unionStmts),
      },
      diff: {
        lines: unionDiffLines,
        covered: unionDiffCov,
        missed: unionDiffLines - unionDiffCov,
        pct: roundPct(unionDiffCov, unionDiffLines),
      },
      formalOnlyLines,
      vectorsOnlyLines,
    },
    files: filesTable,
    uncoveredDiffLines,
    summary,
  };
}

function listFilesSafe(realRoot, provided = null) {
  if (Array.isArray(provided)) return [...new Set(provided.filter(canonicalRepoPath))].sort();
  try {
    const tracked = gitFiles(realRoot);
    if (Array.isArray(tracked) && tracked.length > 0) return [...new Set(tracked.filter(canonicalRepoPath))].sort();
  } catch {}
  const found = [];
  const walk = (abs, prefix, depth) => {
    if (depth > 8 || found.length >= 10_000) return;
    let entries;
    try { entries = readdirSync(abs, { withFileTypes: true }); } catch { return; }
    for (const e of entries) {
      if (e.isSymbolicLink()) continue;
      if (['.git', 'node_modules', '.venv', 'venv', '__pycache__', 'target'].includes(e.name)) continue;
      const rel = prefix ? `${prefix}/${e.name}` : e.name;
      if (e.isDirectory()) walk(join(abs, e.name), rel, depth + 1);
      else if (e.isFile() && canonicalRepoPath(rel)) found.push(rel);
    }
  };
  walk(realRoot, '', 0);
  return found.sort();
}

function detectRepoCoverageLanguage(realRoot, touchedProdFiles, allRepoFiles, testCommand) {
  const prodSample = touchedProdFiles.length > 0 ? touchedProdFiles : allRepoFiles.filter(isProductionCodeFile);
  const pyCount = prodSample.filter(f => PY_FILE_RE.test(f)).length;
  const jsCount = prodSample.filter(f => JS_FILE_RE.test(f)).length;
  const goCount = prodSample.filter(f => GO_FILE_RE.test(f)).length;
  if (pyCount > 0 && pyCount >= jsCount && pyCount >= goCount) return 'python';
  if (jsCount > 0 && jsCount >= pyCount && jsCount >= goCount) return 'javascript';
  if (goCount > 0) return 'go';
  if (typeof testCommand === 'string') {
    if (/\b(?:pytest|unittest|python3?)\b/i.test(testCommand)) return 'python';
    if (/\bgo\s+test\b/i.test(testCommand)) return 'go';
    if (/\b(?:node|npm|pnpm|yarn|vitest|jest|c8)\b/i.test(testCommand)) return 'javascript';
  }
  if (existsSync(join(realRoot, 'pyproject.toml')) || existsSync(join(realRoot, 'pytest.ini'))) return 'python';
  if (existsSync(join(realRoot, 'go.mod'))) return 'go';
  if (existsSync(join(realRoot, 'package.json'))) return 'javascript';
  return 'unknown';
}

export function discoverCoverageSuites({ root, allFiles = null, testCommand = null, touchedProdFiles = [] } = {}) {
  let realRoot;
  try { realRoot = realpathSync(root); } catch { return { formalFiles: [], vectorFiles: [], testCommand, language: 'unknown' }; }
  const repoFiles = listFilesSafe(realRoot, allFiles);
  const language = detectRepoCoverageLanguage(realRoot, touchedProdFiles, repoFiles, testCommand);
  const langMatch = f => (
    language === 'python' ? PY_FILE_RE.test(f)
      : language === 'go' ? GO_FILE_RE.test(f)
        : language === 'javascript' ? JS_FILE_RE.test(f)
          : true
  );
  const isRegularInRoot = rel => {
    try {
      const st = lstatSync(join(realRoot, rel));
      return st.isFile() && !st.isSymbolicLink();
    } catch { return false; }
  };
  const formalFiles = repoFiles.filter(f => FORMAL_TEST_FILE_RE.test(f) && langMatch(f) && isRegularInRoot(f)).sort();
  const vectorFiles = repoFiles.filter(f => VECTOR_TEST_FILE_RE.test(f) && !FORMAL_TEST_FILE_RE.test(f) && langMatch(f) && isRegularInRoot(f)).sort();
  return { formalFiles, vectorFiles, testCommand, language };
}

function collectV8CoverageDir(v8Dir, realRoot) {
  const byFileRuns = new Map();
  if (!existsSync(v8Dir)) return {};
  for (const name of readdirSync(v8Dir)) {
    if (!name.endsWith('.json')) continue;
    let doc;
    try { doc = JSON.parse(readFileSync(join(v8Dir, name), 'utf8')); } catch { continue; }
    for (const script of Array.isArray(doc?.result) ? doc.result : []) {
      const rel = toRepoRelPath(script?.url, realRoot);
      if (!rel || !isProductionCodeFile(rel)) continue;
      const src = readSafeUtf8(realRoot, rel);
      if (typeof src !== 'string') continue;
      const resolved = resolveV8FileCoverage({ sourceText: src, functions: script.functions ?? [] });
      let list = byFileRuns.get(rel);
      if (!list) { list = []; byFileRuns.set(rel, list); }
      list.push(resolved);
    }
  }
  const merged = {};
  for (const [rel, runs] of [...byFileRuns.entries()].sort((a, b) => a[0].localeCompare(b[0]))) {
    merged[rel] = mergeFileCoverageRecords(runs);
  }
  return merged;
}

function runExecMaybeAsync(useAsync, command, args, opts, ports = {}, signalCtrl = null) {
  if (typeof ports.spawnSync === 'function') {
    const res = Array.isArray(args) ? ports.spawnSync(command, args, opts) : ports.spawnSync(command, opts);
    return useAsync ? Promise.resolve(res) : res;
  }
  if (useAsync) return execChildAsync(command, args, opts, signalCtrl);
  return Array.isArray(args) ? spawnSync(command, args, opts) : spawnSync(command, opts);
}

function runNodeSuiteCoverageImpl({ realRoot, suiteName, files, command, v8Dir, timeoutMs, env, useAsync = false, signalCtrl = null }, ports = {}) {
  mkdirSync(v8Dir, { recursive: true });
  const childEnv = { ...scrubChildEnv(env), NODE_V8_COVERAGE: v8Dir, CI: 'true' };
  delete childEnv.NODE_TEST_CONTEXT;
  delete childEnv.NODE_OPTIONS;

  const exec = (cmd, args, opts) => runExecMaybeAsync(useAsync, cmd, args, opts, ports, signalCtrl);

  const finish = ({ ok, timedOut, interruptedBy, errorMsg, cmdDisplay }) => {
    const parsedFiles = interruptedBy ? {} : collectV8CoverageDir(v8Dir, realRoot);
    return {
      status: interruptedBy ? 'interrupted' : (timedOut ? 'timed-out' : (ok ? 'ok' : 'failed')),
      testFiles: files,
      command: cmdDisplay,
      files: parsedFiles,
      error: interruptedBy ? `Interrupted by signal ${interruptedBy}` : errorMsg,
      timedOut,
      interruptedBy,
    };
  };

  if (suiteName === 'all') {
    if (!command) {
      const empty = { status: 'not-found', testFiles: [], command: null, files: {}, error: null, timedOut: false, interruptedBy: null };
      return useAsync ? Promise.resolve(empty) : empty;
    }
    const opts = { cwd: realRoot, env: childEnv, shell: true, encoding: 'utf8', timeout: timeoutMs, maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] };
    const handleProc = proc => {
      const timedOut = proc?.error?.code === 'ETIMEDOUT';
      const interruptedBy = signalCtrl?.signal ?? detectSignalInterruption(proc);
      const ok = !interruptedBy && proc?.status === 0 && !proc?.error && !proc?.signal;
      const errorMsg = !ok && !timedOut && !interruptedBy ? causeText(proc?.stderr || proc?.stdout || proc?.error?.message || `exit ${proc?.status}`) : null;
      return finish({ ok, timedOut, interruptedBy, errorMsg, cmdDisplay: command });
    };
    return useAsync ? exec(command, null, opts).then(handleProc) : handleProc(exec(command, null, opts));
  }

  if (!files.length) {
    const empty = { status: 'not-found', testFiles: [], command: null, files: {}, error: null, timedOut: false, interruptedBy: null };
    return useAsync ? Promise.resolve(empty) : empty;
  }

  const runFilesLoop = async () => {
    let ok = true, timedOut = false, interruptedBy = null, errorMsg = null;
    const cmds = [];
    for (const filePath of files) {
      if (signalCtrl?.signal) { interruptedBy = signalCtrl.signal; ok = false; break; }
      const kind = chooseRunnerForFormalFile(realRoot, filePath);
      if (!kind) { ok = false; errorMsg = `No JS test runner found for ${filePath}`; break; }
      const inv = buildRunnerInvocation(kind, { root: realRoot, files: [filePath] });
      cmds.push(`${inv.bin} ${inv.args.join(' ')}`);
      const proc = await exec(inv.bin, inv.args, { cwd: realRoot, env: childEnv, shell: false, encoding: 'utf8', timeout: timeoutMs, maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
      const sig = signalCtrl?.signal ?? detectSignalInterruption(proc);
      if (sig) { interruptedBy = sig; ok = false; break; }
      if (proc?.error?.code === 'ETIMEDOUT') { timedOut = true; ok = false; break; }
      if (proc?.status !== 0 || proc?.error || proc?.signal) {
        ok = false;
        errorMsg = causeText(proc?.stderr || proc?.stdout || proc?.error?.message || `exit ${proc?.status}`);
      }
    }
    return finish({ ok, timedOut, interruptedBy, errorMsg, cmdDisplay: cmds.join(' && ') });
  };

  if (useAsync) return runFilesLoop();

  let ok = true, timedOut = false, interruptedBy = null, errorMsg = null;
  const cmds = [];
  for (const filePath of files) {
    const kind = chooseRunnerForFormalFile(realRoot, filePath);
    if (!kind) { ok = false; errorMsg = `No JS test runner found for ${filePath}`; break; }
    const inv = buildRunnerInvocation(kind, { root: realRoot, files: [filePath] });
    cmds.push(`${inv.bin} ${inv.args.join(' ')}`);
    const proc = exec(inv.bin, inv.args, { cwd: realRoot, env: childEnv, shell: false, encoding: 'utf8', timeout: timeoutMs, maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
    const sig = detectSignalInterruption(proc);
    if (sig) { interruptedBy = sig; ok = false; break; }
    if (proc?.error?.code === 'ETIMEDOUT') { timedOut = true; ok = false; break; }
    if (proc?.status !== 0 || proc?.error || proc?.signal) {
      ok = false;
      errorMsg = causeText(proc?.stderr || proc?.stdout || proc?.error?.message || `exit ${proc?.status}`);
    }
  }
  return finish({ ok, timedOut, interruptedBy, errorMsg, cmdDisplay: cmds.join(' && ') });
}

function runNodeSuiteCoverage(opts, ports = {}) {
  return runNodeSuiteCoverageImpl({ ...opts, useAsync: false }, ports);
}

function runNodeSuiteCoverageAsync(opts, ports = {}, signalCtrl = null) {
  return runNodeSuiteCoverageImpl({ ...opts, useAsync: true, signalCtrl }, ports);
}

function hasPythonModule(pythonBin, modName, env) {
  const probe = spawnSync(pythonBin, ['-c', `import ${modName}`], {
    env: scrubChildEnv(env),
    encoding: 'utf8',
    timeout: 5000,
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  return probe.status === 0;
}

function parseShellEnvPrefix(command) {
  const extraEnv = {};
  let rest = String(command ?? '').trim();
  if (/^env\s+/.test(rest)) rest = rest.replace(/^env\s+/, '').trim();
  while (true) {
    const m = /^([A-Za-z_][A-Za-z0-9_]*)=([^\s'"]+|'[^']*'|"[^"]*")\s+(.*)$/.exec(rest);
    if (!m) break;
    extraEnv[m[1]] = m[2].replace(/^['"]|['"]$/g, '');
    rest = m[3].trim();
  }
  return { extraEnv, rest };
}

function splitSimpleArgs(cmd) {
  const out = [];
  const re = /'([^']*)'|"([^"]*)"|(\S+)/g;
  for (const m of String(cmd ?? '').matchAll(re)) out.push(m[1] ?? m[2] ?? m[3]);
  return out;
}

function parsePythonTestTarget(command) {
  const { extraEnv, rest } = parseShellEnvPrefix(command);
  const tokens = splitSimpleArgs(rest);
  if (!tokens.length) return { extraEnv, moduleName: null, args: [] };
  const head = tokens[0];
  if (/(?:^|\/)pytest$/.test(head)) return { extraEnv, moduleName: 'pytest', args: tokens.slice(1) };
  if (/(?:^|\/)python(?:\d+(?:\.\d+)?)?$/.test(head) && tokens[1] === '-m' && tokens[2]) {
    return { extraEnv, moduleName: tokens[2], args: tokens.slice(3) };
  }
  return { extraEnv, moduleName: null, args: tokens };
}

const UNSUPPORTED_SHELL_CHAR_RE = /[;|&<>`\n\r()]/;

/**
 * Parse single or `&&`-chained Python test commands (`pytest` / `python -m unittest`),
 * rejecting unsupported shell operators (`||`, `;`, `|`, subshells, redirections) fail-closed.
 */
export function parsePythonTestPipeline(command) {
  const raw = String(command ?? '').trim();
  if (!raw) return { ok: false, segments: [], reason: 'empty command' };
  const rawSegments = [];
  let cur = '';
  let quote = null;
  for (let i = 0; i < raw.length; i += 1) {
    const ch = raw[i];
    if (quote === '\'') {
      if (ch === '\'') quote = null;
      cur += ch;
      continue;
    }
    if (quote === '"') {
      if (ch === '\\' && i + 1 < raw.length) { cur += ch + raw[i + 1]; i += 1; continue; }
      if (ch === '`' || (ch === '$' && raw[i + 1] === '(')) {
        return { ok: false, segments: [], reason: 'contains unsupported command substitution' };
      }
      if (ch === '"') quote = null;
      cur += ch;
      continue;
    }
    if (ch === '\\' && i + 1 < raw.length) { cur += ch + raw[i + 1]; i += 1; continue; }
    if (ch === '\'' || ch === '"') { quote = ch; cur += ch; continue; }
    if (ch === '&' && raw[i + 1] === '&') {
      const seg = cur.trim();
      if (!seg) return { ok: false, segments: [], reason: 'empty command segment around &&' };
      rawSegments.push(seg);
      cur = '';
      i += 1;
      continue;
    }
    if (ch === '$' && raw[i + 1] === '(') {
      return { ok: false, segments: [], reason: 'contains unsupported command substitution' };
    }
    if (UNSUPPORTED_SHELL_CHAR_RE.test(ch)) {
      return { ok: false, segments: [], reason: `contains unsupported shell operator "${ch}"` };
    }
    cur += ch;
  }
  if (quote !== null) return { ok: false, segments: [], reason: 'unclosed quote in command' };
  const lastSeg = cur.trim();
  if (!lastSeg) return { ok: false, segments: [], reason: 'trailing && operator' };
  rawSegments.push(lastSeg);

  const segments = [];
  for (const seg of rawSegments) {
    const parsed = parsePythonTestTarget(seg);
    if (!parsed.moduleName || !['pytest', 'unittest'].includes(parsed.moduleName)) {
      return { ok: false, segments: [], reason: `unsupported Python test segment "${seg}"` };
    }
    segments.push(parsed);
  }
  return { ok: true, segments, reason: null };
}

const PY_STDLIB_TRACE_DRIVER = `
import ast, importlib.util, json, os, runpy, sys, traceback, unittest

out_path = sys.argv[1]
root = os.path.realpath(sys.argv[2])
mode = sys.argv[3]
target_args = sys.argv[4:]

if root not in sys.path:
    sys.path.insert(0, root)
src_dir = os.path.join(root, 'src')
if os.path.isdir(src_dir) and src_dir not in sys.path:
    sys.path.insert(0, src_dir)

executed = {}

def tracer(frame, event, arg):
    if event == 'line':
        fn = frame.f_code.co_filename
        if fn and not fn.startswith('<'):
            try:
                rp = os.path.realpath(fn)
                if rp.startswith(root + os.sep) and rp.endswith('.py'):
                    rel = os.path.relpath(rp, root).replace(os.sep, '/')
                    executed.setdefault(rel, set()).add(frame.f_lineno)
            except Exception:
                pass
    return tracer

def collect_exec_lines(abs_path):
    try:
        with open(abs_path, 'r', encoding='utf-8') as fh:
            src = fh.read()
        tree = ast.parse(src, filename=abs_path)
    except Exception:
        return [], []
    lines = set()
    header_spans = []
    for node in ast.walk(tree):
        if isinstance(node, ast.stmt) and hasattr(node, 'lineno'):
            if isinstance(node, ast.Expr) and isinstance(getattr(node, 'value', None), ast.Constant) and isinstance(node.value.value, str):
                continue
            lines.add(node.lineno)
            cond = getattr(node, 'test', None) if isinstance(node, (ast.If, ast.While)) else (getattr(node, 'value', None) if isinstance(node, ast.Return) else None)
            if cond is not None and getattr(cond, 'lineno', None) is not None:
                c_end = getattr(cond, 'end_lineno', None) or cond.lineno
                if c_end > node.lineno:
                    header_spans.append((node.lineno, cond.lineno, c_end))
    return sorted(lines), header_spans

def run_py_file_tests(files):
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    fn_failed = 0
    for idx, fpath in enumerate(files):
        abs_f = os.path.abspath(fpath)
        spec = importlib.util.spec_from_file_location(f'_pdd_cov_mod_{idx}', abs_f)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        loaded = loader.loadTestsFromModule(mod)
        if loaded.countTestCases() > 0:
            suite.addTests(loaded)
        else:
            for name in sorted(dir(mod)):
                if not name.startswith('test_'):
                    continue
                fn = getattr(mod, name)
                if callable(fn):
                    try:
                        fn()
                    except Exception:
                        fn_failed += 1
                        traceback.print_exc()
    ok = fn_failed == 0
    if suite.countTestCases() > 0:
        res = unittest.TextTestRunner(verbosity=1).run(suite)
        ok = ok and res.wasSuccessful()
    return 0 if ok else 1

exit_code = 0
sys.settrace(tracer)
try:
    if mode == 'pytest':
        import pytest
        exit_code = int(pytest.main(target_args))
    elif mode == 'unittest':
        sys.argv = ['unittest'] + target_args
        try:
            runpy.run_module('unittest', run_name='__main__', alter_sys=True)
        except SystemExit as exc:
            exit_code = int(exc.code) if isinstance(exc.code, int) else (0 if exc.code is None else 1)
    elif mode == 'unittest-files':
        exit_code = run_py_file_tests(target_args)
    else:
        sys.argv = [mode] + target_args
        try:
            runpy.run_module(mode, run_name='__main__', alter_sys=True)
        except SystemExit as exc:
            exit_code = int(exc.code) if isinstance(exc.code, int) else (0 if exc.code is None else 1)
finally:
    sys.settrace(None)

files_out = {}
for dirpath, dirnames, filenames in os.walk(root):
    dirnames[:] = [d for d in dirnames if d not in ('.git', '.venv', 'venv', 'node_modules', '__pycache__', '.pytest_cache')]
    for fn in filenames:
        if not fn.endswith('.py'):
            continue
        abs_p = os.path.join(dirpath, fn)
        if os.path.islink(abs_p):
            continue
        rel = os.path.relpath(abs_p, root).replace(os.sep, '/')
        all_lines, header_spans = collect_exec_lines(abs_p)
        raw_hit = set(executed.get(rel, set()))
        for hdr_ln, c_lo, c_hi in header_spans:
            if any(c_lo <= ln <= c_hi for ln in raw_hit):
                raw_hit.add(hdr_ln)
        all_set = set(all_lines) | raw_hit
        hit = sorted(raw_hit & all_set)
        miss = sorted(all_set - set(hit))
        files_out[rel] = {
            'executed_lines': hit,
            'missing_lines': miss,
            'summary': {'num_statements': len(all_set), 'covered_lines': len(hit)},
        }

with open(out_path, 'w', encoding='utf-8') as fh:
    json.dump({'files': files_out}, fh)
sys.exit(exit_code)
`;

function preparePythonSuitePlan({ realRoot, suiteName, files, command, tempDir, pythonBin, hasCoveragePy, hasPytestMod, sourceDirs, env }) {
  const baseEnv = buildRunnerEnv('pytest', realRoot, scrubChildEnv(env));
  const covFile = join(tempDir, `cov.${suiteName}`);
  const jsonOut = join(tempDir, `cov.${suiteName}.json`);
  let segments;

  if (suiteName === 'all') {
    if (!command) {
      return { earlyResult: { status: 'not-found', testFiles: [], command: null, files: {}, error: null, timedOut: false, interruptedBy: null } };
    }
    const pipeline = parsePythonTestPipeline(command);
    if (!pipeline.ok) {
      return {
        earlyResult: {
          status: 'unavailable',
          testFiles: [],
          command,
          files: {},
          error: `Unsupported Python test command for coverage wrapping (${pipeline.reason}): ${command}`,
          timedOut: false,
          interruptedBy: null,
        },
      };
    }
    if (pipeline.segments.some(s => s.moduleName === 'pytest') && !hasPytestMod) {
      return {
        earlyResult: {
          status: 'unavailable',
          testFiles: [],
          command,
          files: {},
          error: `pytest module is not installed in "${pythonBin}" for coverage wrapping`,
          timedOut: false,
          interruptedBy: null,
        },
      };
    }
    segments = pipeline.segments;
  } else {
    if (!files.length) {
      return { earlyResult: { status: 'not-found', testFiles: [], command: null, files: {}, error: null, timedOut: false, interruptedBy: null } };
    }
    if (hasPytestMod) {
      segments = [{ extraEnv: {}, moduleName: 'pytest', args: ['-q', '--', ...files.map(f => (f.startsWith('-') ? `./${f}` : f))] }];
    } else {
      segments = [{ extraEnv: {}, moduleName: 'unittest-files', args: files }];
    }
  }

  const steps = [];
  const srcArg = sourceDirs.length > 0 ? [`--source=${sourceDirs.join(',')}`] : [];
  if (hasCoveragePy) {
    for (let i = 0; i < segments.length; i += 1) {
      const seg = segments[i];
      const appendFlag = i > 0 ? ['--append'] : [];
      const childEnv = { ...baseEnv, ...seg.extraEnv, COVERAGE_FILE: covFile, CI: 'true' };
      if (seg.moduleName === 'unittest-files') {
        const uRunner = join(tempDir, 'pdd_py_unittest_files.py');
        if (!existsSync(uRunner)) {
          writeFileSync(uRunner, [
            'import os, sys, unittest',
            'root = os.path.realpath(sys.argv[1])',
            'if root not in sys.path: sys.path.insert(0, root)',
            'src_dir = os.path.join(root, "src")',
            'if os.path.isdir(src_dir) and src_dir not in sys.path: sys.path.insert(0, src_dir)',
            'loader = unittest.TestLoader()',
            'suite = unittest.TestSuite()',
            'for fpath in sys.argv[2:]:',
            '    suite.addTests(loader.discover(start_dir=os.path.dirname(os.path.abspath(fpath)), pattern=os.path.basename(fpath), top_level_dir=root))',
            'res = unittest.TextTestRunner(verbosity=1).run(suite)',
            'sys.exit(0 if res.wasSuccessful() else 1)',
          ].join('\n') + '\n', 'utf8');
        }
        const runArgs = ['-m', 'coverage', 'run', ...appendFlag, '--branch', ...srcArg, uRunner, realRoot, ...seg.args];
        steps.push({ args: runArgs, env: childEnv, display: `${pythonBin} ${runArgs.join(' ')}`, jsonOut: null });
      } else {
        const runArgs = ['-m', 'coverage', 'run', ...appendFlag, '--branch', ...srcArg, '-m', seg.moduleName, ...seg.args];
        steps.push({ args: runArgs, env: childEnv, display: `${pythonBin} ${runArgs.join(' ')}`, jsonOut: null });
      }
    }
    return { earlyResult: null, mode: 'coverage.py', covFile, jsonOut, baseEnv: { ...baseEnv, COVERAGE_FILE: covFile, CI: 'true' }, steps };
  }

  const driverPath = join(tempDir, 'pdd_py_trace.py');
  if (!existsSync(driverPath)) writeFileSync(driverPath, PY_STDLIB_TRACE_DRIVER, 'utf8');
  for (let i = 0; i < segments.length; i += 1) {
    const seg = segments[i];
    const segJson = segments.length === 1 ? jsonOut : join(tempDir, `cov.${suiteName}.${i}.json`);
    const childEnv = { ...baseEnv, ...seg.extraEnv, CI: 'true' };
    const traceArgs = [driverPath, segJson, realRoot, seg.moduleName, ...seg.args];
    steps.push({ args: traceArgs, env: childEnv, display: `${pythonBin} <pdd-python-trace> ${seg.moduleName} ${seg.args.join(' ')}`.trim(), jsonOut: segJson });
  }
  return { earlyResult: null, mode: 'python-trace', covFile, jsonOut, baseEnv, steps };
}

function mergeParsedCoverageMaps(maps) {
  const byFile = new Map();
  for (const map of maps) {
    for (const [rel, rec] of Object.entries(map ?? {})) {
      let arr = byFile.get(rel);
      if (!arr) { arr = []; byFile.set(rel, arr); }
      arr.push(rec);
    }
  }
  const merged = {};
  for (const [rel, list] of [...byFile.entries()].sort((a, b) => a[0].localeCompare(b[0]))) {
    merged[rel] = mergeFileCoverageRecords(list);
  }
  return merged;
}

function runPythonSuiteCoverage(opts, ports = {}) {
  const plan = preparePythonSuitePlan(opts);
  if (plan.earlyResult) return plan.earlyResult;
  const { realRoot, files, pythonBin, timeoutMs } = opts;
  const runner = ports.spawnSync ?? spawnSync;

  let ok = true, timedOut = false, missing = false, interruptedBy = null, errorMsg = null;
  for (const step of plan.steps) {
    const proc = runner(pythonBin, step.args, { cwd: realRoot, env: step.env, shell: false, encoding: 'utf8', timeout: timeoutMs, maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
    const sig = detectSignalInterruption(proc);
    if (sig) { interruptedBy = sig; ok = false; break; }
    if (proc?.error?.code === 'ETIMEDOUT') { timedOut = true; ok = false; break; }
    if (proc?.error?.code === 'ENOENT') {
      missing = true;
      ok = false;
      errorMsg = causeText(proc.error.message || `Python binary "${pythonBin}" not found`);
      break;
    }
    if (proc?.status !== 0 || proc?.error || proc?.signal) {
      ok = false;
      errorMsg = causeText(proc?.stderr || proc?.stdout || proc?.error?.message || `exit ${proc?.status}`);
      break;
    }
  }

  let parsedFiles = {};
  if (!interruptedBy && !timedOut && !missing) {
    if (plan.mode === 'coverage.py') {
      if (existsSync(plan.covFile)) {
        runner(pythonBin, ['-m', 'coverage', 'json', '-o', plan.jsonOut], { cwd: realRoot, env: plan.baseEnv, shell: false, encoding: 'utf8', timeout: Math.min(timeoutMs, 60_000), maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
      }
      parsedFiles = existsSync(plan.jsonOut) ? parseCoveragePyJson({ jsonText: readFileSync(plan.jsonOut, 'utf8'), root: realRoot }) : {};
    } else {
      const maps = plan.steps
        .filter(s => s.jsonOut && existsSync(s.jsonOut))
        .map(s => parseCoveragePyJson({ jsonText: readFileSync(s.jsonOut, 'utf8'), root: realRoot }));
      parsedFiles = mergeParsedCoverageMaps(maps);
    }
  }
  return {
    status: interruptedBy ? 'interrupted' : (timedOut ? 'timed-out' : (missing ? 'unavailable' : (ok ? 'ok' : 'failed'))),
    testFiles: files,
    command: plan.steps.map(s => s.display).join(' && '),
    files: parsedFiles,
    error: interruptedBy ? `Interrupted by signal ${interruptedBy}` : (ok || timedOut ? null : errorMsg),
    timedOut,
    interruptedBy,
  };
}

async function runPythonSuiteCoverageAsync(opts, ports = {}, signalCtrl = null) {
  const plan = preparePythonSuitePlan(opts);
  if (plan.earlyResult) return plan.earlyResult;
  const { realRoot, files, pythonBin, timeoutMs } = opts;

  let ok = true, timedOut = false, missing = false, interruptedBy = null, errorMsg = null;
  for (const step of plan.steps) {
    if (signalCtrl?.signal) { interruptedBy = signalCtrl.signal; ok = false; break; }
    const proc = await runExecMaybeAsync(true, pythonBin, step.args, { cwd: realRoot, env: step.env, shell: false, encoding: 'utf8', timeout: timeoutMs, maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] }, ports, signalCtrl);
    const sig = signalCtrl?.signal ?? detectSignalInterruption(proc);
    if (sig) { interruptedBy = sig; ok = false; break; }
    if (proc?.error?.code === 'ETIMEDOUT') { timedOut = true; ok = false; break; }
    if (proc?.error?.code === 'ENOENT') {
      missing = true;
      ok = false;
      errorMsg = causeText(proc.error.message || `Python binary "${pythonBin}" not found`);
      break;
    }
    if (proc?.status !== 0 || proc?.error || proc?.signal) {
      ok = false;
      errorMsg = causeText(proc?.stderr || proc?.stdout || proc?.error?.message || `exit ${proc?.status}`);
      break;
    }
  }

  let parsedFiles = {};
  if (!interruptedBy && !timedOut && !missing && !signalCtrl?.signal) {
    if (plan.mode === 'coverage.py') {
      if (existsSync(plan.covFile)) {
        await runExecMaybeAsync(true, pythonBin, ['-m', 'coverage', 'json', '-o', plan.jsonOut], { cwd: realRoot, env: plan.baseEnv, shell: false, encoding: 'utf8', timeout: Math.min(timeoutMs, 60_000), maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] }, ports, signalCtrl);
      }
      parsedFiles = existsSync(plan.jsonOut) ? parseCoveragePyJson({ jsonText: readFileSync(plan.jsonOut, 'utf8'), root: realRoot }) : {};
    } else {
      const maps = plan.steps
        .filter(s => s.jsonOut && existsSync(s.jsonOut))
        .map(s => parseCoveragePyJson({ jsonText: readFileSync(s.jsonOut, 'utf8'), root: realRoot }));
      parsedFiles = mergeParsedCoverageMaps(maps);
    }
  }
  return {
    status: interruptedBy ? 'interrupted' : (timedOut ? 'timed-out' : (missing ? 'unavailable' : (ok ? 'ok' : 'failed'))),
    testFiles: files,
    command: plan.steps.map(s => s.display).join(' && '),
    files: parsedFiles,
    error: interruptedBy ? `Interrupted by signal ${interruptedBy}` : (ok || timedOut ? null : errorMsg),
    timedOut,
    interruptedBy,
  };
}

function prepareGoSuiteArgs({ realRoot, suiteName, files, tempDir }) {
  const profileOut = join(tempDir, `go-${suiteName}.out`);
  if (suiteName === 'all') return { profileOut, args: ['test', '-covermode=count', `-coverprofile=${profileOut}`, './...'] };
  if (!files.length) return { profileOut, args: null };
  const testNames = [];
  const pkgs = new Set();
  for (const f of files) {
    const dir = posix.dirname(f);
    pkgs.add(dir === '.' ? './.' : `./${dir}`);
    const src = readSafeUtf8(realRoot, f) ?? '';
    for (const m of src.matchAll(/^func\s+(Test[A-Za-z0-9_]*)\s*\(/gm)) testNames.push(m[1]);
  }
  const runFilter = testNames.length > 0 ? ['-run', `^(${testNames.join('|')})$`] : [];
  return { profileOut, args: ['test', '-covermode=count', `-coverprofile=${profileOut}`, ...runFilter, ...pkgs] };
}

function finalizeGoSuiteCoverage({ proc, profileOut, args, files, modulePath, signalCtrl = null }) {
  const timedOut = proc?.error?.code === 'ETIMEDOUT';
  const interruptedBy = signalCtrl?.signal ?? detectSignalInterruption(proc);
  const missing = !interruptedBy && proc?.error?.code === 'ENOENT';
  const ok = !interruptedBy && proc?.status === 0 && !proc?.error && !proc?.signal;
  const parsedFiles = !interruptedBy && existsSync(profileOut)
    ? parseGoCoverProfile({ profileText: readFileSync(profileOut, 'utf8'), modulePath })
    : {};
  return {
    status: interruptedBy ? 'interrupted' : (timedOut ? 'timed-out' : (missing ? 'unavailable' : (ok ? 'ok' : 'failed'))),
    testFiles: files,
    command: `go ${args.join(' ')}`,
    files: parsedFiles,
    error: interruptedBy ? `Interrupted by signal ${interruptedBy}` : (ok || timedOut ? null : causeText(proc?.stderr || proc?.stdout || proc?.error?.message || `exit ${proc?.status}`)),
    timedOut,
    interruptedBy,
  };
}

function runGoSuiteCoverage({ realRoot, suiteName, files, tempDir, modulePath, timeoutMs, env }, ports = {}) {
  const { profileOut, args } = prepareGoSuiteArgs({ realRoot, suiteName, files, tempDir });
  if (!args) return { status: 'not-found', testFiles: [], command: null, files: {}, error: null, timedOut: false, interruptedBy: null };
  const runner = ports.spawnSync ?? spawnSync;
  const proc = runner('go', args, { cwd: realRoot, env: { ...scrubChildEnv(env), CI: 'true' }, shell: false, encoding: 'utf8', timeout: timeoutMs, maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
  return finalizeGoSuiteCoverage({ proc, profileOut, args, files, modulePath });
}

async function runGoSuiteCoverageAsync({ realRoot, suiteName, files, tempDir, modulePath, timeoutMs, env }, ports = {}, signalCtrl = null) {
  const { profileOut, args } = prepareGoSuiteArgs({ realRoot, suiteName, files, tempDir });
  if (!args) return { status: 'not-found', testFiles: [], command: null, files: {}, error: null, timedOut: false, interruptedBy: null };
  const proc = await runExecMaybeAsync(true, 'go', args, { cwd: realRoot, env: { ...scrubChildEnv(env), CI: 'true' }, shell: false, encoding: 'utf8', timeout: timeoutMs, maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] }, ports, signalCtrl);
  return finalizeGoSuiteCoverage({ proc, profileOut, args, files, modulePath, signalCtrl });
}

export function createSignalController() {
  const ctrl = {
    signal: null,
    activeChildren: new Set(),
    cleanups: new Set(),
    handlers: [],
    install() {
      if (ctrl.handlers.length > 0) return;
      for (const sig of ['SIGINT', 'SIGTERM', 'SIGHUP']) {
        const handler = () => {
          if (ctrl.signal) {
            for (const child of ctrl.activeChildren) killProcessTree(child, 'SIGKILL');
            for (const fn of ctrl.cleanups) { try { fn(); } catch {} }
            ctrl.uninstall();
            try { process.kill(process.pid, sig); } catch { process.exit(128); }
            return;
          }
          ctrl.signal = sig;
          for (const child of ctrl.activeChildren) {
            killProcessTree(child, sig);
            const t = setTimeout(() => killProcessTree(child, 'SIGKILL'), 150);
            t.unref?.();
          }
        };
        ctrl.handlers.push([sig, handler]);
        process.on(sig, handler);
      }
    },
    uninstall() {
      for (const [sig, handler] of ctrl.handlers) process.removeListener(sig, handler);
      ctrl.handlers = [];
    },
    reRaiseIfSignaled() {
      for (const fn of ctrl.cleanups) { try { fn(); } catch {} }
      ctrl.cleanups.clear();
      const sig = ctrl.signal;
      ctrl.uninstall();
      if (sig) {
        try { process.kill(process.pid, sig); } catch { process.exit(128); }
      }
    },
  };
  return ctrl;
}

export function withSignalSafeTempDir(prefix, fn) {
  const tempDir = mkdtempSync(join(tmpdir(), prefix));
  let cleaned = false;
  const cleanup = () => {
    if (cleaned) return;
    cleaned = true;
    try { rmSync(tempDir, { recursive: true, force: true }); } catch {}
  };
  process.once('exit', cleanup);
  try {
    return fn(tempDir);
  } finally {
    process.removeListener('exit', cleanup);
    cleanup();
  }
}

export async function withSignalSafeTempDirAsync(prefix, asyncFn, parentSignalCtrl = null) {
  const tempDir = mkdtempSync(join(tmpdir(), prefix));
  let cleaned = false;
  const cleanup = () => {
    if (cleaned) return;
    cleaned = true;
    try { rmSync(tempDir, { recursive: true, force: true }); } catch {}
  };
  const ownsCtrl = !parentSignalCtrl;
  const ctrl = parentSignalCtrl ?? createSignalController();
  ctrl.cleanups.add(cleanup);
  if (ownsCtrl) ctrl.install();
  try {
    return await asyncFn(tempDir, ctrl);
  } finally {
    cleanup();
    ctrl.cleanups.delete(cleanup);
    if (ownsCtrl) ctrl.reRaiseIfSignaled();
  }
}

/**
 * Collect formal-only runtime line coverage for `--mutation-check` when `--coverage` was not already run.
 */
export function collectFormalLineCoverage({ root, formalFiles = [], timeoutMs = 60_000, env = process.env } = {}, ports = {}) {
  if (!root || !Array.isArray(formalFiles) || formalFiles.length === 0) return null;
  let realRoot;
  try { realRoot = realpathSync(root); } catch { return null; }
  const first = formalFiles[0];
  return withSignalSafeTempDir('pdd-prove-fcov-', tempDir => {
    if (JS_FILE_RE.test(first)) {
      const res = runNodeSuiteCoverage({ realRoot, suiteName: 'formal', files: formalFiles, command: null, v8Dir: join(tempDir, 'v8-formal'), timeoutMs, env }, ports);
      return res.status === 'ok' ? res.files : null;
    }
    if (PY_FILE_RE.test(first)) {
      const pythonBin = resolvePythonBinary(realRoot);
      const hasCoveragePy = hasPythonModule(pythonBin, 'coverage', env);
      const hasPytestMod = hasPythonModule(pythonBin, 'pytest', env);
      const sourceDirs = existsSync(join(realRoot, 'src')) ? ['src'] : ['.'];
      const res = runPythonSuiteCoverage({ realRoot, suiteName: 'formal', files: formalFiles, command: null, tempDir, pythonBin, hasCoveragePy, hasPytestMod, sourceDirs, timeoutMs, env }, ports);
      return res.status === 'ok' ? res.files : null;
    }
    if (GO_FILE_RE.test(first)) {
      const goMod = readSafeUtf8(realRoot, 'go.mod') ?? '';
      const modulePath = /^\s*module\s+(\S+)/m.exec(goMod)?.[1] ?? '';
      const res = runGoSuiteCoverage({ realRoot, suiteName: 'formal', files: formalFiles, tempDir, modulePath, timeoutMs, env }, ports);
      return res.status === 'ok' ? res.files : null;
    }
    return null;
  });
}

export async function collectFormalLineCoverageAsync({ root, formalFiles = [], timeoutMs = 60_000, env = process.env } = {}, ports = {}, signalCtrl = null) {
  if (!root || !Array.isArray(formalFiles) || formalFiles.length === 0 || signalCtrl?.signal) return null;
  let realRoot;
  try { realRoot = realpathSync(root); } catch { return null; }
  const first = formalFiles[0];
  return withSignalSafeTempDirAsync('pdd-prove-fcov-', async (tempDir, ctrl) => {
    if (JS_FILE_RE.test(first)) {
      const res = await runNodeSuiteCoverageAsync({ realRoot, suiteName: 'formal', files: formalFiles, command: null, v8Dir: join(tempDir, 'v8-formal'), timeoutMs, env }, ports, ctrl);
      return res.status === 'ok' ? res.files : null;
    }
    if (PY_FILE_RE.test(first)) {
      const pythonBin = resolvePythonBinary(realRoot);
      const hasCoveragePy = hasPythonModule(pythonBin, 'coverage', env);
      const hasPytestMod = hasPythonModule(pythonBin, 'pytest', env);
      const sourceDirs = existsSync(join(realRoot, 'src')) ? ['src'] : ['.'];
      const res = await runPythonSuiteCoverageAsync({ realRoot, suiteName: 'formal', files: formalFiles, command: null, tempDir, pythonBin, hasCoveragePy, hasPytestMod, sourceDirs, timeoutMs, env }, ports, ctrl);
      return res.status === 'ok' ? res.files : null;
    }
    if (GO_FILE_RE.test(first)) {
      const goMod = readSafeUtf8(realRoot, 'go.mod') ?? '';
      const modulePath = /^\s*module\s+(\S+)/m.exec(goMod)?.[1] ?? '';
      const res = await runGoSuiteCoverageAsync({ realRoot, suiteName: 'formal', files: formalFiles, tempDir, modulePath, timeoutMs, env }, ports, ctrl);
      return res.status === 'ok' ? res.files : null;
    }
    return null;
  }, signalCtrl);
}

function finalizeCoverageRun({ tool, baseRef, baseSha, diffLinesByFile, rawSuites, fallbackExecutableLinesByFile, errors, notProvedReasons }) {
  for (const name of SUITE_NAMES) {
    const s = rawSuites[name];
    if (!s) continue;
    if (s.interruptedBy) notProvedReasons.push(`Coverage suite "${name}" interrupted by signal ${s.interruptedBy}.`);
    else if (s.timedOut) notProvedReasons.push(`Coverage suite "${name}" timed out; rerun with --timeout MIN.`);
    else if (s.status === 'unavailable') notProvedReasons.push(`Coverage suite "${name}" unavailable: ${s.error || 'coverage tool unavailable'}.`);
    else if (s.status === 'failed') errors.push(`Error: coverage (${name}): ${s.error || 'suite failed during coverage collection'}`);
  }
  const agg = aggregateCoverageSplit({ tool, diffLinesByFile, suites: rawSuites, fallbackExecutableLinesByFile });
  return {
    tool,
    status: agg.status,
    baseRef,
    baseSha: baseSha ?? null,
    suites: agg.suites,
    unionFormalVectors: agg.unionFormalVectors,
    files: agg.files,
    uncoveredDiffLines: agg.uncoveredDiffLines,
    errors,
    notProvedReasons,
    summary: agg.summary,
  };
}

function prepareCoverageContext({ root, baseSha, baseRef = null, touchedFiles = [], allFiles = null, testCommand = null }) {
  let realRoot;
  try { realRoot = realpathSync(root); } catch {
    return {
      earlyResult: {
        tool: null, status: 'unavailable', baseRef, baseSha: baseSha ?? null,
        suites: {}, unionFormalVectors: null, files: [], uncoveredDiffLines: [],
        errors: [], notProvedReasons: ['Coverage failed: repository root is unreadable.'],
        summary: 'Coverage: unavailable',
      },
    };
  }
  const { diffLinesByFile, fallbackExecutableLinesByFile } = collectDiffLines({ root: realRoot, baseSha, touchedFiles });
  const touchedProdFiles = Object.keys(diffLinesByFile);
  const discovered = discoverCoverageSuites({ root: realRoot, allFiles, testCommand, touchedProdFiles });
  if (discovered.language === 'unknown') {
    const agg = aggregateCoverageSplit({ tool: null, diffLinesByFile, suites: {}, fallbackExecutableLinesByFile });
    const notProvedReasons = touchedProdFiles.length > 0
      ? ['Coverage tool unavailable: could not detect a supported JS/Node, Python, or Go coverage toolchain.']
      : [];
    return {
      earlyResult: {
        tool: null, status: touchedProdFiles.length > 0 ? 'unavailable' : 'not-applicable',
        baseRef, baseSha: baseSha ?? null,
        suites: agg.suites, unionFormalVectors: agg.unionFormalVectors, files: agg.files,
        uncoveredDiffLines: agg.uncoveredDiffLines, errors: [], notProvedReasons,
        summary: touchedProdFiles.length > 0 ? 'Coverage: unavailable (no supported coverage tool)' : agg.summary,
      },
    };
  }
  return { earlyResult: null, realRoot, diffLinesByFile, fallbackExecutableLinesByFile, touchedProdFiles, discovered };
}

/**
 * Run opt-in `pdd prove --coverage`: collect per-file and diff-line coverage split across `formal`, `vectors`, and `all`.
 */
export function runProveCoverage(
  { root, baseSha, baseRef = null, touchedFiles = [], allFiles = null, testCommand = null, timeoutMs = 600_000, env = process.env } = {},
  ports = {},
) {
  const ctx = prepareCoverageContext({ root, baseSha, baseRef, touchedFiles, allFiles, testCommand });
  if (ctx.earlyResult) return ctx.earlyResult;
  const { realRoot, diffLinesByFile, fallbackExecutableLinesByFile, touchedProdFiles, discovered } = ctx;
  const errors = [];
  const notProvedReasons = [];

  return withSignalSafeTempDir('pdd-prove-cov-', tempDir => {
    let tool = null;
    const rawSuites = {};
    const runSeq = tasks => {
      for (const [name, fn] of tasks) {
        const res = fn();
        rawSuites[name] = res;
        if (res?.interruptedBy) break;
      }
    };

    if (discovered.language === 'javascript') {
      tool = 'node-v8';
      runSeq([
        ['formal', () => runNodeSuiteCoverage({ realRoot, suiteName: 'formal', files: discovered.formalFiles, command: null, v8Dir: join(tempDir, 'v8-formal'), timeoutMs, env }, ports)],
        ['vectors', () => runNodeSuiteCoverage({ realRoot, suiteName: 'vectors', files: discovered.vectorFiles, command: null, v8Dir: join(tempDir, 'v8-vectors'), timeoutMs, env }, ports)],
        ['all', () => runNodeSuiteCoverage({ realRoot, suiteName: 'all', files: [], command: discovered.testCommand, v8Dir: join(tempDir, 'v8-all'), timeoutMs, env }, ports)],
      ]);
    } else if (discovered.language === 'python') {
      const pythonBin = resolvePythonBinary(realRoot);
      const hasCoveragePy = hasPythonModule(pythonBin, 'coverage', env);
      const hasPytestMod = hasPythonModule(pythonBin, 'pytest', env);
      tool = hasCoveragePy ? 'coverage.py' : 'python-trace';
      const topDirs = [...new Set(touchedProdFiles.map(f => (f.includes('/') ? f.split('/')[0] : '.')).filter(Boolean))];
      const sourceDirs = topDirs.length > 0 ? topDirs : (existsSync(join(realRoot, 'src')) ? ['src'] : ['.']);
      runSeq([
        ['formal', () => runPythonSuiteCoverage({ realRoot, suiteName: 'formal', files: discovered.formalFiles, command: null, tempDir, pythonBin, hasCoveragePy, hasPytestMod, sourceDirs, timeoutMs, env }, ports)],
        ['vectors', () => runPythonSuiteCoverage({ realRoot, suiteName: 'vectors', files: discovered.vectorFiles, command: null, tempDir, pythonBin, hasCoveragePy, hasPytestMod, sourceDirs, timeoutMs, env }, ports)],
        ['all', () => runPythonSuiteCoverage({ realRoot, suiteName: 'all', files: [], command: discovered.testCommand, tempDir, pythonBin, hasCoveragePy, hasPytestMod, sourceDirs, timeoutMs, env }, ports)],
      ]);
    } else if (discovered.language === 'go') {
      tool = 'go-cover';
      const goMod = readSafeUtf8(realRoot, 'go.mod') ?? '';
      const modulePath = /^\s*module\s+(\S+)/m.exec(goMod)?.[1] ?? '';
      runSeq([
        ['formal', () => runGoSuiteCoverage({ realRoot, suiteName: 'formal', files: discovered.formalFiles, tempDir, modulePath, timeoutMs, env }, ports)],
        ['vectors', () => runGoSuiteCoverage({ realRoot, suiteName: 'vectors', files: discovered.vectorFiles, tempDir, modulePath, timeoutMs, env }, ports)],
        ['all', () => runGoSuiteCoverage({ realRoot, suiteName: 'all', files: [], tempDir, modulePath, timeoutMs, env }, ports)],
      ]);
    }

    return finalizeCoverageRun({ tool, baseRef, baseSha, diffLinesByFile, rawSuites, fallbackExecutableLinesByFile, errors, notProvedReasons });
  });
}

export async function runProveCoverageAsync(
  { root, baseSha, baseRef = null, touchedFiles = [], allFiles = null, testCommand = null, timeoutMs = 600_000, env = process.env } = {},
  ports = {},
  signalCtrl = null,
) {
  const ctx = prepareCoverageContext({ root, baseSha, baseRef, touchedFiles, allFiles, testCommand });
  if (ctx.earlyResult) return ctx.earlyResult;
  const { realRoot, diffLinesByFile, fallbackExecutableLinesByFile, touchedProdFiles, discovered } = ctx;
  const errors = [];
  const notProvedReasons = [];

  return withSignalSafeTempDirAsync('pdd-prove-cov-', async (tempDir, ctrl) => {
    let tool = null;
    const rawSuites = {};
    const runSeq = async tasks => {
      for (const [name, fn] of tasks) {
        if (ctrl.signal) break;
        const res = await fn(ctrl);
        rawSuites[name] = res;
        if (ctrl.signal || res?.interruptedBy) break;
      }
    };

    if (discovered.language === 'javascript') {
      tool = 'node-v8';
      await runSeq([
        ['formal', c => runNodeSuiteCoverageAsync({ realRoot, suiteName: 'formal', files: discovered.formalFiles, command: null, v8Dir: join(tempDir, 'v8-formal'), timeoutMs, env }, ports, c)],
        ['vectors', c => runNodeSuiteCoverageAsync({ realRoot, suiteName: 'vectors', files: discovered.vectorFiles, command: null, v8Dir: join(tempDir, 'v8-vectors'), timeoutMs, env }, ports, c)],
        ['all', c => runNodeSuiteCoverageAsync({ realRoot, suiteName: 'all', files: [], command: discovered.testCommand, v8Dir: join(tempDir, 'v8-all'), timeoutMs, env }, ports, c)],
      ]);
    } else if (discovered.language === 'python') {
      const pythonBin = resolvePythonBinary(realRoot);
      const hasCoveragePy = hasPythonModule(pythonBin, 'coverage', env);
      const hasPytestMod = hasPythonModule(pythonBin, 'pytest', env);
      tool = hasCoveragePy ? 'coverage.py' : 'python-trace';
      const topDirs = [...new Set(touchedProdFiles.map(f => (f.includes('/') ? f.split('/')[0] : '.')).filter(Boolean))];
      const sourceDirs = topDirs.length > 0 ? topDirs : (existsSync(join(realRoot, 'src')) ? ['src'] : ['.']);
      await runSeq([
        ['formal', c => runPythonSuiteCoverageAsync({ realRoot, suiteName: 'formal', files: discovered.formalFiles, command: null, tempDir, pythonBin, hasCoveragePy, hasPytestMod, sourceDirs, timeoutMs, env }, ports, c)],
        ['vectors', c => runPythonSuiteCoverageAsync({ realRoot, suiteName: 'vectors', files: discovered.vectorFiles, command: null, tempDir, pythonBin, hasCoveragePy, hasPytestMod, sourceDirs, timeoutMs, env }, ports, c)],
        ['all', c => runPythonSuiteCoverageAsync({ realRoot, suiteName: 'all', files: [], command: discovered.testCommand, tempDir, pythonBin, hasCoveragePy, hasPytestMod, sourceDirs, timeoutMs, env }, ports, c)],
      ]);
    } else if (discovered.language === 'go') {
      tool = 'go-cover';
      const goMod = readSafeUtf8(realRoot, 'go.mod') ?? '';
      const modulePath = /^\s*module\s+(\S+)/m.exec(goMod)?.[1] ?? '';
      await runSeq([
        ['formal', c => runGoSuiteCoverageAsync({ realRoot, suiteName: 'formal', files: discovered.formalFiles, tempDir, modulePath, timeoutMs, env }, ports, c)],
        ['vectors', c => runGoSuiteCoverageAsync({ realRoot, suiteName: 'vectors', files: discovered.vectorFiles, tempDir, modulePath, timeoutMs, env }, ports, c)],
        ['all', c => runGoSuiteCoverageAsync({ realRoot, suiteName: 'all', files: [], tempDir, modulePath, timeoutMs, env }, ports, c)],
      ]);
    }

    return finalizeCoverageRun({ tool, baseRef, baseSha, diffLinesByFile, rawSuites, fallbackExecutableLinesByFile, errors, notProvedReasons });
  }, signalCtrl);
}
