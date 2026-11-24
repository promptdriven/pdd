// Prompt: prompts/cli/formal-verify.prompt.md

// Layer-1 pluggable multi-language test runner registry (#3561, #3151):
// auto-detection, invocation builders, strict summary parsing, and canonical test-case extraction for
// node:test (TAP v13), vitest (JUnit XML / verbose CLI), pytest (JUnit XML / verbose CLI), cargo test, and go test -json.
import { spawnSync } from 'node:child_process';
import { existsSync, lstatSync, readdirSync } from 'node:fs';
import { basename, delimiter, dirname, join } from 'node:path';
import { readBoundedUtf8 } from '../shared/safe-read.mjs';

export const TEST_RUNNER_KINDS = Object.freeze(['node:test', 'vitest', 'pytest', 'cargo', 'go']);
const stripAnsi = text => String(text ?? '').replace(/\x1b\[[0-9;?]*[ -/]*[@-~]/g, '');

export function normalizeRunnerKind(kind) {
  if (!kind) return null;
  const k = String(kind).trim().toLowerCase();
  if (['node:test', 'node', 'node-test', 'node-tap', 'tap'].includes(k)) return 'node:test';
  if (k === 'vitest') return 'vitest';
  if (k === 'jest') return 'jest';
  if (['pytest', 'python'].includes(k)) return 'pytest';
  if (['cargo', 'cargo test', 'cargo-test', 'rust'].includes(k)) return 'cargo';
  if (['go', 'go test', 'go-test', 'go-json', 'go test -json'].includes(k)) return 'go';
  if (['junit', 'junit-xml', 'xml'].includes(k)) return 'junit';
  return null;
}

/**
 * Resolve repo-local `.venv/bin/pytest` (or `venv/bin/pytest`) when present as a regular untracked file inside `root`,
 * else fall back to `'pytest'`. Rejects symlinked venv directories and git-tracked `.venv`/`venv` executables
 * so an untrusted PR can never achieve pre-review RCE by committing `.venv/bin/pytest`.
 */
export function resolvePytestBinary(root) {
  if (typeof root !== 'string' || !root.trim()) return 'pytest';
  const inGitRepo = existsSync(join(root, '.git'));
  for (const venvDir of ['.venv', 'venv']) {
    const dirPath = join(root, venvDir);
    const binDir = join(dirPath, 'bin');
    const candidate = join(binDir, 'pytest');
    try {
      const dst = lstatSync(dirPath);
      if (dst.isSymbolicLink() || !dst.isDirectory()) continue;
      const bst = lstatSync(binDir);
      if (bst.isSymbolicLink() || !bst.isDirectory()) continue;
      const fst = lstatSync(candidate);
      if (!fst.isFile() || fst.isSymbolicLink()) continue;
      if (inGitRepo) {
        const rel = `${venvDir}/bin/pytest`;
        const tracked = spawnSync('git', ['ls-files', '--error-unmatch', '--', rel], {
          cwd: root,
          stdio: ['ignore', 'ignore', 'ignore'],
          timeout: 5000,
        });
        // status === 1 confirms the file is NOT git-tracked; status === 0 (tracked) or any other error fails closed.
        if (tracked.status !== 1) continue;
      }
      return candidate;
    } catch {
      // absent or unreadable
    }
  }
  return 'pytest';
}

/**
 * Build runner-specific child environment additions (e.g., prepending `src` to `PYTHONPATH` for Python repos).
 */
export function buildRunnerEnv(kind, root, baseEnv = process.env) {
  const env = { ...(baseEnv ?? {}) };
  if (normalizeRunnerKind(kind) === 'pytest') {
    env.PYTHONDONTWRITEBYTECODE = '1';
    if (typeof root === 'string' && root.trim()) {
      const srcDir = join(root, 'src');
      try {
        const st = lstatSync(srcDir);
        if (st.isDirectory() && !st.isSymbolicLink()) {
          const cur = typeof env.PYTHONPATH === 'string' && env.PYTHONPATH.trim() ? env.PYTHONPATH.trim() : '';
          const parts = cur ? cur.split(delimiter).filter(Boolean) : [];
          if (!parts.includes('src') && !parts.includes(srcDir)) {
            env.PYTHONPATH = cur ? `src${delimiter}${cur}` : 'src';
          }
        }
      } catch {
        // no src/ dir
      }
    }
  }
  return env;
}

/**
 * Build deterministic `{ bin, args, reportFormat, junitPath }` invocation for a runner kind and target file list.
 */
export function buildRunnerInvocation(kind, { root = null, files = [], junitPath = null, pytestBin = null } = {}) {
  const norm = normalizeRunnerKind(kind);
  const list = Array.isArray(files) ? files.filter(f => typeof f === 'string' && f.trim()) : [];
  const safeOperands = list.map(f => (f.startsWith('-') ? `./${f}` : f));
  if (norm === 'pytest') {
    const bin = pytestBin || resolvePytestBinary(root);
    const args = ['-v', ...(junitPath ? [`--junitxml=${junitPath}`] : []), ...(safeOperands.length ? ['--', ...safeOperands] : [])];
    return { kind: 'pytest', bin, args, reportFormat: junitPath ? 'junit' : 'pytest', junitPath: junitPath ?? null };
  }
  if (norm === 'vitest') {
    const args = junitPath
      ? ['--no-install', 'vitest', 'run', '--reporter=junit', `--outputFile=${junitPath}`, ...(safeOperands.length ? ['--', ...safeOperands] : [])]
      : ['--no-install', 'vitest', 'run', '--reporter=verbose', ...(safeOperands.length ? ['--', ...safeOperands] : [])];
    return { kind: 'vitest', bin: 'npx', args, reportFormat: junitPath ? 'junit' : 'vitest', junitPath: junitPath ?? null };
  }
  if (norm === 'jest') {
    const args = ['--no-install', 'jest', '--verbose', ...(safeOperands.length ? ['--', ...safeOperands] : [])];
    return { kind: 'jest', bin: 'npx', args, reportFormat: 'jest', junitPath: null };
  }
  if (norm === 'go') {
    const pkgs = list.length
      ? [...new Set(list.map(f => { const d = dirname(f); return d === '.' ? './.' : `./${d}`; }))]
      : ['./...'];
    return { kind: 'go', bin: 'go', args: ['test', '-json', ...pkgs], reportFormat: 'go-json', junitPath: null };
  }
  if (norm === 'cargo') {
    const integrationTargets = list
      .filter(f => /(?:^|\/)tests\/[^/]+\.rs$/i.test(f))
      .map(f => basename(f, '.rs'));
    const args = integrationTargets.length
      ? ['test', ...integrationTargets.flatMap(t => ['--test', t])]
      : ['test'];
    return { kind: 'cargo', bin: 'cargo', args, reportFormat: 'cargo', junitPath: null };
  }
  // Single-file node:test executes directly without `--test` glob expansion, eliminating `[glob]`/`{a,b}`/`-flag` hazards.
  if (safeOperands.length === 1) {
    const singleTarget = root ? join(root, list[0]) : safeOperands[0];
    return {
      kind: 'node:test',
      bin: process.execPath,
      args: ['--test-reporter=tap', '--', singleTarget],
      reportFormat: 'tap',
      junitPath: null,
    };
  }
  return {
    kind: 'node:test',
    bin: process.execPath,
    args: ['--test', '--test-reporter=tap', ...(safeOperands.length ? ['--', ...safeOperands] : [])],
    reportFormat: 'tap',
    junitPath: null,
  };
}

function decodeXmlEntities(text) {
  const named = { lt: '<', gt: '>', amp: '&', quot: '"', apos: "'" };
  return String(text ?? '').replace(/&(#x[0-9a-fA-F]+|#\d+|lt|gt|amp|quot|apos);/g, (full, ent) => {
    if (Object.hasOwn(named, ent)) return named[ent];
    const code = ent.startsWith('#x') ? Number.parseInt(ent.slice(2), 16) : Number.parseInt(ent.slice(1), 10);
    return Number.isInteger(code) && code >= 0 && code <= 0x10ffff ? String.fromCodePoint(code) : full;
  });
}

function parseXmlAttrs(raw) {
  const attrs = {}, s = String(raw ?? '');
  let i = 0;
  while (i < s.length) {
    while (i < s.length && /\s/.test(s[i])) i += 1;
    if (i >= s.length) break;
    const start = i;
    while (i < s.length && /[A-Za-z0-9_.:-]/.test(s[i])) i += 1;
    const name = s.slice(start, i);
    while (i < s.length && /\s/.test(s[i])) i += 1;
    if (!name || s[i] !== '=') return null;
    i += 1;
    while (i < s.length && /\s/.test(s[i])) i += 1;
    const quote = s[i];
    if (quote !== '"' && quote !== "'") return null;
    const valStart = ++i;
    while (i < s.length && s[i] !== quote) i += 1;
    if (i >= s.length) return null;
    attrs[name] = decodeXmlEntities(s.slice(valStart, i));
    i += 1;
  }
  return attrs;
}

export function parseJunitXml(xmlText) {
  const src = String(xmlText ?? '').trim();
  const bad = reason => ({ ok: false, complete: false, format: 'junit', cases: [], counts: null, reason });
  if (!src || !src.startsWith('<')) return bad('malformed_xml');

  const stack = [], cases = [];
  const skipDelims = [['<!--', '-->', 'unclosed_comment'], ['<![CDATA[', ']]>', 'unclosed_cdata'], ['<?', '?>', 'unclosed_pi']];
  let i = 0, seenRoot = false, activeCase = null;
  const currentSuitePrefix = () => stack.filter(n => n.tag === 'testsuite' && n.name).map(n => n.name).join('::');
  const nearestSuite = () => { for (let k = stack.length - 1; k >= 0; k -= 1) if (stack[k].tag === 'testsuite' || stack[k].tag === 'testsuites') return stack[k]; return null; };
  const recordStatusOnSuite = status => { const s = nearestSuite(); if (s) { if (status === 'error') s.seenErrors += 1; else if (status === 'fail') s.seenFailures += 1; } };
  const pushCase = c => {
    const prefix = c.classname || currentSuitePrefix();
    cases.push({ id: prefix ? `${prefix}::${c.name}` : c.name, status: c.status, durationMs: c.durationMs });
    recordStatusOnSuite(c.status);
  };
  const checkSuiteClosure = (top, suitePrefix) => {
    if (top.attrErrors > top.seenErrors) { cases.push({ id: `${suitePrefix || top.tag}::<suite-error-count>`, status: 'error', durationMs: null }); top.seenErrors = top.attrErrors; }
    if (top.attrFailures > top.seenFailures) { cases.push({ id: `${suitePrefix || top.tag}::<suite-failure-count>`, status: 'fail', durationMs: null }); top.seenFailures = top.attrFailures; }
    const parent = nearestSuite();
    if (parent) { parent.seenErrors += top.seenErrors; parent.seenFailures += top.seenFailures; }
  };

  while (i < src.length) {
    const lt = src.indexOf('<', i);
    if (lt < 0) { if (src.slice(i).trim()) return bad('trailing_xml_text'); break; }
    const special = skipDelims.find(([open]) => src.startsWith(open, lt));
    if (special) {
      const end = src.indexOf(special[1], lt + special[0].length);
      if (end < 0) return bad(special[2]);
      i = end + special[1].length; continue;
    }
    if (src.startsWith('<!DOCTYPE', lt)) {
      const end = src.indexOf('>', lt + 9);
      if (end < 0) return bad('unclosed_doctype');
      if (src.slice(lt, end).includes('[') || /<!ENTITY\b/i.test(src.slice(lt, end))) return bad('unsafe_xml_doctype');
      i = end + 1; continue;
    }
    let j = lt + 1, quote = null;
    while (j < src.length && (quote || src[j] !== '>')) {
      if (quote) { if (src[j] === quote) quote = null; }
      else if (src[j] === '"' || src[j] === "'") quote = src[j];
      j += 1;
    }
    if (j >= src.length) return bad('unclosed_tag');
    const rawTag = src.slice(lt + 1, j).trim();
    i = j + 1;
    if (!rawTag) return bad('empty_tag');
    if (rawTag.startsWith('/')) {
      const closeName = rawTag.slice(1).trim().toLowerCase();
      const prefixBeforePop = currentSuitePrefix();
      const top = stack.pop();
      if (!top || top.tag !== closeName) return bad('mismatched_closing_tag');
      if (closeName === 'testcase' && activeCase) { pushCase(activeCase); activeCase = null; }
      else if (closeName === 'testsuite' || closeName === 'testsuites') checkSuiteClosure(top, prefixBeforePop);
      continue;
    }
    const selfClosing = rawTag.endsWith('/');
    const body = selfClosing ? rawTag.slice(0, -1).trim() : rawTag;
    const sp = body.search(/\s/), tag = (sp < 0 ? body : body.slice(0, sp)).toLowerCase();
    if (!/^[a-z_][a-z0-9_.:-]*$/.test(tag)) return bad('invalid_tag_name');
    const attrs = sp < 0 ? {} : parseXmlAttrs(body.slice(sp + 1));
    if (!attrs) return bad('malformed_attributes');
    if (tag === 'testsuites' || tag === 'testsuite') seenRoot = true;
    if (tag === 'testcase') {
      const t = attrs.time !== undefined && attrs.time !== '' ? Number(attrs.time) : NaN;
      const entry = { classname: String(attrs.classname ?? '').trim(), name: String(attrs.name ?? '').trim() || `testcase_${cases.length + 1}`, status: 'pass', durationMs: Number.isFinite(t) && t >= 0 ? Math.round(t * 1000) : null };
      if (selfClosing) pushCase(entry); else { activeCase = entry; stack.push({ tag, name: entry.name }); }
      continue;
    }
    if (activeCase) {
      if (tag === 'error') activeCase.status = 'error';
      else if (tag === 'failure' && activeCase.status !== 'error') activeCase.status = 'fail';
      else if (tag === 'skipped' && activeCase.status === 'pass') activeCase.status = 'skip';
    } else if ((tag === 'error' || tag === 'failure') && (stack.at(-1)?.tag === 'testsuite' || stack.at(-1)?.tag === 'testsuites')) {
      const status = tag === 'error' ? 'error' : 'fail';
      cases.push({ id: `${currentSuitePrefix() || stack.at(-1).tag}::<suite-${tag}>`, status, durationMs: null });
      recordStatusOnSuite(status);
    }
    const isSuiteTag = tag === 'testsuite' || tag === 'testsuites';
    const frame = isSuiteTag
      ? { tag, name: String(attrs.name ?? '').trim(), attrErrors: Math.max(0, Number(attrs.errors ?? 0) || 0), attrFailures: Math.max(0, Number(attrs.failures ?? 0) || 0), seenErrors: 0, seenFailures: 0 }
      : { tag, name: String(attrs.name ?? '').trim() };
    if (selfClosing) { if (isSuiteTag) checkSuiteClosure(frame, [currentSuitePrefix(), frame.name].filter(Boolean).join('::')); }
    else stack.push(frame);
  }
  if (stack.length > 0 || !seenRoot) return bad(stack.length > 0 ? 'unclosed_element' : 'missing_junit_root');
  const passed = cases.filter(c => c.status === 'pass').length;
  const failed = cases.filter(c => c.status === 'fail' || c.status === 'error').length;
  const skipped = cases.filter(c => c.status === 'skip').length;
  return { ok: true, complete: true, format: 'junit', cases, counts: { total: cases.length, passed, failed, skipped, format: 'junit' }, reason: null };
}

export function parseTapReport(rawText) {
  const clean = stripAnsi(rawText);
  const bad = reason => ({ ok: false, complete: false, format: 'tap', cases: [], counts: null, reason });
  if (!clean.trim()) return bad('empty_tap');
  const lines = clean.split(/\r?\n/), keys = ['tests', 'suites', 'pass', 'fail', 'cancelled', 'skipped', 'todo'];
  let tap = false, planCount = null, summary = {}, completeSummary = null, bailout = false;
  const events = [], subtestStack = [];
  for (let idx = 0; idx < lines.length; idx += 1) {
    const line = lines[idx];
    if (/^TAP version 13\s*$/.test(line)) { tap = true; planCount = null; summary = {}; completeSummary = null; continue; }
    if (/^\s*Bail out!/i.test(line)) { bailout = true; break; }
    const planM = /^1\.\.(\d+)(?:\s+#.*)?$/.exec(line);
    if (planM) { planCount = Number(planM[1]); summary = {}; completeSummary = null; continue; }
    const subM = /^(\s*)# Subtest:\s*(.+?)\s*$/.exec(line);
    if (subM) {
      const indent = subM[1].length;
      while (subtestStack.length && subtestStack.at(-1).indent >= indent) subtestStack.pop();
      subtestStack.push({ indent, name: subM[2] }); continue;
    }
    const testM = /^(\s*)(not )?ok(?:\s+(\d+))?(?:\s+-\s+|\s+)?(.*)$/.exec(line);
    if (testM) {
      const indent = testM[1].length, rest = (testM[4] ?? '').trim();
      const dirM = /^(.*?)\s+#\s*(SKIP|TODO)\b.*$/i.exec(rest);
      const name = (dirM ? dirM[1] : rest).trim() || `test_${testM[3] ?? events.length + 1}`;
      const status = dirM ? 'skip' : (testM[2] ? 'fail' : 'pass');
      let durationMs = null, isSuite = false;
      if (/^\s*---\s*$/.test(lines[idx + 1] ?? '')) {
        idx += 2;
        while (idx < lines.length && !/^\s*\.\.\.\s*$/.test(lines[idx])) {
          const dm = /^\s*duration_ms:\s*([0-9]+(?:\.[0-9]+)?)\s*$/.exec(lines[idx]);
          if (dm) durationMs = Number(dm[1]);
          if (/^\s*type:\s*['"]?suite['"]?\s*$/.test(lines[idx])) isSuite = true;
          idx += 1;
        }
      }
      while (subtestStack.length && subtestStack.at(-1).indent >= indent) subtestStack.pop();
      events.push({ indent, name, ancestors: subtestStack.map(s => s.name), status, durationMs, isSuite });
      if (indent === 0) { summary = {}; completeSummary = null; }
      continue;
    }
    const sumM = /^# (tests|suites|pass|fail|cancelled|skipped|todo) (\d+)\s*$/.exec(line);
    if (sumM && Number.isSafeInteger(Number(sumM[2]))) {
      if (sumM[1] === 'tests') { summary = {}; completeSummary = null; }
      if (sumM[1] !== keys[Object.keys(summary).length]) { summary = {}; completeSummary = null; }
      else { summary[sumM[1]] = Number(sumM[2]); if (tap && planCount !== null && keys.every(k => summary[k] !== undefined)) completeSummary = { ...summary }; }
      continue;
    }
    if (!/^# duration_ms \d+(?:\.\d+)?\s*$/.test(line) && !/^\s*1\.\.\d+/.test(line) && line.trim()) { summary = {}; completeSummary = null; }
  }
  if (bailout) return bad('tap_bailout');
  const leafCases = [];
  for (let k = 0; k < events.length; k += 1) {
    const ev = events[k];
    const hasChildren = k > 0 && events[k - 1].indent > ev.indent;
    const id = ev.ancestors.length ? `${ev.ancestors.join(' > ')} > ${ev.name}` : ev.name;
    if (ev.isSuite || hasChildren) {
      if (ev.status === 'fail') {
        let childFailed = false;
        for (let p = k - 1; p >= 0 && events[p].indent > ev.indent; p -= 1) if (events[p].status === 'fail') { childFailed = true; break; }
        if (!childFailed) leafCases.push({ id: `${id}::<suite-hook>`, status: 'fail', durationMs: ev.durationMs });
      }
      continue;
    }
    leafCases.push({ id, status: ev.status, durationMs: ev.durationMs });
  }
  const topCount = events.filter(e => e.indent === 0).length;
  const complete = Boolean(tap && planCount !== null && (completeSummary !== null || (planCount > 0 && topCount === planCount)));
  if (!complete || (topCount > 0 && topCount !== planCount)) return bad('incomplete_tap');
  const counts = completeSummary
    ? { total: completeSummary.tests, passed: completeSummary.pass, failed: completeSummary.fail + completeSummary.cancelled, skipped: completeSummary.skipped + completeSummary.todo, format: 'tap' }
    : { total: leafCases.length, passed: leafCases.filter(c => c.status === 'pass').length, failed: leafCases.filter(c => c.status === 'fail').length, skipped: leafCases.filter(c => c.status === 'skip').length, format: 'tap' };
  const parsedFailCount = leafCases.filter(c => c.status === 'fail' || c.status === 'error').length;
  if (counts.failed > parsedFailCount) leafCases.push({ id: '<tap-summary-failure>', status: 'fail', durationMs: null });
  return { ok: true, complete: true, format: 'tap', cases: leafCases, counts, reason: null };
}

export function parseGoJsonReport(rawText) {
  const lines = stripAnsi(rawText).split(/\r?\n/).map(l => l.trim()).filter(Boolean);
  const bad = reason => ({ ok: false, complete: false, format: 'go-json', cases: [], counts: null, reason });
  if (!lines.length) return bad('empty_go_json');
  const running = new Set(), finished = new Map(), pkgEvents = new Map(), pkgHasFailedTest = new Set();
  const startedPackages = new Set(), finishedPackages = new Set();
  for (const line of lines) {
    if (!line.startsWith('{')) return bad('malformed_go_json');
    let ev;
    try { ev = JSON.parse(line); } catch { return bad('malformed_go_json'); }
    if (!ev || typeof ev !== 'object' || typeof ev.Action !== 'string') return bad('malformed_go_json');
    const pkg = String(ev.Package ?? ''), testName = typeof ev.Test === 'string' && ev.Test ? ev.Test : null;
    const durationMs = typeof ev.Elapsed === 'number' && Number.isFinite(ev.Elapsed) ? Math.round(ev.Elapsed * 1000) : null;
    if (pkg) startedPackages.add(pkg);
    if (testName) {
      const id = pkg ? `${pkg}::${testName}` : testName;
      if (ev.Action === 'run') running.add(id);
      else if (['pass', 'fail', 'skip'].includes(ev.Action)) {
        running.delete(id); finished.set(id, { id, status: ev.Action, durationMs });
        if (ev.Action === 'fail') pkgHasFailedTest.add(pkg);
      }
    } else if (['pass', 'fail', 'skip', 'build-fail'].includes(ev.Action)) {
      pkgEvents.set(pkg, { action: ev.Action, durationMs });
      if (pkg) finishedPackages.add(pkg);
    }
  }
  if (running.size > 0) return bad('incomplete_go_test_run');
  for (const pkg of startedPackages) if (!finishedPackages.has(pkg)) return bad('incomplete_go_package_run');
  const cases = [...finished.values()];
  for (const [pkg, info] of pkgEvents.entries()) {
    if (info.action === 'build-fail') cases.push({ id: `${pkg || 'package'}::<build>`, status: 'error', durationMs: info.durationMs });
    else if (info.action === 'fail' && !pkgHasFailedTest.has(pkg)) cases.push({ id: `${pkg || 'package'}::<package>`, status: 'fail', durationMs: info.durationMs });
  }
  const passed = cases.filter(c => c.status === 'pass').length;
  const failed = cases.filter(c => c.status === 'fail' || c.status === 'error').length;
  const skipped = cases.filter(c => c.status === 'skip').length;
  return { ok: true, complete: true, format: 'go-json', cases, counts: { total: cases.length, passed, failed, skipped, format: 'go-json' }, reason: null };
}

export function parseCargoReport(rawText, { requireRunningHeader = false } = {}) {
  const clean = stripAnsi(rawText);
  const bad = reason => ({ ok: false, complete: false, format: 'cargo', cases: [], counts: null, reason });
  const runningCount = [...clean.matchAll(/^running\s+(\d+)\s+tests?\s*$/gm)].length;
  const results = [...clean.matchAll(/^test result:\s+(ok|FAILED)\.\s+(\d+)\s+passed;\s+(\d+)\s+failed;\s+(\d+)\s+ignored;\s+(\d+)\s+measured;\s+(\d+)\s+filtered out/gm)];
  if (!results.length || (requireRunningHeader && runningCount !== results.length)) return bad('missing_cargo_summary');
  if (runningCount > results.length) return bad('incomplete_cargo_run');
  let passed = 0, failed = 0, skipped = 0;
  for (const m of results) { passed += Number(m[2]); failed += Number(m[3]); skipped += Number(m[4]); }
  const cases = [...clean.matchAll(/^test\s+(.+?)\s+\.\.\.\s+(ok|FAILED|ignored)(?:,|\s|$)/gm)].map(m => ({
    id: m[1].trim(), status: m[2] === 'ok' ? 'pass' : (m[2] === 'FAILED' ? 'fail' : 'skip'), durationMs: null,
  }));
  return { ok: true, complete: true, format: 'cargo', cases, counts: { total: passed + failed + skipped, passed, failed, skipped, format: 'cargo' }, reason: null };
}

function parseVitestSummary(rawText, explicit = false) {
  const clean = stripAnsi(rawText);
  if (!explicit && !/^\s*(?:Test Files|Duration)\s+/m.test(clean)) return null;
  const lines = [...clean.matchAll(/^\s*Tests\s+(.+?)\s*\((\d+)\)\s*$/gm)];
  if (!lines.length) return null;
  const body = lines.at(-1)[1], reportedTotal = Number(lines.at(-1)[2]);
  if (!/\b(?:passed|failed|skipped|todo)\b/i.test(body)) return null;
  const read = label => Number(new RegExp(`\\b(\\d+)\\s+${label}\\b`, 'i').exec(body)?.[1] ?? 0);
  const passed = read('passed'), failed = read('failed'), skipped = read('skipped') + read('todo');
  return { total: Math.max(reportedTotal, passed + failed + skipped), passed, failed, skipped, format: 'vitest' };
}

function parseJestSummary(rawText, explicit = false) {
  const clean = stripAnsi(rawText);
  if (!explicit && !/^\s*Test Suites:\s+/m.test(clean)) return null;
  const lines = [...clean.matchAll(/^\s*Tests:\s+(.+?),\s*(\d+)\s+total\s*$/gm)];
  if (!lines.length) return null;
  const body = lines.at(-1)[1], reportedTotal = Number(lines.at(-1)[2]);
  const read = label => Number(new RegExp(`\\b(\\d+)\\s+${label}\\b`, 'i').exec(body)?.[1] ?? 0);
  const passed = read('passed'), failed = read('failed'), skipped = read('skipped') + read('todo') + read('pending');
  return { total: Math.max(reportedTotal, passed + failed + skipped), passed, failed, skipped, format: 'jest' };
}

function parsePytestSummary(rawText, explicit = false) {
  const clean = stripAnsi(rawText);
  const pat = explicit
    ? /(?:^|={2,}\s*)((?:\d+\s+(?:passed|failed|errors?|skipped|xfailed|xpassed|deselected|warnings?)(?:,\s*)?)+|no tests ran)\s+in\s+[0-9.]+s(?:\s*\([^)\r\n]+\))?(?:\s*={2,}|\s*$)/gim
    : /^={2,}\s*((?:\d+\s+(?:passed|failed|errors?|skipped|xfailed|xpassed|deselected|warnings?)(?:,\s*)?)+|no tests ran)\s+in\s+[0-9.]+s(?:\s*\([^)\r\n]+\))?\s*={2,}\s*$/gim;
  const matches = [...clean.matchAll(pat)];
  if (!matches.length) return null;
  const body = matches.at(-1)[1].toLowerCase();
  if (body.includes('no tests ran')) return { total: 0, passed: 0, failed: 0, skipped: 0, format: 'pytest' };
  const read = re => Number(re.exec(body)?.[1] ?? 0);
  const passed = read(/\b(\d+)\s+passed\b/) + read(/\b(\d+)\s+xpassed\b/);
  const failed = read(/\b(\d+)\s+failed\b/) + read(/\b(\d+)\s+errors?\b/);
  const skipped = read(/\b(\d+)\s+skipped\b/) + read(/\b(\d+)\s+xfailed\b/);
  return { total: passed + failed + skipped, passed, failed, skipped, format: 'pytest' };
}

export function parsePytestVerboseReport(rawText) {
  const clean = stripAnsi(rawText);
  const counts = parsePytestSummary(clean, true);
  if (!counts) return { ok: false, complete: false, format: 'pytest', cases: [], counts: null, reason: 'missing_pytest_summary' };
  const cases = [...clean.matchAll(/^(\S+::[^\r\n]+?)\s+(PASSED|FAILED|SKIPPED|ERROR|XFAIL|XPASS)(?:\s+\[\s*\d+%\s*\])?\s*$/gm)].map(m => ({
    id: m[1].trim(), status: m[2] === 'PASSED' || m[2] === 'XPASS' ? 'pass' : (m[2] === 'FAILED' ? 'fail' : (m[2] === 'ERROR' ? 'error' : 'skip')), durationMs: null,
  }));
  if (counts.total > 0 && cases.length === 0) {
    return { ok: false, complete: false, format: 'pytest', cases: [], counts, reason: 'missing_pytest_verbose_cases' };
  }
  return { ok: true, complete: true, format: 'pytest', cases, counts, reason: null };
}

export function parseVitestVerboseReport(rawText) {
  const clean = stripAnsi(rawText);
  const counts = parseVitestSummary(clean, true);
  if (!counts) return { ok: false, complete: false, format: 'vitest', cases: [], counts: null, reason: 'missing_vitest_summary' };
  const cases = [...clean.matchAll(/^\s*([✓✔×✕↓])\s+(.+?)(?:\s+(\d+)\s*ms)?\s*$/gm)]
    .filter(m => !/\(\d+\s+tests?\b/i.test(m[2]))
    .map(m => ({
      id: m[2].trim(), status: m[1] === '✓' || m[1] === '✔' ? 'pass' : (m[1] === '↓' ? 'skip' : 'fail'), durationMs: m[3] ? Number(m[3]) : null,
    }));
  if (counts.total > 0 && cases.length === 0) {
    return { ok: false, complete: false, format: 'vitest', cases: [], counts, reason: 'missing_vitest_verbose_cases' };
  }
  return { ok: true, complete: true, format: 'vitest', cases, counts, reason: null };
}

export function detectTestRunner(root = null, packageJsonOrFiles = null) {
  let files = null, pkg = null, pyprojectText = null;
  if (Array.isArray(packageJsonOrFiles)) files = packageJsonOrFiles.map(String);
  else if (packageJsonOrFiles && typeof packageJsonOrFiles === 'object') {
    if (Array.isArray(packageJsonOrFiles.files) || packageJsonOrFiles.packageJson || packageJsonOrFiles.pyprojectText) {
      files = packageJsonOrFiles.files ? packageJsonOrFiles.files.map(String) : null;
      pkg = packageJsonOrFiles.packageJson ?? null; pyprojectText = packageJsonOrFiles.pyprojectText ?? null;
    } else pkg = packageJsonOrFiles;
  }
  const hasFile = name => (files ? files.includes(name) : (root ? existsSync(join(root, name)) : false));
  const anyFile = re => (files ? files.some(f => re.test(f)) : (root && existsSync(root) ? readdirSync(root).some(f => re.test(f)) : false));
  if (!pkg && root && existsSync(join(root, 'package.json'))) { try { pkg = JSON.parse(readBoundedUtf8(join(root, 'package.json'), { maxBytes: 262_144, noFollow: true })); } catch {} }
  if (pyprojectText === null && root && existsSync(join(root, 'pyproject.toml'))) { try { pyprojectText = readBoundedUtf8(join(root, 'pyproject.toml'), { maxBytes: 262_144, noFollow: true }); } catch {} }
  const testScript = String(pkg?.scripts?.test ?? ''), allDeps = { ...(pkg?.dependencies ?? {}), ...(pkg?.devDependencies ?? {}) };
  if (/\bvitest\b/i.test(testScript) || Object.hasOwn(allDeps, 'vitest') || anyFile(/^vitest\.config\.(?:[cm]?[jt]s)$/i)) return { kind: 'vitest', command: 'npx vitest run', reportFormat: 'junit', detectedBy: 'vitest' };
  if (/\bnode\b.*--test\b/.test(testScript)) return { kind: 'node:test', command: 'node --test', reportFormat: 'tap', detectedBy: 'package.json:scripts.test' };
  if (hasFile('Cargo.toml')) return { kind: 'cargo', command: 'cargo test', reportFormat: 'cargo', detectedBy: 'Cargo.toml' };
  if (hasFile('go.mod')) return { kind: 'go', command: 'go test -json ./...', reportFormat: 'go-json', detectedBy: 'go.mod' };
  if (hasFile('pytest.ini') || hasFile('conftest.py') || (typeof pyprojectText === 'string' && /\bpytest\b/i.test(pyprojectText)) || anyFile(/(?:^|\/)(?:test_[^/]+\.py|[^/]+_test\.py)$/i)) return { kind: 'pytest', command: 'pytest', reportFormat: 'junit', detectedBy: 'pytest' };
  if (pkg || hasFile('package.json') || anyFile(/\.test\.[cm]?js$/i)) return { kind: 'node:test', command: 'node --test', reportFormat: 'tap', detectedBy: 'package.json' };
  return null;
}

export function parseTestSummaryOutput(output, runnerKind = null) {
  const raw = String(output ?? '');
  if (!raw.trim()) return null;
  const kind = normalizeRunnerKind(runnerKind);
  if (kind === 'junit' || (!kind && /^\s*<(?:\?xml|testsuites?|testsuite)\b/.test(raw))) { const r = parseJunitXml(raw); return r.ok ? r.counts : null; }
  if (kind === 'node:test') { const r = parseTapReport(raw); return r.ok ? r.counts : null; }
  if (kind === 'go') { const r = parseGoJsonReport(raw); return r.ok ? r.counts : null; }
  if (kind === 'cargo') { const r = parseCargoReport(raw); return r.ok ? r.counts : null; }
  if (kind === 'vitest') return /^\s*<(?:\?xml|testsuites?|testsuite)\b/.test(raw) ? (parseJunitXml(raw).counts ?? null) : parseVitestSummary(raw, true);
  if (kind === 'jest') return parseJestSummary(raw, true);
  if (kind === 'pytest') return /^\s*<(?:\?xml|testsuites?|testsuite)\b/.test(raw) ? (parseJunitXml(raw).counts ?? null) : parsePytestSummary(raw, true);
  if (/^TAP version 13\b/m.test(raw)) { const r = parseTapReport(raw); return r.ok ? r.counts : null; }
  if (/^\s*\{.*"Action"\s*:/.test(raw)) { const r = parseGoJsonReport(raw); return r.ok ? r.counts : null; }
  const cargo = parseCargoReport(raw, { requireRunningHeader: true });
  if (cargo.ok) return cargo.counts;
  return parseVitestSummary(raw, false) ?? parseJestSummary(raw, false) ?? parsePytestSummary(raw, false);
}

export function extractTestCases(rawOutputOrReport, format = 'auto') {
  const raw = String(rawOutputOrReport ?? '');
  if (!raw.trim()) return [];
  const kind = format === 'auto' ? null : normalizeRunnerKind(format);
  if (kind === 'junit' || (!kind && /^\s*<(?:\?xml|testsuites?|testsuite)\b/.test(raw)) || ((kind === 'vitest' || kind === 'pytest') && /^\s*<(?:\?xml|testsuites?|testsuite)\b/.test(raw))) return parseJunitXml(raw).cases;
  if (kind === 'node:test' || (!kind && /^TAP version 13\b/m.test(raw))) return parseTapReport(raw).cases;
  if (kind === 'go' || (!kind && /^\s*\{.*"Action"\s*:/.test(raw))) return parseGoJsonReport(raw).cases;
  if (kind === 'cargo' || (!kind && /^test result:/m.test(raw))) return parseCargoReport(raw).cases;
  const clean = stripAnsi(raw);
  if (kind === 'pytest' || (!kind && /\b(?:PASSED|FAILED|SKIPPED|ERROR|XFAIL|XPASS)\b/.test(clean))) {
    return [...clean.matchAll(/^(\S+::[^\r\n]+?)\s+(PASSED|FAILED|SKIPPED|ERROR|XFAIL|XPASS)(?:\s+\[\s*\d+%\s*\])?\s*$/gm)].map(m => ({
      id: m[1].trim(), status: m[2] === 'PASSED' || m[2] === 'XPASS' ? 'pass' : (m[2] === 'FAILED' ? 'fail' : (m[2] === 'ERROR' ? 'error' : 'skip')), durationMs: null,
    }));
  }
  if (kind === 'vitest' || kind === 'jest') {
    return [...clean.matchAll(/^\s*([✓✔×✕↓])\s+(.+?)(?:\s+\(?(\d+)\s*ms\)?)?\s*$/gm)]
      .filter(m => !/\(\d+\s+tests?\b/i.test(m[2]))
      .map(m => ({
        id: m[2].trim(), status: m[1] === '✓' || m[1] === '✔' ? 'pass' : (m[1] === '↓' ? 'skip' : 'fail'), durationMs: m[3] ? Number(m[3]) : null,
      }));
  }
  return [];
}

export const TEST_RUNNERS = Object.freeze({
  'node:test': Object.freeze({ kind: 'node:test', command: 'node --test', reportFormat: 'tap', parseSummary: s => parseTestSummaryOutput(s, 'node:test'), extractCases: s => extractTestCases(s, 'node:test') }),
  vitest: Object.freeze({ kind: 'vitest', command: 'npx vitest run', reportFormat: 'junit', parseSummary: s => parseTestSummaryOutput(s, 'vitest'), extractCases: s => extractTestCases(s, 'vitest') }),
  pytest: Object.freeze({ kind: 'pytest', command: 'pytest', reportFormat: 'junit', parseSummary: s => parseTestSummaryOutput(s, 'pytest'), extractCases: s => extractTestCases(s, 'pytest') }),
  cargo: Object.freeze({ kind: 'cargo', command: 'cargo test', reportFormat: 'cargo', parseSummary: s => parseTestSummaryOutput(s, 'cargo'), extractCases: s => extractTestCases(s, 'cargo') }),
  go: Object.freeze({ kind: 'go', command: 'go test -json ./...', reportFormat: 'go-json', parseSummary: s => parseTestSummaryOutput(s, 'go'), extractCases: s => extractTestCases(s, 'go') }),
});
