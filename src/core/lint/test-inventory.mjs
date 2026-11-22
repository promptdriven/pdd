// Polyglot `pdd lint --diff [BASE]` spotlight: BASE..WORKTREE diff, 5 P0 inventory fixes, hard-fail .only & conflict markers.
import { spawnSync } from 'node:child_process';
import { realpathSync } from 'node:fs';
import { isTestPromptPath } from '../../file-owner.mjs';
import { causeText } from '../../shared/safe-read.mjs';
import { buildLineStarts, formatTeachingDetail, lineNumberAt, readSafeUtf8, resolveDefaultBaseRef } from './diagnostics.mjs';

export { resolveDefaultBaseRef };

const UTILITY_TEST_DIR = /(?:^|\/)(?:helpers?|fixtures?|mocks?|__mocks__|__fixtures__)\//i;
const DOC_OR_FIXTURE_PATH = /(?:^|\/)(?:docs?|fixtures?|__fixtures__)\/|\.md$/i;
const SNAPSHOT_PATH = /\.snap$|(?:^|\/)__snapshots__\//i;
const HARNESS_PATH = /(?:^|\/)(?:package\.json|vitest\.config\.[^/]+|jest\.config\.[^/]+|pytest\.ini|pyproject\.toml|conftest\.py|tox\.ini|setup\.cfg|\.github\/workflows\/[^/]+\.ya?ml)$/i;
const CHAI_MODIFIERS = new Set(['not', 'resolves', 'rejects', 'to', 'be', 'been', 'is', 'that', 'which', 'and', 'has', 'have', 'with', 'at', 'of', 'same', 'but', 'does', 'still', 'also', 'deep', 'nested', 'own', 'ordered', 'any', 'all']);
const CHAI_TERMINAL_PROPS = new Set(['true', 'false', 'null', 'undefined', 'NaN', 'exist', 'empty', 'ok', 'arguments', 'finite', 'extensible', 'sealed', 'frozen']);

function hasExpectAssertionChain(tail) {
  let i = 0, segments = 0, lastIdent = '', allPriorModifiers = true;
  const limit = Math.min(tail.length, 240);
  while (i < limit) {
    while (i < limit && /\s/.test(tail[i])) i++;
    if (i < limit && tail[i] === '(' && segments > 0) return true;
    if (i >= limit || tail[i] !== '.') break;
    i++;
    while (i < limit && /\s/.test(tail[i])) i++;
    const start = i;
    while (i < limit && /[A-Za-z0-9_$]/.test(tail[i])) i++;
    if (i === start) break;
    if (segments > 0 && !CHAI_MODIFIERS.has(lastIdent)) allPriorModifiers = false;
    lastIdent = tail.slice(start, i);
    segments++;
  }
  return segments >= 2 && allPriorModifiers && CHAI_TERMINAL_PROPS.has(lastIdent);
}

export function detectTestLanguage(path, source = '') {
  if (!path || UTILITY_TEST_DIR.test(path)) return null;
  const base = path.split('/').at(-1);
  if (/\.(?:[cm]?[jt]s|[jt]sx)$/.test(base) && (/\.(?:test|spec)\./.test(base) || path.split('/').some(p => ['test', 'tests', '__tests__'].includes(p)))) return 'js';
  if (/^(?:test_.*|.*_test)\.py$/.test(base)) return 'py';
  if (/_test\.go$/.test(base)) return 'go';
  if (/\.rs$/.test(base)) {
    if (/_test\.rs$/.test(base) || path.split('/').some(p => ['test', 'tests'].includes(p))) return 'rs';
    if (typeof source === 'string' && /#\[\s*(?:cfg\s*\(\s*test\s*\)|(?:[A-Za-z_]\w*::)*test\b)/.test(source)) return 'rs';
  }
  return null;
}

function maskJsNonCode(source) {
  let out = '', i = 0, prev = '';
  const canRegex = () => !prev || '(=:,[!&|?{};+*%<>^~'.includes(prev) || /^(?:return|throw|case|in|of|typeof|void|delete|await|yield)$/.test(prev);
  while (i < source.length) {
    const ch = source[i], next = source[i + 1];
    if (ch === '/' && next === '/') { const e = source.indexOf('\n', i + 2); i = e < 0 ? source.length : e; continue; }
    if (ch === '/' && next === '*') { const e = source.indexOf('*/', i + 2); out += (e < 0 ? source.slice(i) : source.slice(i, e + 2)).replace(/[^\n]/g, ' '); i = e < 0 ? source.length : e + 2; continue; }
    if (ch === "'" || ch === '"' || ch === '`') {
      let j = i + 1;
      while (j < source.length) { if (source[j] === '\\') { j += 2; continue; } if (source[j] === ch) { j++; break; } j++; }
      const marker = ch === '`' ? '`' : 'q';
      out += `${marker}${source.slice(i + 1, j).replace(/[^\n]/g, ' ')}`; prev = 'q'; i = j; continue;
    }
    if (ch === '/' && next !== '/' && next !== '*' && canRegex()) {
      let j = i + 1, cls = false, closed = false;
      while (j < source.length && source[j] !== '\n') {
        if (source[j] === '\\') { j += 2; continue; }
        if (source[j] === '[') cls = true; else if (source[j] === ']') cls = false;
        else if (source[j] === '/' && !cls) { closed = true; j++; break; }
        j++;
      }
      if (closed) { while (j < source.length && /[A-Za-z]/.test(source[j])) j++; out += 'r'; prev = 'r'; i = j; continue; }
    }
    if (/[A-Za-z_$]/.test(ch)) {
      let j = i + 1; while (j < source.length && /[A-Za-z0-9_$]/.test(source[j])) j++;
      prev = source.slice(i, j); out += prev; i = j; continue;
    }
    out += ch; if (!/\s/.test(ch)) prev = ch; i++;
  }
  return out;
}

export function findExecutableOnlyMarkers(source, filePath) {
  if (!source || DOC_OR_FIXTURE_PATH.test(filePath) || UTILITY_TEST_DIR.test(filePath)) return [];
  const lang = detectTestLanguage(filePath);
  if (lang === 'py') {
    const lines = source.split(/\r?\n/), hits = [];
    for (let i = 0; i < lines.length; i++) {
      if (/^\s*#/.test(lines[i])) continue;
      if (/^\s*@pytest\.mark\.only\b/.test(lines[i])) hits.push({ path: filePath, line: i + 1, marker: '@pytest.mark.only' });
    }
    return hits;
  }
  if (lang !== 'js') return [];
  const masked = maskJsNonCode(source), ls = buildLineStarts(masked), hits = [], seen = new Set();
  const onlyRe = /(?<![.\w$])(?:(?:test|it|describe|suite|context)\s*\.\s*only(?:\s*\.\s*each(?=\s*[(`])|(?=\s*\())|(?:fit|fdescribe)(?=\s*\())/g;
  for (const m of masked.matchAll(onlyRe)) {
    const line = lineNumberAt(ls, m.index);
    if (seen.has(line)) continue;
    seen.add(line);
    hits.push({ path: filePath, line, marker: m[0].replace(/\s+/g, '') });
  }
  return hits;
}

export function findConflictMarkers(source, filePath) {
  if (!source || DOC_OR_FIXTURE_PATH.test(filePath)) return [];
  const lines = source.split(/\r?\n/), hits = [];
  let inBlock = false;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (/^<{7}(?:\s|$)/.test(line)) { hits.push({ path: filePath, line: i + 1 }); inBlock = true; }
    else if (/^\|{7}(?:\s|$)/.test(line)) { if (!inBlock) hits.push({ path: filePath, line: i + 1 }); }
    else if (/^={7}$/.test(line)) { if (!inBlock) hits.push({ path: filePath, line: i + 1 }); }
    else if (/^>{7}(?:\s|$)/.test(line)) { if (!inBlock) hits.push({ path: filePath, line: i + 1 }); inBlock = false; }
  }
  return hits;
}

function countTableRows(source, lang) {
  if (lang === 'go') return [...source.matchAll(/\bt\.Run\s*\(\s*"([^"]+)"/g)].length;
  if (lang === 'rs') return [...source.matchAll(/#\[\s*(?:(?:[A-Za-z_]\w*::)*case|test_case)\s*\(/g)].length;
  const re = lang === 'js' ? /\b(?:test|it|describe)\.each\s*\(\s*\[([\s\S]*?)\]\s*\)/g : /@pytest\.mark\.parametrize\s*\([^,]+,\s*\[([\s\S]*?)\]\s*\)/g;
  let count = 0;
  for (const m of source.matchAll(re)) if (m[1].trim()) count += m[1].trim().split(/,(?![^[\]{}()]*[\]}])/).filter(x => x.trim()).length;
  return count;
}

function collectJsAssertions(maskedBlock) {
  const assertions = [];
  for (const m of maskedBlock.matchAll(/(?<![.\w$])assert\s*[.(]/g)) assertions.push(m[0]);
  for (const m of maskedBlock.matchAll(/(?<![.\w$])expect\s*\.\s*(?:assertions|hasAssertions)\s*\(/g)) assertions.push(m[0]);
  for (const m of maskedBlock.matchAll(/(?<![.\w$])expect\s*\(/g)) {
    const openIdx = m.index + m[0].length - 1;
    let depth = 0, closeIdx = -1;
    for (let i = openIdx; i < maskedBlock.length; i++) {
      if (maskedBlock[i] === '(') depth++;
      else if (maskedBlock[i] === ')' && --depth === 0) { closeIdx = i; break; }
    }
    if (closeIdx > openIdx && hasExpectAssertionChain(maskedBlock.slice(closeIdx + 1))) assertions.push(maskedBlock.slice(m.index, closeIdx + 1));
  }
  return assertions;
}

export function extractTestCases(source, lang) {
  if (!lang || !source) return { cases: [], tableCaseCount: 0 };
  const lines = source.split(/\r?\n/), found = [];

  if (lang === 'js') {
    const maskedLines = maskJsNonCode(source).split('\n');
    for (let at = 0; at < lines.length; at++) {
      const rawLine = lines[at], maskLine = maskedLines[at] ?? '';
      const decl = /^(\s*)(?:(?:test|it)(?:\.(?:only|skip|todo))?|xit|xtest)\s*\(\s*(['"`])((?:\\.|(?!\2).)*)\2/.exec(rawLine);
      if (!decl || !/^\s*(?:(?:test|it)(?:\.(?:only|skip|todo))?|xit|xtest)\s*\(/.test(maskLine)) continue;
      let parenDepth = 0, started = false, end = at;
      for (let i = at; i < maskedLines.length; i++) {
        for (const ch of maskedLines[i]) { if (ch === '(') { parenDepth++; started = true; } else if (ch === ')') parenDepth--; }
        end = i; if (started && parenDepth <= 0) break;
      }
      const slice = lines.slice(at, end + 1), maskSlice = maskedLines.slice(at, end + 1);
      const assertions = collectJsAssertions(maskSlice.join('\n'));
      const skips = [];
      if (/^\s*(?:(?:test|it)\.(?:skip|todo)|xit|xtest)\s*\(/.test(maskLine) || /\{\s*(?:skip|todo)\s*:\s*(?:true|q|`)/.test(maskLine)) skips.push(rawLine.trim());
      for (let j = 1; j < maskSlice.length; j++) {
        if (/\b(?:t|ctx)\.(?:skip|todo)\s*\(/.test(maskSlice[j])) skips.push(slice[j].trim());
      }
      found.push({ name: decl[3], line: at + 1, assertions, skips });
    }
  } else if (lang === 'py') {
    for (let at = 0; at < lines.length; at++) {
      const m = /^(\s*)(?:async\s+)?def\s+(test_\w+)\s*\(/.exec(lines[at]);
      if (!m) continue;
      let end = lines.length - 1;
      for (let i = at + 1; i < lines.length; i++) {
        if (lines[i].trim() && !/^\s*#/.test(lines[i]) && /^\s*/.exec(lines[i])[0].length <= m[1].length) { end = i - 1; break; }
      }
      const skips = [], assertions = [];
      for (let i = at - 1; i >= 0 && /^\s*@/.test(lines[i]); i--) if (/^\s*@(?:pytest\.mark\.(?:skip|skipif|xfail)|unittest\.skip(?:If|Unless)?)\b/.test(lines[i])) skips.unshift(lines[i].trim());
      for (let i = at + 1; i <= end; i++) {
        const t = lines[i].trim();
        if (!t || t.startsWith('#')) continue;
        if (/^assert\b|\bpytest\.raises\s*\(|\bself\.assert\w*\s*\(/.test(t)) assertions.push(t);
        if (/\bpytest\.skip\s*\(/.test(t)) skips.push(t);
      }
      found.push({ name: m[2], line: at + 1, assertions, skips });
    }
  } else if (lang === 'go') {
    for (let at = 0; at < lines.length; at++) {
      const m = /^func\s+(Test\w*)\s*\(/.exec(lines[at]);
      if (!m) continue;
      let end = lines.length - 1, depth = 0, opened = false;
      for (let i = at; i < lines.length; i++) {
        for (const ch of lines[i]) { if (ch === '{') { depth++; opened = true; } else if (ch === '}') depth--; }
        end = i; if (opened && depth <= 0) break;
      }
      const assertions = [], skips = [], subtests = [];
      for (let i = at + 1; i <= end; i++) {
        const t = lines[i].trim();
        if (!t || t.startsWith('//')) continue;
        const sub = /\bt\.Run\s*\(\s*"([^"]+)"\s*,/.exec(t);
        if (sub) {
          let sEnd = end, sd = 0, sOpen = false;
          for (let j = i; j <= end; j++) {
            for (const ch of lines[j]) { if (ch === '{') { sd++; sOpen = true; } else if (ch === '}') sd--; }
            sEnd = j; if (sOpen && sd <= 0) break;
          }
          const sAsserts = [], sSkips = [];
          for (let j = i + 1; j <= sEnd; j++) {
            const st = lines[j].trim();
            if (!st || st.startsWith('//')) continue;
            if (/\b(?:t\.(?:Error|Errorf|Fatal|Fatalf|Fail|FailNow)|(?:assert|require)\.[A-Z]\w*)\s*\(/.test(st)) sAsserts.push(st);
            if (/\bt\.Skip(?:f|Now)?\s*\(/.test(st)) sSkips.push(st);
          }
          subtests.push({ name: sub[1], line: i + 1, assertions: sAsserts, skips: sSkips });
          i = sEnd;
          continue;
        }
        if (/\b(?:t\.(?:Error|Errorf|Fatal|Fatalf|Fail|FailNow)|(?:assert|require)\.[A-Z]\w*)\s*\(/.test(t)) assertions.push(t);
        if (/\bt\.Skip(?:f|Now)?\s*\(/.test(t)) skips.push(t);
      }
      found.push({ name: m[1], line: at + 1, assertions, skips });
      found.push(...subtests);
    }
  } else if (lang === 'rs') {
    const stripRustComments = line => line.replace(/\/\/.*$/, '');
    const RS_TEST_ATTR_RE = /^#\[\s*(?:(?:[A-Za-z_]\w*::)*test(?:\s*\([^)]*\))?|test_case\s*\(|rstest(?:\s*\([^)]*\))?)\s*\]$/;
    const RS_IGNORE_ATTR_RE = /^#\[\s*ignore(?:\s*=\s*.*|\s*\([^)]*\))?\s*\]$/;
    const RS_SHOULD_PANIC_RE = /^#\[\s*should_panic(?:\s*\([^)]*\))?\s*\]$/;
    const RS_ASSERT_RE = /\b(?:assert|assert_eq|assert_ne|debug_assert|debug_assert_eq|debug_assert_ne|matches|panic|unreachable|unimplemented)!\s*[(\[{]/;
    const RS_FN_RE = /^\s*(?:pub(?:\s*\([^)]*\))?\s+)?(?:async\s+)?fn\s+([A-Za-z_]\w*)\s*(?:<[^>]*>)?\s*\(/;
    let inBlockComment = false;
    const cleanLines = lines.map(raw => {
      let out = '', i = 0;
      while (i < raw.length) {
        if (inBlockComment) {
          const close = raw.indexOf('*/', i);
          if (close < 0) { i = raw.length; break; }
          inBlockComment = false; i = close + 2; continue;
        }
        if (raw[i] === '/' && raw[i + 1] === '/') break;
        if (raw[i] === '/' && raw[i + 1] === '*') { inBlockComment = true; i += 2; continue; }
        out += raw[i++];
      }
      return out;
    });
    for (let at = 0; at < lines.length; at++) {
      const m = RS_FN_RE.exec(cleanLines[at]);
      if (!m) continue;
      const attrs = [];
      for (let i = at - 1; i >= 0; i--) {
        const t = cleanLines[i].trim();
        if (!t) continue;
        if (t.startsWith('#[')) { attrs.unshift(t); continue; }
        break;
      }
      if (!attrs.some(a => RS_TEST_ATTR_RE.test(a))) continue;
      const skips = attrs.filter(a => RS_IGNORE_ATTR_RE.test(a));
      const assertions = attrs.filter(a => RS_SHOULD_PANIC_RE.test(a));
      let end = lines.length - 1, depth = 0, opened = false;
      for (let i = at; i < lines.length; i++) {
        const code = stripRustComments(cleanLines[i]).replace(/"(?:\\.|[^"\\])*"/g, '""');
        for (const ch of code) {
          if (ch === '{') { depth++; opened = true; }
          else if (ch === '}') depth--;
        }
        end = i;
        if (opened && depth <= 0) break;
      }
      for (let i = at; i <= end; i++) {
        const t = cleanLines[i].trim();
        if (!t) continue;
        if (RS_ASSERT_RE.test(t)) assertions.push(t);
      }
      found.push({ name: m[1], line: at + 1, assertions, skips });
    }
  }
  return { cases: found, tableCaseCount: countTableRows(source, lang) };
}

export function analyzeDiffEntries(entries = []) {
  const removedByName = new Map(), addedByName = new Map();
  const removedTests = [], addedTests = [], movedTests = [], newSkips = [], assertionDrops = [], tableDrops = [], snapshotEdits = [], harnessEdits = [], errors = [];

  for (const entry of entries) {
    const newPath = entry.newPath || '', oldPath = entry.oldPath || '', activePath = newPath || oldPath;
    if (newPath && entry.after) {
      for (const hit of findExecutableOnlyMarkers(entry.after, newPath)) {
        const detail = formatTeachingDetail({ invariant: `Executable focus marker "${hit.marker}(" in ${hit.path}:${hit.line} skips the rest of the test suite`, fix: `Remove ".only" / "${hit.marker}" at ${hit.path}:${hit.line}`, rerun: 'pdd lint --diff' });
        errors.push({ path: hit.path, line: hit.line, code: 'diff-focus-only', formatted: `Error: diff gate: ${hit.path}:${hit.line} [diff-focus-only] ${detail}` });
      }
      for (const hit of findConflictMarkers(entry.after, newPath)) {
        const detail = formatTeachingDetail({ invariant: `Unresolved merge conflict marker at ${hit.path}:${hit.line}`, fix: `Resolve the conflict block at ${hit.path}:${hit.line} and remove conflict markers`, rerun: 'pdd lint --diff' });
        errors.push({ path: hit.path, line: hit.line, code: 'diff-conflict-marker', formatted: `Error: diff gate: ${hit.path}:${hit.line} [diff-conflict-marker] ${detail}` });
      }
      if (isTestPromptPath(newPath)) {
        const detail = formatTeachingDetail({ invariant: `Misplaced test prompt "${newPath}" violates PDD ownership (prompts own production modules, not test files)`, fix: `Delete ${newPath} and keep test assertions in native test files`, rerun: 'pdd lint --diff' });
        errors.push({ path: newPath, line: 1, code: 'misplaced-test-prompt', formatted: `Error: diff gate: ${newPath}:1 [misplaced-test-prompt] ${detail}` });
      }
    }

    if (SNAPSHOT_PATH.test(activePath)) snapshotEdits.push(activePath);
    if (HARNESS_PATH.test(activePath)) {
      if (activePath.endsWith('package.json')) {
        let changed = entry.before !== entry.after;
        try { changed = (entry.before ? JSON.parse(entry.before)?.scripts?.test : undefined) !== (entry.after ? JSON.parse(entry.after)?.scripts?.test : undefined); } catch {}
        if (changed) harnessEdits.push(`${activePath} (scripts.test)`);
      } else harnessEdits.push(activePath);
    }

    const oldLang = detectTestLanguage(oldPath, entry.before || ''), newLang = detectTestLanguage(newPath, entry.after || '');
    if (!oldLang && !newLang) continue;
    const prev = extractTestCases(entry.before || '', oldLang), next = extractTestCases(entry.after || '', newLang);
    if (prev.tableCaseCount > next.tableCaseCount) tableDrops.push({ path: activePath, before: prev.tableCaseCount, after: next.tableCaseCount });

    const isFileRename = Boolean(oldPath && newPath && oldPath !== newPath);
    const prevMap = new Map(prev.cases.map(c => [c.name, c])), nextMap = new Map(next.cases.map(c => [c.name, c]));
    for (const c of prev.cases) {
      if (!nextMap.has(c.name)) {
        const rec = { name: c.name, path: oldPath || activePath, line: c.line };
        removedTests.push(rec);
        if (!removedByName.has(c.name)) removedByName.set(c.name, []);
        removedByName.get(c.name).push(rec);
      }
    }
    for (const c of next.cases) {
      if (!prevMap.has(c.name)) {
        const rec = { name: c.name, path: newPath || activePath, line: c.line };
        addedTests.push(rec);
        if (!addedByName.has(c.name)) addedByName.set(c.name, []);
        addedByName.get(c.name).push(rec);
        for (const sk of c.skips) newSkips.push({ path: newPath, name: c.name, line: c.line, marker: sk });
      } else {
        if (isFileRename) movedTests.push({ name: c.name, from: oldPath, to: newPath });
        const oldCase = prevMap.get(c.name);
        if (c.assertions.length < oldCase.assertions.length) assertionDrops.push({ path: newPath, name: c.name, before: oldCase.assertions.length, after: c.assertions.length });
        const oldSkips = new Set(oldCase.skips);
        for (const sk of c.skips) if (!oldSkips.has(sk)) newSkips.push({ path: newPath, name: c.name, line: c.line, marker: sk });
      }
    }
  }

  const movedKeys = new Set();
  for (const [name, remList] of removedByName.entries()) {
    const addList = addedByName.get(name);
    if (!addList?.length) continue;
    for (let i = 0; i < Math.min(remList.length, addList.length); i++) {
      movedTests.push({ name, from: remList[i].path, to: addList[i].path });
      movedKeys.add(`${remList[i].path}\0${name}`);
    }
  }
  const genuinelyRemoved = removedTests.filter(r => !movedKeys.has(`${r.path}\0${r.name}`));

  const advisories = [];
  if (genuinelyRemoved.length) advisories.push(`Diff spotlight: ${genuinelyRemoved.length} test(s) removed (${genuinelyRemoved.slice(0, 6).map(r => `${r.path}::${r.name}`).join(', ')})`);
  if (movedTests.length) advisories.push(`Diff spotlight: ${movedTests.length} test(s) moved across files (${movedTests.slice(0, 4).map(m => `${m.name}: ${m.from} -> ${m.to}`).join(', ')})`);
  if (newSkips.length) advisories.push(`Diff spotlight: ${newSkips.length} new skip(s) introduced (${newSkips.slice(0, 6).map(s => `${s.path}:${s.line} ${s.name}`).join(', ')})`);
  if (assertionDrops.length) advisories.push(`Diff spotlight: ${assertionDrops.length} kept test(s) with fewer assertions (${assertionDrops.slice(0, 6).map(a => `${a.path}::${a.name} ${a.before}->${a.after}`).join(', ')})`);
  if (tableDrops.length) advisories.push(`Diff spotlight: table-driven case count dropped in ${tableDrops.map(t => `${t.path} (${t.before}->${t.after})`).join(', ')}`);
  if (snapshotEdits.length) advisories.push(`Diff spotlight: snapshot file(s) modified (${snapshotEdits.join(', ')})`);
  if (harnessEdits.length) advisories.push(`Diff spotlight: test harness / CI config edited (${harnessEdits.join(', ')})`);

  return { ok: errors.length === 0, errors, advisories, removedTests: genuinelyRemoved, movedTests, addedTests, newSkips, assertionDrops, tableDrops, snapshotEdits, harnessEdits };
}

function baseUnavailableResult(baseRef, reason) {
  const detail = formatTeachingDetail({ invariant: reason, fix: 'Pass a valid local git ref via --diff <REF> or commit an initial base commit', rerun: 'pdd lint --diff' });
  return {
    ok: false, baseAvailable: false, baseRef: baseRef ?? null, baseSha: null, baseError: reason, touchedFiles: [],
    errors: [{ path: '.', line: 1, code: 'diff-base-unavailable', formatted: `Error: diff gate: .:1 [diff-base-unavailable] ${detail}` }],
    advisories: [], removedTests: [], movedTests: [], addedTests: [], newSkips: [], assertionDrops: [], tableDrops: [], snapshotEdits: [], harnessEdits: [],
  };
}

export function runDiffSpotlight({ cwd, baseRef } = {}) {
  const realRoot = realpathSync(cwd);
  const resolvedBase = baseRef || resolveDefaultBaseRef(realRoot);
  if (!resolvedBase) return baseUnavailableResult(baseRef, 'Could not resolve a default base commit locally.');
  const revCheck = spawnSync('git', ['rev-parse', '--verify', `${resolvedBase}^{commit}`], { cwd: realRoot, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  if (revCheck.status !== 0 || !revCheck.stdout.trim()) {
    return baseUnavailableResult(resolvedBase, `Base ref "${resolvedBase}" could not be resolved locally.`);
  }
  const resolvedCommit = revCheck.stdout.trim();
  const mb = spawnSync('git', ['merge-base', 'HEAD', resolvedCommit], { cwd: realRoot, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  if (mb.status !== 0 || !mb.stdout.trim()) {
    return baseUnavailableResult(resolvedBase, `git merge-base between HEAD and "${resolvedBase}" failed: ${causeText(mb.stderr || 'no common ancestor')}`);
  }
  const baseSha = mb.stdout.trim();

  const diffRes = spawnSync('git', ['diff', '--no-ext-diff', '--no-textconv', '--name-status', '-z', '--find-renames', baseSha, '--'], { cwd: realRoot, maxBuffer: 32 * 1024 * 1024 });
  if (diffRes.status !== 0) {
    return baseUnavailableResult(resolvedBase, `git diff against base "${resolvedBase}" failed: ${causeText(diffRes.stderr?.toString('utf8') || 'unknown git diff error')}`);
  }
  const entries = [], seenPaths = new Set();
  const fields = diffRes.stdout.toString('utf8').replace(/\0$/, '').split('\0').filter(Boolean);
  for (let i = 0; i < fields.length;) {
    const st = fields[i++], first = fields[i++], second = st.startsWith('R') || st.startsWith('C') ? fields[i++] : first;
    const oldPath = st === 'A' ? '' : first, newPath = st === 'D' ? '' : second;
    const before = oldPath ? (spawnSync('git', ['show', `${baseSha}:${oldPath}`], { cwd: realRoot, encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 }).stdout ?? '') : '';
    const after = newPath ? (readSafeUtf8(realRoot, newPath) ?? '') : '';
    entries.push({ status: st, oldPath, newPath, before, after });
    if (newPath) seenPaths.add(newPath); if (oldPath) seenPaths.add(oldPath);
  }
  const untracked = spawnSync('git', ['ls-files', '--others', '--exclude-standard', '-z'], { cwd: realRoot, maxBuffer: 16 * 1024 * 1024 });
  if (untracked.status !== 0) {
    return baseUnavailableResult(resolvedBase, `git ls-files failed while collecting untracked files: ${causeText(untracked.stderr?.toString('utf8') || 'unknown error')}`);
  }
  for (const rel of untracked.stdout.toString('utf8').split('\0').filter(Boolean)) {
    if (seenPaths.has(rel)) continue;
    seenPaths.add(rel);
    entries.push({ status: 'A', oldPath: '', newPath: rel, before: '', after: readSafeUtf8(realRoot, rel) ?? '' });
  }
  const analysis = analyzeDiffEntries(entries);
  const checkRes = spawnSync('git', ['diff', '--check', baseSha, '--'], { cwd: realRoot, encoding: 'utf8', maxBuffer: 4 * 1024 * 1024 });
  if (checkRes.status === 2 && checkRes.stdout) {
    for (const line of checkRes.stdout.split(/\r?\n/)) {
      const cm = /^([^:]+):(\d+):\s*leftover conflict marker/i.exec(line);
      if (!cm || DOC_OR_FIXTURE_PATH.test(cm[1])) continue;
      const file = cm[1], lineNo = Number(cm[2]) || 1;
      if (!analysis.errors.some(e => e.code === 'diff-conflict-marker' && e.path === file && e.line === lineNo)) {
        const detail = formatTeachingDetail({ invariant: `Leftover conflict marker reported by git diff --check at ${file}:${lineNo}`, fix: `Resolve the conflict marker at ${file}:${lineNo}`, rerun: 'pdd lint --diff' });
        analysis.errors.push({ path: file, line: lineNo, code: 'diff-conflict-marker', formatted: `Error: diff gate: ${file}:${lineNo} [diff-conflict-marker] ${detail}` });
        analysis.ok = false;
      }
    }
  }
  return { ...analysis, baseAvailable: true, baseRef: resolvedBase, baseSha, touchedFiles: [...seenPaths].sort() };
}
