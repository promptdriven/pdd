// Generated from prompts/cli/autopilot-validator.prompt.md (sha256: 691dd6196bed4cd3f73c6e54357b81dbbd926f01249066f198c14749055ad53b).
import { execFileSync } from 'node:child_process';
import { readSafeUtf8 } from '../../core/lint/diagnostics.mjs';
import { loadProjectLintConfig } from '../../core/lint/project-config.mjs';
import { collectTestFixedSleepFindings, collectTestUnexcusedSkipFindings, lintAutopilotTestHygiene, lintTestFixedSleeps, lintTestUnexcusedSkips } from '../lint-sleep-skip.mjs';
import { MIN_REALISTIC_PAYLOAD_BYTES, NON_PRODUCTION_DIR_RE, canonicalTargetPath, classifyProductionPathSurfaces, normalizePath, resolveRelativeTarget } from './surfaces.mjs';
import {
  EXTERNAL_TOOL_EXEC_RE, GENERIC_CALL_RE, MOCK_USAGE_RE, POLYGLOT_MOCK_USAGE_RE, REAL_DEVICE_PATH_RE, REAL_E2E_EXEC_RE,
  SANDBOX_EXEC_RE, SHELL_RUNTIME_RE, SUBPROCESS_ORIG_NAMES, TRIVIAL_SUBPROCESS_BIN_RE,
  analyzePrimitiveAuthenticity, collectLiteralsInMaskedSlice, detectJsBrowser, detectJsFsState, detectJsServerOrDb,
  detectJsTty, detectLang, extractCallArgsSlice, hasLeadingDot, resolveAuthenticCall, resolveLeadingMemberReceiver, splitLinesWithOffsets,
} from './real-host-probes.mjs';

export { MOCK_USAGE_RE, REAL_E2E_EXEC_RE, collectTestFixedSleepFindings, collectTestUnexcusedSkipFindings, lintAutopilotTestHygiene, lintTestFixedSleeps, lintTestUnexcusedSkips };

const PROD_PATH_LITERAL_RE = /['"`]((?:\.\.\/|\.\/)?(?:bin|cli|cmd|scripts|api|server|routes|handlers|controllers|db|database|migrations|prisma|sql|web|ui|frontend|pages|components|views|app|os|sandbox|tty|pty|subprocess|src)\/[A-Za-z0-9._/-]+)['"`]/g;
const LOOP_START_ALL_RE = /(?<![.\w$])(for|while)[ \t]*\(|\.[ \t]*(forEach|map)[ \t]*\(/g;
const HELPER_DEF_RE = /\b(?:function\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*\(|(?:const|let|var)\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*(?:async\s+)?(?:\([^)]*\)|[A-Za-z_$][A-Za-z0-9_$]*)\s*=>)/;
const SKIP_KEYWORD_RE = /(?:e2e|validation|validator|real-binding)/i;
const PRIVATE_IMPORT_SYM_RE = /^_(?!_)[A-Za-z0-9_$]*$/;
const BACKSIDE_CODE_EXT_RE = /\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|cs|swift)$/i;
const BACKSIDE_SKIP_SUBDIR_RE = /(?:^|\/)(?:fixtures|helpers)\//i;
const BACKSIDE_TEST_FILE_RE = /(?:(?:^|\/)(?:test|tests|__tests__|spec)\/|\.(?:test|spec)\.[a-z0-9]+$|_test\.(?:go|rs|py)$|(?:^|\/)test_[^/]+\.py$)/i;

const decodeEsc = (c) => (c === 'n' ? '\n' : c === 'r' ? '\r' : c === 't' ? '\t' : c);
const isRegexStart = (p) => !p || '([{:;,=!?&|+-*%^~<>}'.includes(p) || /^(?:return|case|throw|in|of|typeof|void|delete|new|else|do|yield|await)$/.test(p);
const hasMockUsage = (code, lang) => MOCK_USAGE_RE.test(code) || (lang !== 'js' && POLYGLOT_MOCK_USAGE_RE.test(code));

function scanSourceWithMetrics(source, lang = 'js') {
  const text = String(source ?? ''), nc = [], ns = [], tpl = [], repUnits = new Map(), lits = new Map();
  let maxInline = 0, nsLen = 0, i = 0, lastTok = '';
  const pushNS = (...ps) => { for (const p of ps) { ns.push(p); nsLen += p.length; } };
  const recLen = (n) => { if (n > maxInline) maxInline = n; if (n >= 0) repUnits.set(nsLen - 1, n); };
  const pushRaw = (open, close) => {
    const oi = nsLen; nc.push(open); pushNS('"'); i += open.length;
    const end = text.indexOf(close, i), body = end < 0 ? text.slice(i) : text.slice(i, end);
    lits.set(oi, body); nc.push(body); for (const c of body) if (c === '\n') pushNS('\n');
    pushNS('"'); recLen(body.length); i = end >= 0 ? (nc.push(close), end + close.length) : text.length; lastTok = '""';
  };
  const prevWord = () => { let j = nc.length - 1; while (j >= 0 && /\s/.test(nc[j])) j -= 1; if (j < 0 || !/[\w$]/.test(nc[j])) return j >= 0 ? nc[j] : ''; const e = j; while (j >= 0 && /[\w$]/.test(nc[j])) j -= 1; return nc.slice(j + 1, e + 1).join(''); };
  const scanTpl = (isStart, oi) => {
    let len = 0, cs = i, parts = null;
    const fin = (end) => lits.set(oi, parts ? (parts.push(text.slice(cs, end)), parts.join('')) : text.slice(cs, end));
    while (i < text.length) {
      const c = text[i];
      if (c === '\\' && i + 1 < text.length) { parts ??= []; if (i > cs) parts.push(text.slice(cs, i)); nc.push(c, text[i + 1]); if (text[i + 1] === '\n') pushNS('\n'); else parts.push(decodeEsc(text[i + 1])); len += 1; i += 2; cs = i; continue; }
      if (c === '$' && text[i + 1] === '{') { fin(i); if (len > maxInline) maxInline = len; nc.push('$', '{'); pushNS('"+('); i += 2; tpl.push(1); lastTok = '('; return; }
      if (c === '`') { fin(i); nc.push(c); pushNS('"'); i += 1; if (isStart) recLen(len); else if (len > maxInline) maxInline = len; lastTok = '""'; return; }
      nc.push(c); if (c === '\n') pushNS('\n'); len += 1; i += 1;
    }
    fin(i); if (len > maxInline) maxInline = len; lastTok = '""';
  };
  while (i < text.length) {
    const ch = text[i], nx = text[i + 1];
    if ((lang === 'py' && ch === '#') || (lang !== 'py' && ch === '/' && nx === '/')) { while (i < text.length && text[i] !== '\n') { nc.push(' '); pushNS(' '); i += 1; } continue; }
    if (lang !== 'py' && ch === '/' && nx === '*') { nc.push(' ', ' '); pushNS(' ', ' '); i += 2; while (i < text.length) { if (text[i] === '*' && text[i + 1] === '/') { nc.push(' ', ' '); pushNS(' ', ' '); i += 2; break; } const k = text[i] === '\n' ? '\n' : ' '; nc.push(k); pushNS(k); i += 1; } continue; }
    if (lang === 'py' && (ch === '\'' || ch === '"') && text[i + 1] === ch && text[i + 2] === ch) { pushRaw(ch.repeat(3), ch.repeat(3)); continue; }
    if (lang === 'rs' && ch === 'r' && (nx === '"' || nx === '#')) { let h = 0; while (text[i + 1 + h] === '#') h += 1; if (text[i + 1 + h] === '"') { pushRaw(`r${'#'.repeat(h)}"`, `"${'#'.repeat(h)}`); continue; } }
    if (lang === 'go' && ch === '`') { pushRaw('`', '`'); continue; }
    if (lang === 'js' && ch === '`') { const oi = nsLen; nc.push(ch); pushNS('"'); i += 1; scanTpl(true, oi); continue; }
    if (lang === 'js' && tpl.length > 0) { if (ch === '{') tpl[tpl.length - 1] += 1; else if (ch === '}' && --tpl[tpl.length - 1] === 0) { tpl.pop(); nc.push('}'); pushNS(')+'); const oi = nsLen; pushNS('"'); i += 1; scanTpl(false, oi); continue; } }
    if (ch === '\'' || ch === '"') {
      const q = ch, oi = nsLen; nc.push(ch); pushNS('"'); i += 1; let cs = i, parts = null, len = 0, closed = false;
      while (i < text.length) {
        const c = text[i];
        if (c === '\\' && i + 1 < text.length) { parts ??= []; if (i > cs) parts.push(text.slice(cs, i)); nc.push(c, text[i + 1]); if (text[i + 1] === '\n') pushNS('\n'); else parts.push(decodeEsc(text[i + 1])); len += 1; i += 2; cs = i; continue; }
        if (c === q || c === '\n') { lits.set(oi, parts ? (parts.push(text.slice(cs, i)), parts.join('')) : text.slice(cs, i)); nc.push(c); pushNS('"', ...(c === '\n' ? ['\n'] : [])); i += 1; if (c === q) recLen(len); closed = true; break; }
        nc.push(c); len += 1; i += 1;
      }
      if (!closed) lits.set(oi, parts ? (parts.push(text.slice(cs, i)), parts.join('')) : text.slice(cs, i));
      lastTok = '""'; continue;
    }
    if (lang === 'js' && ch === '/' && nx !== '/' && nx !== '*' && isRegexStart(lastTok || prevWord())) {
      nc.push(ch); pushNS('/'); i += 1; let cls = false;
      while (i < text.length) { const c = text[i]; if (c === '\\' && i + 1 < text.length) { nc.push(c, text[i + 1]); i += 2; continue; } if (c === '\n') { nc.push('\n'); pushNS('\n'); i += 1; break; } if (c === '[') cls = true; else if (c === ']') cls = false; nc.push(c); i += 1; if (c === '/' && !cls) { pushNS(' /'); break; } }
      lastTok = '/re/'; continue;
    }
    nc.push(ch); pushNS(ch); if (!/\s/.test(ch)) lastTok = /[\w$]/.test(ch) ? '' : ch; i += 1;
  }
  return { codeNoComments: nc.join(''), codeNoStrings: ns.join(''), maxInlineStringBytes: maxInline, repeatLiteralUnits: repUnits, stringLiteralsByOpenPos: lits };
}

export const scanJsPreserveLines = (source) => { const { codeNoComments, codeNoStrings } = scanSourceWithMetrics(source, 'js'); return { codeNoComments, codeNoStrings }; };
export const stripCommentsPreserveLines = (source) => scanJsPreserveLines(source).codeNoComments;
export const maskStringsPreserveLines = (source) => scanJsPreserveLines(source).codeNoStrings;

function isSameLineLoopEnclosing(maskedLine, targetIdx) {
  for (const m of maskedLine.matchAll(LOOP_START_ALL_RE)) {
    const matchIdx = m.index ?? 0, isMethod = Boolean(m[2]);
    if (!isMethod && hasLeadingDot(maskedLine, matchIdx)) continue;
    const openIdx = matchIdx + m[0].length - 1;
    if (openIdx >= targetIdx) break;
    let paren = 1, brace = 0, headerClosed = -1, block = false, sawTok = false, closed = false, pb = 0, ib = 0;
    for (let k = openIdx + 1; k < targetIdx; k += 1) {
      const ch = maskedLine[k];
      if (isMethod) { if (ch === '(') paren += 1; else if (ch === ')' && --paren === 0) { closed = true; break; } continue; }
      if (headerClosed < 0) { if (ch === '(') paren += 1; else if (ch === ')' && --paren === 0) headerClosed = k; continue; }
      if (!block && !sawTok) { if (ch === ' ' || ch === '\t') continue; if (ch === '{') { block = true; brace = 1; continue; } if (ch === ';') { closed = true; break; } sawTok = true; if (ch === '(' || ch === '[') pb += 1; continue; }
      if (block) { if (ch === '{') brace += 1; else if (ch === '}' && --brace === 0) { closed = true; break; } }
      else if (ch === '(' || ch === '[') pb += 1; else if (ch === ')' || ch === ']') pb = Math.max(0, pb - 1);
      else if (ch === '{') ib += 1; else if (ch === '}') { if (ib > 0 && --ib === 0 && pb === 0) { closed = true; break; } }
      else if (ch === ';' && pb === 0 && ib === 0) { closed = true; break; }
    }
    if (isMethod ? (!closed && paren > 0) : (headerClosed >= 0 && !closed && (!block || brace > 0))) return true;
  }
  return false;
}

function countHelperCallsBatch(text, helperNames) {
  const counts = new Map();
  if (!helperNames.size) return counts;
  let prevWord = '', prevNonSpace = '';
  for (let i = 0; i < text.length;) {
    const ch = text[i];
    if (/[A-Za-z_$]/.test(ch)) {
      let j = i + 1; while (j < text.length && /[A-Za-z0-9_$]/.test(text[j])) j += 1;
      const word = text.slice(i, j);
      if (helperNames.has(word) && prevNonSpace !== '.' && prevWord !== 'function') { let k = j; while (k < text.length && (text[k] === ' ' || text[k] === '\t')) k += 1; if (text[k] === '(') counts.set(word, (counts.get(word) ?? 0) + 1); }
      prevWord = word; prevNonSpace = word[word.length - 1]; i = j; continue;
    }
    if (!/\s/.test(ch)) { prevNonSpace = ch; if (ch !== '(' && ch !== ')' && ch !== ',') prevWord = ''; }
    i += 1;
  }
  return counts;
}

function analyzeJsSubprocessCalls(code, auth, litMap) {
  let hasRealSubprocess = false, hasExternalToolSubprocess = false, hasLiveLocalSubprocess = false, hasSandboxSubprocess = false, subprocessCallCount = 0, hasLoopedSubprocess = false;
  const ns = auth.namespaceBindings.get('child_process'), nm = auth.namedBindings.get('child_process');
  const hasBinding = Boolean(ns?.size) || (nm ? [...nm.values()].some((o) => SUBPROCESS_ORIG_NAMES.has(o)) : false);
  if (!hasBinding || auth.mockedModules.has('child_process') || !auth.importedModules.has('child_process')) {
    return { hasRealSubprocess, hasExternalToolSubprocess, hasLiveLocalSubprocess, hasSandboxSubprocess, subprocessCallCount, hasLoopedSubprocess };
  }
  const helpers = new Set(), scopes = [];
  let braceDepth = 0;
  for (const { line, offset } of splitLinesWithOffsets(code)) {
    let leadCloses = 0, idx = 0;
    while (idx < line.length && (line[idx] === ' ' || line[idx] === '\t')) idx += 1;
    while (idx < line.length && line[idx] === '}') { leadCloses += 1; idx += 1; }
    const effDepth = Math.max(0, braceDepth - leadCloses);
    while (scopes.length && scopes.at(-1).depth > effDepth) scopes.pop();
    const defMatch = HELPER_DEF_RE.exec(line), defName = defMatch?.[1] ?? defMatch?.[2] ?? null;
    const isHelper = Boolean(defName && defName !== 'test' && defName !== 'it' && defName !== 'describe');
    if (line.includes('(')) {
      const inOuterLoop = scopes.some((s) => s.kind === 'loop');
      let matched = false, firstCol = -1;
      for (const m of line.matchAll(GENERIC_CALL_RE)) {
        const col = m.index ?? 0, abs = offset + col;
        let rcv = m[2] ? m[1] : ''; const fn = m[2] || m[1];
        if (m[2]) { if (hasLeadingDot(code, abs)) continue; }
        else { const lead = resolveLeadingMemberReceiver(code, abs); if (lead.hasDot) { if (!lead.receiver) continue; rcv = lead.receiver; } }
        if (!resolveAuthenticCall(auth, 'child_process', SUBPROCESS_ORIG_NAMES, fn, rcv)) continue;
        if (firstCol < 0) firstCol = col;
        const { slice, startIdx } = extractCallArgsSlice(code, offset + col + m[0].length - 1, 240), tr = slice.trim();
        if (!tr) continue;
        const lits = collectLiteralsInMaskedSlice(slice, startIdx, litMap), combined = lits.length ? `${slice} ${lits.map((x) => x.value).join(' ')}` : slice;
        const inLoop = inOuterLoop || isSameLineLoopEnclosing(line, col), leadLit = tr[0] === '"' && lits.length && !slice.slice(0, lits[0].sliceStart).trim() ? lits[0] : null;
        if (leadLit) {
          const rawCmd = leadLit.value.trim(), cp = tr.indexOf('"', 1), after = cp >= 0 ? tr.slice(cp + 1).trimStart() : '';
          if (!rawCmd) { if (!after.startsWith('+')) continue; }
          else {
            const base = (rawCmd.split(/\s+/)[0] ?? '').split(/[\\/]/).pop() ?? '';
            if (!base || TRIVIAL_SUBPROCESS_BIN_RE.test(base)) continue;
            if (EXTERNAL_TOOL_EXEC_RE.test(rawCmd) || (SHELL_RUNTIME_RE.test(base) && EXTERNAL_TOOL_EXEC_RE.test(combined))) hasExternalToolSubprocess = true;
            if (SANDBOX_EXEC_RE.test(rawCmd)) hasSandboxSubprocess = true;
          }
        } else if (EXTERNAL_TOOL_EXEC_RE.test(combined)) hasExternalToolSubprocess = true;
        hasRealSubprocess = true; matched = true; subprocessCallCount += 1;
        if (inLoop) hasLoopedSubprocess = true;
        if (/--live-local\b/i.test(combined)) hasLiveLocalSubprocess = true;
        if (SANDBOX_EXEC_RE.test(combined)) hasSandboxSubprocess = true;
      }
      if (matched) {
        if (isHelper && firstCol >= 0 && defMatch.index < firstCol) helpers.add(defName);
        else for (let s = scopes.length - 1; s >= 0; s -= 1) if (scopes[s].kind === 'fn' && scopes[s].name) { helpers.add(scopes[s].name); break; }
      }
    }
    let net = 0, opened = null;
    for (let k = 0; k < line.length; k += 1) { if (line[k] === '{') { braceDepth += 1; net += 1; if (opened === null) opened = braceDepth; } else if (line[k] === '}') { braceDepth = Math.max(0, braceDepth - 1); net -= 1; } }
    while (scopes.length && scopes.at(-1).depth > braceDepth) scopes.pop();
    const openLoop = isSameLineLoopEnclosing(line, line.length);
    if (opened !== null && braceDepth >= opened) { if (openLoop) scopes.push({ kind: 'loop', name: null, depth: opened }); else if (isHelper) scopes.push({ kind: 'fn', name: defName, depth: opened }); }
    else if (net > 0 && isHelper) scopes.push({ kind: 'fn', name: defName, depth: braceDepth });
  }
  for (const calls of countHelperCallsBatch(code, helpers).values()) if (calls > subprocessCallCount) subprocessCallCount = calls;
  return { hasRealSubprocess, hasExternalToolSubprocess, hasLiveLocalSubprocess, hasSandboxSubprocess, subprocessCallCount, hasLoopedSubprocess };
}

function detectPolyglotSignals(lang, code, litMap) {
  const litValues = litMap instanceof Map ? [...litMap.values()] : [], hasMock = hasMockUsage(code, lang);
  let hasBrowser = false, hasServerOrDb = false, hasRealSub = false, hasExtSub = false, hasLiveLocal = false, hasSandbox = false, subCount = 0, hasLoop = false, hasTty = false, hasFs = false;
  const inspectCmd = (openIdx) => {
    const { slice, startIdx } = extractCallArgsSlice(code, openIdx, 240), tr = slice.trim();
    if (!tr) return false;
    const lits = collectLiteralsInMaskedSlice(slice, startIdx, litMap), all = `${slice} ${lits.map((x) => x.value).join(' ')}`;
    const lead = tr[0] === '"' && lits.length && !slice.slice(0, lits[0].sliceStart).trim() ? lits[0].value.trim() : null;
    if (lead !== null) {
      if (!lead && !tr.slice(tr.indexOf('"', 1) + 1).trimStart().startsWith('+')) return false;
      const base = (lead.split(/\s+/)[0] ?? '').split(/[\\/]/).pop() ?? '';
      if (lead && (!base || TRIVIAL_SUBPROCESS_BIN_RE.test(base))) return false;
      if (EXTERNAL_TOOL_EXEC_RE.test(lead) || (SHELL_RUNTIME_RE.test(base) && EXTERNAL_TOOL_EXEC_RE.test(all))) hasExtSub = true;
    } else if (EXTERNAL_TOOL_EXEC_RE.test(all)) hasExtSub = true;
    hasRealSub = true; subCount += 1;
    if (/--live-local\b/i.test(all)) hasLiveLocal = true;
    if (SANDBOX_EXEC_RE.test(all)) hasSandbox = true;
    return true;
  };
  if (lang === 'py') {
    const stubbed = /\b(?:patch|monkeypatch\.setattr|mocker\.patch|setattr)\s*\([^)]*subprocess/i.test(code) || /\bsubprocess\s*\.\s*(?:run|Popen|check_output|check_call)\s*=(?!=)|\bsubprocess\s*=(?!=)/.test(code) || litValues.some((v) => /subprocess\.(?:run|Popen|check_output|check_call)/.test(v));
    if (!stubbed && /\b(?:import\s+subprocess|from\s+subprocess\s+import)\b/.test(code)) for (const m of code.matchAll(/\bsubprocess\.(?:run|Popen|check_output|check_call)\s*\(/g)) inspectCmd((m.index ?? 0) + m[0].length - 1);
    hasLoop = hasRealSub && /\b(?:for|while)\s+[^:\n]+:\s*\n?[ \t]+[^\n]*subprocess\./.test(code);
    hasBrowser = /\bplaywright\b/.test(code) && /\.(?:goto|launch)\s*\(/.test(code) && !hasMock;
    hasServerOrDb = /\b(?:requests\.(?:get|post|put|delete|request)|httpx\.(?:get|post|Client)|urllib\.request\.urlopen|HTTPServer|sqlite3\.connect|psycopg2?\.connect|TestClient)\s*\(/.test(code) && !hasMock;
    hasTty = (/\b(?:pty\.openpty|termios\.tcgetattr|os\.isatty)\s*\(/.test(code) || (/\b(?:open|os\.stat)\s*\(/.test(code) && litValues.some((v) => REAL_DEVICE_PATH_RE.test(v)))) && !hasMock;
    hasFs = /\b(?:tempfile\.mkdtemp|TemporaryDirectory|os\.listdir|Path\(|tmp_path)\b/.test(code);
  } else if (lang === 'go') {
    const execShadowed = /\b(?:var|type)\s+exec\b|\bexec\s*:?=(?!=)|\bfunc\b[^(\n]*\([^)]*\bexec\b/.test(code);
    if (!execShadowed && litValues.includes('os/exec')) for (const m of code.matchAll(/\bexec\.Command(?:Context)?\s*\(/g)) inspectCmd((m.index ?? 0) + m[0].length - 1);
    hasLoop = hasRealSub && /\bfor\b[^{]*\{[^}]*exec\.Command/.test(code);
    hasServerOrDb = /\b(?:httptest\.NewServer|net\.Listen|http\.(?:Get|Post|Do)|sql\.Open)\s*\(/.test(code);
    hasTty = /\bterm\.IsTerminal\s*\(/.test(code) || (/\bos\.(?:Open|Stat)\s*\(/.test(code) && litValues.some((v) => REAL_DEVICE_PATH_RE.test(v)));
    hasFs = /\b(?:os\.MkdirTemp|t\.TempDir|os\.ReadDir|os\.ReadFile)\s*\(/.test(code);
  } else if (lang === 'rs') {
    const cmdShadowed = /\b(?:struct|enum|trait|type)\s+Command\b|\bmod\s+command\b/i.test(code);
    const hasStdCmd = /\b(?:std|tokio|async_process|assert_cmd)::process::(?:\{[^}]*\bCommand\b|Command\b|\*)|\b(?:std|tokio|async_process)::process::Command::new\b/.test(code);
    if (!cmdShadowed && hasStdCmd) {
      for (const m of code.matchAll(/\bCommand::new\s*\(/g)) if (inspectCmd((m.index ?? 0) + m[0].length - 1)) {
        const st = (m.index ?? 0) + m[0].length, semi = code.indexOf(';', st), ch = code.slice(st, semi < 0 ? st + 240 : Math.min(semi, st + 240));
        const all = `${ch} ${collectLiteralsInMaskedSlice(ch, st, litMap).map((x) => x.value).join(' ')}`;
        if (/--live-local\b/i.test(all)) hasLiveLocal = true; if (SANDBOX_EXEC_RE.test(all)) hasSandbox = true; if (EXTERNAL_TOOL_EXEC_RE.test(all)) hasExtSub = true;
      }
    }
    hasLoop = hasRealSub && /\b(?:for|while)\b[^{]*\{[^}]*Command::new/.test(code);
    hasServerOrDb = /\b(?:TcpListener::bind|reqwest::|axum::serve|Connection::open|sqlx::)\b/.test(code);
    hasTty = /\b(?:libc::isatty|nix::pty::)\b/.test(code) || (/\b(?:File::open|fs::metadata)\s*\(/.test(code) && litValues.some((v) => REAL_DEVICE_PATH_RE.test(v)));
    hasFs = /\b(?:tempdir|TempDir|fs::read_dir|fs::read_to_string|fs::create_dir)\b/.test(code);
  }
  const hasLiveBinding = hasBrowser || hasServerOrDb || hasExtSub, hasRealHostSmoke = hasLiveBinding || hasRealSub || hasTty || hasLiveLocal;
  return { hasBrowser, hasServerOrDb, hasRealSubprocess: hasRealSub, hasLiveBinding, hasRealDeviceOrTtyProbe: hasTty, hasRealFsState: hasFs, hasLiveLocal, hasSandboxSubprocess: hasSandbox, subprocessCallCount: subCount, hasLoopedSubprocess: hasLoop, hasRealHostSmoke, hasAnyRealExec: hasRealHostSmoke };
}

function detectRealExecutionSignals(filePath, code, litMap) {
  const lang = detectLang(filePath);
  if (lang !== 'js') return detectPolyglotSignals(lang, code, litMap);
  const auth = analyzePrimitiveAuthenticity(code, litMap), sub = analyzeJsSubprocessCalls(code, auth, litMap);
  const hasBrowser = detectJsBrowser(code, auth), hasServerOrDb = detectJsServerOrDb(code, auth);
  const hasExternalSdk = auth.importedModules.has('external-sdk') && !auth.mockedModules.has('external-sdk') && !MOCK_USAGE_RE.test(code);
  const hasRealDeviceOrTtyProbe = detectJsTty(code, auth, litMap), hasRealFsState = detectJsFsState(code, auth);
  const hasLiveBinding = hasBrowser || hasServerOrDb || sub.hasExternalToolSubprocess || hasExternalSdk;
  const hasRealHostSmoke = hasLiveBinding || sub.hasRealSubprocess || hasRealDeviceOrTtyProbe || sub.hasLiveLocalSubprocess;
  return { hasBrowser, hasServerOrDb, hasRealSubprocess: sub.hasRealSubprocess, hasLiveBinding, hasRealDeviceOrTtyProbe, hasRealFsState, hasLiveLocal: sub.hasLiveLocalSubprocess, hasSandboxSubprocess: sub.hasSandboxSubprocess, subprocessCallCount: sub.subprocessCallCount, hasLoopedSubprocess: sub.hasLoopedSubprocess, hasRealHostSmoke, hasAnyRealExec: hasRealHostSmoke };
}

export function inspectTestBoundaryTargets(testPath, text, { nativeOnlyTargets } = {}) {
  const normTest = normalizePath(testPath), lang = detectLang(normTest), code = scanSourceWithMetrics(text, lang).codeNoComments;
  const targetSet = new Set(), boundaryTargetSet = new Set(), surfaceSet = new Set();
  const nativeSet = nativeOnlyTargets instanceof Set ? nativeOnlyTargets : new Set(Array.isArray(nativeOnlyTargets) ? nativeOnlyTargets.map(canonicalTargetPath).filter(Boolean) : []);
  const consider = (raw) => {
    const resolved = resolveRelativeTarget(normTest, raw);
    if (!resolved || NON_PRODUCTION_DIR_RE.test(resolved.toLowerCase())) return;
    const surfaces = classifyProductionPathSurfaces(resolved), canonical = canonicalTargetPath(resolved);
    if (!surfaces.length || !canonical) return;
    targetSet.add(canonical);
    const boundary = surfaces.filter((s) => s !== 'docs' && s !== 'runtime-code');
    if (nativeSet.has(canonical)) boundary.push('native-only');
    if (boundary.length) { boundaryTargetSet.add(canonical); for (const s of boundary) surfaceSet.add(s); }
  };
  for (const m of code.matchAll(/(?:from|require\s*\()\s*['"`]([^'"`]+)['"`]/g)) if (m[1].startsWith('.') || /^(?:bin|cli|cmd|scripts|api|server|routes|handlers|controllers|db|database|migrations|prisma|sql|web|ui|frontend|pages|components|views|app|os|sandbox|tty|pty|subprocess|src)\//i.test(m[1])) consider(m[1]);
  if (lang === 'py') for (const m of code.matchAll(/\b(?:from|import)\s+([A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)+)/g)) consider(m[1].replace(/\./g, '/'));
  else if (lang === 'go') for (const m of code.matchAll(/"([A-Za-z0-9._-]+\/(?:cmd|cli|api|server|db|os|sandbox|pkg|internal|src)\/[A-Za-z0-9._/-]+)"/g)) consider(m[1].replace(/^[^/]+\//, ''));
  else if (lang === 'rs') for (const m of code.matchAll(/\buse\s+(?:crate|super)::([A-Za-z0-9_:]+)/g)) consider(`src/${m[1].replace(/::/g, '/')}`);
  for (const m of code.matchAll(PROD_PATH_LITERAL_RE)) consider(m[1]);
  if (!boundaryTargetSet.size) {
    const stripped = normTest.replace(/^(?:test|tests|__tests__|spec)\//i, '').replace(/(?:^|\/)test_([^/]+)\.py$/i, '$1.py').replace(/_test\.(go|rs|py)$/i, '.$1').replace(/\.(?:test|spec|vectors\.test|e2e\.test)\.[a-z0-9]+$/i, '.mjs');
    const own = classifyProductionPathSurfaces(stripped).filter((s) => s !== 'docs' && s !== 'runtime-code');
    if (own.length) { for (const s of own) surfaceSet.add(s); boundaryTargetSet.add(`test-stem:${canonicalTargetPath(stripped)}`); }
  }
  return { allTargets: [...targetSet].sort(), boundaryTargets: [...boundaryTargetSet].sort(), boundarySurfaces: [...surfaceSet].sort() };
}

function parseByteExpr(raw) {
  const s = String(raw ?? '').replace(/_/g, '').trim();
  if (!s || s.length > 40 || !/^[0-9\s*+]+$/.test(s)) return null;
  let total = 0;
  for (const add of s.split('+')) { let prod = 1; for (const f of add.split('*').map((x) => x.trim())) if (!/^\d+$/.test(f) || !Number.isSafeInteger(prod *= Number(f))) return null; if (!Number.isSafeInteger(total += prod)) return null; }
  return total;
}

function detectMaxPayloadBytes(code, { maxInlineStringBytes = 0, repeatLiteralUnits = null, lang = 'js' } = {}) {
  let maxBytes = maxInlineStringBytes > 0 ? maxInlineStringBytes : null;
  const rec = (n) => { if (Number.isInteger(n) && n > 0 && (maxBytes === null || n > maxBytes)) maxBytes = n; };
  for (const m of code.matchAll(/"\s*\.\s*repeat\s*\(([0-9_*\s+]{1,40})\)/g)) { const c = parseByteExpr(m[1]); if (c !== null) rec((repeatLiteralUnits?.get(m.index) ?? 1) * c); }
  for (const m of code.matchAll(/\.\s*repeat\s*\(([0-9_*\s+]{1,40})\)/g)) { let p = (m.index ?? 0) - 1; while (p >= 0 && /\s/.test(code[p])) p -= 1; if (p < 0 || code[p] !== '"') rec(parseByteExpr(m[1])); }
  if (lang === 'js') { for (const m of code.matchAll(/\b(?:Buffer\s*\.\s*alloc(?:Unsafe)?|new\s+(?:Uint8Array|Array|Buffer))\s*\(([0-9_*\s+]{1,40})\)/g)) rec(parseByteExpr(m[1])); }
  else if (lang === 'py') { for (const m of code.matchAll(/"\s*\*\s*([0-9_*\s+]{1,40})/g)) { const c = parseByteExpr(m[1]); if (c !== null) rec((repeatLiteralUnits?.get(m.index) ?? 1) * c); } for (const m of code.matchAll(/\b(?:bytearray|bytes)\s*\(\s*([0-9_*\s+]{1,40})/g)) rec(parseByteExpr(m[1])); }
  else if (lang === 'go') { for (const m of code.matchAll(/\bmake\s*\(\s*\[\]byte\s*,\s*([0-9_*\s+]{1,40})|\b(?:strings|bytes)\.Repeat\s*\([^,]{1,40},\s*([0-9_*\s+]{1,40})\)/g)) rec(parseByteExpr(m[1] ?? m[2])); }
  else if (lang === 'rs') { for (const m of code.matchAll(/\bvec!\s*\[\s*[^;]{1,20};\s*([0-9_*\s+]{1,40})\s*\]/g)) rec(parseByteExpr(m[1])); }
  return maxBytes;
}

export function detectRealHostProbesInTest(testPath, text) {
  if (lintValidationCode({ path: testPath, kind: 'test', text, hasRealE2eCoverage: true }).codes.includes('silent-validation-skip')) return { hasRealHostSmoke: false, mockOnly: false, classes: [], maxDetectedPayloadBytes: null, detectedTurns: 0, liveLocal: false };
  const lang = detectLang(testPath), { codeNoStrings, maxInlineStringBytes, repeatLiteralUnits, stringLiteralsByOpenPos } = scanSourceWithMetrics(text, lang);
  const s = detectRealExecutionSignals(testPath, codeNoStrings, stringLiteralsByOpenPos), maxBytes = detectMaxPayloadBytes(codeNoStrings, { maxInlineStringBytes, repeatLiteralUnits, lang });
  const turns = !s.hasRealSubprocess ? 0 : (s.hasLoopedSubprocess ? Math.max(2, s.subprocessCallCount) : s.subprocessCallCount);
  const classes = [...(s.hasRealSubprocess && s.hasSandboxSubprocess ? ['nested-sandbox'] : []), ...(s.hasRealDeviceOrTtyProbe ? ['host-tty-ownership'] : []), ...(s.hasRealSubprocess && turns >= 2 && s.hasRealFsState ? ['multi-turn-cli-state'] : []), ...(s.hasRealHostSmoke && maxBytes !== null && maxBytes > MIN_REALISTIC_PAYLOAD_BYTES ? ['full-size-payload'] : [])].sort();
  return { hasRealHostSmoke: s.hasRealHostSmoke, mockOnly: hasMockUsage(codeNoStrings, lang) && !s.hasRealHostSmoke, classes, maxDetectedPayloadBytes: maxBytes, detectedTurns: turns, liveLocal: s.hasLiveLocal };
}

export function detectRealE2eKindsInTest(testPath, text) {
  if (lintValidationCode({ path: testPath, kind: 'test', text, hasRealE2eCoverage: true }).codes.includes('silent-validation-skip')) return [];
  const lang = detectLang(testPath), { codeNoStrings, stringLiteralsByOpenPos } = scanSourceWithMetrics(text, lang);
  const s = detectRealExecutionSignals(testPath, codeNoStrings, stringLiteralsByOpenPos);
  return [...(s.hasBrowser ? ['browser-playwright'] : []), ...(s.hasServerOrDb ? ['local-server-or-db'] : []), ...(s.hasRealSubprocess ? ['subprocess-cli'] : []), ...(s.hasLiveBinding ? ['live-binding'] : []), ...(s.hasRealHostSmoke ? ['real-host-smoke'] : []), ...(s.hasAnyRealExec || !hasMockUsage(codeNoStrings, lang) ? ['real-execution'] : [])].sort();
}

function matchSilentSkipLine(codeLine, maskedLine, kind, isValFile, lang) {
  if (/^\s*(?:re|pattern)\s*:\s*\//.test(codeLine)) return null;
  if (/\blocalSkipRow\b|\bstoryLocalSkipOk\b|\blocalSkipOnly\b/i.test(maskedLine)) return 'silent validation local-skip helper bypasses real validation';
  if (/\.filter\s*\([^)]*!==\s*""/.test(maskedLine) && /\.filter\s*\([^)]*!==\s*['"`]real-binding-unavailable['"`]/i.test(codeLine)) return 'filters real-binding-unavailable out of blocking refusals';
  if (/\b(?:test|it|t)\.skip\s*\(/.test(maskedLine) && (isValFile || /\b(?:test|it|t)\.skip\s*\([^)]*(?:e2e|validation|validator|real-binding)/i.test(codeLine))) return 'unconditionally skips an E2E or validation test';
  if (/\b(?:test|it|t)\s*\([^)]*,\s*\{[^}]*\bskip\s*:\s*(?:true|""|!)/.test(maskedLine) && (isValFile || SKIP_KEYWORD_RE.test(codeLine))) return 'unconditionally skips an E2E or validation test via test options';
  if (lang === 'go' && /\bt\.Skip(?:f|Now)?\s*\(/.test(maskedLine) && (isValFile || SKIP_KEYWORD_RE.test(codeLine))) return 'unconditionally skips a Go E2E or validation test';
  if (lang === 'rs' && /#\[ignore\b/.test(maskedLine) && (isValFile || SKIP_KEYWORD_RE.test(codeLine))) return 'unconditionally ignores a Rust E2E or validation test';
  if (kind === 'code') {
    if (/\breturn\b[^;\n]*(?:\bok\s*:\s*true|\bpass\s*:\s*true|\bskipped\s*:\s*true|\bskip\s*:\s*true)/i.test(maskedLine) && /\breal-binding-unavailable\b/i.test(codeLine)) return 'treats real-binding-unavailable as an inline pass or silent skip';
    if (/not a defect or needs-person blocker/i.test(codeLine)) return 'rewrites real-binding-unavailable as a non-blocker';
    if (/real-binding-unavailable.*local\s*skip|local\s*skip.*real-binding-unavailable/i.test(codeLine)) return 'treats missing live binding as an excused skip';
  }
  return null;
}

export function lintValidationCode({ path = '', kind = 'test', text = '', hasRealE2eCoverage = false, nativeOnlyTargets } = {}) {
  const filePath = normalizePath(path) || 'unknown', source = String(text ?? ''), lang = detectLang(filePath);
  const { codeNoComments, codeNoStrings, stringLiteralsByOpenPos } = scanSourceWithMetrics(source, lang);
  const codeLines = codeNoComments.split(/\r?\n/), maskedLines = codeNoStrings.split(/\r?\n/);
  const codeSet = new Set(), warnings = [], isValFile = SKIP_KEYWORD_RE.test(filePath), reported = new Set();
  const addSkip = (ln, detail) => { reported.add(ln); codeSet.add('silent-validation-skip'); warnings.push(`Warning: validation lint: ${filePath}:${ln} [silent-validation-skip] ${detail}`); };
  if (kind === 'code' || kind === 'test') {
    for (let i = 0; i < codeLines.length; i += 1) { const d = matchSilentSkipLine(codeLines[i], maskedLines[i] ?? '', kind, isValFile, lang); if (d) addSkip(i + 1, d); }
    if (lang === 'py') for (const f of collectTestUnexcusedSkipFindings(source, { path: filePath })) if (!reported.has(f.line) && (isValFile || SKIP_KEYWORD_RE.test(codeLines.slice(Math.max(0, f.line - 1), f.line + 1).join('\n')))) addSkip(f.line, 'unconditionally skips a Python E2E or validation test');
    for (const [re, detail] of [[/\b(?:test|it|t)\s*\(\s*[^,()]{1,200},\s*\{[^}]{0,400}\bskip\s*:\s*(?:true|""|!)/gs, 'unconditionally skips an E2E or validation test via test options'], [/\b(?:test|it|t)\.skip\s*\(\s*[^,()]{1,200}/gs, 'unconditionally skips an E2E or validation test']]) {
      for (const m of codeNoStrings.matchAll(re)) {
        const sl = codeNoStrings.slice(0, m.index ?? 0).split(/\r?\n/).length, el = sl + m[0].split(/\r?\n/).length - 1;
        if (![...reported].some((ln) => ln >= sl && ln <= el) && (isValFile || SKIP_KEYWORD_RE.test(codeLines.slice(sl - 1, el).join('\n')))) addSkip(sl, detail);
      }
    }
  }
  if (kind === 'test' && hasRealE2eCoverage !== true) {
    const { boundarySurfaces } = inspectTestBoundaryTargets(filePath, source, { nativeOnlyTargets });
    const mockLine = boundarySurfaces.length ? maskedLines.findIndex((l) => hasMockUsage(l, lang)) : -1;
    if (mockLine >= 0 && !detectRealExecutionSignals(filePath, codeNoStrings, stringLiteralsByOpenPos).hasAnyRealExec) {
      codeSet.add('boundary-mock-only-test');
      const detail = (boundarySurfaces.includes('native-only') || boundarySurfaces.includes('os-boundary')) ? `mock-only test covers a ${boundarySurfaces.join('/')} boundary with no real-host smoke or --live-local execution` : 'mock-only test covers a runtime boundary with no real E2E coverage';
      warnings.push(`Warning: validation lint: ${filePath}:${mockLine + 1} [boundary-mock-only-test] ${detail}`);
    }
  }
  return { ok: codeSet.size === 0, codes: [...codeSet].sort(), warnings };
}

export const lintValidationSkips = (text, { path = 'src/module.mjs', kind = 'code' } = {}) => lintValidationCode({ path, kind, text, hasRealE2eCoverage: true }).warnings.filter((w) => w.includes('[silent-validation-skip]'));
export const lintBoundaryMockOnlyTests = (text, { path = 'test/example.test.mjs', hasRealE2eCoverage = false, nativeOnlyTargets } = {}) => lintValidationCode({ path, kind: 'test', text, hasRealE2eCoverage, nativeOnlyTargets }).warnings.filter((w) => w.includes('[boundary-mock-only-test]'));

export function lintRepoValidationBackside({ root, files, config, workspaceRoot } = {}) {
  const relFiles = Array.isArray(files) ? files : (() => { try { return execFileSync('git', ['ls-files', '-z'], { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }).split('\0').filter(Boolean); } catch { return []; } })();
  const cfg = config?.ruleSeverities instanceof Map ? config : (typeof config === 'string' || root ? loadProjectLintConfig(typeof config === 'string' ? config : root, { workspaceRoot: workspaceRoot ?? root }) : null);
  const sevOf = (code) => (cfg?.disabledRules?.has(code) || cfg?.ruleSeverities?.get(code) === 'off' ? 'off' : (cfg?.ruleSeverities?.get(code) === 'error' ? 'error' : 'warn'));
  const covered = new Set(), tests = [], codes = [], findings = [], warnings = [], errors = [];
  for (const rel of relFiles) {
    if (typeof rel !== 'string' || !BACKSIDE_CODE_EXT_RE.test(rel)) continue;
    const isTest = BACKSIDE_TEST_FILE_RE.test(rel) && !BACKSIDE_SKIP_SUBDIR_RE.test(rel), text = readSafeUtf8(root, rel);
    if (text === null) continue;
    if (isTest) {
      const { codeNoStrings, stringLiteralsByOpenPos } = scanSourceWithMetrics(text, detectLang(rel)), boundary = inspectTestBoundaryTargets(rel, text);
      if (detectRealExecutionSignals(rel, codeNoStrings, stringLiteralsByOpenPos).hasAnyRealExec) for (const t of boundary.boundaryTargets) covered.add(t);
      tests.push({ rel, text, targets: boundary.boundaryTargets });
    } else if (!BACKSIDE_SKIP_SUBDIR_RE.test(rel)) codes.push({ rel, text });
  }
  const rec = (rel, val) => {
    for (const w of val.warnings ?? []) {
      const m = /:(\d+)\s+\[([a-z0-9-]+)\]\s*(.*)$/.exec(w), sev = sevOf(m ? m[2] : 'validation-lint');
      if (sev === 'off') continue;
      const msg = sev === 'error' ? w.replace(/^Warning:/, 'Error:') : w;
      findings.push({ path: rel, line: m ? Number(m[1]) : 1, code: m ? m[2] : 'validation-lint', severity: sev, detail: m ? m[3] : w, warning: msg });
      if (sev === 'error') errors.push(msg); else warnings.push(msg);
    }
  };
  for (const { rel, text } of codes) rec(rel, lintValidationCode({ path: rel, kind: 'code', text, hasRealE2eCoverage: true }));
  for (const { rel, text, targets } of tests) rec(rel, lintValidationCode({ path: rel, kind: 'test', text, hasRealE2eCoverage: targets.length > 0 && targets.every((t) => covered.has(t)) }));
  return { ok: errors.length === 0, errors, warnings, findings };
}

export function lintChangedTestPrivateImports({ root, files = [], changedFiles = [], config } = {}) {
  if (!root || !Array.isArray(changedFiles) || !changedFiles.length) return { findings: [] };
  const cfg = loadProjectLintConfig(config !== undefined ? config : root);
  if (cfg.disabledRules?.has('test-private-import') || cfg.ruleSeverities?.get('test-private-import') === 'off') return { findings: [] };
  const severity = cfg.ruleSeverities?.get('test-private-import') ?? 'warn', allowed = new Set(Array.isArray(files) ? files : []), findings = [];
  const push = (rel, line, sym, spec) => {
    const message = `Test imports private internal symbol "${sym}" from "${spec}". Test observable behavior through public exports instead of private helpers.`;
    findings.push({ path: rel, line, code: 'test-private-import', category: 'public-interface test', severity, message, formatted: `${severity === 'error' ? 'Error' : 'Warning'}: public-interface test: ${rel}:${line} [test-private-import] ${message}` });
  };
  for (const rel of changedFiles) {
    if (typeof rel !== 'string' || !allowed.has(rel) || !BACKSIDE_TEST_FILE_RE.test(rel) || BACKSIDE_SKIP_SUBDIR_RE.test(rel)) continue;
    const text = readSafeUtf8(root, rel); if (text === null) continue;
    const lang = detectLang(rel);
    if (lang === 'js') for (const m of text.matchAll(/\bimport\s+\{([^}]+)\}\s+from\s+['"](\.\.?\/[^'"]+)['"]/g)) { const line = text.slice(0, m.index).split('\n').length; for (const p of m[1].split(',')) { const sym = p.trim().split(/\s+as\s+/i)[0]?.trim(); if (sym && PRIVATE_IMPORT_SYM_RE.test(sym)) push(rel, line, sym, m[2]); } }
    else if (lang === 'py') for (const m of text.matchAll(/^[ \t]*from\s+(\.+[A-Za-z0-9_.]*|[A-Za-z0-9_.]+)\s+import\s+([^\n#]+)/gm)) { const line = text.slice(0, m.index).split('\n').length; for (const p of m[2].replace(/[()]/g, '').split(',')) { const sym = p.trim().split(/\s+as\s+/i)[0]?.trim(); if (sym && PRIVATE_IMPORT_SYM_RE.test(sym)) push(rel, line, sym, m[1]); } }
    else if (lang === 'rs') for (const m of text.matchAll(/\buse\s+(crate::[A-Za-z0-9_:]+)::(_(?!_)[A-Za-z0-9_]+)/g)) push(rel, text.slice(0, m.index).split('\n').length, m[2], m[1]);
  }
  return { findings };
}

export function lintTestHygiene({ root, files = [], changedFiles = [], config = {} } = {}) {
  const s = lintAutopilotTestHygiene({ root, files: changedFiles.length ? changedFiles : files, config });
  const p = lintChangedTestPrivateImports({ root, files, changedFiles, config });
  const pe = p.findings.filter((f) => f.severity === 'error').map((f) => f.formatted);
  const pw = p.findings.filter((f) => f.severity !== 'error').map((f) => f.formatted);
  return { ok: s.errors.length === 0 && pe.length === 0, errors: [...s.errors, ...pe], warnings: [...s.warnings, ...pw], findings: [...s.findings, ...p.findings] };
}
