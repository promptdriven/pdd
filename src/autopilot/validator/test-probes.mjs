// Layer-2 lean polyglot (JS/TS, Python, Go, Rust) test probes & backside validation lint.
import { execFileSync } from 'node:child_process';
import { readSafeUtf8 } from '../../core/lint/diagnostics.mjs';
import { loadProjectLintConfig } from '../../core/lint/project-config.mjs';
import { collectTestFixedSleepFindings, collectTestUnexcusedSkipFindings, lintAutopilotTestHygiene, lintTestFixedSleeps, lintTestUnexcusedSkips } from '../lint-sleep-skip.mjs';
import { MIN_REALISTIC_PAYLOAD_BYTES, NON_PRODUCTION_DIR_RE, canonicalTargetPath, classifyProductionPathSurfaces, normalizePath, resolveRelativeTarget } from './surfaces.mjs';
export { collectTestFixedSleepFindings, collectTestUnexcusedSkipFindings, lintAutopilotTestHygiene, lintTestFixedSleeps, lintTestUnexcusedSkips };

export const MOCK_USAGE_RE = /\b(?:mock\.|vi\.mock|vi\.doMock|vi\.fn|vi\.spyOn|vi\.stubGlobal|jest\.mock|jest\.doMock|jest\.fn|jest\.spyOn|sinon\.stub|MagicMock|AsyncMock|unittest\.mock|monkeypatch\.setattr|mocker\.patch|gomock|mockall|httptest\.NewRecorder|fakeClient|fakeServer|fakeTransport|fakeSandbox|mockSandbox|stubSandbox|fakeTty|mockTty|stubTty|fakeDb|mockDb|fakeDriver|mockDriver|mockSpawn|fakeSpawn|fakeSubprocess|fakeCli|stubCli)\b|stub(?:bed)?(?:Handler|Wrapper)|#\[automock\]/i;
export const REAL_E2E_EXEC_RE = /\b(?:spawn|spawnSync|execFile|execFileSync|execSync|createServer|playwright|puppeteer|supertest|DatabaseSync|subprocess\.(?:run|Popen|check_output|check_call)|exec\.Command(?:Context)?|httptest\.NewServer|Command::new|TcpListener::bind)\b|\.\s*listen\s*\(|\bfetch\s*\(|\bhttps?\.request\s*\(|\b(?:chromium|firefox|webkit)\.launch\s*\(|\bpage\.goto\s*\(/i;

const REAL_DEVICE_PATH_RE = /\/dev\/(?:tty|ptmx|pts\/)/, SANDBOX_EXEC_RE = /\b(?:sandbox-exec|sandbox_apply|bwrap|bubblewrap|seatbelt|seccomp|landlock|unshare|chroot|firejail)\b/i;
const TRIVIAL_BIN_RE = /^(?:echo|printf|true|false|pwd|uname|whoami|id|date|sleep|cat|ls|test|\[|:)(?:\s|$)/i, SHELL_BIN_RE = /^(?:sh|bash|zsh|dash|fish|cmd|cmd\.exe|powershell|pwsh|node|nodejs|python|python3|ruby|deno|bun|tsx|ts-node)$/i;
const EXTERNAL_TOOL_RE = /\b(?:gcloud|gsutil|bq|aws|az|stripe|docker|docker-compose|kubectl|helm|terraform|gh|pdd|curl|wget|psql|mysql|redis-cli|mongosh|ssh|scp|vault|npm|npx|git)\b/i;
const PROD_PATH_LITERAL_RE = /['"`]((?:\.\.\/|\.\/)?(?:bin|cli|cmd|scripts|api|server|routes|handlers|controllers|db|database|migrations|prisma|sql|web|ui|frontend|pages|components|views|app|os|sandbox|tty|pty|subprocess|src)\/[A-Za-z0-9._/-]+)['"`]/g;
const SKIP_KEYWORD_RE = /(?:e2e|validation|validator|real-binding)/i, PRIVATE_IMPORT_SYM_RE = /^_(?!_)[A-Za-z0-9_$]*$/;
const BACKSIDE_CODE_EXT_RE = /\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|cs|swift)$/i, BACKSIDE_SKIP_SUBDIR_RE = /(?:^|\/)(?:fixtures|helpers)\//i;
const BACKSIDE_TEST_FILE_RE = /(?:(?:^|\/)(?:test|tests|__tests__|spec)\/|\.(?:test|spec)\.[a-z0-9]+$|_test\.(?:go|rs|py)$|(?:^|\/)test_[^/]+\.py$)/i;

const detectLang = (p) => (/\.py$/i.test(p) ? 'py' : /\.go$/i.test(p) ? 'go' : /\.rs$/i.test(p) ? 'rs' : 'js');
const decodeEsc = (c) => (c === 'n' ? '\n' : c === 'r' ? '\r' : c === 't' ? '\t' : c);
const isRegexStart = (p) => !p || '([{:;,=!?&|+-*%^~<>}'.includes(p) || /^(?:return|case|throw|in|of|typeof|void|delete|new|else|do|yield|await)$/.test(p);
const hasLeadDot = (t, idx) => { let j = idx - 1; while (j >= 0 && /\s/.test(t[j])) j -= 1; return j >= 0 && t[j] === '.'; };

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

function detectMaxPayloadBytes(code, { maxInlineStringBytes = 0, repeatLiteralUnits = null } = {}) {
  let maxBytes = maxInlineStringBytes > 0 ? maxInlineStringBytes : null;
  const rec = (n) => { if (Number.isInteger(n) && n > 0 && (maxBytes === null || n > maxBytes)) maxBytes = n; };
  for (const m of code.matchAll(/"\s*(?:\.\s*repeat\s*\(([0-9_*\s+]{1,40})\)|\*\s*([0-9_*\s+]{1,40}))/g)) { const c = parseByteExpr(m[1] ?? m[2]); if (c !== null) rec((repeatLiteralUnits?.get(m.index) ?? 1) * c); }
  for (const m of code.matchAll(/\.\s*repeat\s*\(([0-9_*\s+]{1,40})\)/g)) { let p = (m.index ?? 0) - 1; while (p >= 0 && /\s/.test(code[p])) p -= 1; if (p < 0 || code[p] !== '"') { const c = parseByteExpr(m[1]); if (c !== null) rec(c); } }
  for (const m of code.matchAll(/\b(?:Buffer\s*\.\s*alloc(?:Unsafe)?|new\s+(?:Uint8Array|Array|Buffer)|bytearray|bytes|make\s*\(\s*\[\]byte\s*,)\s*\(?([0-9_*\s+]{1,40})|\b(?:strings|bytes)\.Repeat\s*\([^,]{1,40},\s*([0-9_*\s+]{1,40})\)|\bvec!\s*\[\s*[^;]{1,20};\s*([0-9_*\s+]{1,40})\s*\]/g)) { const n = parseByteExpr(m[1] ?? m[2] ?? m[3]); if (n !== null) rec(n); }
  return maxBytes;
}

function extractCallArgs(text, openIdx, maxLen = 240) {
  if (openIdx < 0 || text[openIdx] !== '(') return { slice: '', startIdx: openIdx + 1, endIdx: openIdx + 1, closed: false };
  const startIdx = openIdx + 1, lim = Math.min(text.length, startIdx + maxLen);
  for (let d = 1, q = '', i = startIdx; i < lim; i += 1) {
    const c = text[i];
    if (q) { if (c === '\\' && i + 1 < lim) i += 1; else if (c === q) q = ''; continue; }
    if (c === '"' || c === '\'' || c === '`') q = c; else if (c === '(') d += 1; else if (c === ')' && --d === 0) return { slice: text.slice(startIdx, i), startIdx, endIdx: i, closed: true };
  }
  return { slice: text.slice(startIdx, lim), startIdx, endIdx: lim, closed: false };
}

function literalsInSlice(slice, startIdx, litMap) {
  const out = [];
  for (let k = 0; k < slice.length; k += 1) if (slice[k] === '"') { const v = litMap.get(startIdx + k); if (v !== undefined) out.push({ value: v, pos: k }); k += 1; while (k < slice.length && slice[k] !== '"') k += 1; }
  return out;
}

const classifyMod = (spec) => {
  const s = String(spec ?? '').trim().toLowerCase();
  if (/^(?:node:)?child_process$/.test(s)) return 'child_process';
  if (/^(?:node:)?fs(?:\/promises)?$/.test(s)) return 'fs';
  if (/^(?:node:)?(?:https?|http2|net)$|^(?:supertest|express|fastify|koa|hono)$/.test(s)) return 'http';
  if (/^(?:node:)?tty$|^node-pty$/.test(s)) return 'tty';
  if (/^(?:node:sqlite|pg|mysql2?|better-sqlite3|sqlite3?|mongodb|redis|ioredis|@prisma\/client)$/.test(s)) return 'db';
  if (/^(?:@playwright\/test|playwright(?:-core|-chromium|-firefox|-webkit)?|puppeteer(?:-core)?)$/.test(s)) return 'browser';
  if (/^(?:@google-cloud\/.+|@aws-sdk\/.+|aws-sdk|stripe|dockerode|@kubernetes\/client-node|@octokit\/.+|googleapis)$/.test(s)) return 'external-sdk';
  return null;
};

function detectExecutionSignals(filePath, code, litMap) {
  const lang = detectLang(filePath), litValues = [...litMap.values()], hasMock = MOCK_USAGE_RE.test(code);
  const litAt = (m) => { const r = m[0].lastIndexOf('""'); return r < 0 ? '' : (litMap.get((m.index ?? 0) + r) ?? ''); };
  let hasBrowser = false, hasServerOrDb = false, hasRealSub = false, hasExtSub = false, hasLiveLocal = false;
  let hasSandboxSub = false, subCount = 0, hasLoopSub = false, hasDevTty = false, hasFsState = false, hasExtSdk = false;

  const inspectCmd = (openParenIdx) => {
    const { slice, startIdx } = extractCallArgs(code, openParenIdx, 240), tr = slice.trim();
    if (!tr) return false;
    const lits = literalsInSlice(slice, startIdx, litMap), all = `${slice} ${lits.map((l) => l.value).join(' ')}`;
    const lead = tr[0] === '"' && lits.length && !slice.slice(0, lits[0].pos).trim() ? lits[0].value.trim() : null;
    if (lead !== null) {
      if (!lead && !tr.slice(tr.indexOf('"', 1) + 1).trimStart().startsWith('+')) return false;
      const base = (lead.split(/\s+/)[0] ?? '').split(/[\\/]/).pop() ?? '';
      if (lead && (!base || TRIVIAL_BIN_RE.test(base))) return false;
      if (EXTERNAL_TOOL_RE.test(lead) || (SHELL_BIN_RE.test(base) && EXTERNAL_TOOL_RE.test(all))) hasExtSub = true;
    } else if (EXTERNAL_TOOL_RE.test(all)) hasExtSub = true;
    hasRealSub = true; subCount += 1;
    if (/--live-local\b/i.test(all)) hasLiveLocal = true;
    if (SANDBOX_EXEC_RE.test(all)) hasSandboxSub = true;
    return true;
  };

  if (lang === 'py') {
    const patched = /\b(?:patch|monkeypatch\.setattr)\s*\([^)]*subprocess/i.test(code) || litValues.some((v) => /subprocess\.(?:run|Popen|check_output|check_call)/.test(v));
    if (!patched && /\b(?:import\s+subprocess|from\s+subprocess\s+import)\b/.test(code)) for (const m of code.matchAll(/\bsubprocess\.(?:run|Popen|check_output|check_call)\s*\(/g)) inspectCmd((m.index ?? 0) + m[0].length - 1);
    hasLoopSub = hasRealSub && /\b(?:for|while)\s+[^:\n]+:\s*\n?[ \t]+[^\n]*subprocess\./.test(code);
    hasBrowser = /\bplaywright\b/.test(code) && /\.(?:goto|launch)\s*\(/.test(code) && !hasMock;
    hasServerOrDb = /\b(?:requests\.(?:get|post|put|delete|request)|httpx\.(?:get|post|Client)|urllib\.request\.urlopen|HTTPServer|sqlite3\.connect|psycopg2?\.connect|TestClient)\s*\(/.test(code) && !hasMock;
    hasDevTty = (/\b(?:pty\.openpty|termios\.tcgetattr|os\.isatty)\s*\(/.test(code) || (/\b(?:open|os\.stat)\s*\(/.test(code) && litValues.some((v) => REAL_DEVICE_PATH_RE.test(v)))) && !hasMock;
    hasFsState = /\b(?:tempfile\.mkdtemp|TemporaryDirectory|os\.listdir|Path\(|tmp_path)\b/.test(code);
  } else if (lang === 'go') {
    if (litValues.includes('os/exec')) for (const m of code.matchAll(/\bexec\.Command(?:Context)?\s*\(/g)) inspectCmd((m.index ?? 0) + m[0].length - 1);
    hasLoopSub = hasRealSub && /\bfor\b[^{]*\{[^}]*exec\.Command/.test(code);
    hasServerOrDb = /\b(?:httptest\.NewServer|net\.Listen|http\.(?:Get|Post|Do)|sql\.Open)\s*\(/.test(code);
    hasDevTty = /\bterm\.IsTerminal\s*\(/.test(code) || (/\bos\.(?:Open|Stat)\s*\(/.test(code) && litValues.some((v) => REAL_DEVICE_PATH_RE.test(v)));
    hasFsState = /\b(?:os\.MkdirTemp|t\.TempDir|os\.ReadDir|os\.ReadFile)\s*\(/.test(code);
  } else if (lang === 'rs') {
    for (const m of code.matchAll(/\bCommand::new\s*\(/g)) if (inspectCmd((m.index ?? 0) + m[0].length - 1)) {
      const st = (m.index ?? 0) + m[0].length, semi = code.indexOf(';', st), ch = code.slice(st, semi < 0 ? st + 240 : Math.min(semi, st + 240));
      const all = `${ch} ${literalsInSlice(ch, st, litMap).map((l) => l.value).join(' ')}`;
      if (/--live-local\b/i.test(all)) hasLiveLocal = true; if (SANDBOX_EXEC_RE.test(all)) hasSandboxSub = true; if (EXTERNAL_TOOL_RE.test(all)) hasExtSub = true;
    }
    hasLoopSub = hasRealSub && /\b(?:for|while)\b[^{]*\{[^}]*Command::new/.test(code);
    hasServerOrDb = /\b(?:TcpListener::bind|reqwest::|axum::serve|Connection::open|sqlx::)\b/.test(code);
    hasDevTty = /\b(?:libc::isatty|nix::pty::)\b/.test(code) || (/\b(?:File::open|fs::metadata)\s*\(/.test(code) && litValues.some((v) => REAL_DEVICE_PATH_RE.test(v)));
    hasFsState = /\b(?:tempdir|TempDir|fs::read_dir|fs::read_to_string|fs::create_dir)\b/.test(code);
  } else {
    const mocked = new Set(), imported = new Set(), shadowed = new Set(), cpNs = new Set(), cpNamed = new Map();
    for (const m of code.matchAll(/\b(?:(?:vi|jest)\.(?:mock|doMock)|mock\.module)[ \t]*\(\s*("")/g)) { const c = classifyMod(litAt(m)); if (c) mocked.add(c); }
    const addImp = (spec, clause) => {
      const tr = String(clause ?? '').trim(); if (!tr || /^type\s+/.test(tr)) return;
      const cat = classifyMod(spec), lo = spec.trim().toLowerCase(), ns = [], named = new Map();
      const nsm = /\*\s+as\s+([A-Za-z_$][\w$]*)/.exec(tr); if (nsm) ns.push(nsm[1]);
      const bs = tr.indexOf('{'), be = tr.lastIndexOf('}');
      if (bs >= 0 && be > bs) {
        const bef = tr.slice(0, bs).replace(/,\s*$/, '').trim(); if (/^[A-Za-z_$][\w$]*$/.test(bef)) ns.push(bef);
        for (const p of tr.slice(bs + 1, be).split(',')) { const x = p.split('=')[0].trim(); if (!x || /^type\s+/.test(x)) continue; const a = /^([A-Za-z_$][\w$]*)(?:\s+as\s+|\s*:\s*)([A-Za-z_$][\w$]*)$/.exec(x); if (a) { if (a[1] === 'default') ns.push(a[2]); else named.set(a[2], a[1]); } else if (/^[A-Za-z_$][\w$]*$/.test(x)) named.set(x, x); }
      } else if (!nsm && /^[A-Za-z_$][\w$]*$/.test(tr)) ns.push(tr);
      if (!cat) { for (const k of [...ns, ...named.keys()]) shadowed.add(k); return; }
      if (mocked.has(cat)) return;
      imported.add(cat); if (lo === '@playwright/test') imported.add('pw-test'); if (cat === 'db' && lo !== 'node:sqlite') imported.add('non-sqlite-db');
      if (cat === 'child_process') { for (const n of ns) cpNs.add(n); for (const [l, o] of named) cpNamed.set(l, o); }
    };
    for (const m of code.matchAll(/(?<!\.)\bimport\s+([A-Za-z_$*{][A-Za-z0-9_$,*{}\s]{0,600})\bfrom\s*("")/g)) addImp(litAt(m), m[1]);
    for (const m of code.matchAll(/\b(?:const|let|var)[ \t]+([A-Za-z_$][\w$]*|\{[A-Za-z0-9_$,:=\s]{1,200}\})[ \t]*=[ \t]*require[ \t]*\(\s*("")\s*\)/g)) addImp(litAt(m), m[1]);
    for (const m of code.matchAll(/\b(?:const|let|var|function|class)[ \t]+([A-Za-z_$][\w$]*)(?![ \t]*=[ \t]*require\b)/g)) if (/^(?:spawn|spawnSync|execFile|execFileSync|execSync|fetch|createServer|statSync|openSync|isatty|DatabaseSync|page|browser|chromium)$/.test(m[1])) shadowed.add(m[1]);
    for (const m of code.matchAll(/\b(?:globalThis|global|window|self)\s*\.\s*(fetch)\s*(?:&&|\|\||\?\?)?=(?![=>])|(?<![\w$.])(fetch|page|browser)\s*(?:&&|\|\||\?\?)?=(?![=>])|\b(?:vi\.stubGlobal|mock\.method|vi\.spyOn|jest\.spyOn|sinon\.stub)\s*\((?:[^,\n)]{1,80},\s*)?("")|(?<![\w$])[A-Za-z_$][\w$]*\s*\.\s*(spawn|spawnSync|execFile|execFileSync|execSync|statSync|openSync|isatty|DatabaseSync|launch|goto)\s*(?:&&|\|\||\?\?)?=(?![=>])/g)) { const k = m[1] || m[2] || m[4] || litAt(m); if (k) shadowed.add(k); }

    const subNames = new Set(['spawn', 'spawnSync', 'execFile', 'execFileSync', 'execSync']);
    if (imported.has('child_process')) {
      const helpers = new Set();
      for (const m of code.matchAll(/(?<![\w$])([A-Za-z_$][\w$]*)(?:\s*\.\s*([A-Za-z_$][\w$]*))?[ \t]*\(/g)) {
        const rcv = m[2] ? m[1] : '', fn = m[2] || m[1];
        const ok = rcv ? (cpNs.has(rcv) && subNames.has(fn) && !shadowed.has(fn) && !shadowed.has(rcv)) : (subNames.has(cpNamed.get(fn)) && !shadowed.has(fn) && !shadowed.has(cpNamed.get(fn)));
        if (!ok || hasLeadDot(code, m.index ?? 0) || !inspectCmd((m.index ?? 0) + m[0].length - 1)) continue;
        if (/\b(?:for|while)\s*\([^)]*\)\s*(?:\{[^}]*)?$|\.(?:forEach|map)\s*\([^)]*$/.test(code.slice(code.lastIndexOf('\n', m.index ?? 0) + 1, m.index ?? 0))) hasLoopSub = true;
        const hm = [...code.slice(Math.max(0, (m.index ?? 0) - 400), m.index ?? 0).matchAll(/\b(?:function\s+([A-Za-z_$][\w$]*)\s*\(|(?:const|let|var)\s+([A-Za-z_$][\w$]*)\s*=\s*(?:async\s+)?(?:\([^)]*\)|[A-Za-z_$][\w$]*)\s*=>)/g)].at(-1);
        const hn = hm?.[1] ?? hm?.[2]; if (hn && !/^(?:test|it|describe)$/.test(hn)) helpers.add(hn);
      }
      for (const h of helpers) { const c = [...code.matchAll(new RegExp(`(?<![.\\w$])${h.replace(/\$/g, '\\$')}[ \\t]*\\(`, 'g'))].length - (code.includes(`function ${h}`) ? 1 : 0); if (c > subCount) subCount = c; }
    }
    if (!shadowed.has('fetch')) for (const m of code.matchAll(/(?<![\w$.])\bfetch\s*\(/g)) {
      const idx = m.index ?? 0; if (hasLeadDot(code, idx) || /\b(?:async|static|get|set|function|abstract|public|private|protected|override|declare)[ \t]+$/.test(code.slice(Math.max(0, idx - 32), idx))) continue;
      const args = extractCallArgs(code, idx + m[0].length - 1, 240), after = args.closed ? code.slice(args.endIdx + 1, args.endIdx + 80).trimStart() : '';
      if (!after.startsWith('{') && !/^:\s*[A-Za-z_$][^{;=\n]{0,60}\{/.test(after)) { hasServerOrDb = true; break; }
    }
    if (!hasServerOrDb && imported.has('http')) hasServerOrDb = (!shadowed.has('createServer') && /\b(?:createServer|request)\s*\(/.test(code)) || (/\.\s*listen\s*\(/.test(code) && !/\b(?:fake|mock|stub)[\w$]*\s*\.\s*listen\s*\(/i.test(code)) || /\bsupertest\s*\(/.test(code);
    if (!hasServerOrDb && imported.has('db')) hasServerOrDb = (!shadowed.has('DatabaseSync') && /\bnew\s+(?:[A-Za-z_$][\w$]*\s*\.\s*)?DatabaseSync\s*\(/.test(code)) || (imported.has('non-sqlite-db') && !hasMock);
    hasBrowser = imported.has('browser') && !shadowed.has('page') && !shadowed.has('launch') && !shadowed.has('goto') && (/\b(?:chromium|firefox|webkit|browser|context)\s*\.\s*(?:launch|launchPersistentContext|newPage|newContext|connect)\s*\(/.test(code) || (imported.has('pw-test') && /\bpage\s*\.\s*goto\s*\(/.test(code)));
    if (imported.has('tty')) hasDevTty = (!shadowed.has('isatty') && /\bisatty\s*\(/.test(code)) || /\bnew\s+(?:[A-Za-z_$][\w$]*\s*\.\s*)?(?:ReadStream|WriteStream)\s*\(/.test(code);
    if (imported.has('fs')) {
      hasFsState = /\b(?:mkdtempSync|mkdtemp|readdirSync|readdir|existsSync|readFileSync|readFile|statSync|stat)\s*\(/.test(code);
      const devVars = new Set([...code.matchAll(/\b(?:const|let|var)[ \t]+([A-Za-z_$][\w$]*)[ \t]*=[ \t]*("")/g)].filter((m) => REAL_DEVICE_PATH_RE.test(litAt(m))).map((m) => m[1]));
      if (!hasDevTty && !shadowed.has('statSync') && !shadowed.has('openSync')) for (const m of code.matchAll(/\b(?:openSync|open|statSync|stat|fstatSync|lstatSync|accessSync)\s*\(/g)) {
        const { slice, startIdx } = extractCallArgs(code, (m.index ?? 0) + m[0].length - 1, 200);
        if (literalsInSlice(slice, startIdx, litMap).some((l) => REAL_DEVICE_PATH_RE.test(l.value)) || [...devVars].some((v) => new RegExp(`(?<![\\w$.])${v.replace(/\$/g, '\\$')}(?![\\w$])`).test(slice))) { hasDevTty = true; break; }
      }
    }
    hasExtSdk = imported.has('external-sdk') && !hasMock;
  }
  const hasLiveBinding = hasBrowser || hasServerOrDb || hasExtSub || hasExtSdk, hasRealHostSmoke = hasLiveBinding || hasRealSub || hasDevTty || hasLiveLocal;
  return { hasBrowser, hasServerOrDb, hasRealSubprocess: hasRealSub, hasLiveBinding, hasRealDeviceOrTtyProbe: hasDevTty, hasRealFsState: hasFsState, hasLiveLocal, hasSandboxSubprocess: hasSandboxSub, subprocessCallCount: subCount, hasLoopedSubprocess: hasLoopSub, hasRealHostSmoke, hasAnyRealExec: hasRealHostSmoke };
}

export function detectRealHostProbesInTest(testPath, text) {
  if (lintValidationCode({ path: testPath, kind: 'test', text, hasRealE2eCoverage: true }).codes.includes('silent-validation-skip')) return { hasRealHostSmoke: false, mockOnly: false, classes: [], maxDetectedPayloadBytes: null, detectedTurns: 0, liveLocal: false };
  const { codeNoStrings, maxInlineStringBytes, repeatLiteralUnits, stringLiteralsByOpenPos } = scanSourceWithMetrics(text, detectLang(testPath));
  const s = detectExecutionSignals(testPath, codeNoStrings, stringLiteralsByOpenPos), maxBytes = detectMaxPayloadBytes(codeNoStrings, { maxInlineStringBytes, repeatLiteralUnits });
  const turns = !s.hasRealSubprocess ? 0 : (s.hasLoopedSubprocess ? Math.max(2, s.subprocessCallCount) : s.subprocessCallCount);
  const classes = [...(s.hasRealSubprocess && s.hasSandboxSubprocess ? ['nested-sandbox'] : []), ...(s.hasRealDeviceOrTtyProbe ? ['host-tty-ownership'] : []), ...(s.hasRealSubprocess && turns >= 2 && s.hasRealFsState ? ['multi-turn-cli-state'] : []), ...(s.hasRealHostSmoke && maxBytes !== null && maxBytes > MIN_REALISTIC_PAYLOAD_BYTES ? ['full-size-payload'] : [])].sort();
  return { hasRealHostSmoke: s.hasRealHostSmoke, mockOnly: MOCK_USAGE_RE.test(codeNoStrings) && !s.hasRealHostSmoke, classes, maxDetectedPayloadBytes: maxBytes, detectedTurns: turns, liveLocal: s.hasLiveLocal };
}

export function detectRealE2eKindsInTest(testPath, text) {
  if (lintValidationCode({ path: testPath, kind: 'test', text, hasRealE2eCoverage: true }).codes.includes('silent-validation-skip')) return [];
  const { codeNoStrings, stringLiteralsByOpenPos } = scanSourceWithMetrics(text, detectLang(testPath)), s = detectExecutionSignals(testPath, codeNoStrings, stringLiteralsByOpenPos);
  return [...(s.hasBrowser ? ['browser-playwright'] : []), ...(s.hasServerOrDb ? ['local-server-or-db'] : []), ...(s.hasRealSubprocess ? ['subprocess-cli'] : []), ...(s.hasLiveBinding ? ['live-binding'] : []), ...(s.hasRealHostSmoke ? ['real-host-smoke'] : []), ...(s.hasAnyRealExec || !MOCK_USAGE_RE.test(codeNoStrings) ? ['real-execution'] : [])].sort();
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
    const mockLine = boundarySurfaces.length ? maskedLines.findIndex((l) => MOCK_USAGE_RE.test(l)) : -1;
    if (mockLine >= 0 && !detectExecutionSignals(filePath, codeNoStrings, stringLiteralsByOpenPos).hasAnyRealExec) {
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
      if (detectExecutionSignals(rel, codeNoStrings, stringLiteralsByOpenPos).hasAnyRealExec) for (const t of boundary.boundaryTargets) covered.add(t);
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
