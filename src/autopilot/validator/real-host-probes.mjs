// Generated from prompts/cli/autopilot-validator.prompt.md (sha256: 75fde4547979ce8f760b5cb49996fe40b92c8567837622ceac4c2dd1c41f41ce).
export const MOCK_USAGE_RE = /\b(?:mock\.|vi\.mock|vi\.doMock|vi\.fn|vi\.spyOn|vi\.stubGlobal|jest\.mock|jest\.doMock|jest\.fn|jest\.spyOn|sinon\.stub|MagicMock|unittest\.mock|fakeClient|fakeServer|fakeTransport|fakeSandbox|mockSandbox|stubSandbox|fakeTty|mockTty|stubTty|fakeDb|mockDb|fakeDriver|mockDriver|mockSpawn|fakeSpawn|fakeSubprocess|fakeCli|stubCli)\b|stub(?:bed)?(?:Handler|Wrapper)/i;
export const REAL_E2E_EXEC_RE = /\b(?:spawn|spawnSync|execFile|execFileSync|execSync|createServer|playwright|puppeteer|supertest|DatabaseSync)\b|\.\s*listen\s*\(|\bfetch\s*\(|\bhttps?\.request\s*\(|\b(?:chromium|firefox|webkit)\.launch\s*\(|\bpage\.goto\s*\(/i;
export const POLYGLOT_MOCK_USAGE_RE = /\b(?:AsyncMock|monkeypatch\.setattr|mocker\.patch|gomock|mockall|httptest\.NewRecorder)\b|#\[automock\]/i;
export const REAL_DEVICE_PATH_RE = /\/dev\/(?:tty|ptmx|pts\/)/;
export const SANDBOX_EXEC_RE = /\b(?:sandbox-exec|sandbox_apply|bwrap|bubblewrap|seatbelt|seccomp|landlock|unshare|chroot|firejail)\b/i;
export const TRIVIAL_SUBPROCESS_BIN_RE = /^(?:echo|printf|true|false|pwd|uname|whoami|id|date|sleep|cat|ls|test|\[|:)(?:\s|$)/i;
export const SHELL_RUNTIME_RE = /^(?:sh|bash|zsh|dash|fish|cmd|cmd\.exe|powershell|pwsh|node|nodejs|python|python3|ruby|deno|bun|tsx|ts-node)$/i;
export const EXTERNAL_TOOL_EXEC_RE = /\b(?:gcloud|gsutil|bq|aws|az|stripe|docker|docker-compose|kubectl|helm|terraform|gh|pdd|curl|wget|psql|mysql|redis-cli|mongosh|ssh|scp|vault|npm|npx|git)\b/i;
export const GENERIC_CALL_RE = /(?<![A-Za-z0-9_$])([A-Za-z_$][A-Za-z0-9_$]*)(?:\s*\.\s*([A-Za-z_$][A-Za-z0-9_$]*))?[ \t]*\(/g;
export const SUBPROCESS_ORIG_NAMES = new Set(['spawn', 'spawnSync', 'execFile', 'execFileSync', 'execSync']);

const GENERIC_NEW_RE = /\bnew[ \t]+([A-Za-z_$][A-Za-z0-9_$]*)(?:\s*\.\s*([A-Za-z_$][A-Za-z0-9_$]*))?[ \t]*\(/g;
const FS_DEVICE_ORIG_NAMES = new Set(['openSync', 'open', 'statSync', 'stat', 'fstatSync', 'fstat', 'lstatSync', 'lstat', 'accessSync', 'access', 'createReadStream', 'createWriteStream']);
const FS_STATE_ORIG_NAMES = new Set(['mkdtempSync', 'mkdtemp', 'readdirSync', 'readdir', 'existsSync', 'readFileSync', 'readFile', 'statSync', 'stat', 'lstatSync', 'lstat', 'accessSync']);
const HTTP_ORIG_NAMES = new Set(['createServer', 'request']);
const TTY_CTOR_ORIG_NAMES = new Set(['ReadStream', 'WriteStream']);
const TTY_CALL_ORIG_NAMES = new Set(['isatty']);
const TTY_PTY_ORIG_NAMES = new Set(['spawn']);
const DB_CTOR_ORIG_NAMES = new Set(['DatabaseSync']);
const BROWSER_METHOD_NAMES = new Set(['launch', 'launchPersistentContext', 'goto', 'newPage', 'newContext', 'connect', 'connectOverCDP', 'pages']);
const BROWSER_WELL_KNOWN_VARS = new Set(['page', 'browser', 'context', 'chromium', 'firefox', 'webkit']);
const GLOBAL_OBJ_NAMES = new Set(['globalThis', 'global', 'window', 'self']);
const PRIMITIVE_SHADOW_NAMES = new Set([
  'spawn', 'spawnSync', 'execFile', 'execFileSync', 'execSync', 'createServer', 'fetch', 'DatabaseSync',
  'openSync', 'open', 'statSync', 'stat', 'fstatSync', 'fstat', 'lstatSync', 'lstat', 'accessSync', 'access',
  'mkdtempSync', 'mkdtemp', 'readdirSync', 'readdir', 'existsSync', 'readFileSync', 'readFile',
  'createReadStream', 'createWriteStream', 'isatty', 'ReadStream', 'WriteStream',
]);
const METHOD_STUB_NAMES = new Set([...PRIMITIVE_SHADOW_NAMES, 'request', 'listen', ...BROWSER_METHOD_NAMES]);

const MODULE_MOCK_CALL_RE = /\b(?:(?:vi|jest)\.(?:mock|doMock)|mock\.module)[ \t]*\(\s*("")/g;
const ESM_IMPORT_RE = /(?<!\.)\bimport\s+([A-Za-z_$*{][A-Za-z0-9_$,*{}\s]{0,1000})\bfrom\s*("")/g;
const CJS_REQUIRE_RE = /\b(?:const|let|var)[ \t]+([A-Za-z_$][A-Za-z0-9_$]*|\{[A-Za-z0-9_$,:=\s]{1,300}\})[ \t]*=[ \t]*require[ \t]*\(\s*("")\s*\)(?:\s*\.\s*([A-Za-z_$][A-Za-z0-9_$]*))?/g;
const SHADOW_DECL_LIST_RE = /\b(?:const|let|var)[ \t]+([^;\n]{1,300})/g;
const SHADOW_DESTRUCTURE_RE = /\b(?:const|let|var)[ \t]*\{([^};]{1,200})\}[ \t]*=[ \t]*\r?\n?[ \t]*([^;\n]{0,200})/g;
const SHADOW_ARRAY_DESTRUCTURE_RE = /\b(?:const|let|var)[ \t]*\[([^\];]{1,200})\][ \t]*=[ \t]*\r?\n?[ \t]*([^;\n]{0,200})/g;
const SHADOW_FN_RE = /\bfunction[ \t]+([A-Za-z_$][A-Za-z0-9_$]*)[ \t]*\(/g;
const SHADOW_CLASS_RE = /\bclass[ \t]+([A-Za-z_$][A-Za-z0-9_$]*)(?![A-Za-z0-9_$])/g;
const GLOBAL_FETCH_PROP_ASSIGN_RE = /\b(?:globalThis|global|window|self)\s*\.\s*fetch\s*(?:&&|\|\||\?\?)?=(?![=>])/;
const BARE_FETCH_ASSIGN_RE = /(?<![A-Za-z0-9_$.])fetch\s*(?:&&|\|\||\?\?)?=(?![=>])/g;
const PROP_ASSIGN_STUB_RE = /(?<![A-Za-z0-9_$])([A-Za-z_$][A-Za-z0-9_$]*)\s*\.\s*(spawn|spawnSync|execFile|execFileSync|execSync|openSync|open|statSync|stat|fstatSync|fstat|lstatSync|lstat|accessSync|access|mkdtempSync|mkdtemp|readdirSync|readdir|existsSync|readFileSync|readFile|createReadStream|createWriteStream|createServer|request|listen|fetch|isatty|ReadStream|WriteStream|DatabaseSync|launch|launchPersistentContext|goto|newPage|newContext|connect|connectOverCDP|pages)\s*(?:&&|\|\||\?\?)?=(?![=>])/g;
const BRACKET_ASSIGN_STUB_RE = /(?<![A-Za-z0-9_$])([A-Za-z_$][A-Za-z0-9_$]*)\s*\[[ \t]*("")[ \t]*\]\s*(?:&&|\|\||\?\?)?=(?![=>])/g;
const DEFINE_PROP_STUB_RE = /\bObject\.defineProperty[ \t]*\(\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*,\s*("")/g;
const STUB_GLOBAL_CALL_RE = /\bvi\.stubGlobal[ \t]*\(\s*("")/g;
const METHOD_STUB_RE = /\b(?:mock\.method|vi\.spyOn|jest\.spyOn|sinon\.stub)[ \t]*\(\s*([^,\n)]{1,120}),\s*("")/g;
const BROWSER_ORIGIN_RHS_RE = /(?<![A-Za-z0-9_$])([A-Za-z_$][A-Za-z0-9_$]*)\s*\.\s*(launch|launchPersistentContext|newPage|newContext|connect|connectOverCDP|pages)[ \t]*\(/;
const BARE_BROWSER_REASSIGN_RE = /(?<![A-Za-z0-9_$.])(page|browser|context|chromium|firefox|webkit)\s*(?:&&|\|\||\?\?)?=(?![=>])[ \t]*\r?\n?[ \t]*([^;\n]{0,200})/g;
const BARE_IDENT_ASSIGN_RE = /(?<![A-Za-z0-9_$.])([A-Za-z_$][A-Za-z0-9_$]*)\s*(?:&&|\|\||\?\?)?=(?![=>])/g;
const VALID_IDENT_RE = /^[A-Za-z_$][A-Za-z0-9_$]*$/;

export const detectLang = (p) => (/\.py$/i.test(p) ? 'py' : /\.go$/i.test(p) ? 'go' : /\.rs$/i.test(p) ? 'rs' : 'js');

export function extractCallArgsSlice(text, openParenIdx, maxLen = 240) {
  if (typeof text !== 'string' || openParenIdx < 0 || text[openParenIdx] !== '(') return { slice: '', startIdx: openParenIdx + 1, endIdx: openParenIdx + 1, closed: false };
  const startIdx = openParenIdx + 1, limit = Math.min(text.length, startIdx + maxLen);
  let depth = 1, quote = '';
  for (let i = startIdx; i < limit; i += 1) {
    const ch = text[i];
    if (quote) { if (ch === '\\' && i + 1 < limit) i += 1; else if (ch === quote) quote = ''; continue; }
    if (ch === '"' || ch === '\'' || ch === '`') quote = ch;
    else if (ch === '(') depth += 1;
    else if (ch === ')' && --depth === 0) return { slice: text.slice(startIdx, i), startIdx, endIdx: i, closed: true };
  }
  return { slice: text.slice(startIdx, limit), startIdx, endIdx: limit, closed: false };
}

export function collectLiteralsInMaskedSlice(slice, sliceStartIdx, litMap) {
  const out = [];
  if (!(litMap instanceof Map) || !slice) return out;
  for (let k = 0; k < slice.length; k += 1) {
    if (slice[k] !== '"') continue;
    const lit = litMap.get(sliceStartIdx + k);
    if (lit !== undefined) out.push({ value: lit, sliceStart: k });
    k += 1;
    while (k < slice.length && slice[k] !== '"') k += 1;
  }
  return out;
}

export function splitLinesWithOffsets(text) {
  const out = [];
  for (let start = 0; start <= text.length;) {
    const nl = text.indexOf('\n', start);
    if (nl < 0) { out.push({ line: text.endsWith('\r') && start < text.length ? text.slice(start, -1) : text.slice(start), offset: start }); break; }
    out.push({ line: text.slice(start, nl > start && text[nl - 1] === '\r' ? nl - 1 : nl), offset: start });
    start = nl + 1;
  }
  return out;
}

export function hasLeadingDot(text, idx) {
  let j = idx - 1;
  while (j >= 0 && /\s/.test(text[j])) j -= 1;
  return j >= 0 && text[j] === '.';
}

export function resolveLeadingMemberReceiver(text, idx) {
  let j = idx - 1;
  while (j >= 0 && /\s/.test(text[j])) j -= 1;
  if (j < 0 || text[j] !== '.') return { hasDot: false, receiver: '' };
  j -= 1;
  while (j >= 0 && /\s/.test(text[j])) j -= 1;
  if (j < 0 || !/[A-Za-z0-9_$]/.test(text[j])) return { hasDot: true, receiver: '' };
  const end = j + 1;
  while (j >= 0 && /[A-Za-z0-9_$]/.test(text[j])) j -= 1;
  const start = j + 1, ident = text.slice(start, end);
  if (!/^[A-Za-z_$]/.test(ident) || hasLeadingDot(text, start)) return { hasDot: true, receiver: '' };
  return { hasDot: true, receiver: ident };
}

function classifyImportedModule(spec) {
  const s = String(spec ?? '').trim().toLowerCase();
  if (!s) return null;
  if (/^(?:node:)?child_process$/.test(s)) return 'child_process';
  if (/^(?:node:)?fs(?:\/promises)?$/.test(s)) return 'fs';
  if (/^(?:node:)?(?:https?|http2|net)$|^(?:supertest|express|fastify|koa|hono)$/.test(s)) return 'http';
  if (/^(?:node:)?tty$|^node-pty$/.test(s)) return 'tty';
  if (/^(?:node:sqlite|pg|mysql2?|better-sqlite3|sqlite3?|mongodb|redis|ioredis|@prisma\/client)$/.test(s)) return 'db';
  if (/^(?:@playwright\/test|playwright(?:-core|-chromium|-firefox|-webkit)?|puppeteer(?:-core)?)$/.test(s)) return 'browser';
  if (/^(?:@google-cloud\/.+|@aws-sdk\/.+|aws-sdk|stripe|dockerode|@kubernetes\/client-node|@octokit\/.+|googleapis)$/.test(s)) return 'external-sdk';
  return null;
}

function extractBindingNamesFromClause(clause) {
  const namespaces = [], named = new Map(), tr = String(clause ?? '').trim();
  if (!tr) return { namespaces, named };
  const nsMatch = /\*\s+as\s+([A-Za-z_$][A-Za-z0-9_$]*)/.exec(tr);
  if (nsMatch) namespaces.push(nsMatch[1]);
  const bs = tr.indexOf('{'), be = tr.lastIndexOf('}');
  if (bs >= 0 && be > bs) {
    const before = tr.slice(0, bs).replace(/,\s*$/, '').trim();
    if (VALID_IDENT_RE.test(before)) namespaces.push(before);
    for (const part of tr.slice(bs + 1, be).split(',')) {
      const piece = part.split('=')[0].trim();
      if (!piece || /^type\s+/.test(piece)) continue;
      const alias = /^([A-Za-z_$][A-Za-z0-9_$]*)(?:\s+as\s+|\s*:\s*)([A-Za-z_$][A-Za-z0-9_$]*)$/.exec(piece);
      if (alias) { if (alias[1] === 'default') namespaces.push(alias[2]); else named.set(alias[2], alias[1]); }
      else if (VALID_IDENT_RE.test(piece)) named.set(piece, piece);
    }
  } else if (!nsMatch && VALID_IDENT_RE.test(tr)) namespaces.push(tr);
  return { namespaces, named };
}

function splitTopLevelDeclaratorsWithOffsets(listText, listStartOffset) {
  const out = [];
  let start = 0, depth = 0;
  for (let i = 0; i < listText.length; i += 1) {
    const ch = listText[i];
    if (ch === '(' || ch === '{' || ch === '[') depth += 1;
    else if (ch === ')' || ch === '}' || ch === ']') depth = Math.max(0, depth - 1);
    else if (ch === ',' && depth === 0) { out.push({ text: listText.slice(start, i), offset: listStartOffset + start }); start = i + 1; }
  }
  out.push({ text: listText.slice(start), offset: listStartOffset + start });
  return out;
}

function splitDeclaratorLhsRhs(piece) {
  let depth = 0;
  for (let k = 0; k < piece.length; k += 1) {
    const ch = piece[k];
    if (ch === '{' || ch === '[' || ch === '(') depth += 1;
    else if (ch === '}' || ch === ']' || ch === ')') depth = Math.max(0, depth - 1);
    else if (ch === '=' && depth === 0 && piece[k + 1] !== '=' && piece[k + 1] !== '>') return { lhs: piece.slice(0, k).trim(), hasEq: true, rhs: piece.slice(k + 1).trim() };
  }
  return { lhs: piece.trim(), hasEq: false, rhs: '' };
}

function extractBoundIdentsFromPattern(rawPattern) {
  const out = [], p = String(rawPattern ?? '').trim();
  if (!p) return out;
  if ((p.startsWith('{') && p.endsWith('}')) || (p.startsWith('[') && p.endsWith(']'))) {
    const isObj = p[0] === '{';
    for (const entry of splitTopLevelDeclaratorsWithOffsets(p.slice(1, -1), 0)) {
      let part = entry.text.trim();
      if (!part) continue;
      if (part.startsWith('...')) { const r = part.slice(3).trim(); if (VALID_IDENT_RE.test(r)) out.push(r); continue; }
      let target = part;
      if (isObj) {
        let colon = -1, d = 0;
        for (let k = 0; k < part.length; k += 1) {
          const ch = part[k];
          if (ch === '{' || ch === '[' || ch === '(') d += 1;
          else if (ch === '}' || ch === ']' || ch === ')') d = Math.max(0, d - 1);
          else if (ch === ':' && d === 0) { colon = k; break; }
          else if (ch === '=' && d === 0) break;
        }
        if (colon >= 0) target = part.slice(colon + 1).trim();
      }
      const lhs = splitDeclaratorLhsRhs(target).lhs;
      if (lhs.startsWith('{') || lhs.startsWith('[')) out.push(...extractBoundIdentsFromPattern(lhs));
      else if (VALID_IDENT_RE.test(lhs)) out.push(lhs);
    }
    return out;
  }
  if (VALID_IDENT_RE.test(p)) out.push(p);
  return out;
}

export function analyzePrimitiveAuthenticity(codeNoStrings, litMap) {
  const litAt = (m) => { const rel = litMap instanceof Map ? m[0].lastIndexOf('""') : -1; return rel < 0 ? '' : (litMap.get((m.index ?? 0) + rel) ?? ''); };
  const mockedModules = new Set(), importedModules = new Set(), namespaceBindings = new Map(), namedBindings = new Map();
  const allNamespaceIdents = new Set(), allImportedLocalNames = new Set(), shadowedPrimitives = new Set(), shadowedNamespaces = new Set();
  const stubbedNamespaceMethods = new Set(), shadowedBrowserVars = new Set(), cleanBrowserVars = new Set(), browserVarDeps = [], authReqSpans = [];
  let hasNodePtyImport = false, hasNonSqliteDbImport = false, hasPlaywrightTestImport = false;

  for (const m of codeNoStrings.matchAll(MODULE_MOCK_CALL_RE)) { const c = classifyImportedModule(litAt(m)); if (c) mockedModules.add(c); }
  const addImport = (spec, clause, propAccess = '') => {
    const tr = String(clause ?? '').trim();
    if (!tr || /^type\s+/.test(tr)) return null;
    const { namespaces, named } = extractBindingNamesFromClause(tr);
    if (propAccess && namespaces.length === 1 && named.size === 0) { named.set(namespaces[0], propAccess); namespaces.length = 0; }
    if (!namespaces.length && !named.size) return null;
    const lo = String(spec ?? '').trim().toLowerCase(), bound = [...namespaces, ...named.keys()], cat = classifyImportedModule(spec);
    if (!cat) {
      for (const l of bound) { if (l === 'fetch') { if (!lo.startsWith('node:')) shadowedPrimitives.add('fetch'); } else if (PRIMITIVE_SHADOW_NAMES.has(l)) shadowedPrimitives.add(l); }
    } else if (bound.includes('fetch') && !lo.startsWith('node:')) shadowedPrimitives.add('fetch');
    if (cat !== 'browser') for (const l of bound) shadowedBrowserVars.add(l);
    if (!cat || mockedModules.has(cat)) return cat;
    if (lo === 'node-pty') hasNodePtyImport = true;
    if (lo === '@playwright/test') hasPlaywrightTestImport = true;
    if (cat === 'db' && lo !== 'node:sqlite') hasNonSqliteDbImport = true;
    importedModules.add(cat);
    if (!namespaceBindings.has(cat)) namespaceBindings.set(cat, new Set());
    for (const n of namespaces) { namespaceBindings.get(cat).add(n); allNamespaceIdents.add(n); }
    if (!namedBindings.has(cat)) namedBindings.set(cat, new Map());
    for (const [l, o] of named) { namedBindings.get(cat).set(l, o); allImportedLocalNames.add(l); }
    return cat;
  };
  for (const m of codeNoStrings.matchAll(ESM_IMPORT_RE)) addImport(litAt(m), m[1]);
  for (const m of codeNoStrings.matchAll(CJS_REQUIRE_RE)) { const cat = addImport(litAt(m), m[1], m[3] ?? ''); if (cat) authReqSpans.push([m.index ?? 0, (m.index ?? 0) + m[0].length]); }
  const inAuthReq = (idx) => authReqSpans.some(([s, e]) => idx >= s && idx < e);

  const recordPropStub = (rcv, method) => {
    if (!METHOD_STUB_NAMES.has(method)) return;
    if (GLOBAL_OBJ_NAMES.has(rcv)) { shadowedPrimitives.add(method); return; }
    if (allNamespaceIdents.has(rcv)) { stubbedNamespaceMethods.add(`${rcv}.${method}`); shadowedPrimitives.add(method); return; }
    if (BROWSER_METHOD_NAMES.has(method) || BROWSER_WELL_KNOWN_VARS.has(rcv)) stubbedNamespaceMethods.add(`${rcv}.${method}`);
  };
  if (GLOBAL_FETCH_PROP_ASSIGN_RE.test(codeNoStrings)) shadowedPrimitives.add('fetch');
  if (!shadowedPrimitives.has('fetch')) for (const m of codeNoStrings.matchAll(BARE_FETCH_ASSIGN_RE)) if (!hasLeadingDot(codeNoStrings, m.index ?? 0)) { shadowedPrimitives.add('fetch'); break; }
  for (const m of codeNoStrings.matchAll(PROP_ASSIGN_STUB_RE)) if (!hasLeadingDot(codeNoStrings, m.index ?? 0)) recordPropStub(m[1], m[2]);
  for (const m of codeNoStrings.matchAll(BRACKET_ASSIGN_STUB_RE)) if (!hasLeadingDot(codeNoStrings, m.index ?? 0)) recordPropStub(m[1], litAt(m));
  for (const m of codeNoStrings.matchAll(DEFINE_PROP_STUB_RE)) recordPropStub(m[1], litAt(m));
  for (const m of codeNoStrings.matchAll(STUB_GLOBAL_CALL_RE)) { const t = litAt(m); if (t === 'fetch' || PRIMITIVE_SHADOW_NAMES.has(t)) shadowedPrimitives.add(t); }
  for (const m of codeNoStrings.matchAll(METHOD_STUB_RE)) { const t = litAt(m); if (METHOD_STUB_NAMES.has(t)) shadowedPrimitives.add(t); }

  const parseBrowserOrigin = (rhs) => {
    const tr = String(rhs ?? '').trim();
    if (!tr || tr.startsWith('{') || /\b(?:fake|mock|stub|vi\.|jest\.)/i.test(tr)) return null;
    const o = BROWSER_ORIGIN_RHS_RE.exec(tr);
    if (!o || hasLeadingDot(tr, o.index)) return null;
    const [, rcv, met] = o;
    if (shadowedPrimitives.has(met) || stubbedNamespaceMethods.has(`${rcv}.${met}`) || /^(?:fake|mock|stub)/i.test(rcv) || shadowedBrowserVars.has(rcv) || shadowedNamespaces.has(rcv) || shadowedPrimitives.has(rcv)) return null;
    return { originReceiver: rcv, originMethod: met };
  };
  const recordDecl = (ident, hasEq, rhs) => {
    if (!VALID_IDENT_RE.test(ident)) return;
    if (PRIMITIVE_SHADOW_NAMES.has(ident) || allImportedLocalNames.has(ident)) shadowedPrimitives.add(ident);
    if (allNamespaceIdents.has(ident)) shadowedNamespaces.add(ident);
    const origin = hasEq ? parseBrowserOrigin(rhs) : null;
    if (origin) { cleanBrowserVars.add(ident); browserVarDeps.push({ ident, ...origin }); }
    else { shadowedBrowserVars.add(ident); cleanBrowserVars.delete(ident); }
  };

  for (const m of codeNoStrings.matchAll(SHADOW_DESTRUCTURE_RE)) if (!inAuthReq(m.index ?? 0)) for (const l of extractBoundIdentsFromPattern(`{${m[1]}}`)) recordDecl(l, true, m[2]);
  for (const m of codeNoStrings.matchAll(SHADOW_ARRAY_DESTRUCTURE_RE)) if (!inAuthReq(m.index ?? 0)) for (const l of extractBoundIdentsFromPattern(`[${m[1]}]`)) recordDecl(l, true, m[2]);
  for (const { line, offset } of splitLinesWithOffsets(codeNoStrings)) {
    for (const m of line.matchAll(SHADOW_DECL_LIST_RE)) {
      const listStart = offset + (m.index ?? 0) + m[0].length - m[1].length;
      for (const d of splitTopLevelDeclaratorsWithOffsets(m[1], listStart)) {
        const ws = d.text.length - d.text.trimStart().length;
        if (inAuthReq(d.offset + ws)) continue;
        const piece = d.text.trim();
        if (!piece) continue;
        let { lhs, hasEq, rhs } = splitDeclaratorLhsRhs(piece);
        if (!lhs) continue;
        if (hasEq && !rhs) { const after = codeNoStrings.slice(d.offset + d.text.length, d.offset + d.text.length + 512).replace(/^[ \t]*\r?\n[ \t]*/, ''); const stop = after.search(/[;\r\n]/); rhs = (stop < 0 ? after : after.slice(0, stop)).slice(0, 200).trim(); }
        for (const id of (lhs.startsWith('{') || lhs.startsWith('[') ? extractBoundIdentsFromPattern(lhs) : (VALID_IDENT_RE.test(lhs) ? [lhs] : []))) recordDecl(id, hasEq, rhs);
      }
    }
    for (const m of line.matchAll(SHADOW_FN_RE)) { if (PRIMITIVE_SHADOW_NAMES.has(m[1]) || allImportedLocalNames.has(m[1])) shadowedPrimitives.add(m[1]); if (allNamespaceIdents.has(m[1])) shadowedNamespaces.add(m[1]); if (BROWSER_WELL_KNOWN_VARS.has(m[1])) shadowedBrowserVars.add(m[1]); }
    for (const m of line.matchAll(SHADOW_CLASS_RE)) { if (PRIMITIVE_SHADOW_NAMES.has(m[1]) || allImportedLocalNames.has(m[1])) shadowedPrimitives.add(m[1]); if (allNamespaceIdents.has(m[1])) shadowedNamespaces.add(m[1]); }
  }
  if (allImportedLocalNames.size || allNamespaceIdents.size) {
    for (const m of codeNoStrings.matchAll(BARE_IDENT_ASSIGN_RE)) {
      const idx = m.index ?? 0;
      if (inAuthReq(idx) || hasLeadingDot(codeNoStrings, idx)) continue;
      if (allImportedLocalNames.has(m[1])) shadowedPrimitives.add(m[1]);
      if (allNamespaceIdents.has(m[1])) shadowedNamespaces.add(m[1]);
    }
  }
  for (const m of codeNoStrings.matchAll(BARE_BROWSER_REASSIGN_RE)) {
    const idx = m.index ?? 0;
    if (inAuthReq(idx) || hasLeadingDot(codeNoStrings, idx)) continue;
    const origin = parseBrowserOrigin(m[2] ?? '');
    if (!origin) { shadowedBrowserVars.add(m[1]); cleanBrowserVars.delete(m[1]); }
    else browserVarDeps.push({ ident: m[1], ...origin });
  }
  for (let changed = true; changed;) {
    changed = false;
    for (const { ident, originReceiver: r, originMethod: met } of browserVarDeps) {
      if (shadowedBrowserVars.has(ident)) continue;
      if (shadowedBrowserVars.has(r) || shadowedNamespaces.has(r) || shadowedPrimitives.has(r) || shadowedPrimitives.has(met) || stubbedNamespaceMethods.has(`${r}.${met}`)) {
        shadowedBrowserVars.add(ident); cleanBrowserVars.delete(ident); changed = true;
      }
    }
  }
  return { mockedModules, importedModules, namespaceBindings, namedBindings, shadowedPrimitives, shadowedNamespaces, stubbedNamespaceMethods, shadowedBrowserVars, cleanBrowserVars, hasNodePtyImport, hasNonSqliteDbImport, hasPlaywrightTestImport };
}

export function resolveAuthenticCall(auth, cat, allowed, local, rawRcv) {
  if (auth.mockedModules.has(cat) || !auth.importedModules.has(cat) || auth.shadowedPrimitives.has(local)) return null;
  const rcv = rawRcv ? rawRcv.trim().replace(/\.$/, '').trim() : '';
  if (rcv) return allowed.has(local) && !auth.shadowedNamespaces.has(rcv) && !auth.stubbedNamespaceMethods.has(`${rcv}.${local}`) && auth.namespaceBindings.get(cat)?.has(rcv) === true ? local : null;
  const orig = auth.namedBindings.get(cat)?.get(local);
  return orig && allowed.has(orig) && !auth.shadowedPrimitives.has(orig) ? orig : null;
}

export function detectJsTty(code, auth, litMap) {
  if (!auth.mockedModules.has('tty') && auth.importedModules.has('tty')) {
    for (const m of code.matchAll(GENERIC_NEW_RE)) if (resolveAuthenticCall(auth, 'tty', TTY_CTOR_ORIG_NAMES, m[2] || m[1], m[2] ? m[1] : '')) return true;
    for (const m of code.matchAll(GENERIC_CALL_RE)) {
      if (hasLeadingDot(code, m.index ?? 0)) continue;
      const r = m[2] ? m[1] : '', fn = m[2] || m[1];
      if (resolveAuthenticCall(auth, 'tty', TTY_CALL_ORIG_NAMES, fn, r) || (auth.hasNodePtyImport && resolveAuthenticCall(auth, 'tty', TTY_PTY_ORIG_NAMES, fn, r))) return true;
    }
  }
  if (auth.mockedModules.has('fs') || !auth.importedModules.has('fs')) return false;
  const devVars = new Set();
  if (litMap instanceof Map) for (const m of code.matchAll(/\b(?:const|let|var)[ \t]+([A-Za-z_$][A-Za-z0-9_$]*)[ \t]*=[ \t]*("")/g)) if (REAL_DEVICE_PATH_RE.test(litMap.get((m.index ?? 0) + m[0].lastIndexOf('""')) ?? '')) devVars.add(m[1]);
  for (const m of code.matchAll(GENERIC_CALL_RE)) {
    if (hasLeadingDot(code, m.index ?? 0) || !resolveAuthenticCall(auth, 'fs', FS_DEVICE_ORIG_NAMES, m[2] || m[1], m[2] ? m[1] : '')) continue;
    const { slice, startIdx } = extractCallArgsSlice(code, (m.index ?? 0) + m[0].length - 1, 240);
    if (!slice) continue;
    if (collectLiteralsInMaskedSlice(slice, startIdx, litMap).some((x) => REAL_DEVICE_PATH_RE.test(x.value))) return true;
    if (devVars.size) for (const id of slice.matchAll(/(?<![A-Za-z0-9_$])[A-Za-z_$][A-Za-z0-9_$]*(?![A-Za-z0-9_$])/g)) {
      if (!devVars.has(id[0])) continue;
      const bef = slice.slice(0, id.index ?? 0).trimEnd(), aft = slice.slice((id.index ?? 0) + id[0].length).trimStart();
      if (bef.endsWith('.') || ((bef.endsWith('{') || bef.endsWith(',')) && aft.startsWith(':'))) continue;
      return true;
    }
  }
  return false;
}

export function detectJsServerOrDb(code, auth) {
  if (!auth.shadowedPrimitives.has('fetch')) {
    for (const m of code.matchAll(/(?<![A-Za-z0-9_$.])\bfetch\s*\(/g)) {
      const idx = m.index ?? 0;
      if (hasLeadingDot(code, idx) || /\b(?:async|static|get|set|function|abstract|public|private|protected|override|declare)[ \t]+$/.test(code.slice(Math.max(0, idx - 32), idx))) continue;
      const args = extractCallArgsSlice(code, idx + m[0].length - 1, 240);
      if (args.closed) {
        let a = args.endIdx + 1; while (a < code.length && /\s/.test(code[a])) a += 1;
        if (code[a] === '{') continue;
        if (code[a] === ':') {
          let k = a + 1, lim = Math.min(code.length, k + 200), ang = 0, par = 0, brk = 0, brc = 0, saw = false, prev = '', isBody = false;
          while (k < lim) {
            const c = code[k];
            if (!ang && !par && !brk && !brc && (c === ';' || ((c === '\n' || c === '\r') && prev !== '|' && prev !== '&'))) break;
            if (c === '=' && code[k + 1] === '>') { if (!ang && !par && !brk && !brc) break; prev = '>'; k += 2; continue; }
            if (c === '<') { ang += 1; saw = true; prev = c; } else if (c === '>') { ang = Math.max(0, ang - 1); prev = c; }
            else if (c === '(') { par += 1; saw = true; prev = c; } else if (c === ')') { par = Math.max(0, par - 1); prev = c; }
            else if (c === '[') { brk += 1; saw = true; prev = c; } else if (c === ']') { brk = Math.max(0, brk - 1); prev = c; }
            else if (c === '{') { if (!ang && !par && !brk && !brc && saw && prev !== '|' && prev !== '&') { isBody = true; break; } brc += 1; saw = true; prev = c; }
            else if (c === '}') { brc = Math.max(0, brc - 1); prev = c; }
            else if (c !== ' ' && c !== '\t' && c !== '\n' && c !== '\r') { saw = true; prev = c; }
            k += 1;
          }
          if (isBody) continue;
        }
      }
      return true;
    }
  }
  if (!auth.mockedModules.has('http') && auth.importedModules.has('http')) {
    for (const m of code.matchAll(GENERIC_CALL_RE)) if (!hasLeadingDot(code, m.index ?? 0) && resolveAuthenticCall(auth, 'http', HTTP_ORIG_NAMES, m[2] || m[1], m[2] ? m[1] : '')) return true;
    if (!auth.shadowedPrimitives.has('listen') && /\.\s*listen\s*\(/.test(code) && !/\b(?:fake|mock|stub)[A-Za-z0-9_$]*\s*\.\s*listen\s*\(/i.test(code)) return true;
    if (/\bsupertest\s*\(/.test(code)) return true;
  }
  if (!auth.mockedModules.has('db') && auth.importedModules.has('db')) {
    for (const m of code.matchAll(GENERIC_NEW_RE)) if (resolveAuthenticCall(auth, 'db', DB_CTOR_ORIG_NAMES, m[2] || m[1], m[2] ? m[1] : '')) return true;
    if (auth.hasNonSqliteDbImport && (/\bnew\s+(?:Pool|Client)\s*\(/.test(code) || !MOCK_USAGE_RE.test(code))) return true;
  }
  return false;
}

export function detectJsBrowser(code, auth) {
  if (auth.mockedModules.has('browser') || !auth.importedModules.has('browser')) return false;
  const bad = (id) => /^(?:fake|mock|stub)/i.test(id) || auth.shadowedBrowserVars.has(id) || auth.shadowedNamespaces.has(id) || auth.shadowedPrimitives.has(id);
  for (const m of code.matchAll(/(?<![A-Za-z0-9_$])([A-Za-z_$][A-Za-z0-9_$]*)[ \t]*\.[ \t]*(?:([A-Za-z_$][A-Za-z0-9_$]*)[ \t]*\.[ \t]*)?(launch|launchPersistentContext|goto|newPage|newContext|connect|connectOverCDP)[ \t]*\(/g)) {
    if (hasLeadingDot(code, m.index ?? 0)) continue;
    const outer = m[2] ? m[1] : '', rcv = m[2] || m[1], met = m[3];
    if (auth.shadowedPrimitives.has(met) || auth.stubbedNamespaceMethods.has(`${rcv}.${met}`) || bad(rcv)) continue;
    if (outer && (auth.stubbedNamespaceMethods.has(`${outer}.${rcv}`) || bad(outer))) continue;
    if (met === 'goto' && !auth.hasPlaywrightTestImport && !auth.cleanBrowserVars.has(rcv)) continue;
    return true;
  }
  return false;
}

export function detectJsFsState(code, auth) {
  if (auth.mockedModules.has('fs') || !auth.importedModules.has('fs')) return false;
  for (const m of code.matchAll(GENERIC_CALL_RE)) {
    if (!hasLeadingDot(code, m.index ?? 0) && resolveAuthenticCall(auth, 'fs', FS_STATE_ORIG_NAMES, m[2] || m[1], m[2] ? m[1] : '')) return true;
  }
  return false;
}
