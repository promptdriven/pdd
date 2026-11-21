// Real JS/ESM lexical tokenizer, import/re-export/dynamic-import/createRequire/spawn parser, and ESM resolver.
import { builtinModules } from 'node:module';
import { posix } from 'node:path';

const BUILTINS = new Set(builtinModules.flatMap(m => [m, m.startsWith('node:') ? m.slice(5) : `node:${m}`]));
const REGEX_PREV_KEYWORDS = new Set([
  'return', 'throw', 'case', 'delete', 'void', 'typeof', 'in', 'instanceof', 'new', 'of', 'await', 'yield', 'else', 'do',
]);
const REGEX_PREV_PUNCTS = new Set([
  '(', '[', '{', ',', ';', ':', '?', '=', '!', '&', '|', '^', '~', '+', '-', '*', '%', '<', '>', '=>', '&&', '||', '??',
]);
const STMT_BOUNDARY_KEYWORDS = new Set([
  'import', 'export', 'const', 'let', 'var', 'function', 'class', 'await', 'return', 'if', 'for', 'while', 'try',
]);
const SPAWN_FNS = new Set(['spawn', 'spawnSync', 'execFile', 'execFileSync', 'fork', 'Worker']);
const REPO_JS_PATH_RE = /^(?:\.\.?\/)*(?:src|bin)\/[A-Za-z0-9_./-]+\.(?:mjs|js|cjs)$/;
const REL_JS_PATH_RE = /^\.\.?\/[A-Za-z0-9_./-]+\.(?:mjs|js|cjs)$/;
const NODE_EXEC_IDENT_RE = /^(?:execPath|nodePath|nodeBin|nodeExe|node)$/i;

export function tokenizeJs(source) {
  const tokens = [];
  const n = source.length;
  let i = 0;
  let line = 1;
  const tplDepthStack = [];
  let braceDepth = 0;

  if (source.startsWith('#!')) {
    const nl = source.indexOf('\n');
    i = nl < 0 ? n : nl + 1;
    if (nl >= 0) line = 2;
  }

  const allowsRegexAfter = () => {
    const prev = tokens.at(-1);
    if (!prev) return true;
    if (prev.kind === 'ident') return REGEX_PREV_KEYWORDS.has(prev.value);
    if (prev.kind === 'punct') return REGEX_PREV_PUNCTS.has(prev.value);
    return false;
  };

  const readString = quote => {
    const startLine = line;
    let out = '';
    i++;
    while (i < n && source[i] !== quote) {
      if (source[i] === '\\' && i + 1 < n) {
        const nxt = source[i + 1];
        if (nxt === '\n') line++;
        else out += nxt === 'n' ? '\n' : nxt === 'r' ? '\r' : nxt === 't' ? '\t' : nxt;
        i += 2;
        continue;
      }
      if (source[i] === '\n') line++;
      out += source[i++];
    }
    if (i < n) i++;
    tokens.push({ kind: 'string', value: out, line: startLine });
  };

  const readTemplateChunk = isStart => {
    const startLine = line;
    let out = '';
    while (i < n) {
      const ch = source[i];
      if (ch === '\\' && i + 1 < n) { if (source[i + 1] === '\n') line++; out += source[i + 1]; i += 2; continue; }
      if (ch === '`') { i++; tokens.push({ kind: isStart ? 'string' : 'tpl_end', value: out, line: startLine, ...(isStart ? { isTemplate: true } : {}) }); return; }
      if (ch === '$' && source[i + 1] === '{') { tokens.push({ kind: 'tpl_head', value: out, line: startLine }); i += 2; braceDepth++; tplDepthStack.push(braceDepth); return; }
      if (ch === '\n') line++;
      out += ch;
      i++;
    }
  };

  while (i < n) {
    const ch = source[i];
    if (ch === ' ' || ch === '\t' || ch === '\r' || ch === '\f' || ch === '\v') { i++; continue; }
    if (ch === '\n') { line++; i++; continue; }
    if (ch === '/' && source[i + 1] === '/') {
      const nl = source.indexOf('\n', i + 2);
      if (nl < 0) break;
      i = nl + 1;
      line++;
      continue;
    }
    if (ch === '/' && source[i + 1] === '*') {
      i += 2;
      while (i < n && !(source[i] === '*' && source[i + 1] === '/')) {
        if (source[i] === '\n') line++;
        i++;
      }
      i += 2;
      continue;
    }
    if (ch === '\'' || ch === '"') { readString(ch); continue; }
    if (ch === '`') { i++; readTemplateChunk(true); continue; }
    if (ch === '/' && allowsRegexAfter()) {
      const startLine = line;
      i++;
      let inClass = false;
      while (i < n) {
        const c = source[i];
        if (c === '\\' && i + 1 < n) { i += 2; continue; }
        if (c === '[') inClass = true;
        else if (c === ']') inClass = false;
        else if (c === '/' && !inClass) { i++; break; }
        else if (c === '\n') { line++; break; }
        i++;
      }
      while (i < n && /[a-z]/i.test(source[i])) i++;
      tokens.push({ kind: 'regex', value: '//', line: startLine });
      continue;
    }
    if (ch === '{') { braceDepth++; tokens.push({ kind: 'punct', value: '{', line }); i++; continue; }
    if (ch === '}') {
      if (tplDepthStack.length > 0 && tplDepthStack.at(-1) === braceDepth) {
        tplDepthStack.pop();
        braceDepth--;
        i++;
        readTemplateChunk(false);
        continue;
      }
      braceDepth = Math.max(0, braceDepth - 1);
      tokens.push({ kind: 'punct', value: '}', line });
      i++;
      continue;
    }
    if (/[A-Za-z_$]/.test(ch)) {
      const start = i;
      while (i < n && /[A-Za-z0-9_$]/.test(source[i])) i++;
      tokens.push({ kind: 'ident', value: source.slice(start, i), line });
      continue;
    }
    if (/[0-9]/.test(ch)) {
      const start = i;
      while (i < n && /[0-9a-fA-FxXoObBn._eE+-]/.test(source[i])) {
        if ((source[i] === '+' || source[i] === '-') && !/[eE]/.test(source[i - 1])) break;
        i++;
      }
      tokens.push({ kind: 'number', value: source.slice(start, i), line });
      continue;
    }
    const two = source.slice(i, i + 2);
    if (two === '=>' || two === '&&' || two === '||' || two === '??' || two === '?.') {
      tokens.push({ kind: 'punct', value: two, line });
      i += 2;
      continue;
    }
    tokens.push({ kind: 'punct', value: ch, line });
    i++;
  }
  return tokens;
}

function findMatchingDelim(tokens, openIdx, openCh, closeCh) {
  let depth = 0;
  for (let i = openIdx; i < tokens.length; i++) {
    if (tokens[i].kind === 'punct' && tokens[i].value === openCh) depth++;
    else if (tokens[i].kind === 'punct' && tokens[i].value === closeCh) {
      depth--;
      if (depth === 0) return i;
    }
  }
  return -1;
}

function splitTopLevelCallArgs(tokens, openIdx, closeIdx) {
  const args = [];
  let start = openIdx + 1;
  let depth = 0;
  for (let i = openIdx + 1; i < closeIdx; i++) {
    const v = tokens[i].kind === 'punct' ? tokens[i].value : '';
    if (v === '(' || v === '[' || v === '{') depth++;
    else if (v === ')' || v === ']' || v === '}') depth = Math.max(0, depth - 1);
    else if (v === ',' && depth === 0) {
      args.push([start, i]);
      start = i + 1;
    }
  }
  if (start < closeIdx) args.push([start, closeIdx]);
  return args;
}

function normalizeSpawnLiteral(raw, fromRelPath) {
  const clean = String(raw ?? '').trim().replace(/[?#].*$/, '').replace(/\\/g, '/');
  if (REPO_JS_PATH_RE.test(clean)) return posix.normalize(clean.replace(/^(?:\.\.?\/)+/, ''));
  if (REL_JS_PATH_RE.test(clean)) return posix.normalize(posix.join(posix.dirname(fromRelPath), clean));
  return null;
}

function extractJoinedRepoPath(tokens, start, end, relPath) {
  const strParts = [];
  for (let k = start; k < end; k++) {
    if (tokens[k].kind === 'string') {
      const direct = normalizeSpawnLiteral(tokens[k].value, relPath);
      if (direct && (direct.startsWith('src/') || direct.startsWith('bin/'))) return direct;
      strParts.push(tokens[k].value.replace(/\\/g, '/'));
    }
  }
  if (strParts.length >= 2) {
    const joined = normalizeSpawnLiteral(strParts.join('/'), relPath);
    if (joined && (joined.startsWith('src/') || joined.startsWith('bin/'))) return joined;
  }
  return null;
}

function isNodeExecutableArg(tokens, start, end) {
  for (let k = start; k < end; k++) {
    const tok = tokens[k];
    if (tok.kind === 'string') {
      const base = posix.basename(tok.value.replace(/\\/g, '/')).toLowerCase();
      if (base === 'node' || base === 'node.exe') return true;
    } else if (tok.kind === 'ident' && NODE_EXEC_IDENT_RE.test(tok.value)) {
      return true;
    }
  }
  return false;
}

function collectSpawnTargetsInRange(tokens, start, end, relPath, pathVars) {
  const targets = [];
  const seen = new Set();
  const add = t => { if (t && !seen.has(t)) { seen.add(t); targets.push(t); } };
  for (let k = start; k < end; k++) {
    const tok = tokens[k];
    if (tok.kind === 'string') {
      const norm = normalizeSpawnLiteral(tok.value, relPath);
      if (norm && (norm.startsWith('src/') || norm.startsWith('bin/'))) add(norm);
    } else if (tok.kind === 'ident' && (tok.value === 'join' || tok.value === 'resolve') && tokens[k + 1]?.value === '(') {
      const jClose = findMatchingDelim(tokens, k + 1, '(', ')');
      if (jClose > k + 1 && jClose <= end) add(extractJoinedRepoPath(tokens, k + 2, jClose, relPath));
    } else if (tok.kind === 'ident' && pathVars.has(tok.value)) {
      add(pathVars.get(tok.value));
    }
  }
  return targets;
}

function registerImportAliases(tokens, braceStart, braceEnd, spec, createRequireFns, spawnFnKind) {
  const isMod = spec === 'node:module' || spec === 'module';
  const isCp = spec === 'node:child_process' || spec === 'child_process';
  const isWt = spec === 'node:worker_threads' || spec === 'worker_threads';
  if (!isMod && !isCp && !isWt) return;
  for (let k = braceStart + 1; k < braceEnd; k++) {
    if (tokens[k].kind !== 'ident') continue;
    const orig = tokens[k].value;
    let local = orig;
    if (tokens[k + 1]?.kind === 'ident' && tokens[k + 1].value === 'as' && tokens[k + 2]?.kind === 'ident') {
      local = tokens[k + 2].value;
      k += 2;
    }
    if (isMod && orig === 'createRequire') createRequireFns.add(local);
    if (isCp && SPAWN_FNS.has(orig) && orig !== 'Worker') spawnFnKind.set(local, orig);
    if (isWt && orig === 'Worker') spawnFnKind.set(local, 'Worker');
  }
}

export function parseJsModuleEdges(source, relPath) {
  const tokens = tokenizeJs(source);
  const imports = [];
  const spawns = [];
  const createRequireFns = new Set(['createRequire']);
  const spawnFnKind = new Map([...SPAWN_FNS].map(fn => [fn, fn]));
  const requireIdents = new Set(['require']);
  const pathVars = new Map();

  // Pass 1A: discover hoisted static import aliases (`createRequire as mkReq`, `fork as spawnChild`) before scanning bindings/calls.
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    const prevIsDot = tokens[i - 1]?.kind === 'punct' && (tokens[i - 1].value === '.' || tokens[i - 1].value === '?.');
    if (t.kind !== 'ident' || t.value !== 'import' || prevIsDot || tokens[i + 1]?.value === '(' || tokens[i + 1]?.value === '.') continue;
    let braceStart = -1, braceEnd = -1, k = i + 1;
    while (k < tokens.length && k < i + 200) {
      const cur = tokens[k];
      if (cur.kind === 'punct' && cur.value === '{') {
        braceStart = k;
        braceEnd = findMatchingDelim(tokens, k, '{', '}');
        if (braceEnd < 0) break;
        k = braceEnd + 1;
        continue;
      }
      if (cur.kind === 'punct' && cur.value === ';') break;
      if (cur.kind === 'ident' && STMT_BOUNDARY_KEYWORDS.has(cur.value)) break;
      if (cur.kind === 'ident' && cur.value === 'from' && tokens[k + 1]?.kind === 'string') {
        if (braceStart >= 0 && braceEnd > braceStart) {
          registerImportAliases(tokens, braceStart, braceEnd, tokens[k + 1].value, createRequireFns, spawnFnKind);
        }
        break;
      }
      k++;
    }
  }

  // Pass 1B: discover require bindings, promisify aliases, and repo path constants.
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    if (t.kind !== 'ident' || (t.value !== 'const' && t.value !== 'let' && t.value !== 'var')) continue;
    const nameTok = tokens[i + 1];
    const eqTok = tokens[i + 2];
    if (nameTok?.kind !== 'ident' || eqTok?.kind !== 'punct' || eqTok.value !== '=') continue;
    const rhs0 = tokens[i + 3], rhs1 = tokens[i + 4], rhs2 = tokens[i + 5];
    if ((rhs0?.kind === 'ident' && createRequireFns.has(rhs0.value) && rhs1?.value === '(')
      || (rhs0?.kind === 'ident' && rhs1?.value === '.' && rhs2?.value === 'createRequire')) {
      requireIdents.add(nameTok.value);
    }
    if (rhs0?.kind === 'ident' && rhs0.value === 'promisify' && rhs1?.value === '(' && rhs2?.kind === 'ident' && spawnFnKind.has(rhs2.value)) {
      spawnFnKind.set(nameTok.value, spawnFnKind.get(rhs2.value));
    }
    let end = i + 3, depth = 0;
    while (end < tokens.length && end < i + 40) {
      const cur = tokens[end];
      if (cur.kind === 'punct' && (cur.value === '(' || cur.value === '[' || cur.value === '{')) depth++;
      else if (cur.kind === 'punct' && (cur.value === ')' || cur.value === ']' || cur.value === '}')) depth = Math.max(0, depth - 1);
      else if (depth === 0 && cur.kind === 'punct' && (cur.value === ';' || cur.value === ',')) break;
      else if (depth === 0 && cur.kind === 'ident' && STMT_BOUNDARY_KEYWORDS.has(cur.value)) break;
      end++;
    }
    const targetPath = extractJoinedRepoPath(tokens, i + 3, end, relPath);
    if (targetPath) pathVars.set(nameTok.value, targetPath);
  }

  // Pass 2: extract static imports, re-exports, dynamic imports, createRequire, and Node/fork/Worker path-string spawns.
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    const prevIsDot = tokens[i - 1]?.kind === 'punct' && (tokens[i - 1].value === '.' || tokens[i - 1].value === '?.');

    if (t.kind === 'ident' && t.value === 'import' && !prevIsDot) {
      const next = tokens[i + 1];
      if (!next || next.value === '.') continue;
      if (next.kind === 'punct' && next.value === '(') {
        const arg = tokens[i + 2], afterArg = tokens[i + 3];
        if (arg?.kind === 'string' && afterArg?.kind === 'punct' && (afterArg.value === ')' || afterArg.value === ',')) {
          imports.push({ kind: 'dynamic-import', specifier: arg.value, line: t.line });
        }
        continue;
      }
      if (next.kind === 'string') { imports.push({ kind: 'static-import', specifier: next.value, line: t.line }); continue; }
      let k = i + 1, depth = 0;
      while (k < tokens.length && k < i + 400) {
        const cur = tokens[k];
        if (cur.kind === 'punct' && cur.value === '{') depth++;
        else if (cur.kind === 'punct' && cur.value === '}') depth = Math.max(0, depth - 1);
        else if (depth === 0 && ((cur.kind === 'punct' && cur.value === ';') || (cur.kind === 'ident' && STMT_BOUNDARY_KEYWORDS.has(cur.value)))) break;
        else if (depth === 0 && cur.kind === 'ident' && cur.value === 'from' && tokens[k + 1]?.kind === 'string') {
          imports.push({ kind: 'static-import', specifier: tokens[k + 1].value, line: t.line });
          i = k + 1;
          break;
        }
        k++;
      }
      continue;
    }

    if (t.kind === 'ident' && t.value === 'export' && !prevIsDot) {
      const next = tokens[i + 1];
      if (next?.kind === 'punct' && next.value === '*') {
        if (tokens[i + 2]?.kind === 'ident' && tokens[i + 2].value === 'from' && tokens[i + 3]?.kind === 'string') {
          imports.push({ kind: 'reexport', specifier: tokens[i + 3].value, line: t.line });
          i += 3;
        } else if (tokens[i + 2]?.kind === 'ident' && tokens[i + 2].value === 'as' && tokens[i + 3]?.kind === 'ident'
          && tokens[i + 4]?.kind === 'ident' && tokens[i + 4].value === 'from' && tokens[i + 5]?.kind === 'string') {
          imports.push({ kind: 'reexport', specifier: tokens[i + 5].value, line: t.line });
          i += 5;
        }
      } else if (next?.kind === 'punct' && next.value === '{') {
        const closeBrace = findMatchingDelim(tokens, i + 1, '{', '}');
        if (closeBrace > i + 1) {
          if (tokens[closeBrace + 1]?.kind === 'ident' && tokens[closeBrace + 1].value === 'from' && tokens[closeBrace + 2]?.kind === 'string') {
            imports.push({ kind: 'reexport', specifier: tokens[closeBrace + 2].value, line: t.line });
            i = closeBrace + 2;
          } else {
            i = closeBrace;
          }
        }
      }
      continue;
    }

    if (t.kind === 'ident' && createRequireFns.has(t.value) && tokens[i + 1]?.value === '(') {
      const close = findMatchingDelim(tokens, i + 1, '(', ')');
      if (close > 0 && tokens[close + 1]?.value === '(' && tokens[close + 2]?.kind === 'string') {
        imports.push({ kind: 'create-require', specifier: tokens[close + 2].value, line: t.line });
      }
      continue;
    }

    if (t.kind === 'ident' && requireIdents.has(t.value) && !prevIsDot) {
      if (tokens[i + 1]?.value === '(' && tokens[i + 2]?.kind === 'string') {
        imports.push({ kind: 'create-require', specifier: tokens[i + 2].value, line: t.line });
      } else if (tokens[i + 1]?.value === '.' && tokens[i + 2]?.value === 'resolve' && tokens[i + 3]?.value === '(' && tokens[i + 4]?.kind === 'string') {
        imports.push({ kind: 'create-require', specifier: tokens[i + 4].value, line: t.line });
      }
      continue;
    }

    let canonicalKind = null;
    let callOpenIdx = -1;
    if (t.kind === 'ident' && spawnFnKind.has(t.value) && tokens[i + 1]?.value === '(') {
      canonicalKind = spawnFnKind.get(t.value);
      callOpenIdx = i + 1;
    } else if (t.kind === 'ident' && spawnFnKind.has(t.value) && tokens[i + 1]?.value === ')' && tokens[i + 2]?.value === '(') {
      canonicalKind = spawnFnKind.get(t.value);
      callOpenIdx = i + 2;
    }
    if (canonicalKind && callOpenIdx >= 0) {
      const callCloseIdx = findMatchingDelim(tokens, callOpenIdx, '(', ')');
      if (callCloseIdx > callOpenIdx) {
        const args = splitTopLevelCallArgs(tokens, callOpenIdx, callCloseIdx);
        if (!args.length) continue;
        let targets = [];
        if (canonicalKind === 'fork' || canonicalKind === 'Worker') {
          targets = collectSpawnTargetsInRange(tokens, args[0][0], args[0][1], relPath, pathVars);
        } else {
          const directCmd = collectSpawnTargetsInRange(tokens, args[0][0], args[0][1], relPath, pathVars);
          if (directCmd.length > 0) targets = directCmd;
          else if (isNodeExecutableArg(tokens, args[0][0], args[0][1]) && args.length >= 2) {
            targets = collectSpawnTargetsInRange(tokens, args[1][0], args[1][1], relPath, pathVars);
          }
        }
        for (const target of targets) spawns.push({ fn: canonicalKind, target, line: t.line });
      }
    }
  }
  return { imports, spawns };
}

export function resolveImportSpecifier(fromRelPath, spec, fileSet, kind = 'static-import') {
  const cleanSpec = String(spec ?? '').replace(/[?#].*$/, '');
  if (BUILTINS.has(cleanSpec) || cleanSpec.startsWith('node:')) return { kind: 'builtin', specifier: spec };
  if (cleanSpec.startsWith('./') || cleanSpec.startsWith('../') || cleanSpec.startsWith('/')) {
    const base = cleanSpec.startsWith('/') ? cleanSpec.slice(1) : posix.normalize(posix.join(posix.dirname(fromRelPath), cleanSpec));
    const isCjs = kind === 'create-require' || kind === 'require';
    const cands = isCjs
      ? [base, `${base}.mjs`, `${base}.js`, `${base}.cjs`, `${base}/index.mjs`, `${base}/index.js`, `${base}/index.cjs`]
      : [base, `${base}.mjs`, `${base}.js`, `${base}.cjs`];
    for (const cand of cands) {
      if (fileSet.has(cand)) return { kind: 'repo', target: cand };
    }
    return { kind: 'missing-local', target: base };
  }
  const pkg = cleanSpec.startsWith('@') ? cleanSpec.split('/').slice(0, 2).join('/') : cleanSpec.split('/')[0];
  return { kind: 'npm', packageName: pkg, specifier: spec };
}
