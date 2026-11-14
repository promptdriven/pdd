import { existsSync, readFileSync, readdirSync } from 'node:fs';
import { join, posix, resolve } from 'node:path';

const WINDOW = 50;
const MIN_CLONE_LINES = 5;
const BIG_FILE = 1500;
const HEADER_BYTES = 4096;
const SCAN_DIRS = ['src', 'bin', 'scripts', 'test', 'tests', 'prompts'];
const SKIP_DIRS = new Set(['.git', 'node_modules']);
const ESCAPE = 'ESCAPE';

const BOXES = {
  0: `secret-redaction toml-string github-calls cost-ledger machine-resources process-lifecycle approval-policy path-diagnostic
    prompt-tests-words runtime-exit test-selection codex-limits agent-config metrics-store metrics-hooks metrics-gap metrics-capture
    metrics-model validation-evidence test-suite-queue test-suite-recorder test-suite-entry workflow-runs
    workflow-run-lock workflow-chat-state command-routes github-issue-transport`,
  2: `runtime-seam runtime-api file-owner screen-compare screen-design-check svg-layout compiled-test interpreter-version try-doors
    product-documents`,
  3: `issue-dependencies-github issue-dependencies-intake issue-sort-github issue-dependencies issue-sort issue-mixed issue-claims
    autopilot autopilot-areas autopilot-parking autopilot-base autopilot-environment`,
  4: `workflow-runner workflow-chat workflow-results workflow-replay workflow-herdr-layout workflow-pr-body workflow-inventory
    workflow-github workflow-worktree workflow-story-card workflow-prove approval-evidence workflow-pr-evidence workflow-view
    workflow-agents workflow-worker-completion workflow-areas workflow-launch-profile workflow-small-change workflow-eligibility
    agent-adapters agent-job agent-mcp-setup prompt-approval workflow-status workflow-evidence-ledger workflow-pr-publish
    workflow-auto-pr1 workflow-step workflow-gates workflow-delivery workflow-parking workflow-open workflow-start
    workflow-chat-restart workflow-chat-cleanup`,
  5: `autopilot-core autopilot-launcher autopilot-alerts autopilot-audit autopilot-retire autopilot-intake autopilot-github
    autopilot-regressions autopilot-doctor autopilot-reports machine-guard product issue-dependency-graph issue-dependency-graph-view
    metrics-command autopilot-prompts autopilot-ci autopilot-evidence autopilot-merge autopilot-jobs autopilot-end`,
  6: `pdd pdd-cli argument-parser command-catalog completion project-setup project-files skills-install setup-interaction
    workflow-setup prompt-approve runtime-wiring`,
};
const BOX_OF = new Map(Object.entries(BOXES).flatMap(([box, names]) => names.split(/\s+/).filter(Boolean).map(name => [name, Number(box)])));

const PUNCTUATORS = new Set(['>>>=', '...', '===', '!==', '**=', '<<=', '>>=', '>>>', '&&=', '||=', '??=', '=>', '==', '!=', '<=', '>=',
  '&&', '||', '??', '?.', '++', '--', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '**', '<<', '>>']);
const WORDS_BEFORE_EXPRESSION = new Set(['return', 'typeof', 'instanceof', 'in', 'of', 'new', 'delete', 'void', 'throw', 'case', 'do',
  'else', 'yield', 'await', 'extends']);
const STATEMENT_WORDS = new Set(['export', 'import', 'const', 'let', 'var', 'function', 'class', 'if', 'for', 'while', 'return', 'throw',
  'try', 'switch', 'do']);
const ASSIGNMENTS = new Set(['=', '??=', '||=', '&&=']);
const ID_START = /[A-Za-z_$\u0080-\uffff]/;
const ID_PART = /[A-Za-z0-9_$\u0080-\uffff]/;
const SPACE = /[ \t\r\f\v\u00a0\ufeff\u2028\u2029]/;
const IDENTIFIER = /^[A-Za-z_$][\w$]*$/;
const WORD = /[A-Za-z_$][\w$]*/g;
const HEADER = /^(?:\/\/+\s*Generated from \S+\.prompt\.md(?: \(sha256: [a-f0-9]{64}\))?\.?\s*|\/\*+\s*Generated from \S+\.prompt\.md(?: \(sha256: [a-f0-9]{64}\))?\.?\s*\*\/)$/;
const LICENSE = /\b(?:SPDX-License-Identifier|@license|copyright|licensed under)\b/i;
const EXTERNAL = /^\/\/\s*external:/;
const INTERFACE = /<details\b[^>]*>\s*<summary\b[^>]*>\s*(?:<strong\b[^>]*>\s*)?Runtime\s+interface(?:\s*:\s*[^<]+?)?\s*(?:<\/strong\s*>\s*)?(?:\s*:\s*[^<]+?)?\s*<\/summary\s*>\s*```json\b\s*([\s\S]*?)\s*```\s*<\/details\s*>/gi;
const HISTORY = [
  /(?<![\w&])#\d{3,5}\b/g,
  /(?<![\w.])v?0\.1\.\d+\b(?!\.\d)/g,
  /\btesters?\b|\bround[- ]\d+\b|\b(?:Claude|Codex) rounds?\b|\bdebates?\b|\b\d{4} session\b/gi,
  /\b[Oo]ption [A-Z]\b/g,
];
const CLI_PROMPT = /^prompts\/cli\/[^/]+\.prompt\.md$/;

const segments = rel => rel.split('/');
const inRuntime = rel => segments(rel)[0] === 'src' && segments(rel)[1] === 'runtime';
const inVendor = rel => segments(rel)[0] === 'src' && segments(rel)[1] === 'vendor';
const isHost = rel => rel.endsWith('.mjs') && ((rel.startsWith('src/') && !inRuntime(rel) && !inVendor(rel)) || rel.startsWith('bin/'));
const isTest = rel => /^tests?\//.test(rel);
const isCode = rel => /\.(?:mjs|js)$/.test(rel) && !inVendor(rel) && /^(?:src|bin|scripts|tests?)\//.test(rel);
const moduleName = rel => posix.basename(rel).replace(/\.m?js$/, '');
const boxOf = rel => inRuntime(rel) ? 1 : BOX_OF.get(moduleName(rel)) ?? null;
const isRuntimeEntry = rel => inRuntime(rel) && segments(rel).slice(2).join('/') === 'index.mjs';
const isP = (t, v) => t !== undefined && t.t === 'p' && t.v === v;
const isId = (t, v) => t !== undefined && t.t === 'id' && (v === undefined || t.v === v);
const afterDot = (toks, i) => isP(toks[i - 1], '.') || isP(toks[i - 1], '?.');
const lineCount = text => text.length === 0 ? 0 : text.split('\n').length - (text.endsWith('\n') ? 1 : 0);

function walk(root, dir, out = []) {
  const abs = join(root, dir);
  if (!existsSync(abs)) return out;
  for (const entry of readdirSync(abs, { withFileTypes: true })) {
    if (SKIP_DIRS.has(entry.name)) continue;
    const rel = `${dir}/${entry.name}`;
    if (entry.isDirectory()) walk(root, rel, out);
    else if (entry.isFile()) out.push(rel);
  }
  return out;
}

function lex(src) {
  const toks = [], comments = [], braces = [];
  const n = src.length;
  let i = 0, line = 1, newline = false;
  const push = (t, v, at) => { toks.push({ t, v, line: at, nl: newline }); newline = false; };
  const regexAllowed = () => {
    const prev = toks[toks.length - 1];
    if (!prev) return true;
    if (prev.t === 'p') return prev.v !== ')' && prev.v !== ']' && prev.v !== '}';
    return prev.t === 'id' && WORDS_BEFORE_EXPRESSION.has(prev.v);
  };
  const template = first => {
    let raw = '';
    while (i < n) {
      const c = src[i];
      if (c === '\\') { raw += src.slice(i, i + 2); if (src[i + 1] === '\n') line++; i += 2; continue; }
      if (c === '`') { i++; push('tpl', raw, first); return; }
      if (c === '$' && src[i + 1] === '{') { i += 2; braces.push('tpl'); push('tpl', raw, first); return; }
      if (c === '\n') line++;
      raw += c; i++;
    }
    push('tpl', raw, first);
  };
  while (i < n) {
    const c = src[i];
    if (c === '\n') { line++; i++; newline = true; continue; }
    if (SPACE.test(c)) { i++; continue; }
    if (i === 0 && c === '#' && src[1] === '!') { while (i < n && src[i] !== '\n') i++; continue; }
    if (c === '/' && src[i + 1] === '/') {
      const at = i;
      while (i < n && src[i] !== '\n') i++;
      comments.push({ at, first: line, last: line, text: src.slice(at, i) });
      continue;
    }
    if (c === '/' && src[i + 1] === '*') {
      const at = i, first = line, close = src.indexOf('*/', i + 2), end = close < 0 ? n : close + 2;
      for (let k = i; k < end; k++) if (src[k] === '\n') line++;
      if (line > first) newline = true;
      comments.push({ at, first, last: line, text: src.slice(at, end) });
      i = end;
      continue;
    }
    if (c === '"' || c === "'") {
      const first = line;
      let v = '';
      i++;
      while (i < n && src[i] !== c && src[i] !== '\n') {
        if (src[i] === '\\') { v += src[i + 1] ?? ''; if (src[i + 1] === '\n') line++; i += 2; continue; }
        v += src[i]; i++;
      }
      if (src[i] === c) i++;
      push('str', v, first);
      continue;
    }
    if (c === '`') { i++; template(line); continue; }
    if (c === '}' && braces[braces.length - 1] === 'tpl') { braces.pop(); i++; template(line); continue; }
    if (c === '/' && regexAllowed()) {
      const first = line;
      let v = '', cls = false;
      i++;
      while (i < n && src[i] !== '\n') {
        const d = src[i];
        if (d === '\\') { v += src.slice(i, i + 2); i += 2; continue; }
        if (d === '[') cls = true;
        else if (d === ']') cls = false;
        else if (d === '/' && !cls) { i++; break; }
        v += d; i++;
      }
      while (i < n && ID_PART.test(src[i])) i++;
      push('re', v, first);
      continue;
    }
    if (ID_START.test(c)) {
      const at = i;
      while (i < n && ID_PART.test(src[i])) i++;
      push('id', src.slice(at, i), line);
      continue;
    }
    if ((c >= '0' && c <= '9') || (c === '.' && src[i + 1] >= '0' && src[i + 1] <= '9')) {
      const at = i;
      i++;
      while (i < n && /[0-9A-Za-z_.]/.test(src[i])) i++;
      push('num', src.slice(at, i), line);
      continue;
    }
    let v = c;
    for (const size of [4, 3, 2]) {
      const candidate = src.slice(i, i + size);
      if (PUNCTUATORS.has(candidate) && !(candidate === '?.' && src[i + 2] >= '0' && src[i + 2] <= '9')) { v = candidate; break; }
    }
    if (v === '{') braces.push('{');
    else if (v === '}') braces.pop();
    push('p', v, line);
    i += v.length;
  }
  return { toks, comments };
}

function parse(rel, text) {
  const { toks, comments } = lex(text);
  const pair = new Int32Array(toks.length).fill(-1), parent = new Int32Array(toks.length).fill(-1), depth = new Int32Array(toks.length);
  const stack = [];
  let braces = 0;
  for (let i = 0; i < toks.length; i++) {
    const t = toks[i];
    if (t.t === 'p' && (t.v === ')' || t.v === ']' || t.v === '}')) {
      if (stack.length) {
        const open = stack.pop();
        pair[open] = i; pair[i] = open; parent[i] = parent[open];
        if (toks[open].v === '{') braces--;
      }
      depth[i] = braces;
      continue;
    }
    parent[i] = stack.length ? stack[stack.length - 1] : -1;
    depth[i] = braces;
    if (t.t === 'p' && (t.v === '(' || t.v === '[' || t.v === '{')) { stack.push(i); if (t.v === '{') braces++; }
  }
  return { rel, text, toks, comments, pair, parent, depth };
}

function elements(F, open) {
  const { toks, pair, parent } = F, close = pair[open], out = [];
  if (close < 0) return out;
  let start = open + 1;
  for (let i = open + 1; i <= close; i++) {
    if (i === close || (parent[i] === open && isP(toks[i], ','))) { out.push([start, i]); start = i + 1; }
  }
  return out;
}

function objectKeys(F, open) {
  const keys = [];
  for (const [a, b] of elements(F, open)) {
    if (a >= b) continue;
    const t = F.toks[a];
    if (isP(t, '...')) return ESCAPE;
    if (t.t === 'id' || t.t === 'str' || t.t === 'num') keys.push(t.v);
  }
  return keys;
}

function patternBindings(F, open) {
  const { toks } = F, out = [], object = isP(toks[open], '{');
  for (const [a, b] of elements(F, open)) {
    if (a >= b) continue;
    let at = a;
    if (isP(toks[at], '...')) at++;
    else if (object && isP(toks[at + 1], ':')) at += 2;
    if (isId(toks[at])) out.push(at);
    else if ((isP(toks[at], '{') || isP(toks[at], '[')) && F.pair[at] > at) out.push(...patternBindings(F, at));
  }
  return out;
}

function skipExpression(F, start) {
  const { toks, pair } = F;
  for (let m = start; m < toks.length; m++) {
    const t = toks[m];
    if (m > start && t.nl && t.t === 'id' && STATEMENT_WORDS.has(t.v)) return m;
    if (t.t !== 'p') continue;
    if (t.v === ',' || t.v === ';' || t.v === ')' || t.v === ']' || t.v === '}') return m;
    if ((t.v === '(' || t.v === '[' || t.v === '{') && pair[m] > m) m = pair[m];
  }
  return toks.length;
}

function declarators(F, start) {
  const { toks, pair } = F, out = [];
  let m = start;
  while (m < toks.length) {
    if (isId(toks[m])) out.push(m++);
    else if ((isP(toks[m], '{') || isP(toks[m], '[')) && pair[m] > m) { out.push(...patternBindings(F, m)); m = pair[m] + 1; }
    else break;
    if (isP(toks[m], '=')) m = skipExpression(F, m + 1);
    if (!isP(toks[m], ',')) break;
    m++;
  }
  return out;
}

function staticImport(F, k) {
  const { toks, pair } = F;
  let m = k + 1;
  if (toks[m]?.t === 'str') return { spec: toks[m].v, names: [], locals: [] };
  const names = [], locals = [];
  let ns = null;
  if (isId(toks[m]) && (isP(toks[m + 1], ',') || isId(toks[m + 1], 'from'))) { names.push('default'); locals.push(toks[m].v); m += isP(toks[m + 1], ',') ? 2 : 1; }
  if (isP(toks[m], '*') && isId(toks[m + 1], 'as') && isId(toks[m + 2])) { ns = { ns: toks[m + 2].v, at: m + 2 }; m += 3; }
  else if (isP(toks[m], '{') && pair[m] > m) {
    for (const [a, b] of elements(F, m)) {
      if (a >= b) continue;
      names.push(toks[a].v);
      locals.push(isId(toks[a + 1], 'as') && toks[a + 2] ? toks[a + 2].v : toks[a].v);
    }
    m = pair[m] + 1;
  }
  if (!isId(toks[m], 'from') || toks[m + 1]?.t !== 'str') return null;
  return { spec: toks[m + 1].v, names, ns, locals };
}

function exportDecl(F, k) {
  const { toks, pair } = F, result = { exports: [], listed: [], spec: null, names: null };
  let m = k + 1;
  if (isP(toks[m], '*')) {
    let f = m + 1;
    if (isId(toks[f], 'as')) f += 2;
    if (isId(toks[f], 'from') && toks[f + 1]?.t === 'str') { result.spec = toks[f + 1].v; result.names = '*'; }
    return result;
  }
  if (isP(toks[m], '{') && pair[m] > m) {
    const close = pair[m], from = isId(toks[close + 1], 'from') && toks[close + 2]?.t === 'str', locals = [];
    for (let i = m; i <= close; i++) result.listed.push(i);
    for (const [a, b] of elements(F, m)) {
      if (a >= b) continue;
      const local = toks[a].v, name = isId(toks[a + 1], 'as') && toks[a + 2] ? toks[a + 2].v : local;
      locals.push(local);
      result.exports.push({ name, local, kind: from ? 'reexport' : 'list' });
    }
    if (from) { result.spec = toks[close + 2].v; result.names = locals; }
    return result;
  }
  if (isId(toks[m], 'default')) { result.exports.push({ name: 'default', local: null, kind: 'default' }); return result; }
  if (isId(toks[m], 'async')) m++;
  if (isId(toks[m], 'function') || isId(toks[m], 'class')) {
    m++;
    if (isP(toks[m], '*')) m++;
    if (isId(toks[m])) result.exports.push({ name: toks[m].v, local: toks[m].v, kind: 'decl' });
    return result;
  }
  if (isId(toks[m], 'const') || isId(toks[m], 'let') || isId(toks[m], 'var')) {
    for (const at of declarators(F, m + 1)) result.exports.push({ name: toks[at].v, local: toks[at].v, kind: 'decl' });
  }
  return result;
}

function grouping(toks, open) {
  const prev = toks[open - 1];
  if (!prev) return true;
  if (prev.t === 'id') return WORDS_BEFORE_EXPRESSION.has(prev.v);
  return !(isP(prev, ')') || isP(prev, ']') || prev.t === 'tpl');
}

function operandStart(F, i) {
  const { toks, pair } = F;
  for (;;) {
    const t = toks[i];
    if (!t) return i + 1;
    if (isP(t, ')') || isP(t, ']')) {
      const open = pair[i];
      if (open < 0) return i;
      const prev = toks[open - 1];
      if (prev && ((prev.t === 'id' && !WORDS_BEFORE_EXPRESSION.has(prev.v)) || isP(prev, ')') || isP(prev, ']'))) { i = open - 1; continue; }
      return open;
    }
    if (afterDot(toks, i)) { i -= 2; continue; }
    return i;
  }
}

function statementStart(toks, i) {
  const prev = toks[i - 1];
  if (!prev || isP(prev, ';') || isP(prev, '{') || isP(prev, '}')) return true;
  return toks[i].nl && (prev.t !== 'p' || prev.v === ')' || prev.v === ']');
}

function statementEnd(toks, e) {
  const next = toks[e + 1];
  return !next || isP(next, ';') || isP(next, '}') || next.nl;
}

function thenNames(F, open) {
  const { toks } = F;
  if (!isP(toks[open], '(')) return { names: ESCAPE };
  let j = open + 1;
  if (isId(toks[j], 'async')) j++;
  if (isP(toks[j], '(') && isP(toks[j + 1], '{')) return { names: objectKeys(F, j + 1) };
  return { names: ESCAPE };
}

function declaredName(toks, s) {
  const left = toks[s - 2], lead = toks[s - 3];
  if (!isId(left) || afterDot(toks, s - 2)) return null;
  if (isId(lead, 'const') || isId(lead, 'let') || isId(lead, 'var') || isP(lead, ',')) return { ns: left.v, at: s - 2 };
  if (statementStart(toks, s - 2)) return { ns: left.v, at: s - 2 };
  return null;
}

function promiseAllElement(F, s, e) {
  const { toks, pair, parent } = F, open = parent[s], call = open - 1;
  if (open < 0 || !isP(toks[open], '[') || !isP(toks[call], '(') || pair[call] !== pair[open] + 1) return null;
  if (!(isId(toks[call - 1], 'all') || isId(toks[call - 1], 'allSettled')) || !isP(toks[call - 2], '.') || !isId(toks[call - 3], 'Promise')) return null;
  if (!(isP(toks[s - 1], '[') || isP(toks[s - 1], ',')) || !(isP(toks[e + 1], ',') || isP(toks[e + 1], ']'))) return null;
  let index = 0;
  for (let i = open + 1; i < s; i++) if (parent[i] === open && isP(toks[i], ',')) index++;
  let s2 = call - 3, e2 = pair[call];
  for (;;) {
    if (isId(toks[s2 - 1], 'await')) { s2--; continue; }
    if (isP(toks[s2 - 1], '(') && pair[s2 - 1] === e2 + 1 && grouping(toks, s2 - 1)) { s2--; e2++; continue; }
    break;
  }
  if (isP(toks[e2 + 1], '.') || isP(toks[e2 + 1], '?.')) return { names: ESCAPE };
  if (isP(toks[s2 - 1], '=') && isP(toks[s2 - 2], ']') && pair[s2 - 2] >= 0) {
    const item = elements(F, pair[s2 - 2])[index];
    if (!item || item[0] >= item[1]) return { names: [] };
    const first = toks[item[0]];
    if (isP(first, '{')) return { names: objectKeys(F, item[0]) };
    if (isId(first) && (item[1] - item[0] === 1 || isP(toks[item[0] + 1], '='))) return { ns: first.v, at: item[0] };
    return { names: ESCAPE };
  }
  if (statementStart(toks, s2) && statementEnd(toks, e2)) return { names: [] };
  return { names: ESCAPE };
}

function bindingOf(F, start, end) {
  const { toks, pair } = F;
  let s = start, e = end;
  for (;;) {
    const next = toks[e + 1];
    if ((isP(next, '.') || isP(next, '?.')) && isId(toks[e + 2])) return toks[e + 2].v === 'then' ? thenNames(F, e + 3) : { names: [toks[e + 2].v] };
    const before = toks[s - 1];
    if (isId(before, 'await')) { s--; continue; }
    if (isP(before, '(') && pair[s - 1] === e + 1 && grouping(toks, s - 1)) { s--; e++; continue; }
    if (isP(before, '??') || isP(before, '||') || isP(before, '&&')) { s = operandStart(F, s - 2); continue; }
    break;
  }
  if (isP(toks[s - 1], '=')) {
    if (isP(toks[s - 2], '}') && pair[s - 2] >= 0) return { names: objectKeys(F, pair[s - 2]) };
    return declaredName(toks, s) ?? { names: ESCAPE };
  }
  const item = promiseAllElement(F, s, e);
  if (item) return item;
  if (statementStart(toks, s) && statementEnd(toks, e)) return { names: [] };
  return { names: ESCAPE };
}

function literalIndex(toks, open) {
  return toks[open + 1]?.t === 'str' && isP(toks[open + 2], ']') ? [toks[open + 1].v] : ESCAPE;
}

function namespaceUse(F, i) {
  const { toks, pair } = F, prev = toks[i - 1], next = toks[i + 1];
  if (isP(next, '.') || isP(next, '?.')) {
    if (isId(toks[i + 2])) return [toks[i + 2].v];
    if (isP(toks[i + 2], '[')) return literalIndex(toks, i + 2);
    return ESCAPE;
  }
  if (isP(next, '[')) return literalIndex(toks, i + 1);
  if (next && next.t === 'p' && ASSIGNMENTS.has(next.v)) return [];
  if (isP(prev, '=') && isP(toks[i - 2], '}') && pair[i - 2] >= 0) return objectKeys(F, pair[i - 2]);
  if ((isP(prev, '{') || isP(prev, ',')) && isP(next, ':')) return [];
  if (isId(prev, 'const') || isId(prev, 'let') || isId(prev, 'var')) return [];
  return ESCAPE;
}

function resolveSpec(from, spec, files) {
  if (typeof spec !== 'string' || !spec.startsWith('.')) return null;
  const target = posix.normalize(posix.join(posix.dirname(from), spec.split('?')[0]));
  if (files.has(target)) return target;
  return files.has(`${target}.mjs`) ? `${target}.mjs` : null;
}

function references(F, files) {
  const { toks, pair, parent, depth } = F;
  const refs = [], ns = new Map(), declared = new Set(), listed = new Set(), exports = [], strings = new Set(), requireNames = new Set(['require']);
  const imported = new Map();
  for (let k = 2; k < toks.length; k++) {
    if (isId(toks[k], 'createRequire') && isP(toks[k + 1], '(') && isP(toks[k - 1], '=') && isId(toks[k - 2])) requireNames.add(toks[k - 2].v);
  }
  const bind = (to, kind, binding) => {
    if (binding.ns) {
      if (!ns.has(binding.ns)) ns.set(binding.ns, new Set());
      ns.get(binding.ns).add(to);
      declared.add(binding.at);
      refs.push({ to, kind, names: 'NS' });
    } else refs.push({ to, kind, names: binding.names });
  };
  for (let k = 0; k < toks.length; k++) {
    const t = toks[k];
    if (t.t === 'str' && IDENTIFIER.test(t.v)) strings.add(t.v);
    if (t.t !== 'id') continue;
    if (afterDot(toks, k)) { strings.add(t.v); continue; }
    if (t.v === 'import') {
      if (isP(toks[k + 1], '(')) {
        const arg = toks[k + 2];
        if (pair[k + 1] > k && arg && (arg.t === 'str' || arg.t === 'tpl') && (isP(toks[k + 3], ')') || isP(toks[k + 3], ','))) {
          const to = resolveSpec(F.rel, arg.v, files);
          if (to) bind(to, 'dynamic', bindingOf(F, k, pair[k + 1]));
        }
        continue;
      }
      if (isP(toks[k + 1], '.') || depth[k] !== 0) continue;
      const decl = staticImport(F, k);
      const to = decl && resolveSpec(F.rel, decl.spec, files);
      if (!to) continue;
      bind(to, 'static', decl.ns ?? { names: decl.names });
      for (const local of decl.locals) imported.set(local, to);
      continue;
    }
    if (t.v === 'export' && depth[k] === 0) {
      const decl = exportDecl(F, k);
      const to = decl.spec && resolveSpec(F.rel, decl.spec, files);
      exports.push(...decl.exports.map(e => ({ ...e, from: to || null })));
      for (const i of decl.listed) listed.add(i);
      if (to) refs.push({ to, kind: 'static', names: decl.names });
      continue;
    }
    if (requireNames.has(t.v) && isP(toks[k + 1], '(') && toks[k + 2]?.t === 'str' && isP(toks[k + 3], ')')) {
      const to = resolveSpec(F.rel, toks[k + 2].v, files);
      if (to) bind(to, 'require', bindingOf(F, k, k + 3));
      continue;
    }
    if (t.v === 'createRequire' && isP(toks[k + 1], '(') && pair[k + 1] > k && isP(toks[pair[k + 1] + 1], '(')) {
      const open = pair[k + 1] + 1, arg = toks[open + 1];
      const to = arg?.t === 'str' && isP(toks[open + 2], ')') && resolveSpec(F.rel, arg.v, files);
      if (to) bind(to, 'require', bindingOf(F, k, open + 2));
      continue;
    }
    if (t.v === 'new' && isId(toks[k + 1], 'URL') && isP(toks[k + 2], '(') && toks[k + 3]?.t === 'str' && /\.m?js$/.test(toks[k + 3].v)
      && isP(toks[k + 4], ',') && isId(toks[k + 5], 'import')) {
      const to = resolveSpec(F.rel, toks[k + 3].v, files);
      if (to) refs.push({ to, kind: 'url', names: ESCAPE });
    }
  }
  if (ns.size) {
    const used = new Map([...ns.keys()].map(name => [name, new Set()])), escaped = new Set();
    for (let i = 0; i < toks.length; i++) {
      const t = toks[i];
      if (t.t !== 'id' || !ns.has(t.v) || declared.has(i) || listed.has(i) || afterDot(toks, i)) continue;
      const use = namespaceUse(F, i);
      if (use === ESCAPE) escaped.add(t.v);
      else for (const name of use) used.get(t.v).add(name);
    }
    for (const [name, targets] of ns) {
      for (const to of targets) refs.push({ to, kind: 'ns', names: escaped.has(name) ? ESCAPE : [...used.get(name)] });
    }
  }
  for (const e of exports) if (e.kind === 'list' && imported.has(e.local)) e.from = imported.get(e.local);
  return { refs, exports, listed, strings };
}

function internalCounts(F, listed) {
  const { toks } = F, counts = new Map();
  for (let i = 0; i < toks.length; i++) {
    const t = toks[i];
    if (t.t === 'str' || t.t === 'tpl') { for (const [word] of t.v.matchAll(WORD)) counts.set(word, (counts.get(word) ?? 0) + 1); continue; }
    if (t.t !== 'id' || listed.has(i) || afterDot(toks, i)) continue;
    if ((isP(toks[i - 1], '{') || isP(toks[i - 1], ',')) && isP(toks[i + 1], ':')) continue;
    counts.set(t.v, (counts.get(t.v) ?? 0) + 1);
  }
  return counts;
}

function loopSizes(nodes, adjacency) {
  let index = 0;
  const order = new Map(), low = new Map(), stack = [], onStack = new Set(), sizes = [];
  const visit = v => {
    order.set(v, index); low.set(v, index); index++;
    stack.push(v); onStack.add(v);
    for (const w of adjacency.get(v)) {
      if (!order.has(w)) { visit(w); low.set(v, Math.min(low.get(v), low.get(w))); }
      else if (onStack.has(w)) low.set(v, Math.min(low.get(v), order.get(w)));
    }
    if (low.get(v) !== order.get(v)) return;
    let w, size = 0;
    do { w = stack.pop(); onStack.delete(w); size++; } while (w !== v);
    if (size > 1) sizes.push(size);
  };
  for (const v of nodes) if (!order.has(v)) visit(v);
  return sizes;
}

function importGraph(host, refs) {
  const hostSet = new Set(host), pairs = new Map(), adjacency = new Map(host.map(rel => [rel, new Set()]));
  for (const r of refs) {
    if (r.kind !== 'static' && r.kind !== 'dynamic' && r.kind !== 'require') continue;
    if (!hostSet.has(r.from) || r.from === r.to || !(hostSet.has(r.to) || inRuntime(r.to))) continue;
    pairs.set(`${r.from}\n${r.to}`, r);
    if (hostSet.has(r.to)) adjacency.get(r.from).add(r.to);
  }
  const loops = loopSizes(host, adjacency);
  let upward = 0;
  for (const { from, to } of pairs.values()) {
    const a = boxOf(from), b = boxOf(to);
    if (a !== null && b !== null && (b > a || (b === 1 && !(a === 2 && isRuntimeEntry(to))))) upward++;
  }
  return {
    largestLoop: Math.max(0, ...loops),
    modulesInLoops: loops.reduce((sum, size) => sum + size, 0),
    upward,
    unassigned: host.filter(rel => boxOf(rel) === null),
  };
}

function cloneLines(host, parsed) {
  const ids = new Map(), seen = new Map();
  const streams = host.map(rel => {
    const { toks } = parsed.get(rel);
    const codes = Int32Array.from(toks, t => {
      const key = `${t.t}\u0000${t.v}`;
      if (!ids.has(key)) ids.set(key, ids.size);
      return ids.get(key);
    });
    return { codes, lines: toks.map(t => t.line) };
  });
  const same = (a, p, b, q) => { for (let j = 0; j < WINDOW; j++) if (a[p + j] !== b[q + j]) return false; return true; };
  let total = 0;
  streams.forEach(({ codes, lines }, f) => {
    const mark = new Uint8Array(codes.length), covered = new Set();
    for (let i = 0; i + WINDOW <= codes.length; i++) {
      let h1 = 0, h2 = 0;
      for (let j = i; j < i + WINDOW; j++) { h1 = (Math.imul(h1, 31) + codes[j]) | 0; h2 = (Math.imul(h2, 1000003) ^ codes[j]) | 0; }
      const key = (h1 >>> 0) * 2097152 + ((h2 >>> 0) & 2097151), first = seen.get(key);
      if (first === undefined) { seen.set(key, [f, i]); continue; }
      const [g, p] = first;
      if ((g === f && p + WINDOW > i) || !same(streams[g].codes, p, codes, i)) continue;
      mark.fill(1, i, i + WINDOW);
    }
    for (let i = 0; i < codes.length; i++) {
      if (!mark[i]) continue;
      let j = i;
      while (j + 1 < codes.length && mark[j + 1]) j++;
      if (lines[j] - lines[i] + 1 >= MIN_CLONE_LINES) for (let l = lines[i]; l <= lines[j]; l++) covered.add(l);
      i = j;
    }
    total += covered.size;
  });
  return total;
}

function commentLines(host, parsed) {
  let total = 0;
  for (const rel of host) {
    const { text, comments } = parsed.get(rel), lines = new Set();
    for (const c of comments) {
      const alone = text.slice(text.lastIndexOf('\n', c.at - 1) + 1, c.at).trim() === '';
      if ((alone && c.at < HEADER_BYTES && HEADER.test(c.text)) || EXTERNAL.test(c.text) || LICENSE.test(c.text)) continue;
      for (let l = c.first; l <= c.last; l++) lines.add(l);
    }
    total += lines.size;
  }
  return total;
}

function runtimePrompts(files, read) {
  const owned = new Set();
  for (const rel of files.filter(inRuntime)) {
    for (const [, prompt] of read(rel).slice(0, HEADER_BYTES).matchAll(/Generated from (\S+\.prompt\.md)/g)) owned.add(prompt);
  }
  return new Set(files.filter(rel => CLI_PROMPT.test(rel) && (posix.basename(rel).startsWith('runtime-') || owned.has(rel))));
}

function historyReferences(prompts, read) {
  return prompts.reduce((sum, rel) => {
    const prose = read(rel).replace(INTERFACE, '');
    return sum + HISTORY.reduce((n, re) => n + (prose.match(re)?.length ?? 0), 0);
  }, 0);
}

function testOnlyExports(host, info, refs, prodStrings) {
  const incoming = new Map();
  for (const r of refs) {
    if (r.from === r.to) continue;
    if (!incoming.has(r.to)) incoming.set(r.to, []);
    incoming.get(r.to).push(r);
  }
  const uses = (list, name) => list.some(r => r.names === '*' || (Array.isArray(r.names) && r.names.includes(name)));
  let count = 0;
  for (const rel of host) {
    const { exports, counts } = info.get(rel), ins = incoming.get(rel) ?? [];
    const prod = ins.filter(r => !isTest(r.from)), test = ins.filter(r => isTest(r.from));
    const escapedProd = prod.some(r => r.names === ESCAPE), escapedTest = test.some(r => r.names === ESCAPE);
    for (const e of exports) {
      if (e.from && inRuntime(e.from)) continue;
      if (uses(prod, e.name) || (escapedProd && prodStrings.has(e.name))) continue;
      if (!uses(test, e.name) && !escapedTest) continue;
      if ((e.kind === 'decl' || e.kind === 'list') && (counts.get(e.local) ?? 0) > 1) continue;
      count++;
    }
  }
  return count;
}

function measure(root) {
  if (!existsSync(join(root, 'src'))) throw new Error(`no src folder in ${root}`);
  const files = SCAN_DIRS.flatMap(dir => walk(root, dir)).sort(), fileSet = new Set(files), cache = new Map();
  const read = rel => { if (!cache.has(rel)) cache.set(rel, readFileSync(join(root, rel), 'utf8')); return cache.get(rel); };
  const host = files.filter(isHost), hostSet = new Set(host), parsed = new Map(), info = new Map(), refs = [], prodStrings = new Set();
  for (const rel of files.filter(isCode)) {
    const F = parse(rel, read(rel));
    const r = references(F, fileSet);
    for (const ref of r.refs) refs.push({ from: rel, ...ref });
    if (!isTest(rel)) for (const s of r.strings) prodStrings.add(s);
    if (hostSet.has(rel)) {
      parsed.set(rel, F);
      info.set(rel, { exports: r.exports, counts: internalCounts(F, r.listed) });
    }
    if (!hostSet.has(rel) && !inRuntime(rel)) cache.delete(rel);
  }
  const runtime = runtimePrompts(files, read);
  const sizes = host.map(rel => ({ file: rel, lines: lineCount(read(rel)) })).sort((a, b) => b.lines - a.lines || a.file.localeCompare(b.file));
  const textLines = keep => files.filter(keep).reduce((sum, rel) => {
    const bytes = readFileSync(join(root, rel));
    return sum + (bytes.subarray(0, 8192).includes(0) ? 0 : lineCount(bytes.toString('utf8')));
  }, 0);
  return {
    biggest: sizes[0] ?? { file: '-', lines: 0 },
    over: sizes.filter(s => s.lines > BIG_FILE).length,
    graph: importGraph(host, refs),
    clones: cloneLines(host, parsed),
    comments: commentLines(host, parsed),
    history: historyReferences(files.filter(rel => CLI_PROMPT.test(rel) && !runtime.has(rel)), read),
    testOnly: testOnlyExports(host, info, refs, prodStrings),
    code: sizes.reduce((sum, s) => sum + s.lines, 0),
    tests: textLines(rel => segments(rel)[0] === 'test' && segments(rel)[1] !== 'runtime-package'),
    prompts: textLines(rel => segments(rel)[0] === 'prompts' && !runtime.has(rel)),
  };
}

const MEASURES = [
  ['Biggest host file (lines)', m => m.biggest.lines, m => `${fmt(m.biggest.lines)} \`${posix.basename(m.biggest.file)}\``],
  [`Host files over ${fmt(BIG_FILE)} lines`, m => m.over],
  ['Largest import loop (modules)', m => m.graph.largestLoop],
  ['Modules in import loops', m => m.graph.modulesInLoops],
  ['Upward imports (module pairs)', m => m.graph.upward],
  [`Exact clone lines (${WINDOW}-token window)`, m => m.clones],
  ['Comment lines not on the keep-list', m => m.comments],
  ['History references in host prompts', m => m.history],
  ['Test-only exports', m => m.testOnly],
  ['Lines of host code', m => m.code],
  ['Lines of host tests', m => m.tests],
  ['Lines of host prompts', m => m.prompts],
];

function fmt(n) {
  return n.toLocaleString('en-US');
}

function rows(base, head) {
  return MEASURES.map(([measure, value, show = m => fmt(value(m))]) => {
    const change = value(head) - value(base);
    return { measure, base: value(base), head: value(head), change, verdict: change < 0 ? 'better' : change > 0 ? 'worse' : 'same', show: [show(base), show(head)] };
  });
}

function markdown(base, head) {
  const table = rows(base, head), signed = n => n > 0 ? `+${fmt(n)}` : fmt(n);
  const out = [
    '| Measure | Base | Head | Change | Result |',
    '|---|---:|---:|---:|---|',
    ...table.map(r => `| ${r.measure} | ${r.show[0]} | ${r.show[1]} | ${signed(r.change)} | ${r.verdict} |`),
    '',
    `Net host lines (code, tests, prompts): ${signed(table.slice(-3).reduce((sum, r) => sum + r.change, 0))}. Lower is better on every row. This report never blocks.`,
    `Host only: src/**/*.mjs and bin/ without the Runtime package and src/vendor/; test/ without test/runtime-package/; prompts/ without the Runtime prompts. Loops and upward imports count static, import() and createRequire edges. Clones: ${WINDOW}-token windows seen earlier in host code, runs of ${MIN_CLONE_LINES}+ lines.`,
  ];
  const missing = [...new Set([...base.graph.unassigned, ...head.graph.unassigned])];
  if (missing.length) out.push(`Modules with no box (add them to BOXES in test/tools/ratchet.mjs): ${missing.map(rel => posix.basename(rel)).join(', ')}.`);
  return `${out.join('\n')}\n`;
}

const args = process.argv.slice(2), json = args.includes('--json'), [baseDir, headDir] = args.filter(a => a !== '--json');
try {
  if (!baseDir || !headDir) throw new Error('usage: node test/tools/ratchet.mjs <baseDir> <headDir> [--json]');
  const base = measure(resolve(baseDir)), head = measure(resolve(headDir));
  process.stdout.write(json ? `${JSON.stringify(rows(base, head).map(({ show, ...r }) => r), null, 2)}\n` : markdown(base, head));
} catch (error) {
  const message = error?.message ?? String(error);
  process.stdout.write(json ? `${JSON.stringify({ error: message })}\n` : `Ratchet report failed: ${message}\n`);
}
process.exitCode = 0;
