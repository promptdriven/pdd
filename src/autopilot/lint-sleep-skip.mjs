// Layer-2 Autopilot test hygiene checks (#3562): O(N) `test-fixed-sleep` & `test-unexcused-skip` (JS/TS + Python).
import { isTestOwnedPath } from '../file-owner.mjs';
import { buildLineStarts, canonicalRepoPath, lineNumberAt, readSafeUtf8 } from '../core/lint/diagnostics.mjs';

const TEST_CODE_EXT = /\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|cs|swift)$/i;
const SKIP_SUBDIR = /(?:^|\/)(?:fixtures|helpers)\//i;
const SEAM_FILE = /(?:^|\/)[^/]*seam\.test\.[A-Za-z0-9]+$/i;
const SLEEP_ALLOW_RE = /\b(?:pdd-allow-sleep|sleep-ok|allow-sleep)\b/i;
const SKIP_ALLOW_RE = /\bpdd-allow-skip\b/i;
const TRACKING_REF_RE = /(?:^|[\s([,:;'`"])#[1-9]\d*\b|(?<![A-Za-z0-9_.\-/])[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+#[1-9]\d*\b|\b[A-Z]{2,10}-[1-9]\d*\b|\bissue\s+#?[1-9]\d*\b|https:\/\/github\.com\/[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+\/issues\/[1-9]\d*\b/i;
const PLACEHOLDER_SKIP = new Set(['todo', 'skip', 'skipped', 'wip', 'later', 'flaky', 'broken', 'fixme', 'temp', 'temporary', 'disabled', 'tbd', 'xxx', 'none', 'na', 'n/a']);
const SIMPLE_NUM_RE = /^[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[+-]?\d+)?$/i;
const POLL_HELPER_RE = /^(?:waitFor|waitUntil|wait_for|wait_until|until|eventually|poll(?:For|Until|While)?|retry(?:WithBackoff)?|withRetry|withBackoff|backoff)(?:$|[A-Z0-9_])/i;
const DATA_DRAIN_RE = /\.\s*(?:pop|shift|splice|dequeue)\s*\(/;
const NONEMPTY_LEN_RE = /^(?:[A-Za-z_$][\w$.]*\.(?:length|size)|len\s*\([^()]*\))(?:\s*(?:>|!==?|>=)\s*0)?$/;
const POLL_DEADLINE_RE = /\b(?:Date\s*\.\s*now|performance\s*\.\s*now|hrtime|time\s*\.\s*(?:time|monotonic|perf_counter)|deadline|end|until|timeout|expires|maxWait|elapsed)\b/i;
const POLL_STATE_RE = /\b(?:ready|done|finished|stopped|alive|pending|waiting|connected|closed|exited|complete|completed|attempt|attempts|retries|tries|settled|healthy|running|state|status)\b/i;
const COUNTER_VAR_RE = /^(?:[a-z]\d*|i|j|k|n|idx|index|count|step|iter|num|pos|offset)$/i;
const EMPTY_SET = new Set();

export const isInspectableTestCodePath = p => isTestOwnedPath(p) && TEST_CODE_EXT.test(p) && !SKIP_SUBDIR.test(p) && !SEAM_FILE.test(p);
const hasTrackingRef = v => TRACKING_REF_RE.test(String(v ?? ''));
const hasSubstantiveReason = v => { const s = String(v ?? '').trim(); return Boolean(s) && (hasTrackingRef(s) || (!PLACEHOLDER_SKIP.has(s.toLowerCase()) && s.length >= 12 && /\s/.test(s))); };
const decodeEsc = raw => raw.replace(/\\(.)/gs, (_, c) => (c === 'n' ? '\n' : c === 'r' ? '\r' : c === 't' ? '\t' : c));
const addIds = (sl, set) => { for (const m of sl.matchAll(/(?<![\w$.])([A-Za-z_$][\w$]*)(?![\w$])/g)) set.add(m[1]); };
const singleLit = (e, lits) => { const t = String(e ?? '').trim(), m = t.length <= 32 && /^__STR_(\d+)__$/.exec(t); return m && typeof lits[Number(m[1])] === 'string' ? lits[Number(m[1])] : null; };
const exprText = (e, lits) => [...String(e ?? '').slice(0, 512).matchAll(/__STR_(\d+)__/g)].map(m => lits[Number(m[1])]).filter(v => typeof v === 'string').join(' ');
const prevWord = (s, idx) => { let q = idx; while (q >= 0 && /\s/.test(s[q])) q--; let a = q; while (a >= 0 && /[\w$]/.test(s[a])) a--; return { word: s.slice(a + 1, q + 1), start: a + 1 }; };
const skipNested = (s, k, lim, d) => { const c = s[k], m = c === '(' ? d.cp[k] : c === '{' ? d.cb[k] : c === '[' ? d.ck[k] : -1; return m > k && m < lim ? m + 1 : -1; };

function tokenizeTestCode(src, hashComments) {
  const literals = [], lineComments = [], lineHasCode = [], lineHasComment = [], tplStack = [];
  let lineNo = 1, out = '', i = 0, prev = '';
  const mark = (sl, raw) => { lineHasCode[sl - 1] = true; let nl = 0; for (let k = 0; k < raw.length; k++) if (raw[k] === '\n') lineHasCode[sl - 1 + (++nl)] = true; return nl; };
  const recCom = (sl, raw) => { const ps = raw.split('\n'); for (let k = 0; k < ps.length; k++) { const idx = sl - 1 + k; lineHasComment[idx] = true; lineComments[idx] = lineComments[idx] ? `${lineComments[idx]} ${ps[k]}` : ps[k]; } return ps.length - 1; };
  const addLit = (val, raw) => { const id = literals.length; literals.push(val); const nl = mark(lineNo, raw); lineNo += nl; return `__STR_${id}__${'\n'.repeat(nl)}`; };
  const canRegex = () => !prev || '(=:,[!&|?{};+-*%<>^~'.includes(prev) || /^(?:return|throw|case|in|of|typeof|void|delete|await|yield)$/.test(prev);
  const eatTpl = s => {
    let j = s;
    while (j < src.length && src[j] !== '`') {
      if (src[j] === '\\') { j += 2; continue; }
      if (src[j] === '$' && src[j + 1] === '{') { const c = src.slice(s, j); tplStack.push({ d: 1 }); prev = '('; return { t: `(${addLit(decodeEsc(c), c)} + (`, n: j + 2 }; }
      j++;
    }
    const c = src.slice(s, j); prev = 'str';
    return { t: `${addLit(decodeEsc(c), c)})`, n: j < src.length ? j + 1 : j };
  };
  while (i < src.length) {
    const ch = src[i], nx = src[i + 1];
    if ((!hashComments && ch === '/' && nx === '/') || (hashComments && ch === '#')) {
      const e = src.indexOf('\n', i + (hashComments ? 1 : 2));
      recCom(lineNo, e < 0 ? src.slice(i + (hashComments ? 1 : 2)) : src.slice(i + (hashComments ? 1 : 2), e));
      if (e < 0) break; out += '\n'; lineNo++; i = e + 1; continue;
    }
    if (!hashComments && ch === '/' && nx === '*') { const e = src.indexOf('*/', i + 2), nl = recCom(lineNo, e < 0 ? src.slice(i + 2) : src.slice(i + 2, e)); out += '\n'.repeat(nl); lineNo += nl; i = e < 0 ? src.length : e + 2; continue; }
    if (ch === "'" || ch === '"') {
      if (hashComments && src[i + 1] === ch && src[i + 2] === ch) {
        let j = i + 3, e = -1;
        while (j < src.length) { if (src[j] === '\\') { j += 2; continue; } if (src[j] === ch && src[j + 1] === ch && src[j + 2] === ch) { e = j; break; } j++; }
        const b = e < 0 ? src.slice(i + 3) : src.slice(i + 3, e); out += addLit(b, b); prev = 'str'; i = e < 0 ? src.length : e + 3; continue;
      }
      let j = i + 1; while (j < src.length && src[j] !== ch && src[j] !== '\n') j += src[j] === '\\' ? 2 : 1;
      const b = src.slice(i + 1, j); out += addLit(decodeEsc(b), b); prev = 'str'; i = j < src.length && src[j] === ch ? j + 1 : j; continue;
    }
    if (!hashComments && ch === '`') {
      let j = i + 1, interp = false;
      while (j < src.length && src[j] !== '`') { if (src[j] === '\\') { j += 2; continue; } if (src[j] === '$' && src[j + 1] === '{') { interp = true; break; } j++; }
      if (!interp) { const b = src.slice(i + 1, j); out += addLit(decodeEsc(b), b); prev = 'str'; i = j < src.length ? j + 1 : j; }
      else { const step = eatTpl(i + 1); out += step.t; i = step.n; } continue;
    }
    if (tplStack.length) {
      if (ch === '{') { tplStack.at(-1).d++; lineHasCode[lineNo - 1] = true; out += ch; prev = '{'; i++; continue; }
      if (ch === '}' && --tplStack.at(-1).d === 0) { tplStack.pop(); lineHasCode[lineNo - 1] = true; const s = eatTpl(i + 1); out += `) + ${s.t}`; i = s.n; continue; }
    }
    if (!hashComments && ch === '/' && nx !== '/' && nx !== '*' && canRegex()) {
      let j = i + 1, cls = false, cl = false;
      while (j < src.length && src[j] !== '\n') { if (src[j] === '\\') { if (j + 1 < src.length && src[j + 1] !== '\n') { j += 2; continue; } break; } if (src[j] === '[') cls = true; else if (src[j] === ']') cls = false; else if (src[j] === '/' && !cls) { cl = true; j++; break; } j++; }
      if (cl) { while (j < src.length && /[A-Za-z]/.test(src[j])) j++; lineHasCode[lineNo - 1] = true; out += '/__RE__/'; prev = 'regex'; i = j; continue; }
    }
    if (/\s/.test(ch)) { if (ch === '\n') lineNo++; out += ch; i++; continue; }
    if (/[A-Za-z_$]/.test(ch)) { let j = i + 1; while (j < src.length && /[A-Za-z0-9_$]/.test(src[j])) j++; prev = src.slice(i, j); lineHasCode[lineNo - 1] = true; out += prev; i = j; continue; }
    lineHasCode[lineNo - 1] = true; out += ch; prev = ch; i++;
  }
  return { skeleton: out, literals, lineComments, lineHasCode, lineHasComment };
}

function buildDelims(text) {
  const n = text.length, mk = () => new Int32Array(n).fill(-1);
  const cp = mk(), op = mk(), cb = mk(), ck = mk(), eb = mk(), ek = mk(), ps = [], bs = [], ks = [];
  for (let i = 0; i < n; i++) {
    eb[i] = bs.length ? bs.at(-1) : -1; ek[i] = ks.length ? ks.at(-1) : -1;
    const c = text[i];
    if (c === '(') ps.push(i); else if (c === ')' && ps.length) { const o = ps.pop(); cp[o] = i; op[i] = o; }
    else if (c === '{') bs.push(i); else if (c === '}' && bs.length) cb[bs.pop()] = i;
    else if (c === '[') ks.push(i); else if (c === ']' && ks.length) ck[ks.pop()] = i;
  }
  return { cp, op, cb, ck, eb, ek };
}

function parseArgs(text, openIdx, d, maxArgs = 4) {
  const end = d.cp[openIdx]; if (end < 0) return null;
  const args = [], argStarts = []; let start = openIdx + 1, k = start;
  while (k < end) {
    const jump = skipNested(text, k, end, d);
    if (jump > 0) k = jump;
    else if (text[k] === ',') { args.push(text.slice(start, k)); argStarts.push(start); start = ++k; if (args.length >= maxArgs) return { args, argStarts, endIdx: end + 1 }; }
    else k++;
  }
  const tail = text.slice(start, end);
  if (args.length || tail.trim()) { args.push(tail); argStarts.push(start); }
  return { args, argStarts, endIdx: end + 1 };
}

function adjComments(lc, hc, hm, ln) {
  const idx = ln - 1; if (idx < 0) return '';
  const out = lc[idx] ? [lc[idx]] : [];
  for (let b = 1; b <= 6 && idx - b >= 0 && hm[idx - b] && !hc[idx - b]; b++) if (lc[idx - b]) out.push(lc[idx - b]);
  return out.join('\n');
}

function stripOuterParens(expr) {
  const s = String(expr ?? '').trim(); if (!s.startsWith('(') || !s.endsWith(')')) return s;
  const pairs = []; let lo = 0, hi = s.length - 1;
  while (lo < hi) {
    while (lo < hi && /\s/.test(s[lo])) lo++; while (lo < hi && /\s/.test(s[hi])) hi--;
    if (lo < hi && s[lo] === '(' && s[hi] === ')') pairs.push([lo++, hi--]); else break;
  }
  if (!pairs.length) return s;
  const [iLo, iHi] = pairs.at(-1); let depth = pairs.length, minD = depth;
  for (let i = iLo + 1; i < iHi; i++) { if (s[i] === '(') depth++; else if (s[i] === ')') { if (--depth < 0) return s; if (depth < minD) minD = depth; } }
  return depth !== pairs.length || minD <= 0 ? s : s.slice(pairs[minD - 1][0] + 1, pairs[minD - 1][1]).trim();
}

function evalNum(expr) {
  const s = stripOuterParens(expr).replace(/_/g, ''); if (!s) return null;
  if (SIMPLE_NUM_RE.test(s)) { const n = Number(s); return Number.isFinite(n) ? n : null; }
  if (!/^[0-9.eE+\s*]+$/.test(s) || !s.includes('*')) return null;
  const fs = s.split('*').map(p => p.trim()); if (!fs.length || fs.some(f => !SIMPLE_NUM_RE.test(f))) return null;
  const prod = fs.reduce((acc, f) => acc * Number(f), 1); return Number.isFinite(prod) ? prod : null;
}

const isPosDelay = (arg, pv, ex = EMPTY_SET) => { const s = stripOuterParens(arg), n = evalNum(s); return n !== null ? n > 0 : /^[A-Za-z_$][\w$]*$/.test(s) && pv.has(s) && !ex.has(s); };

function collectPositiveVars(skel, hash, d) {
  const disq = new Set(), decls = new Map(), cands = new Set();
  if (!hash) {
    for (const m of skel.matchAll(/=>/g)) {
      let p = m.index - 1; while (p >= 0 && /\s/.test(skel[p])) p--;
      if (p >= 0 && skel[p] === ')' && d.op[p] >= 0 && p - d.op[p] <= 300) addIds(skel.slice(d.op[p] + 1, p), disq);
      else if (p >= 0 && /[\w$]/.test(skel[p])) disq.add(prevWord(skel, p).word);
    }
    for (const m of skel.matchAll(/\bfunction\b/g)) { let k = m.index + 8, lim = Math.min(skel.length, k + 80); while (k < lim && !'({;'.includes(skel[k])) k++; if (k < lim && skel[k] === '(' && d.cp[k] > k && d.cp[k] - k <= 300) addIds(skel.slice(k + 1, d.cp[k]), disq); }
    for (const m of skel.matchAll(/\b(const|let|var)\b/g)) {
      let k = m.index + m[1].length, lim = Math.min(skel.length, k + 512);
      while (k < lim) {
        while (k < lim && /[ \t]/.test(skel[k])) k++;
        if (k >= lim || skel[k] === ';' || skel[k] === '\n') break;
        if (skel[k] === '{' || skel[k] === '[') { const cl = skel[k] === '{' ? d.cb[k] : d.ck[k]; if (cl > k && cl < lim) addIds(skel.slice(k + 1, cl), disq); break; }
        const a = k; while (k < lim && /[\w$]/.test(skel[k])) k++; const id = skel.slice(a, k); if (!/^[A-Za-z_$][\w$]*$/.test(id)) break;
        decls.set(id, (decls.get(id) ?? 0) + 1); while (k < lim && /[ \t]/.test(skel[k])) k++;
        if (skel[k] !== '=' || skel[k + 1] === '=') { disq.add(id); if (skel[k] === ',') { k++; continue; } break; }
        const rs = ++k;
        while (k < lim) { const j = skipNested(skel, k, lim, d); if (j > 0) k = j; else if (skel[k] === ',' || skel[k] === ';' || skel[k] === '\n') break; else k++; }
        const v = evalNum(skel.slice(rs, k).trim()); if (m[1] === 'const' && v !== null && v > 0) cands.add(id); else disq.add(id);
        if (skel[k] === ',') { k++; continue; } break;
      }
    }
    for (const m of skel.matchAll(/(?<![.\w$])([A-Za-z_$][\w$]*)\s*(?:[+\-*/%&|^]?=(?![=>])|\+\+|--)/g)) if (!/\b(?:const|let|var)\s+$/.test(skel.slice(Math.max(0, m.index - 12), m.index))) disq.add(m[1]);
  } else {
    for (const m of skel.matchAll(/\bdef\b/g)) { let k = m.index + 3, lim = Math.min(skel.length, k + 80); while (k < lim && skel[k] !== '(' && skel[k] !== '\n') k++; if (k < lim && skel[k] === '(' && d.cp[k] > k && d.cp[k] - k <= 300) addIds(skel.slice(k + 1, d.cp[k]), disq); }
    for (const m of skel.matchAll(/\blambda\b/g)) { const head = skel.slice(m.index + 6, m.index + 207), colon = head.indexOf(':'), nl = head.indexOf('\n'); if (colon > 0 && (nl < 0 || colon < nl) && colon <= 194) addIds(head.slice(0, colon), disq); }
    for (const m of skel.matchAll(/(?:^|\n)[ \t]*([A-Za-z_]\w*)[ \t]*=(?!=)[ \t]*([^\n;]+)/g)) { decls.set(m[1], (decls.get(m[1]) ?? 0) + 1); const v = evalNum(m[2]); if (v !== null && v > 0) cands.add(m[1]); else disq.add(m[1]); }
  }
  return new Set([...cands].filter(id => decls.get(id) === 1 && !disq.has(id)));
}

function isPureCounter(cond, body) {
  const m = /^([A-Za-z_$][\w$]*)\s*(?:<|<=|>|>=|!=|!==)\s*(?:\d+|[A-Za-z_$][\w$.]*)$/.exec(cond);
  if (!m || POLL_DEADLINE_RE.test(cond) || POLL_STATE_RE.test(cond)) return false;
  if (COUNTER_VAR_RE.test(m[1])) return true;
  const e = m[1].replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  return new RegExp(`(?:\\+\\+|--)\\s*\\b${e}\\b|\\b${e}\\b\\s*(?:\\+\\+|--|\\+=|-=|=(?!=)\\s*${e}\\s*[+-])`).test(body);
}

function isPollingLoop(kind, header, body, isPy = false) {
  const h = String(header ?? '').trim();
  if (/\b(?:if|try)\b/.test(body) && /\b(?:break|return)\b/.test(body)) return true;
  if (DATA_DRAIN_RE.test(body)) return false;
  if (kind === 'for') { const m = /^[^;]*;([^;]*);([^;]*)$/.exec(h), c = m ? m[1].trim() : ''; return Boolean(c) && !isPureCounter(c, `${m?.[2] ?? ''}\n${body}`) && (/&&|\|\||!|\(|===|!==|==|!=/.test(c) || POLL_DEADLINE_RE.test(c)); }
  if (/^(?:true|1|!0|True)$/.test(h) || isPureCounter(h, body)) return false;
  if (POLL_DEADLINE_RE.test(h)) return true;
  if (NONEMPTY_LEN_RE.test(h) || (/\.\s*(?:length|size)\b|\blen\s*\(/.test(h) && !/&&|\|\||\band\b|\bor\b/.test(h))) return false;
  return (isPy ? /\b(?:and|or|not)\b|==|!=|\(/ : /&&|\|\||!|===|!==|==|!=|\(/).test(h) || POLL_STATE_RE.test(h);
}

function buildPythonPollingTable(lines) {
  const n = lines.length, parentHeader = new Int32Array(n).fill(-1), headerState = new Int8Array(n), st = [];
  const indOf = s => { let c = 0; for (let k = 0; k < s.length; k++) { if (s[k] === ' ') c++; else if (s[k] === '\t') c += 8 - (c % 8); else break; } return c; };
  const close = f => {
    if (f.k === 'loop' && isPollingLoop(f.lk, f.lh, `${f.c ? 'if ' : ''}${f.j ? 'break ' : ''}${f.d ? '.pop() ' : ''}${[...f.v].map(v => `${v}+=1`).join(' ')}`, true)) headerState[f.s] = 1;
    else if (f.k === 'def') headerState[f.s] = POLL_HELPER_RE.test(f.fn) && (f.l || (f.c && f.j)) ? 1 : -1;
    else if (f.k === 'class') headerState[f.s] = -1;
    if (st.length) { const p = st.at(-1); if (f.k === 'other') { p.c ||= f.c; p.j ||= f.j; p.d ||= f.d; p.l ||= f.l; for (const v of f.v) p.v.add(v); } else if (f.k === 'loop') p.l = true; }
  };
  for (let i = 0; i < n; i++) {
    const t = lines[i].trim(); if (!t) continue; const ind = indOf(lines[i]);
    while (st.length && st.at(-1).ind >= ind) close(st.pop());
    if (st.length) { const top = st.at(-1); parentHeader[i] = top.s; if (/\b(?:if|try)\b/.test(t)) top.c = true; if (/\b(?:break|return)\b/.test(t)) top.j = true; if (DATA_DRAIN_RE.test(t)) top.d = true; if (/^(?:while|for)\b/.test(t)) top.l = true; const inc = /^([A-Za-z_]\w*)\s*(?:\+=|-=|=(?!=)\s*\1\s*[+-])/.exec(t); if (inc) top.v.add(inc[1]); }
    const dm = /^(?:async\s+)?def\s+([A-Za-z_]\w*)\s*\(/.exec(t), lm = !dm && /^(while|for)\s+(.+):\s*$/.exec(t);
    const frame = dm ? { k: 'def', fn: dm[1] } : /^class\s+/.test(t) ? { k: 'class' } : lm ? { k: 'loop', lk: lm[1], lh: lm[2] } : t.endsWith(':') ? { k: 'other' } : null;
    if (frame) st.push({ ...frame, ind, s: i, c: false, j: false, d: false, l: false, v: new Set() });
  }
  while (st.length) close(st.pop());
  return { parentHeader, headerState };
}

function isPollingContext(skel, offset, lineNo, ctx) {
  if (ctx.hash) {
    ctx.py ??= buildPythonPollingTable(ctx.lines ?? []);
    const idx = lineNo - 1; if (idx < 0 || idx >= ctx.py.parentHeader.length) return false;
    for (let h = ctx.py.parentHeader[idx], hops = 0; h >= 0 && hops < 32; h = ctx.py.parentHeader[h], hops++) { if (ctx.py.headerState[h] === 1) return true; if (ctx.py.headerState[h] === -1) return false; }
    return false;
  }
  for (let br = ctx.ek[offset], hops = 0; br >= 0 && hops < 3; br = ctx.ek[br], hops++) {
    let p = br - 1; while (p >= 0 && /\s/.test(skel[p])) p--;
    const endBr = ctx.ck[br];
    if (p < 0 || skel[p] !== '(' || endBr < 0 || !/\bPromise\s*\.\s*race\s*$/.test(skel.slice(Math.max(0, p - 32), p))) continue;
    let aS = br + 1, cnt = 0, cS = -1, cE = -1;
    for (let k = aS; k < endBr; k++) { const j = skipNested(skel, k, endBr, ctx); if (j > 0) k = j - 1; else if (skel[k] === ',') { if (offset >= aS && offset < k) { cS = aS; cE = k; } aS = k + 1; cnt++; } }
    if (cnt > 0) {
      if (cS < 0 && offset >= aS && offset < endBr) { cS = aS; cE = endBr; }
      if (cS >= 0 && skel.slice(cS, offset).replace(/[\s(]+/g, '') === '') {
        const o = skel.indexOf('(', offset), cl = o >= 0 && o < cE ? ctx.cp[o] : -1;
        if (cl > o && cl < cE && skel.slice(cl + 1, cE).replace(/[\s)]+/g, '') === '') return true;
      }
    }
  }
  for (let p = offset - 1; p >= Math.max(0, offset - 160); ) {
    while (p >= 0 && /\s/.test(skel[p])) p--;
    if (p >= 0 && skel[p] === ')' && ctx.op[p] >= 0) { const o = ctx.op[p], { word } = prevWord(skel, o - 1); if ((word === 'while' || word === 'for') && isPollingLoop(word, skel.slice(o + 1, p), '')) return true; break; }
    const { word, start } = prevWord(skel, p); if (word === 'await' || word === 'return') { p = start - 1; continue; } break;
  }
  for (let b = ctx.eb[offset], hops = 0; b >= 0 && hops < 8; b = ctx.eb[b], hops++) {
    let k = b - 1; while (k >= 0 && /\s/.test(skel[k])) k--; if (k < 0) break;
    const endB = ctx.cb[b], body = endB > b ? skel.slice(b + 1, Math.min(endB, b + 4000)) : '';
    let fn = null, isFn = false;
    if (k >= 1 && skel[k - 1] === '=' && skel[k] === '>') {
      isFn = true; let q = k - 2; while (q >= 0 && /\s/.test(skel[q])) q--;
      q = skel[q] === ')' && ctx.op[q] >= 0 ? ctx.op[q] : prevWord(skel, q).start;
      fn = /(?:(?:const|let|var)\s+|(?:^|[;,\n{]\s*))([A-Za-z_$][\w$]*)\s*(?:=|:)\s*(?:async\s+)?$/.exec(skel.slice(Math.max(0, q - 120), q))?.[1] ?? null;
    } else if (skel[k] === ')' && ctx.op[k] >= 0) {
      const o = ctx.op[k], { word, start } = prevWord(skel, o - 1);
      if (word === 'while' || word === 'for') { if (isPollingLoop(word, skel.slice(o + 1, k), body)) return true; continue; }
      if (/^(?:if|catch|switch|with)$/.test(word)) continue;
      isFn = true; fn = word === 'function' ? /(?:(?:const|let|var)\s+|(?:^|[;,\n{]\s*))([A-Za-z_$][\w$]*)\s*(?:=|:)\s*(?:async\s+)?$/.exec(skel.slice(Math.max(0, start - 120), start))?.[1] ?? null : (/^[A-Za-z_$][\w$]*$/.test(word) ? word : null);
    } else if (prevWord(skel, k).word === 'do' && endB >= 0) {
      const wm = /^\s*while\s*\(/.exec(skel.slice(endB + 1, Math.min(skel.length, endB + 64))), wo = wm ? endB + 1 + wm[0].length - 1 : -1, wc = wo >= 0 ? ctx.cp[wo] : -1;
      if (wc > wo && isPollingLoop('do-while', skel.slice(wo + 1, wc), body)) return true; continue;
    }
    if (isFn) return Boolean(fn && POLL_HELPER_RE.test(fn) && (/\b(?:while|for)\s*\(/.test(body) || (/\b(?:if|try)\b/.test(body) && /\breturn\b/.test(body))));
  }
  return false;
}

export function collectTestFixedSleepFindings(text, { path = 'test/example.test.mjs' } = {}) {
  if (!canonicalRepoPath(path) || !isInspectableTestCodePath(path)) return [];
  const hash = /\.(?:py|rb)$/i.test(path), { skeleton, literals, lineComments, lineHasCode, lineHasComment } = tokenizeTestCode(String(text ?? ''), hash);
  const ls = buildLineStarts(skeleton), d = buildDelims(skeleton), pv = collectPositiveVars(skeleton, hash, d);
  const ctx = { hash, lines: hash ? skeleton.split('\n') : null, ...d }, out = [], seen = new Set();
  const rec = (off, snip) => {
    const line = lineNumberAt(ls, off); if (seen.has(line)) return;
    const com = adjComments(lineComments, lineHasCode, lineHasComment, line);
    if (SLEEP_ALLOW_RE.test(com) || hasTrackingRef(com) || isPollingContext(skeleton, off, line, ctx)) return;
    seen.add(line);
    const detail = `Fixed-duration sleep (${snip}) in test code introduces timing flakiness. Wait on a deterministic event, condition, or injected clock instead (or annotate with // pdd-allow-sleep: <reason> or a tracking #issue).`;
    out.push({ filePath: path, line, order: 20, code: 'test-fixed-sleep', category: 'test hygiene', defaultSeverity: 'warn', detail, warning: `Warning: test hygiene: ${path}:${line} [test-fixed-sleep] ${detail}` });
  };
  if (!hash) {
    const tpFns = new Set(), tpNs = new Set(['timersPromises']);
    for (const m of skeleton.matchAll(/\bimport\b/g)) {
      let k = m.index + 6; while (k < skeleton.length && /[ \t]/.test(skeleton[k])) k++;
      if (k >= skeleton.length || '(.'.includes(skeleton[k]) || skeleton.startsWith('__STR_', k)) continue;
      let bd = 0, end = k, lim = Math.min(skeleton.length, k + 240);
      while (end < lim) { const c = skeleton[end]; if (c === '{') bd++; else if (c === '}' && bd > 0) bd--; else if (c === ';' || (c === '\n' && !bd) || (!bd && c === 'i' && skeleton.startsWith('import', end) && (end === k || !/[\w$]/.test(skeleton[end - 1])) && !/[\w$]/.test(skeleton[end + 6] ?? ''))) break; end++; }
      const st = skeleton.slice(k, end), fm = /\bfrom\s+__STR_(\d+)__/.exec(st);
      if (!fm || !/^(?:node:)?timers\/promises$/.test(String(literals[Number(fm[1])] ?? '').trim())) continue;
      const cl = st.slice(0, fm.index).trim(), ns = /\*\s+as\s+([A-Za-z_$][\w$]*)/.exec(cl); if (ns) tpNs.add(ns[1]);
      const bs = cl.indexOf('{'), be = cl.lastIndexOf('}');
      if (bs >= 0 && be > bs) for (const p of cl.slice(bs + 1, be).split(',')) { const t = p.trim(), am = /^setTimeout\s+as\s+([A-Za-z_$][\w$]*)$/.exec(t); if (am) tpFns.add(am[1]); else if (t === 'setTimeout') tpFns.add('setTimeout'); }
      else if (!ns && /^[A-Za-z_$][\w$]*$/.test(cl)) tpNs.add(cl);
    }
    for (const m of skeleton.matchAll(/\bnew\s+Promise\s*\(/g)) {
      const o = m.index + m[0].length - 1, e = d.cp[o]; if (e < 0 || e - o > 600) continue;
      const body = skeleton.slice(o + 1, e), em = /^\s*(?:async\s+)?(?:\(\s*([A-Za-z_$][\w$]*)(?:\s*,\s*([A-Za-z_$][\w$]*))?\s*\)\s*=>|([A-Za-z_$][\w$]*)\s*=>|function(?:\s+[A-Za-z_$][\w$]*)?\s*\(\s*([A-Za-z_$][\w$]*)(?:\s*,\s*([A-Za-z_$][\w$]*))?\s*\))/.exec(body);
      if (!em) continue; const res = em[1] ?? em[3] ?? em[4], rej = em[2] ?? em[5] ?? null; if (!res || res === '_') continue;
      const rest = body.slice(em[0].length); if (/\b(?:addEventListener|once|on|reject|abort|clearInterval|clearTimeout)\b/.test(rest)) continue;
      const st = /\bsetTimeout\s*\(/.exec(rest), p = st && parseArgs(skeleton, o + 1 + em[0].length + st.index + st[0].length - 1, d, 3); if (!p || p.args.length < 2) continue;
      const cb = stripOuterParens(p.args[0]), eR = res.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
      if (cb !== res && ((rej && new RegExp(`(?<![\\w$])${rej.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}(?![\\w$])`).test(cb)) || /\b(?:reject|abort|kill|destroy|clearInterval|clearTimeout|throw|Error|exit)\b/.test(cb) || !/^(?:async\s+)?(?:\([^()]*\)|[A-Za-z_$][\w$]*)\s*=>|^function\b/.test(cb) || !new RegExp(`(?<![\\w$])${eR}\\s*\\(`).test(cb))) continue;
      const wp = new Set(), bef = skeleton.slice(Math.max(0, m.index - 120), m.index), ai = bef.lastIndexOf('=>');
      if (ai >= 0) { let q = Math.max(0, m.index - 120) + ai - 1; while (q >= Math.max(0, m.index - 120) && /\s/.test(skeleton[q])) q--; if (skeleton[q] === ')' && d.op[q] >= 0 && q - d.op[q] <= 120) addIds(skeleton.slice(d.op[q] + 1, q), wp); else if (/[\w$]/.test(skeleton[q])) wp.add(prevWord(skeleton, q).word); }
      if (isPosDelay(p.args[1], pv, wp)) rec(m.index, 'new Promise(...setTimeout...)');
    }
    for (const m of skeleton.matchAll(/(?<![\w$])([A-Za-z_$][\w$]*)\s*\.\s*(?:promises\s*\.\s*)?setTimeout\s*\(/g)) { if (!/\.\s*promises\s*\./.test(m[0]) && !tpNs.has(m[1])) continue; const p = parseArgs(skeleton, m.index + m[0].length - 1, d, 2); if (p?.args.length && isPosDelay(p.args[0], pv)) rec(m.index, `${m[1]}.setTimeout(...)`); }
    if (tpFns.size) for (const m of skeleton.matchAll(/(?<![.\w$])([A-Za-z_$][\w$]*)\s*\(/g)) { if (!tpFns.has(m[1]) || /\bfunction\s*$/.test(skeleton.slice(Math.max(0, m.index - 24), m.index))) continue; const p = parseArgs(skeleton, m.index + m[0].length - 1, d, 2); if (p?.args.length && isPosDelay(p.args[0], pv)) rec(m.index, `timers/promises ${m[1]}(...)`); }
    for (const m of skeleton.matchAll(/\bAtomics\s*\.\s*wait\s*\(/g)) { const p = parseArgs(skeleton, m.index + m[0].length - 1, d, 4); if (p?.args.length >= 4 && isPosDelay(p.args[3], pv)) rec(m.index, 'Atomics.wait(...)'); }
  }
  for (const m of skeleton.matchAll(/\b(time|asyncio)\s*\.\s*sleep\s*\(/g)) { const p = parseArgs(skeleton, m.index + m[0].length - 1, d, 2); if (p?.args.length && isPosDelay(p.args[0], pv)) rec(m.index, `${m[1]}.sleep(...)`); }
  for (const m of skeleton.matchAll(/(?<![.\w$])sleep\s*\(/g)) { if (/(?:\bfunction|\bdef)\s*$/.test(skeleton.slice(Math.max(0, m.index - 24), m.index))) continue; const o = m.index + m[0].length - 1, e = d.cp[o]; if (e < 0 || /^\s*\{/.test(skeleton.slice(e + 1, Math.min(skeleton.length, e + 16)))) continue; const p = parseArgs(skeleton, o, d, 2); if (p?.args.length && isPosDelay(p.args[0], pv)) rec(m.index, 'sleep(...)'); }
  return out.sort((a, b) => a.line - b.line);
}

export const lintTestFixedSleeps = (text, opts = {}) => collectTestFixedSleepFindings(text, opts).map(i => i.warning);

function findProp(skel, ob, d, prop, lits) {
  const eb = d.cb[ob]; if (eb < 0) return null;
  for (let ps = ob + 1, k = ps; k <= eb; ) {
    if (k < eb) { const j = skipNested(skel, k, eb, d); if (j > 0) { k = j; continue; } if (skel[k] !== ',') { k++; continue; } }
    let ci = -1;
    for (let s = ps; s < k; ) { const j = skipNested(skel, s, k, d); if (j > 0) s = j; else if (skel[s] === ':') { ci = s; break; } else s++; }
    if (ci >= 0 && (singleLit(skel.slice(ps, ci).trim(), lits) ?? skel.slice(ps, ci).trim()) === prop) return skel.slice(ci + 1, k).trim();
    ps = ++k;
  }
  return null;
}

export function collectTestUnexcusedSkipFindings(text, { path = 'test/example.test.mjs' } = {}) {
  if (!canonicalRepoPath(path) || !isInspectableTestCodePath(path)) return [];
  const hash = /\.(?:py|rb)$/i.test(path), { skeleton, literals, lineComments, lineHasCode, lineHasComment } = tokenizeTestCode(String(text ?? ''), hash);
  const ls = buildLineStarts(skeleton), d = buildDelims(skeleton), out = [], seen = new Set();
  const rec = (off, lbl) => {
    const line = lineNumberAt(ls, off); if (seen.has(line)) return;
    const com = adjComments(lineComments, lineHasCode, lineHasComment, line); if (SKIP_ALLOW_RE.test(com) || hasTrackingRef(com)) return;
    seen.add(line);
    const detail = `Unexcused skipped test (${lbl}) without a tracking issue reference or substantive reason. Cite an issue (e.g. #1234) or use a conditional guard instead of silently skipping tests.`;
    out.push({ filePath: path, line, order: 21, code: 'test-unexcused-skip', category: 'test hygiene', defaultSeverity: 'warn', detail, warning: `Warning: test hygiene: ${path}:${line} [test-unexcused-skip] ${detail}` });
  };
  if (!hash) {
    for (const m of skeleton.matchAll(/(?<![\w$.])((?:test|it|describe|suite)\s*\.\s*skip|xit|xtest|xdescribe)\s*\(/g)) { const p = parseArgs(skeleton, m.index + m[0].length - 1, d, 2); if (!p?.args[0] || !hasTrackingRef(exprText(p.args[0], literals))) rec(m.index, m[1].replace(/\s+/g, '')); }
    for (const m of skeleton.matchAll(/(?<![\w$.])(test|it|describe|suite)\s*\(/g)) {
      const p = parseArgs(skeleton, m.index + m[0].length - 1, d, 3); if (!p || p.args.length < 2) continue;
      const bAt = idx => { let k = p.argStarts[idx], e = k + p.args[idx].length; while (k < e && /\s/.test(skeleton[k])) k++; if (k >= e || skeleton[k] !== '{') return -1; const cl = d.cb[k]; if (cl < 0 || cl >= e) return -1; for (let t = cl + 1; t < e; t++) if (!/\s/.test(skeleton[t])) return -1; return k; };
      let oi = 1, ob = bAt(1); if (ob < 0) { oi = 0; ob = bAt(0); } if (ob < 0) continue;
      const sv = findProp(skeleton, ob, d, 'skip', literals), cv = sv !== null ? stripOuterParens(sv) : '';
      if (!cv || /^(?:false|undefined|null)$/.test(cv) || (oi === 1 && hasTrackingRef(exprText(p.args[0], literals)))) continue;
      if (cv === 'true' || cv === '!0') { rec(m.index, oi === 0 ? `${m[1]}({ skip: true }, ...)` : `${m[1]}(..., { skip: true })`); continue; }
      const ss = singleLit(cv, literals); if (ss !== null && !hasSubstantiveReason(ss)) rec(m.index, `${m[1]}(..., { skip: ${JSON.stringify(ss)} })`);
    }
    for (const m of skeleton.matchAll(/(?<![\w$.])(t|ctx)\s*\.\s*skip\s*\(/g)) { const p = parseArgs(skeleton, m.index + m[0].length - 1, d, 2); if (!p) continue; if (!p.args.length || !p.args[0].trim()) rec(m.index, `${m[1]}.skip()`); else { const rs = singleLit(p.args[0], literals); if (rs !== null && !hasSubstantiveReason(rs)) rec(m.index, `${m[1]}.skip(${JSON.stringify(rs)})`); } }
  } else {
    const checkPySkip = (idx, openParen, lbl, keyRe) => {
      const p = parseArgs(skeleton, openParen, d, 4);
      if (!p || !p.args.length || p.args.every(a => !a.trim())) { rec(idx, `${lbl}()`); return; }
      const re = p.args.map(a => keyRe.exec(a)?.[1]?.trim()).find(Boolean) ?? (!p.args[0].includes('=') ? p.args[0].trim() : null);
      if (!re) { rec(idx, `${lbl}(...)`); return; }
      const rs = singleLit(re, literals); if (rs !== null && !hasSubstantiveReason(rs)) rec(idx, `${lbl}(${JSON.stringify(rs)})`);
    };
    for (const m of skeleton.matchAll(/@(pytest\s*\.\s*mark\s*\.\s*skip|unittest\s*\.\s*skip)\b/g)) {
      const lbl = `@${m[1].replace(/\s+/g, '')}`; let w = m.index + m[0].length; while (w < skeleton.length && /[ \t]/.test(skeleton[w])) w++;
      if (skeleton[w] !== '(') rec(m.index, lbl); else checkPySkip(m.index, w, lbl, /^\s*reason\s*=\s*([\s\S]+)$/);
    }
    for (const m of skeleton.matchAll(/(?<![.\w])pytest\s*\.\s*skip\s*\(/g)) checkPySkip(m.index, m.index + m[0].length - 1, 'pytest.skip', /^\s*(?:reason|msg)\s*=\s*([\s\S]+)$/);
  }
  return out.sort((a, b) => a.line - b.line);
}

export const lintTestUnexcusedSkips = (text, opts = {}) => collectTestUnexcusedSkipFindings(text, opts).map(i => i.warning);

export function lintAutopilotTestHygiene({ root, files = [], config = {} } = {}) {
  const disabled = new Set(Array.isArray(config?.disable) ? config.disable : []);
  const rules = config?.rules && typeof config.rules === 'object' ? config.rules : {};
  const severityOf = code => (disabled.has(code) || rules[code] === 'off' ? 'off' : (rules[code] === 'error' ? 'error' : 'warn'));
  const warnings = [], errors = [], findings = [];
  for (const rel of files) {
    if (!canonicalRepoPath(rel) || !isInspectableTestCodePath(rel)) continue;
    const text = readSafeUtf8(root, rel);
    if (text === null) continue;
    for (const item of [...collectTestFixedSleepFindings(text, { path: rel }), ...collectTestUnexcusedSkipFindings(text, { path: rel })]) {
      const sev = severityOf(item.code);
      if (sev === 'off') continue;
      const line = sev === 'error' ? item.warning.replace(/^Warning:/, 'Error:') : item.warning;
      findings.push({ ...item, path: rel, severity: sev });
      if (sev === 'error') errors.push(line);
      else warnings.push(line);
    }
  }
  return { ok: errors.length === 0, errors, warnings, findings };
}
