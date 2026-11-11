// Generated from prompts/cli/autopilot-ci-jobs.prompt.md (sha256: 4b5e5a5ccaead3975b2e58544fc2154c29ce483bfd5d9a19c5fd253befef6ef9).
import * as nativeFs from 'node:fs';
import { join, isAbsolute } from 'node:path';
import { redactSecrets } from './secret-redaction.mjs';
import { workflowTriggers, workflowRunsOnPr } from './autopilot-core.mjs';

const KIB = 1024, MAX_FILE = 256 * KIB, MAX_FILES = 50, MAX_LINES = 5000, MAX_DEPTH = 40, MAX_ENTRIES = 256;
const HOUR = 60 * 60 * 1000, DAY = 24 * HOUR, ASK_WAIT = 6 * HOUR, KEEP = 14 * DAY, KEEP_RECORDS = 50;
const CACHE = 'ci-jobs.json', SCHEMA = 'pdd.ci-jobs.v1', MISSED = 'ci-missed.jsonl', DEFAULT_BRANCH = 'pdd/core-autopilot';
const GOOD = ['success', 'neutral', 'skipped'];
const SHA = /^[0-9a-f]{40}$/;
const EXPR = /\$\{\{([\s\S]*?)\}\}/g;
const SECRET = /\bsecrets\s*(?:\.|\[)|\bgithub\.token\b/;
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const scalarish = value => value === null || ['string', 'boolean', 'number'].includes(typeof value);
const text = value => value === null || value === undefined ? '' : String(value);
const oneLine = (value, max = 300) => String(value ?? '').replace(/\s+/g, ' ').trim().slice(0, max);
const short = sha => String(sha ?? '').slice(0, 7);
const readJson = (fs, file) => { try { return JSON.parse(fs.readFileSync(file, 'utf8')); } catch { return null; } };
function save(fs, file, content) {
  fs.mkdirSync(join(file, '..'), { recursive: true, mode: 0o700 });
  const temp = `${file}.${process.pid}.tmp`;
  fs.writeFileSync(temp, content, { mode: 0o600 }); fs.renameSync(temp, file);
}
const familyOf = platform => ({ linux: 'Linux', darwin: 'macOS', win32: 'Windows' })[platform] ?? String(platform);
const githubError = (method, endpoint, status) => Object.assign(new Error(`GitHub ${method} ${endpoint.split('?')[0]} returned ${status || 'no reply'}`), { code: 'github' });

// ---- The YAML subset ------------------------------------------------------------------------------------
// A line reader for the YAML that workflow files use. What it cannot read is an error that names the line: the caller
// counts that file as CI-only (the safe side).
const yamlError = (line, why) => Object.assign(new Error(`line ${line}: ${why}`), { code: 'yaml' });
const isItem = value => value === '-' || value.startsWith('- ');
function next(p) {
  for (let k = p.i; k < p.end; k++) {
    if (p.over.has(k)) return k;
    const raw = p.lines[k];
    if (raw.trim() && !/^\s*#/.test(raw)) return k;
  }
  return -1;
}
function lineAt(p, k) {
  if (p.over.has(k)) return p.over.get(k);
  const raw = p.lines[k];
  if (/^---(\s|$)/.test(raw)) throw yamlError(k + 1, 'a second document is not supported');
  const m = /^( *)(.*?)\s*$/.exec(raw);
  if (m[2].startsWith('\t')) throw yamlError(k + 1, 'a tab in the indentation');
  return { indent: m[1].length, text: m[2] };
}
const plainScalar = value => ['', '~', 'null', 'Null', 'NULL'].includes(value) ? null : ['true', 'True', 'TRUE'].includes(value) ? true : ['false', 'False', 'FALSE'].includes(value) ? false : value;
const ESCAPES = { '\\': '\\', '"': '"', '/': '/', n: '\n', t: '\t', r: '\r', 0: '\0', b: '\b', f: '\f' };
function quoted(t, at, k) {
  let out = '', j = at + 1;
  for (;;) {
    if (j >= t.length) throw yamlError(k + 1, 'a quoted scalar over several lines is not supported');
    const c = t[j];
    if (t[at] === "'") {
      if (c === "'") { if (t[j + 1] === "'") { out += "'"; j += 2; continue; } return { value: out, end: j + 1 }; }
      out += c; j++; continue;
    }
    if (c === '"') return { value: out, end: j + 1 };
    if (c !== '\\') { out += c; j++; continue; }
    const e = t[j + 1];
    if (e !== undefined && Object.hasOwn(ESCAPES, e)) { out += ESCAPES[e]; j += 2; continue; }
    const size = e === 'x' ? 2 : e === 'u' ? 4 : 0, digits = t.slice(j + 2, j + 2 + size);
    if (!size || digits.length !== size || !/^[0-9a-fA-F]+$/.test(digits)) throw yamlError(k + 1, 'an escape that is not supported');
    out += String.fromCharCode(parseInt(digits, 16)); j += 2 + size;
  }
}
const checkKey = (key, k) => {
  if (key === '<<') throw yamlError(k + 1, 'merge keys are not supported');
  if (key === '__proto__') throw yamlError(k + 1, 'the key __proto__ is not allowed');
  return key;
};
function flow(t, at, k, depth) {
  if (depth > MAX_DEPTH) throw yamlError(k + 1, `the nesting is deeper than ${MAX_DEPTH}`);
  const close = t[at] === '[' ? ']' : '}', list = close === ']', out = list ? [] : {};
  let j = at + 1;
  const space = () => { while (j < t.length && /\s/.test(t[j])) j++; };
  const node = () => {
    space();
    const c = t[j];
    if (c === '[' || c === '{') { const f = flow(t, j, k, depth + 1); j = f.end; return f.value; }
    if (c === '"' || c === "'") { const q = quoted(t, j, k); j = q.end; return q.value; }
    if (c !== undefined && '&*!%@`|>'.includes(c)) throw yamlError(k + 1, 'a YAML feature that is not supported in a flow collection');
    const from = j;
    while (j < t.length && !',[]{}'.includes(t[j]) && !(t[j] === ':' && (j + 1 >= t.length || /[\s,[\]{}]/.test(t[j + 1])))) {
      if (t[j] === '#' && j > from && /\s/.test(t[j - 1])) throw yamlError(k + 1, 'a comment inside a flow collection');
      j++;
    }
    if (j === from) throw yamlError(k + 1, 'an empty item in a flow collection');
    return plainScalar(t.slice(from, j).trim());
  };
  for (;;) {
    space();
    if (j >= t.length) throw yamlError(k + 1, 'a flow collection over several lines is not supported');
    if (t[j] === close) return { value: out, end: j + 1 };
    if (list) {
      out.push(node());
      space();
      if (t[j] === ':') throw yamlError(k + 1, 'a mapping inside a flow sequence is not supported');
    } else {
      const key = node();
      if (!scalarish(key) || key === null) throw yamlError(k + 1, 'a flow mapping key that is not supported');
      const name = checkKey(String(key), k);
      if (Object.hasOwn(out, name)) throw yamlError(k + 1, `the key "${name}" comes twice`);
      space();
      let value = null;
      if (t[j] === ':') { j++; space(); if (t[j] !== ',' && t[j] !== close) value = node(); }
      out[name] = value;
    }
    space();
    if (t[j] === ',') { j++; continue; }
    if (t[j] !== close) throw yamlError(k + 1, 'a flow collection that is not supported');
  }
}
const afterValue = (rest, k) => { if (!/^(\s+#.*)?\s*$/.test(rest)) throw yamlError(k + 1, 'text after a value'); };
// The value on a line: empty (the value is on the next lines), a block scalar header, or one value.
function inlineValue(value, k) {
  const t = value.trim();
  if (!t || t.startsWith('#')) return { empty: true };
  const c = t[0];
  if (c === '"' || c === "'") { const q = quoted(t, 0, k); afterValue(t.slice(q.end), k); return { value: q.value }; }
  if (c === '[' || c === '{') { const f = flow(t, 0, k, 0); afterValue(t.slice(f.end), k); return { value: f.value }; }
  if (c === '|' || c === '>') {
    const m = /^([|>])([1-9])?([-+])?([1-9])?(\s+#.*)?$/.exec(t);
    if (!m || (m[2] && m[4])) throw yamlError(k + 1, 'a block scalar header that is not supported');
    return { block: { style: m[1], indent: Number(m[2] ?? m[4] ?? 0), chomp: m[3] ?? '' } };
  }
  if ('&*!%@`'.includes(c)) throw yamlError(k + 1, `"${c}" (an anchor, alias, tag or reserved start) is not supported`);
  if (c === '?' && (t.length === 1 || /\s/.test(t[1]))) throw yamlError(k + 1, 'complex keys are not supported');
  let end = t.length;
  for (let j = 1; j < t.length; j++) if (t[j] === '#' && /\s/.test(t[j - 1])) { end = j; break; }
  const plain = t.slice(0, end).trim();
  if (/:(\s|$)/.test(plain)) throw yamlError(k + 1, 'a value with ": " in it (quote the value)');
  return { value: plainScalar(plain) };
}
// "KEY: REST" on a line, or null when the line is no key line.
function splitKey(t, k) {
  let key, rest;
  if (t[0] === '"' || t[0] === "'") {
    const q = quoted(t, 0, k), m = /^\s*:(?:\s+|$)/.exec(t.slice(q.end));
    if (!m) return null;
    key = q.value; rest = t.slice(q.end + m[0].length);
  } else {
    if (/^[[{#]/.test(t) || isItem(t)) return null;
    let at = -1;
    for (let j = 0; j < t.length; j++) {
      if (t[j] === '#' && j > 0 && /\s/.test(t[j - 1])) return null;
      if (t[j] === ':' && (j + 1 === t.length || /\s/.test(t[j + 1]))) { at = j; break; }
    }
    if (at < 0) return null;
    key = t.slice(0, at).trim(); rest = t.slice(at + 1).trim();
    if (!key) throw yamlError(k + 1, 'an empty key');
    if (/^[?&*!|>%@`]/.test(key)) throw yamlError(k + 1, `the key "${key}" uses a YAML feature that is not supported`);
  }
  return { key: checkKey(key, k), rest };
}
function fold(lines) {
  let out = lines[0] ?? '';
  for (let i = 1; i < lines.length; i++) {
    const prev = lines[i - 1], line = lines[i];
    if (line === '') { out += '\n'; continue; }
    out += (prev === '' ? '' : /^\s/.test(line) || /^\s/.test(prev) ? '\n' : ' ') + line;
  }
  return out;
}
function blockScalar(p, parent, { style, indent, chomp }) {
  let content = indent ? Math.max(parent, 0) + indent : 0;
  if (!content) {
    for (let x = p.i; x < p.end; x++) if (p.lines[x].trim()) { content = /^ */.exec(p.lines[x])[0].length; break; }
    if (content <= parent) content = parent + 1;
  }
  const lines = [];
  let x = p.i;
  for (; x < p.end; x++) {
    const raw = p.lines[x];
    if (!raw.trim()) { lines.push(raw.length > content ? raw.slice(content) : ''); continue; }
    if (/^ */.exec(raw)[0].length < content) break;
    lines.push(raw.slice(content));
  }
  p.i = x;
  let n = lines.length;
  while (n > 0 && !lines[n - 1].trim()) n--;
  const main = lines.slice(0, n), trail = lines.length - n;
  if (!main.length) return chomp === '+' ? '\n'.repeat(trail) : '';
  const body = style === '|' ? main.join('\n') : fold(main);
  return chomp === '-' ? body : chomp === '+' ? `${body}\n${'\n'.repeat(trail)}` : `${body}\n`;
}
function parseNode(p, parent, depth) {
  if (depth > MAX_DEPTH) throw yamlError(p.i + 1, `the nesting is deeper than ${MAX_DEPTH}`);
  const k = next(p);
  if (k < 0) return null;
  const line = lineAt(p, k);
  if (line.indent <= parent) return null;
  if (isItem(line.text)) return parseSeq(p, line.indent, depth);
  if (splitKey(line.text, k)) return parseMap(p, line.indent, depth);
  p.over.delete(k); p.i = k + 1;
  const v = inlineValue(line.text, k);
  if (v.block) return blockScalar(p, parent, v.block);
  const after = next(p);
  if (after >= 0 && lineAt(p, after).indent > parent) throw yamlError(after + 1, 'a plain scalar goes on to the next line');
  return v.empty ? null : v.value;
}
function valueAfterKey(p, rest, indent, depth, k) {
  const v = inlineValue(rest, k);
  if (v.block) return blockScalar(p, indent, v.block);
  if (!v.empty) return v.value;
  const n = next(p);
  if (n < 0) return null;
  const line = lineAt(p, n);
  if (line.indent > indent) return parseNode(p, indent, depth + 1);
  if (line.indent === indent && isItem(line.text)) return parseSeq(p, indent, depth + 1);
  return null;
}
function parseMap(p, indent, depth) {
  const map = {};
  for (;;) {
    const k = next(p);
    if (k < 0) break;
    const line = lineAt(p, k);
    if (line.indent < indent) break;
    if (line.indent > indent) throw yamlError(k + 1, 'unexpected indentation');
    if (isItem(line.text)) throw yamlError(k + 1, 'a list item where a key was expected');
    const sk = splitKey(line.text, k);
    if (!sk) throw yamlError(k + 1, 'expected "KEY: VALUE"');
    if (Object.hasOwn(map, sk.key)) throw yamlError(k + 1, `the key "${sk.key}" comes twice`);
    p.over.delete(k); p.i = k + 1;
    map[sk.key] = valueAfterKey(p, sk.rest, indent, depth, k);
  }
  return map;
}
function parseSeq(p, indent, depth) {
  const list = [];
  for (;;) {
    const k = next(p);
    if (k < 0) break;
    const line = lineAt(p, k);
    if (line.indent < indent) break;
    if (line.indent > indent) throw yamlError(k + 1, 'unexpected indentation');
    if (!isItem(line.text)) break;
    const after = line.text.slice(1), rest = after.trimStart(), col = indent + 1 + after.length - rest.length;
    p.over.delete(k);
    if (!rest || rest.startsWith('#')) { p.i = k + 1; list.push(parseNode(p, indent, depth + 1)); continue; }
    if (isItem(rest) || splitKey(rest, k)) {
      p.over.set(k, { indent: col, text: rest }); p.i = k;
      list.push(isItem(rest) ? parseSeq(p, col, depth + 1) : parseMap(p, col, depth + 1));
      continue;
    }
    p.i = k + 1;
    const v = inlineValue(rest, k);
    list.push(v.block ? blockScalar(p, indent, v.block) : v.value);
  }
  return list;
}
export function parseWorkflowYaml(source) {
  const lines = String(source ?? '').replace(/^﻿/, '').split(/\r?\n/);
  if (lines.length > MAX_LINES) throw yamlError(MAX_LINES + 1, `the file has more than ${MAX_LINES} lines`);
  const p = { lines, i: 0, end: lines.length, over: new Map() };
  const stop = lines.findIndex(line => /^\.\.\.(\s+#.*)?\s*$/.test(line));
  if (stop >= 0) {
    p.end = stop;
    const extra = lines.findIndex((line, k) => k > stop && line.trim() && !/^\s*#/.test(line));
    if (extra >= 0) throw yamlError(extra + 1, 'text after the end of the document');
  }
  const first = next(p);
  if (first >= 0 && /^---(\s+#.*)?\s*$/.test(lines[first])) p.i = first + 1;
  const value = parseNode(p, -1, 0), rest = next(p);
  if (rest >= 0) throw yamlError(rest + 1, 'unexpected text');
  return value;
}

// ---- Shell commands -------------------------------------------------------------------------------------
// A bounded reader of a step's shell text: which commands are setup, the full suite, or real work.
function splitOutside(line, test) {
  const out = []; let cur = '', q = null;
  for (let i = 0; i < line.length; i++) {
    const c = line[i];
    if (q) { cur += c; if (c === q) q = null; else if (c === '\\' && q === '"' && i + 1 < line.length) cur += line[++i]; continue; }
    if (c === "'" || c === '"') { q = c; cur += c; continue; }
    if (c === '\\' && i + 1 < line.length) { cur += c + line[++i]; continue; }
    const cut = test(line, i);
    if (cut) { out.push(cur); cur = ''; i += cut - 1; continue; }
    cur += c;
  }
  out.push(cur);
  return out.map(part => part.trim());
}
const splitCommands = line => splitOutside(line, (s, i) => s[i] === ';' ? 1 : (s[i] === '&' && s[i + 1] === '&') || (s[i] === '|' && s[i + 1] === '|') ? 2 : 0);
const splitPipes = line => splitOutside(line, (s, i) => s[i] === '|' && s[i + 1] !== '|' && s[i - 1] !== '|' ? 1 : 0);
function words(command) {
  const out = []; let cur = '', q = null, has = false;
  for (let i = 0; i < command.length; i++) {
    const c = command[i];
    if (q) { if (c === q) q = null; else if (c === '\\' && q === '"' && i + 1 < command.length) cur += command[++i]; else cur += c; continue; }
    if (c === "'" || c === '"') { q = c; has = true; continue; }
    if (c === '\\' && i + 1 < command.length) { cur += command[++i]; continue; }
    if (/\s/.test(c)) { if (cur || has) out.push(cur); cur = ''; has = false; continue; }
    cur += c;
  }
  if (cur || has) out.push(cur);
  return out;
}
// Lines joined after a final "\", here-document bodies kept with their command, blank and comment lines gone.
function commandLines(script) {
  const raw = String(script).split(/\r?\n/), out = [];
  for (let i = 0; i < raw.length;) {
    let line = raw[i++];
    while (/\\$/.test(line) && i < raw.length) line = `${line.slice(0, -1)} ${raw[i++]}`;
    const doc = /<<(-?)\s*(['"]?)([A-Za-z_]\w*)\2/.exec(line);
    if (doc) { while (i < raw.length && (doc[1] ? raw[i].replace(/^\t+/, '') : raw[i]) !== doc[3]) i++; i++; }
    const t = line.trim();
    if (t && !t.startsWith('#')) out.push(t);
  }
  return out;
}
const NPM_TEST = ['npm test', 'npm run test', 'npm t', 'npm run-script test'];
const LEAD = new Set(['if', 'elif', 'then', 'else', 'do', 'while', 'until', '!']);
const CONTROL = new Set(['fi', 'done', 'esac', '{', '}', '(', ')', 'for', 'case']);
const PACKAGES = new Set(['apt-get', 'apt', 'brew', 'yum', 'dnf', 'apk', 'choco', 'snap', 'port', 'pacman', 'zypper']);
const ASSIGN = /^[A-Za-z_]\w*=/, NAME = /^[A-Za-z_]\w*$/;
const normal = value => words(String(value ?? '')).join(' ');
function suiteSpellings(testCommand, scripts) {
  const set = new Set(), command = normal(testCommand), test = typeof scripts?.test === 'string' ? normal(scripts.test) : '';
  if (command) set.add(command);
  if (command && (NPM_TEST.includes(command) || command === test)) { for (const spelling of NPM_TEST) set.add(spelling); if (test) set.add(test); }
  return set;
}
function isSuite(command, suite) {
  const parts = splitPipes(command);
  if (parts.slice(1).some(part => words(part)[0] !== 'tee')) return false;
  const w = words(parts[0]), kept = [];
  for (let i = 0; i < w.length; i++) {
    const m = /^(?:\d*|&)>>?(&\d+|.*)$/.exec(w[i]);
    if (m) { if (!m[1]) i++; continue; }
    kept.push(w[i]);
  }
  return suite.has(kept.join(' '));
}
const isInstall = v => (v[0] === 'npm' && ['ci', 'install', 'i'].includes(v[1])) || (v[0] === 'pnpm' && ['install', 'i'].includes(v[1]))
  || (v[0] === 'yarn' && (v[1] === 'install' || v.slice(1).every(word => word.startsWith('-'))));
function classify(command, suite) {
  const w = words(command);
  while (w.length && LEAD.has(w[0])) w.shift();
  if (!w.length || CONTROL.has(w[0])) return 'control';
  if (['set', 'exit', 'true', ':'].includes(w[0]) || (w.length === 1 && ASSIGN.test(w[0]))
    || (['export', 'readonly', 'local'].includes(w[0]) && w.slice(1).every(word => ASSIGN.test(word) || NAME.test(word) || /^-\w+$/.test(word)))) return 'plumbing';
  if (['echo', 'printf'].includes(w[0])) return 'probe';
  if (['command', 'which', 'type', 'hash'].includes(w[0]) && w.slice(1).every(word => /^-\w+$/.test(word) || /^[\w.+-]+$/.test(word))) return 'probe';
  if (w.length === 2 && ['--version', '-v', '-V', 'version'].includes(w[1])) return 'probe';
  let v = w;
  while (v.length && ASSIGN.test(v[0])) v = v.slice(1);
  const sudo = v[0] === 'sudo';
  if (sudo) { v = v.slice(1); while (v.length && (v[0].startsWith('-') || ASSIGN.test(v[0]))) v = v.slice(1); }
  if (v.length && PACKAGES.has(v[0])) return 'system';
  if (sudo) return 'sudo';
  if (isInstall(v)) return 'install';
  if (isSuite(command, suite)) return 'suite';
  return 'real';
}
function stepKind(script, suite) {
  const commands = commandLines(script).flatMap(splitCommands).filter(Boolean), kinds = commands.map(command => classify(command, suite));
  const has = kind => kinds.includes(kind);
  if (has('system') && has('real')) return { reason: { need: 'system packages', why: 'installs system packages in a step with other commands' } };
  if (has('sudo')) return { reason: { need: 'sudo', why: 'runs a command with sudo' } };
  if (has('real')) return { kind: 'real' };
  if (has('suite')) return { kind: 'suite', parts: commands.filter((_, i) => kinds[i] === 'suite') };
  return { kind: 'setup' };
}

// ---- Conditions, expressions, matrix --------------------------------------------------------------------
// A condition for a ready (not draft) PR: true, false, or null when Autopilot cannot check it.
function termValue(t) {
  let m;
  if ((m = /^github\.event_name\s*(==|!=)\s*'([^']*)'$/.exec(t))) return (m[2] === 'pull_request') === (m[1] === '==');
  if ((m = /^github\.event\.pull_request\.draft\s*(==|!=)\s*(true|false)$/.exec(t))) return (m[2] === 'false') === (m[1] === '==');
  if (t === '!github.event.pull_request.draft') return true;
  if (t === 'github.event.pull_request.draft') return false;
  if (['always()', 'success()', '!cancelled()', 'true'].includes(t)) return true;
  if (['failure()', 'cancelled()', 'false'].includes(t)) return false;
  return null;
}
function condition(value) {
  if (value === undefined || value === null) return true;
  if (typeof value === 'boolean') return value;
  if (typeof value !== 'string') return null;
  let s = value.trim();
  const m = /^\$\{\{([\s\S]*)\}\}$/.exec(s);
  if (m) s = m[1].trim();
  if (!s || /[()]/.test(s.replace(/\b(?:always|success|failure|cancelled)\(\)/g, ''))) return null;
  let any = false;
  for (const or of s.split('||')) {
    let all = true;
    for (const term of or.split('&&')) { const t = termValue(term.trim()); if (t === null) return null; all = all && t; }
    any = any || all;
  }
  return any;
}
// The inner texts of the ${{ }} expressions of a value; null when a "${{" has no "}}".
function expressions(value) {
  const s = String(value ?? '');
  return s.replace(EXPR, '').includes('${{') ? null : [...s.matchAll(EXPR)].map(m => m[1].trim());
}
function knownExpression(inner, entry, env) {
  let m;
  if ((m = /^matrix\.([A-Za-z_][\w-]*)$/.exec(inner))) return Object.hasOwn(entry, m[1]);
  if (/^runner\.(?:os|temp)$/.test(inner) || inner === 'github.workspace') return true;
  if ((m = /^env\.([A-Za-z_]\w*)$/.exec(inner))) return Object.hasOwn(env, m[1]) && !env[m[1]].includes('${{');
  return false;
}
const fillMatrix = (value, entry) => String(value).replace(EXPR, (all, inner) => {
  const m = /^\s*matrix\.([A-Za-z_][\w-]*)\s*$/.exec(inner);
  return m && Object.hasOwn(entry, m[1]) ? text(entry[m[1]]) : all;
});
function expandMatrix(matrix) {
  if (matrix === undefined || matrix === null) return { entries: [{}] };
  if (!object(matrix)) return { error: 'builds its matrix from an expression' };
  const axes = Object.entries(matrix).filter(([key]) => key !== 'include' && key !== 'exclude');
  let entries = axes.length ? [{}] : [];
  for (const [key, values] of axes) {
    if (!Array.isArray(values) || !values.length || !values.every(scalarish)) return { error: `has a matrix axis "${key}" that Autopilot cannot read` };
    const product = [];
    for (const entry of entries) for (const value of values) {
      product.push({ ...entry, [key]: value });
      if (product.length > MAX_ENTRIES) return { error: `has more than ${MAX_ENTRIES} matrix entries` };
    }
    entries = product;
  }
  const maps = list => list === undefined || list === null ? [] : Array.isArray(list) && list.every(item => object(item) && Object.values(item).every(scalarish)) ? list : null;
  const exclude = maps(matrix.exclude), include = maps(matrix.include);
  if (!exclude || !include) return { error: 'has a matrix include or exclude that Autopilot cannot read' };
  const same = (a, b) => String(a) === String(b), original = new Set(axes.map(([key]) => key));
  entries = entries.filter(entry => !exclude.some(ex => Object.entries(ex).every(([key, value]) => Object.hasOwn(entry, key) && same(entry[key], value))));
  const added = [];
  for (const item of include) {
    let fit = false;
    for (const entry of entries) if (Object.entries(item).every(([key, value]) => !original.has(key) || same(entry[key], value))) { Object.assign(entry, item); fit = true; }
    if (!fit) added.push({ ...item });
  }
  entries.push(...added);
  if (entries.length > MAX_ENTRIES) return { error: `has more than ${MAX_ENTRIES} matrix entries` };
  return { entries: entries.length ? entries : [{}] };
}
const jobName = (job, id) => object(job) && scalarish(job.name) && text(job.name).trim() ? text(job.name).trim() : id;
function checkName(job, id, entry) {
  const name = jobName(job, id), values = Object.values(entry);
  if (name.includes('${{')) return fillMatrix(name, entry);
  return values.length ? `${name} (${values.map(text).join(', ')})` : name;
}
function versionMatches(spec, version) {
  const s = text(spec).trim().replace(/^v/, ''), [major, minor, patch] = String(version).split('.');
  let m;
  if ((m = /^(\d+)(?:\.x)?$/.exec(s))) return m[1] === major;
  if ((m = /^(\d+)\.(\d+)(?:\.x)?$/.exec(s))) return m[1] === major && m[2] === minor;
  if ((m = /^(\d+)\.(\d+)\.(\d+)$/.exec(s))) return m[1] === major && m[2] === minor && m[3] === patch;
  return false;
}
function runnerReason(runsOn, entry, family) {
  if (runsOn === undefined) return { need: 'unreadable', why: 'Autopilot could not read the job: it has no runs-on' };
  const label = Array.isArray(runsOn) && runsOn.length === 1 ? runsOn[0] : runsOn;
  if (typeof label !== 'string') {
    const shown = Array.isArray(runsOn) ? runsOn.map(text).join(', ') : 'a runner group';
    return { need: `runner ${shown}`, why: `runs on ${shown}` };
  }
  const filled = fillMatrix(label, entry).trim();
  const own = /^ubuntu-/.test(filled) ? 'Linux' : /^macos-/.test(filled) ? 'macOS' : /^windows-/.test(filled) ? 'Windows' : null;
  if (!own) return { need: `runner ${filled}`, why: `runs on ${filled}` };
  return own === family ? null : { need: own, why: `runs on ${filled} (this machine is ${family})` };
}

// ---- Sort -----------------------------------------------------------------------------------------------
const insideCheckout = path => !path.startsWith('/') && !path.startsWith('~') && !/^[A-Za-z]:/.test(path) && !path.split(/[\\/]+/).includes('..');
const runDefaults = value => object(value) && object(value.run) ? value.run : {};
function sortStep(step, job, wf, entry, ctx) {
  if (step.uses !== undefined) {
    if (typeof step.uses !== 'string') return { reason: { need: 'unreadable', why: 'Autopilot could not read a step' } };
    const action = step.uses.trim(), ref = action.split('@')[0], [owner, repo] = ref.split('/');
    if (/^actions\/(?:checkout|cache)(?:\/|$)/.test(ref) || /^actions\/setup-[\w.-]+$/.test(ref)) {
      const uses = object(step.with) ? step.with : {};
      if (ref === 'actions/setup-node') {
        const version = uses['node-version'];
        if (typeof version === 'string' && /\$\{\{\s*matrix\./.test(version)) {
          const shown = fillMatrix(version, entry);
          if (!versionMatches(shown, ctx.machine.node)) return { reason: { need: `Node ${shown}`, why: `uses Node ${shown} (this machine has Node ${ctx.machine.node})` } };
        }
      } else if (ref.startsWith('actions/setup-')) {
        const tool = ref.slice('actions/setup-'.length);
        for (const value of Object.values(uses)) if (typeof value === 'string' && /\$\{\{\s*matrix\./.test(value)) {
          const shown = fillMatrix(value, entry);
          return { reason: { need: `${tool} ${shown}`, why: `uses ${tool} ${shown} from the matrix (Autopilot cannot know this machine's ${tool} version)` } };
        }
      }
      return { kind: 'setup' };
    }
    const need = /^github\/codeql-action(?:\/|$)/.test(ref) ? 'CodeQL' : action.startsWith('./') ? 'local action' : action.startsWith('docker://') ? 'docker image' : owner && repo ? `${owner}/${repo}` : 'action';
    return { reason: { need, why: `uses ${oneLine(action, 120)}` } };
  }
  if (typeof step.run !== 'string') return { reason: { need: 'unreadable', why: 'Autopilot could not read a step' } };
  const when = condition(step.if);
  if (when === null) return { reason: { need: 'condition', why: `has a step condition that Autopilot cannot check: ${oneLine(step.if, 120)}` } };
  if (when === false) return { kind: 'skip' };
  const keepGoing = step['continue-on-error'];
  if (keepGoing === true) return { kind: 'skip' };
  if (keepGoing !== undefined && keepGoing !== false) return { reason: { need: 'condition', why: `has a continue-on-error that Autopilot cannot check: ${oneLine(keepGoing, 120)}` } };
  if (typeof step.if === 'string' && /always\(\)|!cancelled\(\)/.test(step.if) && step.run.includes('GITHUB_STEP_SUMMARY')) return { kind: 'skip' };
  const shell = step.shell ?? runDefaults(job.defaults).shell ?? runDefaults(wf.defaults).shell ?? null;
  if (shell !== null && !['bash', 'sh'].includes(shell)) return { reason: { need: 'shell', why: `uses the shell ${oneLine(shell, 60)}` } };
  // The working directory: only matrix values and github.workspace (the checkout itself) are filled in here.
  let wd = step['working-directory'] ?? runDefaults(job.defaults)['working-directory'] ?? runDefaults(wf.defaults)['working-directory'] ?? null;
  if (wd !== null) {
    const filled = typeof wd === 'string' ? fillMatrix(wd, entry).replace(/\$\{\{\s*github\.workspace\s*\}\}/g, '.') : null;
    if (filled === null || filled.includes('${{') || !insideCheckout(filled.trim())) return { reason: { need: 'working directory', why: `uses the working directory ${oneLine(wd, 80)}` } };
    wd = filled.trim().replace(/^(?:\.\/)+/, '') || '.';
  }
  const env = {};
  for (const map of [wf.env, job.env, step.env]) {
    if (map === undefined || map === null) continue;
    if (!object(map)) return { reason: { need: 'unreadable', why: 'has an env that Autopilot cannot read' } };
    for (const [name, value] of Object.entries(map)) {
      if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(name) || !scalarish(value)) return { reason: { need: 'unreadable', why: 'has an env that Autopilot cannot read' } };
      env[name] = text(value);
    }
  }
  for (const value of [step.run, ...Object.values(env)]) {
    const found = expressions(value);
    if (found === null) return { reason: { need: 'expression', why: 'has a "${{" with no "}}"' } };
    const unknown = found.find(inner => !knownExpression(inner, entry, env));
    if (unknown !== undefined) return { reason: { need: 'expression', why: `uses the expression \${{ ${oneLine(unknown, 80)} }}` } };
  }
  if (/\bGITHUB_(?:ENV|PATH)\b/.test(step.run)) return { reason: { need: 'GITHUB_ENV', why: 'passes values to later steps through GITHUB_ENV or GITHUB_PATH' } };
  const kind = stepKind(step.run, ctx.suite);
  if (kind.reason || kind.kind !== 'real') return kind;
  const name = typeof step.name === 'string' && step.name.trim() ? oneLine(step.name, 80) : oneLine(step.run.split('\n').find(line => line.trim()) ?? 'run', 80);
  return { kind: 'real', step: { name, shell, script: step.run, workingDirectory: wd, env } };
}
function sortEntry(job, wf, entry, ctx) {
  const runner = runnerReason(job['runs-on'], entry, ctx.family);
  if (runner) return { reason: runner };
  const steps = [], parts = [];
  for (const step of job.steps) {
    const s = sortStep(step, job, wf, entry, ctx);
    if (s.reason) return { reason: s.reason };
    if (s.kind === 'suite') parts.push(...s.parts);
    if (s.kind === 'real') steps.push(s.step);
  }
  const suite = parts.length > 0;
  if (steps.length) return { kind: 'local', suite, steps, commands: steps.map(step => step.script), why: `runs ${steps.length} command(s) that Autopilot can run on this machine${suite ? ', and the full test command' : ''}` };
  return { kind: 'covered', suite, steps: [], commands: parts, why: suite ? `runs only the full test command (${ctx.testCommand})` : 'runs only setup steps' };
}
function sortJob(file, wf, id, job, ctx) {
  const workflow = file.name, title = typeof wf.name === 'string' && wf.name.trim() ? wf.name.trim() : workflow, dispatch = Boolean(workflowTriggers(file.text)?.has('workflow_dispatch'));
  const entryOf = fields => ({ workflow, title, job: id, check: null, checks: [], kind: 'ci-only', why: '', need: null, suite: false, commands: [], steps: [], matrix: null, dispatch, ...fields });
  const matrix = object(job) ? (job.strategy === undefined || job.strategy === null ? expandMatrix(undefined) : object(job.strategy) ? expandMatrix(job.strategy.matrix) : { error: 'builds its strategy from an expression' }) : { error: 'unreadable' };
  // A CI-only reason of the whole job: one entry for all its matrix entries.
  const whole = (need, why) => {
    const checks = matrix.entries ? matrix.entries.map(entry => checkName(job, id, entry)) : [jobName(job, id)];
    return [entryOf({ check: checks.length === 1 ? checks[0] : jobName(job, id), checks, need, why, matrix: matrix.entries?.length === 1 ? matrix.entries[0] : null })];
  };
  if (!object(job)) return whole('unreadable', 'Autopilot could not read the job');
  if (typeof job.uses === 'string') return whole('reusable workflow', `calls the reusable workflow ${oneLine(job.uses, 120)}`);
  if (!Array.isArray(job.steps) || !job.steps.length || !job.steps.every(object)) return whole('unreadable', 'Autopilot could not read the job');
  if (SECRET.test(JSON.stringify(job)) || SECRET.test(JSON.stringify(wf.env ?? null))) return whole('secrets', 'uses a secret');
  if (job.environment !== undefined) return whole('environment', `deploys to the environment ${oneLine(object(job.environment) ? job.environment.name : job.environment, 80)}`);
  if (job.services !== undefined) return whole('services', 'needs service containers');
  if (job.container !== undefined) return whole('container', 'runs in a container');
  const runs = condition(job.if);
  if (runs === false) return [];
  if (runs === null) return whole('condition', `has a condition that Autopilot cannot check: ${oneLine(job.if, 120)}`);
  if (matrix.error) return whole('matrix', matrix.error);
  const out = [], ciOnly = [];
  for (const entry of matrix.entries) {
    const r = sortEntry(job, wf, entry, ctx), check = checkName(job, id, entry);
    if (r.reason) ciOnly.push({ check, entry, ...r.reason });
    else out.push(entryOf({ check, checks: [check], kind: r.kind, why: r.why, suite: r.suite, commands: r.commands, steps: r.steps, matrix: entry }));
  }
  if (ciOnly.length) {
    const needs = [...new Set(ciOnly.map(c => c.need))];
    out.push(entryOf({ check: ciOnly.length === 1 ? ciOnly[0].check : jobName(job, id), checks: ciOnly.map(c => c.check), need: needs.slice(0, 3).join(', '),
      why: `${ciOnly[0].why}${ciOnly.length > 1 ? `, and ${ciOnly.length - 1} more` : ''}`, matrix: ciOnly.length === 1 ? ciOnly[0].entry : null }));
  }
  return out;
}
const fileEntry = (workflow, why, need) => ({ workflow, title: workflow, job: null, check: null, checks: [], kind: 'ci-only', why, need, suite: false, commands: [], steps: [], matrix: null, dispatch: false });
function sortFile(file, base, branch, changed, ctx) {
  const name = text(file?.name) || 'unknown', source = typeof file?.text === 'string' ? file.text : null;
  if (source !== null && !workflowRunsOnPr(source, branch, base, changed)) return [];
  const bad = why => [fileEntry(name, `Autopilot could not read the workflow file: ${why}`, 'unreadable')];
  if (source === null) return bad(oneLine(file?.error, 200) || 'it could not be read');
  let wf;
  try { wf = parseWorkflowYaml(source); } catch (error) { return bad(error.code === 'yaml' ? error.message : 'it could not be read'); }
  if (!object(wf)) return bad('its top is not a mapping');
  if (!object(wf.jobs) || !Object.keys(wf.jobs).length) return bad('it has no jobs');
  return Object.entries(wf.jobs).flatMap(([id, job]) => sortJob({ name, text: source }, wf, id, job, ctx));
}
export function sortCiJobs({ files = [], base = 'main', branch = DEFAULT_BRANCH, changed = null, testCommand = null, scripts = null, machine = {} } = {}) {
  const platform = machine?.platform ?? process.platform, node = text(machine?.node ?? process.versions.node).replace(/^v/, '');
  const ctx = { machine: { platform, node }, family: familyOf(platform), suite: suiteSpellings(testCommand, scripts), testCommand: normal(testCommand) };
  const list = Array.isArray(files) ? files : [];
  const jobs = list.length > MAX_FILES ? [fileEntry(null, `the base has ${list.length} workflow files (more than ${MAX_FILES})`, 'too many workflows')]
    : list.flatMap(file => sortFile(file, base, branch, changed, ctx));
  return { jobs, summary: ciJobsSummary(jobs) };
}
export function ciJobsSummary(jobs = []) {
  if (!jobs.length) return 'CI: none';
  const count = kind => jobs.filter(job => job.kind === kind).length, ciOnly = jobs.filter(job => job.kind === 'ci-only');
  const needs = [...new Set(ciOnly.map(job => text(job.need) || 'unknown'))];
  const shown = `${needs.slice(0, 4).join(', ')}${needs.length > 4 ? `, and ${needs.length - 4} more` : ''}`;
  return `CI: ${count('covered')} covered, ${count('local')} local, ${ciOnly.length} CI-only${ciOnly.length ? ` (${shown})` : ''}`;
}

// ---- Read the base tip ----------------------------------------------------------------------------------
export async function readCiJobs(input = {}, ports = {}) {
  const { base, root = null } = input;
  if (typeof base !== 'string' || !/^[\w./-]+$/.test(base) || base.startsWith('-') || base.includes('..')) throw new TypeError('base must be a branch name');
  const fs = ports.fs ?? nativeFs, git = ports.git;
  const failSafe = error => { const jobs = [fileEntry(null, `Autopilot could not read the workflow files of the base: ${oneLine(error?.message, 200)}`, 'unreadable')]; return { tree: null, jobs, summary: ciJobsSummary(jobs) }; };
  let tree;
  try {
    // Only the base tip: never HEAD, never the PR head (a PR can change a workflow).
    const tip = await git(['rev-parse', '--verify', '-q', `origin/${base}^{commit}`]);
    if (!SHA.test(tip)) throw new Error(`no commit for origin/${base}`);
    const row = String(await git(['ls-tree', '-z', tip, '--', '.github/workflows'])).split('\0').filter(Boolean)[0];
    const m = row ? /^\d+ (\w+) ([0-9a-f]+)\t/.exec(row) : null;
    if (!m || m[1] !== 'tree') return { tree: null, jobs: [], summary: 'CI: none' };
    tree = m[2];
  } catch (error) { return failSafe(error); }
  const file = root ? join(root, CACHE) : null, cached = file ? readJson(fs, file) : null;
  let files;
  if (cached?.schema === SCHEMA && cached.tree === tree && Array.isArray(cached.files)) files = cached.files;
  else {
    try {
      const rows = String(await git(['ls-tree', '-z', '-l', tree])).split('\0').filter(Boolean).map(row => /^(\d+) (\w+) ([0-9a-f]+) +(-|\d+)\t([\s\S]*)$/.exec(row))
        .filter(m => m && m[2] === 'blob' && /\.ya?ml$/.test(m[5]));
      files = [];
      if (rows.length > MAX_FILES) files = rows.map(m => ({ name: m[5], text: null, error: 'not read' }));
      else for (const m of rows) {
        if (Number(m[4]) > MAX_FILE) { files.push({ name: m[5], text: null, error: 'the file is larger than 256 KiB' }); continue; }
        try { files.push({ name: m[5], text: String(await git(['cat-file', 'blob', m[3]])) }); }
        catch (error) { files.push({ name: m[5], text: null, error: oneLine(error?.message, 200) || 'it could not be read' }); }
      }
    } catch (error) { return failSafe(error); }
  }
  const result = sortCiJobs({ ...input, files });
  if (file && (cached?.tree !== tree || cached?.summary !== result.summary)) {
    try { save(fs, file, `${JSON.stringify({ schema: SCHEMA, tree, files, summary: result.summary }, null, 2)}\n`); } catch { /* The next read tries again. */ }
  }
  return { tree, ...result };
}
export function cachedCiSummary({ root } = {}, ports = {}) {
  const cached = root ? readJson(ports.fs ?? nativeFs, join(root, CACHE)) : null;
  return typeof cached?.summary === 'string' ? cached.summary : null;
}

// ---- Local jobs at the final head -----------------------------------------------------------------------
const quote = value => `'${String(value).replaceAll("'", "'\\''")}'`;
const SHELL_ARGS = { bash: ['--noprofile', '--norc', '-eo', 'pipefail'], sh: ['-e'], default: ['-e'] };
export function localJobPlan({ jobs = [], head, checkout, temp, machine = {} } = {}) {
  if (!SHA.test(String(head ?? ''))) throw new TypeError('head must be 40 hex digits');
  if (!isAbsolute(String(checkout ?? '')) || !isAbsolute(String(temp ?? ''))) throw new TypeError('checkout and temp must be absolute paths');
  const os = familyOf(machine?.platform ?? process.platform);
  return jobs.filter(job => job.kind === 'local').map((entry, index) => {
    const folder = join(temp, `job-${index + 1}`), values = object(entry.matrix) ? entry.matrix : {};
    const env = { CI: 'true', GITHUB_WORKSPACE: checkout, RUNNER_TEMP: join(folder, 'runner-temp'), GITHUB_STEP_SUMMARY: join(folder, 'step-summary.md'), GITHUB_OUTPUT: join(folder, 'output') };
    const fill = (value, names) => String(value).replace(EXPR, (all, inner) => {
      const t = inner.trim();
      let m;
      if ((m = /^matrix\.([A-Za-z_][\w-]*)$/.exec(t)) && Object.hasOwn(values, m[1])) return text(values[m[1]]);
      if (t === 'runner.os') return os;
      if (t === 'runner.temp') return env.RUNNER_TEMP;
      if (t === 'github.workspace') return checkout;
      if ((m = /^env\.([A-Za-z_]\w*)$/.exec(t)) && Object.hasOwn(names, m[1])) return names[m[1]];
      return all;
    });
    const steps = (entry.steps ?? []).map(step => {
      const raw = object(step.env) ? step.env : {}, own = Object.fromEntries(Object.entries(raw).map(([name, value]) => [name, fill(value, raw)]));
      const command = step.shell === 'sh' ? 'sh' : 'bash';
      return { name: step.name, command, args: [...SHELL_ARGS[step.shell ?? 'default'], '-c', fill(step.script, own)], cwd: step.workingDirectory && step.workingDirectory !== '.' ? join(checkout, step.workingDirectory) : checkout, env: { ...env, ...own }, own };
    });
    const lines = [`mkdir -p ${quote(env.RUNNER_TEMP)} || exit 1`, `: > ${quote(env.GITHUB_STEP_SUMMARY)}; : > ${quote(env.GITHUB_OUTPUT)}`];
    steps.forEach((step, i) => {
      const assignments = Object.entries(step.own).map(([name, value]) => quote(`${name}=${value}`));
      lines.push(`echo ${quote(`pdd-ci-local: step ${i + 1} of ${steps.length}: ${step.name}`)}`,
        `(cd -- ${quote(step.cwd)} && exec env ${[...assignments, quote(step.command), ...step.args.map(quote)].join(' ')}); code=$?`,
        `if [ "$code" -ne 0 ]; then echo "pdd-ci-local: step ${i + 1} failed with exit $code"; exit "$code"; fi`);
    });
    lines.push(`echo ${quote(`pdd-ci-local: all ${steps.length} steps passed`)}`);
    return { key: `${entry.workflow}#${entry.check}`, workflow: entry.workflow, job: entry.job, check: entry.check, head, cwd: checkout, env, command: lines.join('\n'),
      steps: steps.map(({ own, ...step }) => step) };
  });
}
export function localJobResult(entry, run) {
  const row = { key: entry?.key ?? null, workflow: entry?.workflow ?? null, job: entry?.job ?? null, check: entry?.check ?? null, head: entry?.head ?? null, state: 'pass', step: null, exit: null, tool: null, why: null, tail: null };
  const code = run?.exit?.code;
  if (code === 0) return row;
  const log = String(run?.log ?? ''), failed = [...log.matchAll(/^pdd-ci-local: step (\d+) failed with exit (\d+)\s*$/gm)].at(-1);
  const step = failed ? entry?.steps?.[Number(failed[1]) - 1]?.name ?? null : null;
  if (!Number.isSafeInteger(code)) return { ...row, state: 'could-not-run', step, why: `the local run did not finish${run?.exit?.signal ? ` (${run.exit.signal})` : ''}` };
  if (code === 127) {
    const tool = [...log.matchAll(/(?:^|:\s)([^\s:]+): (?:command )?not found\s*$/gm)].at(-1)?.[1] ?? null;
    return { ...row, state: 'could-not-run', step, exit: 127, tool, why: `${tool ?? 'a tool'} is missing on this machine` };
  }
  const tail = redactSecrets(log.split(/\r?\n/).filter(line => line.trim()).slice(-15).map(line => line.slice(0, 300)).join('\n'));
  return { ...row, state: 'fail', step, exit: code, tail: tail || null };
}
export function localJobsRecord({ head, plan = [], runs = {}, at = null } = {}) {
  return { head, at, jobs: plan.map(entry => localJobResult(entry, object(runs) && Object.hasOwn(runs, entry.key) ? runs[entry.key] : null)) };
}
export function localJobReds(record) {
  return (record?.jobs ?? []).filter(job => job.state === 'fail').map(job => `CI job ${job.check} failed when Autopilot ran it on this machine for head ${short(record.head)} (CI did not start): step "${job.step ?? 'unknown'}" exited with ${job.exit}.${job.tail ? `\nLast lines:\n${job.tail}` : ''}`);
}

// ---- The CI lines of the merge note ---------------------------------------------------------------------
const resultOf = record => { const rows = new Map(); for (const row of record?.jobs ?? []) rows.set(row.key, row); return entry => rows.get(`${entry.workflow}#${entry.check}`) ?? null; };
export function ciMergeNote({ jobs = [], record = null, notStarted = null } = {}) {
  const reason = notStarted?.reason === 'billing' ? `GitHub said "${oneLine(notStarted.message, 200)}"`
    : notStarted?.reason === 'queued' && Number.isFinite(notStarted.since) ? `queued since ${new Date(notStarted.since).toISOString().slice(11, 16)} UTC` : 'reason unknown';
  const covered = jobs.filter(job => job.kind === 'covered' || (job.kind === 'local' && job.suite)).map(job => job.check);
  const lines = [`- CI: did not start (${reason})${covered.length ? `; covered by the local full suite: ${covered.join(', ')}` : ''}`], result = resultOf(record);
  for (const job of jobs) {
    if (job.kind === 'local') {
      const r = result(job);
      lines.push(r?.state === 'pass' ? `- CI job ${job.check}: local pass` : r?.state === 'fail' ? `- CI job ${job.check}: local fail (step "${r.step ?? 'unknown'}", exit ${r.exit})`
        : `- CI job ${job.check}: not run yet (CI did not start; ${r?.why ?? 'no local result'})`);
    } else if (job.kind === 'ci-only') {
      lines.push(job.job === null ? `- CI workflow ${job.workflow ?? 'files'}: not run yet (CI did not start)` : `- CI job ${job.checks?.length ? job.checks.join(', ') : job.check}: not run yet (CI did not start)`);
    }
  }
  return lines;
}

// ---- Missed CI on the base ------------------------------------------------------------------------------
export function missedCiJobs({ jobs = [], record = null } = {}) {
  const result = resultOf(record);
  return jobs.filter(job => job.workflow && (job.kind === 'ci-only' || (job.kind === 'local' && !['pass', 'fail'].includes(result(job)?.state))))
    .map(job => ({ workflow: job.workflow, job: job.job, checks: job.checks?.length ? [...job.checks] : [job.check].filter(Boolean), dispatch: Boolean(job.dispatch) }))
    .filter(job => job.checks.length);
}
const validRecord = record => object(record) && SHA.test(String(record.merge ?? '')) && Array.isArray(record.jobs) && record.jobs.length > 0
  && record.jobs.every(job => object(job) && typeof job.workflow === 'string' && Array.isArray(job.checks));
export function readMissedCi({ root } = {}, ports = {}) {
  let content = '';
  try { content = (ports.fs ?? nativeFs).readFileSync(join(root, MISSED), 'utf8'); } catch { return []; }
  return content.split('\n').map(line => { try { return JSON.parse(line); } catch { return null; } }).filter(validRecord);
}
export function recordMissedCi({ root, merge, pr = null, issue = null, missed = [] } = {}, ports = {}) {
  if (!Array.isArray(missed) || !missed.length) return null;
  if (!SHA.test(String(merge ?? ''))) throw new TypeError('merge must be 40 hex digits');
  const fs = ports.fs ?? nativeFs, now = ports.now ?? Date.now, file = join(root, MISSED);
  const record = { merge, pr, issue, at: now(), jobs: missed.map(job => ({ workflow: job.workflow, job: job.job ?? null, checks: [...job.checks], dispatch: Boolean(job.dispatch), state: 'missed' })) };
  fs.mkdirSync(root, { recursive: true, mode: 0o700 });
  // A cut last line (no newline) must not swallow this record.
  let cut = false;
  try { const old = fs.readFileSync(file, 'utf8'); cut = old.length > 0 && !old.endsWith('\n'); } catch { /* A new file. */ }
  fs.appendFileSync(file, `${cut ? '\n' : ''}${JSON.stringify(record)}\n`, { mode: 0o600 });
  return record;
}
function writeMissed(fs, root, records) {
  const file = join(root, MISSED);
  if (!records.length) { fs.rmSync(file, { force: true }); return; }
  save(fs, file, `${records.map(record => JSON.stringify(record)).join('\n')}\n`);
}
async function nameState(runs, name, billing) {
  const run = runs.filter(r => r?.name === name).sort((a, b) => (b.id ?? 0) - (a.id ?? 0))[0];
  if (!run) return 'missing';
  if (run.status !== 'completed') return 'running';
  if (GOOD.includes(run.conclusion)) return 'pass';
  return await billing(run) ? 'blocked' : 'red';
}
export async function checkMissedCi({ root, repo, base, tip = null, ciDown = null } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs, now = ports.now ?? Date.now, billing = ports.billing ?? (async () => null), gh = ports.gh;
  const records = readMissedCi({ root }, { fs });
  const result = { state: 'clear', red: [], waiting: [], stuck: [], lines: [] };
  if (records.length && !ciDown) {
    const reads = new Map();
    const checkRuns = async sha => {
      if (!reads.has(sha)) {
        const endpoint = `repos/${repo}/commits/${sha}/check-runs?per_page=100`, r = await gh.call('GET', endpoint);
        if (r?.status !== 200) throw githubError('GET', endpoint, r?.status);
        reads.set(sha, Array.isArray(r.value?.check_runs) ? r.value.check_runs : []);
      }
      return reads.get(sha);
    };
    const post = (endpoint, body) => Promise.resolve().then(() => gh.call('POST', endpoint, body)).then(r => r?.status ?? 0, () => 0);
    const tipOk = SHA.test(String(tip ?? ''));
    for (const record of records) for (const job of record.jobs) {
      if (job.state === 'pass') continue;
      if (job.state === 'red') {
        // A red job holds merges until its names pass at the current base tip.
        if (!tipOk) continue;
        const runs = await checkRuns(tip), states = [];
        for (const name of job.red?.names ?? []) states.push(await nameState(runs, name, billing));
        if (states.length && states.every(state => state === 'pass')) job.state = 'pass';
        continue;
      }
      // Each name: the merge commit decides when it has a result; else the current base tip (a later commit holds the
      // merged change; a rerun, a dispatch, a person's run or a later push shows there).
      const states = [];
      for (const name of job.checks) {
        let state = await nameState(await checkRuns(record.merge), name, billing), sha = record.merge;
        if (!['pass', 'red'].includes(state) && tipOk && tip !== record.merge) {
          const later = await nameState(await checkRuns(tip), name, billing);
          if (['pass', 'red', 'running'].includes(later)) { state = later; sha = tip; }
        }
        states.push({ name, state, sha });
      }
      const red = states.filter(s => s.state === 'red');
      if (red.length) { job.state = 'red'; job.red = { names: red.map(s => s.name), sha: red[0].sha, at: now() }; continue; }
      if (states.every(s => s.state === 'pass')) { job.state = 'pass'; continue; }
      if (states.some(s => s.state === 'running') || job.state === 'stuck') continue;
      if (job.asked) { if (!(job.asked.status >= 200 && job.asked.status < 300) || now() - job.asked.at >= ASK_WAIT) job.state = 'stuck'; continue; }
      // Ask once: rerun the workflow run of the merge commit, or start the workflow on the base.
      const endpoint = `repos/${repo}/actions/runs?head_sha=${record.merge}&per_page=50`, r = await gh.call('GET', endpoint);
      if (r?.status !== 200) throw githubError('GET', endpoint, r?.status);
      const path = `.github/workflows/${job.workflow}`;
      const run = (Array.isArray(r.value?.workflow_runs) ? r.value.workflow_runs : []).filter(w => String(w?.path ?? '').split('@')[0] === path).sort((a, b) => (b.id ?? 0) - (a.id ?? 0))[0];
      if (run && run.status !== 'completed') continue;
      if (run && Number.isSafeInteger(run.id)) job.asked = { how: 'rerun', sha: record.merge, at: now(), status: await post(`repos/${repo}/actions/runs/${run.id}/rerun`) };
      else if (job.dispatch && tipOk) job.asked = { how: 'dispatch', sha: tip, at: now(), status: await post(`repos/${repo}/actions/workflows/${encodeURIComponent(job.workflow)}/dispatches`, { ref: base }) };
      else { job.state = 'stuck'; continue; }
      if (!(job.asked.status >= 200 && job.asked.status < 300)) job.state = 'stuck';
      writeMissed(fs, root, records);
    }
  }
  const cutoff = now() - KEEP;
  const kept = records.map(record => ({ ...record, jobs: record.jobs.filter(job => job.state !== 'pass') }))
    .filter(record => record.jobs.length && (record.at >= cutoff || record.jobs.some(job => job.state === 'red'))).slice(-KEEP_RECORDS);
  if (records.length && !ciDown) writeMissed(fs, root, kept);
  for (const record of kept) for (const job of record.jobs) {
    const row = { merge: record.merge, pr: record.pr, issue: record.issue, workflow: job.workflow, checks: job.checks }, names = job.checks.join(', ');
    if (job.state === 'red') result.red.push({ merge: record.merge, pr: record.pr, issue: record.issue, workflow: job.workflow, names: job.red?.names ?? job.checks, sha: job.red?.sha ?? record.merge });
    else if (job.state === 'stuck') { result.stuck.push(row); result.lines.push(`missed CI: CI job ${names} for PR #${record.pr} (${short(record.merge)}) did not run on ${base}, and Autopilot cannot start it: run the workflow ${job.workflow} by hand`); }
    else { result.waiting.push(row); result.lines.push(`missed CI: CI job ${names} for PR #${record.pr} (${short(record.merge)}) waits to run on ${base}`); }
  }
  result.state = result.red.length ? 'red' : kept.length ? 'waiting' : 'clear';
  return result;
}
export function missedCiHeldLine(red, base, issue = null) {
  return `merges held: CI job ${(red?.names ?? []).join(', ')} failed on ${base} after a merge without CI (${Number.isSafeInteger(issue) ? `issue #${issue}` : short(red?.merge)})`;
}
