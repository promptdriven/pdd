// Prompt: prompts/cli/autopilot-validator.prompt.md

import { execFileSync } from 'node:child_process';
import { readSafeUtf8 } from '../../core/lint/diagnostics.mjs';
import { loadProjectLintConfig } from '../../core/lint/project-config.mjs';
import { TEST_FILE_PATH_RE, isTestHelperSpecifier, readPytestTestpaths } from '../../shared/test-paths.mjs';
import { collectTestFixedSleepFindings, collectTestUnexcusedSkipFindings, lintAutopilotTestHygiene, lintTestFixedSleeps, lintTestUnexcusedSkips } from '../lint-sleep-skip.mjs';
import { normalizePath } from './surfaces.mjs';

export { collectTestFixedSleepFindings, collectTestUnexcusedSkipFindings, lintAutopilotTestHygiene, lintTestFixedSleeps, lintTestUnexcusedSkips };

const SKIP_KEYWORD_RE = /(?:e2e|validation|validator|real-binding)/i;
const PRIVATE_IMPORT_SYM_RE = /^_(?!_)[A-Za-z0-9_$]*$/;
const BACKSIDE_CODE_EXT_RE = /\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|cs|swift)$/i;
const BACKSIDE_SKIP_SUBDIR_RE = /(?:^|\/)(?:fixtures|helpers)\//i;
const BACKSIDE_TEST_FILE_RE = /(?:(?:^|\/)(?:test|tests|__tests__|spec)\/|\.(?:test|spec)\.[a-z0-9]+$|_test\.(?:go|rs|py)$|(?:^|\/)test_[^/]+\.py$)/i;

const detectLang = (p) => (/\.py$/i.test(p) ? 'py' : /\.go$/i.test(p) ? 'go' : /\.rs$/i.test(p) ? 'rs' : 'js');
const isRegexStart = (p) => !p || '([{:;,=!?&|+-*%^~<>}'.includes(p) || /^(?:return|case|throw|in|of|typeof|void|delete|new|else|do|yield|await)$/.test(p);

function scanCodePreserveLines(source, lang = 'js') {
  const text = String(source ?? ''), nc = [], ns = [], tpl = [];
  let i = 0, lastTok = '';
  const pushRaw = (open, close) => {
    nc.push(open); ns.push('"'); i += open.length;
    const end = text.indexOf(close, i), body = end < 0 ? text.slice(i) : text.slice(i, end);
    nc.push(body); for (const c of body) if (c === '\n') ns.push('\n');
    ns.push('"'); i = end >= 0 ? (nc.push(close), end + close.length) : text.length; lastTok = '""';
  };
  const prevWord = () => { let j = nc.length - 1; while (j >= 0 && /\s/.test(nc[j])) j -= 1; if (j < 0 || !/[\w$]/.test(nc[j])) return j >= 0 ? nc[j] : ''; const e = j; while (j >= 0 && /[\w$]/.test(nc[j])) j -= 1; return nc.slice(j + 1, e + 1).join(''); };
  const scanTpl = () => {
    while (i < text.length) {
      const c = text[i];
      if (c === '\\' && i + 1 < text.length) { nc.push(c, text[i + 1]); if (text[i + 1] === '\n') ns.push('\n'); i += 2; continue; }
      if (c === '$' && text[i + 1] === '{') { nc.push('$', '{'); ns.push('"+('); i += 2; tpl.push(1); lastTok = '('; return; }
      if (c === '`') { nc.push(c); ns.push('"'); i += 1; lastTok = '""'; return; }
      nc.push(c); if (c === '\n') ns.push('\n'); i += 1;
    }
    lastTok = '""';
  };
  while (i < text.length) {
    const ch = text[i], nx = text[i + 1];
    if ((lang === 'py' && ch === '#') || (lang !== 'py' && ch === '/' && nx === '/')) { while (i < text.length && text[i] !== '\n') { nc.push(' '); ns.push(' '); i += 1; } continue; }
    if (lang !== 'py' && ch === '/' && nx === '*') { nc.push(' ', ' '); ns.push(' ', ' '); i += 2; while (i < text.length) { if (text[i] === '*' && text[i + 1] === '/') { nc.push(' ', ' '); ns.push(' ', ' '); i += 2; break; } const k = text[i] === '\n' ? '\n' : ' '; nc.push(k); ns.push(k); i += 1; } continue; }
    if (lang === 'py' && (ch === '\'' || ch === '"') && text[i + 1] === ch && text[i + 2] === ch) { pushRaw(ch.repeat(3), ch.repeat(3)); continue; }
    if (lang === 'rs' && ch === 'r' && (nx === '"' || nx === '#')) { let h = 0; while (text[i + 1 + h] === '#') h += 1; if (text[i + 1 + h] === '"') { pushRaw(`r${'#'.repeat(h)}"`, `"${'#'.repeat(h)}`); continue; } }
    if (lang === 'go' && ch === '`') { pushRaw('`', '`'); continue; }
    if (lang === 'js' && ch === '`') { nc.push(ch); ns.push('"'); i += 1; scanTpl(); continue; }
    if (lang === 'js' && tpl.length > 0) { if (ch === '{') tpl[tpl.length - 1] += 1; else if (ch === '}' && --tpl[tpl.length - 1] === 0) { tpl.pop(); nc.push('}'); ns.push(')+"'); i += 1; scanTpl(); continue; } }
    if (ch === '\'' || ch === '"') {
      const q = ch; nc.push(ch); ns.push('"'); i += 1;
      while (i < text.length) {
        const c = text[i];
        if (c === '\\' && i + 1 < text.length) { nc.push(c, text[i + 1]); if (text[i + 1] === '\n') ns.push('\n'); i += 2; continue; }
        if (c === q || c === '\n') { nc.push(c); ns.push('"', ...(c === '\n' ? ['\n'] : [])); i += 1; break; }
        nc.push(c); i += 1;
      }
      lastTok = '""'; continue;
    }
    if (lang === 'js' && ch === '/' && nx !== '/' && nx !== '*' && isRegexStart(lastTok || prevWord())) {
      nc.push(ch); ns.push('/'); i += 1; let cls = false;
      while (i < text.length) { const c = text[i]; if (c === '\\' && i + 1 < text.length) { nc.push(c, text[i + 1]); i += 2; continue; } if (c === '\n') { nc.push('\n'); ns.push('\n'); i += 1; break; } if (c === '[') cls = true; else if (c === ']') cls = false; nc.push(c); i += 1; if (c === '/' && !cls) { ns.push(' /'); break; } }
      lastTok = '/re/'; continue;
    }
    nc.push(ch); ns.push(ch); if (!/\s/.test(ch)) lastTok = /[\w$]/.test(ch) ? '' : ch; i += 1;
  }
  return { codeNoComments: nc.join(''), codeNoStrings: ns.join('') };
}

export const scanJsPreserveLines = (source) => scanCodePreserveLines(source, 'js');
export const stripCommentsPreserveLines = (source) => scanJsPreserveLines(source).codeNoComments;
export const maskStringsPreserveLines = (source) => scanJsPreserveLines(source).codeNoStrings;

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

export function lintValidationCode({ path = '', kind = 'test', text = '' } = {}) {
  const filePath = normalizePath(path) || 'unknown', source = String(text ?? ''), lang = detectLang(filePath);
  const { codeNoComments, codeNoStrings } = scanCodePreserveLines(source, lang);
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
  return { ok: codeSet.size === 0, codes: [...codeSet].sort(), warnings };
}

export const lintValidationSkips = (text, { path = 'src/module.mjs', kind = 'code' } = {}) => lintValidationCode({ path, kind, text }).warnings.filter((w) => w.includes('[silent-validation-skip]'));

export function lintRepoValidationBackside({ root, files, config, workspaceRoot } = {}) {
  const relFiles = Array.isArray(files) ? files : (() => { try { return execFileSync('git', ['ls-files', '-z'], { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }).split('\0').filter(Boolean); } catch { return []; } })();
  const cfg = config?.ruleSeverities instanceof Map ? config : (typeof config === 'string' || root ? loadProjectLintConfig(typeof config === 'string' ? config : root, { workspaceRoot: workspaceRoot ?? root }) : null);
  const sevOf = (code) => (cfg?.disabledRules?.has(code) || cfg?.ruleSeverities?.get(code) === 'off' ? 'off' : (cfg?.ruleSeverities?.get(code) === 'error' ? 'error' : 'warn'));
  const findings = [], warnings = [], errors = [];
  for (const rel of relFiles) {
    if (typeof rel !== 'string' || !BACKSIDE_CODE_EXT_RE.test(rel) || BACKSIDE_SKIP_SUBDIR_RE.test(rel)) continue;
    const text = readSafeUtf8(root, rel);
    if (text === null) continue;
    const kind = BACKSIDE_TEST_FILE_RE.test(rel) ? 'test' : 'code';
    const val = lintValidationCode({ path: rel, kind, text });
    for (const w of val.warnings ?? []) {
      const m = /:(\d+)\s+\[([a-z0-9-]+)\]\s*(.*)$/.exec(w), sev = sevOf(m ? m[2] : 'validation-lint');
      if (sev === 'off') continue;
      const msg = sev === 'error' ? w.replace(/^Warning:/, 'Error:') : w;
      findings.push({ path: rel, line: m ? Number(m[1]) : 1, code: m ? m[2] : 'validation-lint', severity: sev, detail: m ? m[3] : w, warning: msg });
      if (sev === 'error') errors.push(msg); else warnings.push(msg);
    }
  }
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
  const testpaths = typeof config === 'string' && config
    ? readPytestTestpaths(config)
    : (config === undefined ? readPytestTestpaths(root) : []);
  for (const rel of changedFiles) {
    if (typeof rel !== 'string' || !allowed.has(rel) || !BACKSIDE_TEST_FILE_RE.test(rel) || BACKSIDE_SKIP_SUBDIR_RE.test(rel)) continue;
    const text = readSafeUtf8(root, rel); if (text === null) continue;
    const lang = detectLang(rel);
    if (lang === 'js') for (const m of text.matchAll(/\bimport\s+\{([^}]+)\}\s+from\s+['"](\.\.?\/[^'"]+)['"]/g)) { if (isTestHelperSpecifier(m[2], rel, testpaths, allowed)) continue; const line = text.slice(0, m.index).split('\n').length; for (const p of m[1].split(',')) { const sym = p.trim().split(/\s+as\s+/i)[0]?.trim(); if (sym && PRIVATE_IMPORT_SYM_RE.test(sym)) push(rel, line, sym, m[2]); } }
    else if (lang === 'py') for (const m of text.matchAll(/^[ \t]*from\s+(\.+[A-Za-z0-9_.]*|[A-Za-z0-9_.]+)\s+import\s+([^\n#]+)/gm)) { if (isTestHelperSpecifier(m[1], rel, testpaths, allowed)) continue; const line = text.slice(0, m.index).split('\n').length; for (const p of m[2].replace(/[()]/g, '').split(',')) { const sym = p.trim().split(/\s+as\s+/i)[0]?.trim(); if (sym && PRIVATE_IMPORT_SYM_RE.test(sym)) push(rel, line, sym, m[1]); } }
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
