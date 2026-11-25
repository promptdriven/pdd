// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// Shared Layer-1 adversarial real-host boundary verification gate for `kind: native-only` modules (#3633).
import { readdirSync, realpathSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { headerPrompts, isTestOwnedPath, promptClaims } from '../../file-owner.mjs';
import { gitFiles } from '../../shared/git-context.mjs';
import { canonicalRepoPath, formatTeachingDetail, readSafeHeadUtf8, readSafeUtf8 } from './diagnostics.mjs';
import { isNativeOnlyPrompt } from './prompt-metadata.mjs';
import { compileGlobMatcher } from './regex-safety.mjs';

export const ADVERSARIAL_BOUNDARY_SURFACES = Object.freeze(['http-auth-browser-mcp', 'binary-parser', 'storage-dr', 'cli-day0']);
export const ADVERSARIAL_SURFACE_CHECKLISTS = Object.freeze({
  'http-auth-browser-mcp': 'unauthenticated/forged-body/header access, revocation, server-clock expiry (rejecting caller now), CSRF/Origin, strict boolean/type coercion ("false"/null/missing keys), path traversal, SSRF/redirect downgrade, interactive <form> under CSP script-src \'none\', and real MCP/OAuth wire handshakes',
  'binary-parser': 'malformed/adversarial PDF (encoding/filter tricks, XMP/ObjStm, /JavaScript), XLSX/XML/archive (XXE, formulas, macros, zip-bombs), and ReDoS/timeout fuzzing',
  'storage-dr': 'concurrent DB transactions, audit-failure rollback atomicity, and corrupt-DB startup/recovery resilience',
  'cli-day0': 'clean-HOME end-to-end walkthrough (real binary, --help, auth/bootstrap, real persistence, and non-zero error exit)',
  'general-native-boundary': 'non-mocked real-host negative/rejection/failure probes (never happy-path smoke alone)',
});

const SIMULATED_VECTOR_RE = /^(?:tests?|__tests__)\/(?:runtime\/)?[^/]+\.json$|^(?:tests?|__tests__)\/.+\.vectors\.json$/i, NATIVE_TEST_RE = /(?:(?:^|\/)(?:test|tests|__tests__|spec)\/.*\.(?:[cm]?[jt]sx?|py|go|rs)$|\.(?:test|spec)\.[cm]?[jt]sx?$|_test\.(?:py|go|rs)$|(?:^|\/)test_[^/]+\.py$)/i;
const SKIP_TEST_SUBDIR_RE = /(?:^|\/)(?:helpers?|fixtures?|mocks?|__mocks__|__fixtures__|node_modules|\.venv|venv)\//i, NON_PROD_RE = /^(?:test|tests|__tests__|spec|fixtures|examples|prompts|user_stories|docs)\//i, CODE_EXT_RE = /\.(?:[cm]?[jt]sx?|py|go|rs|sh|sql)$/i;
const HTTP_PATH_RE = /(?:^|[^a-z0-9])(?:http|https|server|router|routes|api|web|browser|mcp|oauth|auth|csrf|handlers?|controllers?)(?:$|[^a-z0-9])/i;
const HTTP_CODE_RE = /\b(?:fastapi|starlette|flask|aiohttp|http\.server|express|fastify|hono|koa|APIRouter|create_app|createServer|net\/http|axum|actix_web|playwright|Content-Security-Policy|jsonrpc|oauth2?|pkce)\b|['"](?:node:)?https?['"]/i;
const HTTP_PROMPT_RE = /\b(?:fastapi|starlette|flask|express|fastify|hono|http\s+(?:server|routes?|endpoints?|api|transport|requests?|post|get)|https?\s+transport|browser|html\s+<form|<form|script-src|csp|csrf|origin\s+check|oauth|pkce|mcp\s+(?:server|endpoint|wire|initialize|tools)|cookie|session\s+revocation|ssrf)\b/i;
const PARSER_RE = /(?:^|[^a-z0-9])(?:pdf|xlsx|xls|docx|zip|tar|gzip|zlib|xml|archive|redact|upload|ingest|parser|spreadsheet|workbook|xmp|objstm)(?:$|[^a-z0-9])|\b(?:pypdf2?|fitz|pdfminer|openpyxl|xlrd|zipfile|tarfile|xml\.etree|lxml|defusedxml|pdf-lib|pdfjs|jszip|adm-zip|archive\/zip|encoding\/xml)\b/i;
const STORAGE_RE = /(?:^|[^a-z0-9])(?:sqlite|sqlite3|postgres|postgresql|mysql|database|db|storage|store|journal|continuity|wal|rollback|migration|recovery|backup|persist)(?:$|[^a-z0-9])|\b(?:sqlite3|node:sqlite|better-sqlite3|psycopg2?|sqlalchemy|DatabaseSync|database\/sql|rusqlite|sqlx|BEGIN\s+IMMEDIATE|PRAGMA\s+journal_mode|CREATE\s+TABLE)\b/i;
const CLI_PATH_RE = /^(?:bin|cli|cmd)\/|(?:\.sh$)|(?:^|[^a-z0-9])(?:cli|day-?0|terminal)(?:$|[^a-z0-9])/i, CLI_CODE_PROMPT_RE = /\b(?:argparse|click\.command|typer\.|console_scripts|commander|yargs|cobra\.Command|clap::|day-?0|clean[- ]home|subcommands?|--help)\b/i;
const GENERIC_DIRS = new Set(['src', 'lib', 'app', 'pkg', 'internal', 'packages', 'core', 'service', 'services', 'adapter', 'adapters', 'common', 'shared', 'utils']), GENERIC_BASES = new Set(['index', 'main', 'app', 'service', 'routes', 'router', 'handler', 'handlers', 'adapter', 'mod', 'init', '__init__', 'server', 'client']);
const VALUE_FLAGS = new Set(['-t', '--top-level-directory', '-k', '-c', '--config', '-o', '--rootdir', '--import', '-r', '--require', '--loader', '--test-name-pattern', '--test-reporter', '--reporter', '--outputFile']), HTTP_NEG_PROBES = new Set(['auth-forged-access', 'clock-expiry', 'csrf-origin', 'strict-coercion', 'path-traversal', 'ssrf-redirect']);
const CAP_RE = {
  http: { js: /\b(?:fetch|createServer|supertest)\s*\(|\.\s*listen\s*\(|\.(?:goto|launch)\s*\(/, py: /\b(?:TestClient|HTTPServer|httpx\.(?:Client|AsyncClient|get|post|put|delete|request)|requests\.(?:get|post|put|delete|request|Session)|urllib\.request\.urlopen)\s*\(/, go: /\b(?:httptest\.NewServer|net\.Listen|http\.(?:Get|Post|Do|NewRequest))\s*\(/, rs: /\b(?:TcpListener::bind|reqwest::|axum::)\b/ },
  db: { js: /\b(?:DatabaseSync)\s*\(|\bnew\s+(?:Pool|Client)\s*\(/, py: /\b(?:sqlite3\.connect|psycopg2?\.connect)\s*\(/, go: /\bsql\.Open\s*\(/, rs: /\b(?:Connection::open|sqlx::)\b/ },
  subproc: { js: /\b(?:spawnSync|execFileSync|execSync|spawn|execFile)\s*\(/, py: /\bsubprocess\.(?:run|Popen|check_output|check_call)\s*\(/, go: /\bexec\.Command(?:Context)?\s*\(/, rs: /\bCommand::new\b/ },
};
const TRIVIAL_BIN_RE = /^(?:spawnSync|execFileSync|execSync|spawn|execFile|subprocess\.(?:run|Popen|check_output|check_call)|Command::new|exec\.Command(?:Context)?)\s*\(\s*(?:\[\s*)?['"`](?:(?:\/(?:usr\/)?bin\/)?(?:true|false|echo|pwd|printf|exit|sleep|cat|ls|env|id|uname|whoami|test|:)(?:['"`]|\s)|(?:\/(?:usr\/)?bin\/)?(?:sh|bash|zsh)(?:\s+-c\s+['"]?|['"`]\s*,\s*(?:\[\s*)?['"`]-c['"`]\s*,\s*['"`]\s*)(?:true|false|echo\b|pwd\b|printf\b|exit(?:\s+\d+)?|:))/i;
const BINARY_CONSTRUCT_RE = /(?:b['"]%PDF|b['"]PK\\x03\\x04|\bzipfile\.ZipFile\s*\(|\bzlib\.compress\s*\(|\btarfile\.open\s*\(|\bBuffer\.from\s*\(|\bnew\s+Uint8Array\s*\(|(?:\.|(?<![A-Za-z0-9_$]))(?:write_bytes|writeFileSync)\s*\()/;
const PROD_IMPORT_RE = { js: /\b(?:from|require\s*\()\s*['"`](?:\.\.?\/|src\/)/, py: /\b(?:from\s+[A-Za-z_][\w.]*\s+import|import\s+(?:src|app|[a-z_]+\.[a-z_]+))/, go: /"[^"]+\/[^"]+"/, rs: /\buse\s+(?:crate|super)::/ };
const PRIMITIVE_SHADOW_RE = /\b(?:globalThis|global|window)\.fetch\s*=|(?<![.\w$])(?:(?:const|let|var)\s+(?:fetch|spawnSync|execFileSync|DatabaseSync|createServer)\s*=|(?:const|let|var)\s*\{[^}]{0,200}\b(?:fetch|spawnSync|execFileSync|DatabaseSync|createServer)\b[^}]{0,200}\}\s*=(?!\s*require\s*\()|function\s+(?:fetch|spawnSync|execFileSync|DatabaseSync|createServer)\s*\(|class\s+(?:TestClient|DatabaseSync|requests|httpx|sqlite3|subprocess)\b|def\s+(?:TestClient|requests|httpx)\s*\()|\b(?:TestClient|sqlite3\.connect|requests\.(?:get|post|put|delete|request|Session)|httpx\.(?:Client|get|post)|subprocess\.(?:run|Popen))\s*=(?!=)|\b(?:requests|httpx|sqlite3|subprocess)\s*=(?!\s*(?:=|\[|\d|\{|None\b))|\b(?:from\s+(?!fastapi\b|starlette\b|flask\b|httpx\b|requests\b|sqlite3\b|subprocess\b|urllib\b|http\b)[A-Za-z0-9_.]+\s+import\s+[^\n]*\b(?:TestClient|HTTPServer|sqlite3|subprocess|requests|httpx)\b|\bas\s+(?:TestClient|HTTPServer|sqlite3|subprocess|requests|httpx)\b)|\b(?:MockTransport|PortSimulator)\b/;
const NON_BUILTIN_SHADOW_RE = /\bimport\s+(?:(?:fetch|spawnSync|execFileSync|DatabaseSync|createServer)\b|\{[^}]{0,200}\b(?:fetch|spawnSync|execFileSync|DatabaseSync|createServer)\b[^}]{0,200}\})\s*from\s*['"](?!(?:node:)?(?:https?|http2|child_process|sqlite|undici)['"])|\b(?:const|let|var)\s+(?:(?:fetch|spawnSync|execFileSync|DatabaseSync|createServer)\b|\{[^}]{0,200}\b(?:fetch|spawnSync|execFileSync|DatabaseSync|createServer)\b[^}]{0,200}\})\s*=\s*require\s*\(\s*['"](?!(?:node:)?(?:https?|http2|child_process|sqlite|undici)['"])/;
const MOCK_CALL_RE = /\b(?:MagicMock|unittest\.mock|mocker\.patch|monkeypatch\.setattr|vi\.(?:mock|doMock|fn|stubGlobal)|jest\.(?:mock|doMock|fn)|mock\.(?:module|fn|method|getter|patch)|sinon\.stub|fakeClient|mockClient|fakeServer|mockServer|fakeDb|mockDb|PortSimulator|MockTransport)\b|@patch\b|\bwith\s+patch\s*\(/i;
const ATOM = '(?:True|False|None|true|false|null|not\\s+(?:True|False|None|0|1)|!\\s*(?:true|false|0|1)|\\d+|""|\'\'|\\[\\])', LIT = `(?:${ATOM}|\\(\\s*${ATOM}\\s*\\))`;
const TAUT_RE = new RegExp(`(?:\\bassert\\s+)?(?<![\\w$])${LIT}\\s*(?:===?|!==?|is(?:\\s+not)?)\\s*${LIT}(?![\\w$])|\\bassert\\s+(?:not\\s+)?\\(?\\s*${ATOM}\\s*\\)?(?=\\s*(?:$|[\\n;#,]))|\\b(?:(?:self\\.)?assert(?:Is|Equal|NotEqual)|(?:assert|expect)\\.(?:strictEqual|equal|deepEqual))\\s*\\(\\s*${LIT}\\s*,\\s*${LIT}\\s*\\)|\\b(?:self\\.)?assert(?:True|False)\\s*\\(\\s*${LIT}\\s*\\)`, 'g');
const HTTP_REJ_RE = /\b(?:status(?:_code)?|exception\.code)\s*(?:===?|>=)\s*(?:4(?:00|01|03|05|09|13|15|22|29)|5(?:00|02|03))\b|\b(?:status(?:_code)?|exception\.code)\s*in\s*[\(\[{][^)\]}\n]*\b(?:4(?:00|01|03|05|09|13|15|22|29)|5(?:00|02|03))\b[^)\]}\n]*[\)\]}]|(?:assertEqual|strictEqual|equal|toBe|assert_eq!)\s*\([^,\n]*(?:status|code)[^,\n]*,\s*(?:4(?:00|01|03|05|09|13|15|22|29)|5(?:00|02|03))\b|(?:400|401|403|405|422|503)[^\n]*\.includes\s*\([^)\n]*status/i;
const HTTP_404_RE = /\bstatus(?:_code)?\s*(?:===?\s*404\b|in\s*[\(\[{][^)\]}\n]*\b404\b[^)\]}\n]*[\)\]}])|(?:assertEqual|strictEqual|equal|toBe|assert_eq!)\s*\([^,\n]*(?:status|code)[^,\n]*,\s*404\b/i;
const PERMISSIVE_2XX_RE = /\b20[014]\b[^\n]*(?:\bor\b|\|\|)|(?:\bor\b|\|\|)[^\n]*\b20[014]\b|[\(\[{][^\n)\]}]*\b20[014]\b[^\n)\]}]*[\)\]}]/;
const ERR_INTRINSIC_RE = /\b(?:pytest\.raises|assertRaises(?:Regex)?|assert\.(?:throws|rejects)|toThrow|rejects\b|should_panic|is_err\s*\(|err\s*!=\s*nil)\b|notEqual\s*\([^,\n]*(?:returncode|exitCode|exit_code|status)[^,\n]*,\s*0\b/i, EXIT_NONZERO_RE = /\b(?:returncode|exitCode|exit_code)\s*(?:!==?\s*0\b|(?:===?|>=?)\s*[1-9]\d*\b)/i;
const NEG_DOMAIN_RE = /\bassert\s+not\s+[^\n]*\.exists\s*\(|\bexistsSync\s*\([^)]+\)\s*===?\s*false|\b(?:self\.)?assertFalse\s*\(\s*[^)\n]+\)|\bassert\s+[^\n]+(?:\bis\s+False\b|==\s*False\b)|\b(?:self\.)?assert(?:Is|Equal)\s*\(\s*[^,\n]+,\s*False\b|\bassert\.(?:strictEqual|equal)\s*\(\s*[^,\n]+,\s*false\b|(?:rowcount|count|rows|fetchall|SELECT\s+COUNT)[^\n]*===?\s*0\b/i;
const HAPPY_NEG_KEY_RE = /\b(?:is_error|has_error|failed|revoked|expired|denied|rejected|blocked|errors?)\b[^\n]*(?:is\s+False|==\s*False|===?\s*false|,\s*(?:False|false)\b|\[\s*\])|\bassertFalse\s*\([^)\n]*\b(?:is_error|has_error|failed|revoked|expired|denied|rejected|blocked)\b/i;
const ACTIVE_CALL_RE = /(?<![A-Za-z0-9_$])(?!assert\b|expect\b|print\b|if\b|for\b|while\b|with\b|return\b)[A-Za-z_$][A-Za-z0-9_$]*(?:\s*\.\s*[A-Za-z_$][A-Za-z0-9_$]*)*\s*\(/;
const ANY_ASSERT_RE = /\bassert(?:\s+\S|\.)|\bexpect\s*\(\s*[^)\s]|assert(?:Equal|NotEqual|True|False|Is|IsNot|In|NotIn|NotNone|IsNotNone|Ok|_eq!)|t\.(?:Fatal|Error)/i, ASSERT_OR_THROW_RE = /\b(?:assert(?:\s+\S|\.)|expect\s*\(\s*[^)\s]|raise\b|throw\b)|assert(?:Equal|NotEqual|True|False|Is|IsNot|In|NotIn|NotNone|IsNotNone|Ok|_eq!)|t\.(?:Fatal|Error)/i;

const detectLang = (p) => (/\.py$/i.test(p) ? 'py' : /\.go$/i.test(p) ? 'go' : /\.rs$/i.test(p) ? 'rs' : 'js'), normPath = (p) => String(p ?? '').trim().replace(/\\/g, '/').replace(/\/+/g, '/').replace(/^(?:\.\/)+/, ''), escRe = (s) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), globMatch = (pat, val) => compileGlobMatcher(pat)?.test(val) ?? false;
const isJsRegexStart = (p) => !p || '([{:;,=!?&|+-*%^~<>}'.includes(p) || /^(?:return|case|throw|in|of|typeof|void|delete|new|else|do|yield|await)$/.test(p);
const pyBlockEnd = (lines, at, indent) => { for (let j = at + 1; j < lines.length; j += 1) if (lines[j].trim() && /^\s*/.exec(lines[j])[0].length <= indent) return j - 1; return lines.length - 1; };
const scanBalancedEnd = (lines, at, o, cl) => { let d = 0, st = false; for (let j = at; j < lines.length; j += 1) for (const ch of lines[j]) { if (ch === o) { d += 1; st = true; } else if (ch === cl && (d -= 1) <= 0 && st) return j; } return lines.length - 1; };
const countNonTrivialSubproc = (raw, masked, lang) => (CAP_RE.subproc[lang].test(masked) ? [...raw.matchAll(new RegExp(CAP_RE.subproc[lang].source, 'g'))].filter((m) => !TRIVIAL_BIN_RE.test(raw.slice(m.index, m.index + 140))).length : 0);
const detectCaps = (raw, masked, lang) => new Set([...(CAP_RE.http[lang].test(masked) ? ['http'] : []), ...(CAP_RE.db[lang].test(masked) ? ['db'] : []), ...(countNonTrivialSubproc(raw, masked, lang) > 0 ? ['subproc'] : [])]);
const stripAssertMsgs = (raw) => raw.split(/\r?\n/).map((l) => l.replace(/^(\s*assert\b.+?),\s*[rRuUfFbB]{0,2}(?:'[^'\n]*'|"[^"\n]*")\s*$/, '$1').replace(/(assert(?:Equal|NotEqual|Is)|(?:assert|expect)\.(?:strictEqual|equal|deepEqual))\s*\(([^,\n]+,[^,\n]+),\s*['"`][^'"`\n]*['"`]\s*\)/g, '$1($2)')).join('\n');

/** Single-pass linear O(N) comment/docstring stripper and string-literal masker preserving line breaks. */
function scanCode(source, lang = 'js') {
  const s = String(source ?? ''), c = [], m = [], tpl = [];
  let i = 0, lineStart = true, lastTok = '';
  const push = (t) => { c.push(t); m.push(t); }, mask = (t) => `"${t.replace(/[^\n]/g, '')}"`;
  const prevWord = () => { let j = c.length - 1; while (j >= 0 && /\s/.test(c[j])) j -= 1; if (j < 0 || !/[\w$]/.test(c[j])) return j >= 0 ? c[j] : ''; const e = j; while (j >= 0 && /[\w$]/.test(c[j])) j -= 1; return c.slice(j + 1, e + 1).join(''); };
  const scanTpl = () => { m.push('"'); while (i < s.length) { if (s[i] === '\\' && i + 1 < s.length) { c.push(s[i], s[i + 1]); if (s[i + 1] === '\n') m.push('\n'); i += 2; continue; } if (s[i] === '$' && s[i + 1] === '{') { c.push('$', '{'); m.push('"+('); i += 2; tpl.push(1); lineStart = false; lastTok = '('; return; } if (s[i] === '`') { c.push('`'); m.push('"'); i += 1; lineStart = false; lastTok = 'q'; return; } c.push(s[i]); if (s[i] === '\n') m.push('\n'); i += 1; } m.push('"'); lineStart = false; lastTok = 'q'; };
  while (i < s.length) {
    const ch = s[i], nx = s[i + 1];
    if (lang === 'py' && ch === '#') { while (i < s.length && s[i] !== '\n') { push(' '); i += 1; } continue; }
    if (lang === 'py') {
      const pre = !/[\w$]/.test(s[i - 1] ?? '') && /^[rRuUfFbB]{1,2}['"]/.test(s.slice(i, i + 3)) ? (/^[rRuUfFbB]{2}['"]/.test(s.slice(i, i + 3)) ? 2 : 1) : 0, q = i + pre;
      if ((s[q] === '"' || s[q] === '\'') && s[q + 1] === s[q] && s[q + 2] === s[q]) {
        const d = s[q]; let j = q + 3; while (j < s.length) { if (s[j] === '\\' && j + 1 < s.length) { j += 2; continue; } if (s[j] === d && s[j + 1] === d && s[j + 2] === d) { j += 3; break; } j += 1; }
        let k = j; while (k < s.length && (s[k] === ' ' || s[k] === '\t' || s[k] === '\r')) k += 1;
        const raw = s.slice(i, j); if (lineStart && (k >= s.length || s[k] === '\n' || s[k] === '#')) push(raw.replace(/[^\n]/g, ' ')); else { c.push(raw); m.push(mask(raw)); }
        i = j; lineStart = false; lastTok = 'q'; continue;
      }
      if (pre > 0) { const d = s[q]; let j = q + 1; while (j < s.length && s[j] !== '\n') { if (s[j] === '\\' && j + 1 < s.length) { j += 2; continue; } if (s[j] === d) { j += 1; break; } j += 1; } c.push(s.slice(i, j)); m.push('""'); i = j; lineStart = false; lastTok = 'q'; continue; }
    } else if (ch === '/' && nx === '/') { while (i < s.length && s[i] !== '\n') { push(' '); i += 1; } continue; }
    else if (ch === '/' && nx === '*') { push('  '); i += 2; while (i < s.length) { if (s[i] === '*' && s[i + 1] === '/') { push('  '); i += 2; break; } push(s[i] === '\n' ? '\n' : ' '); i += 1; } continue; }
    else if (lang === 'js' && ch === '`') { c.push('`'); i += 1; scanTpl(); continue; }
    else if (lang === 'js' && tpl.length > 0 && (ch === '{' || ch === '}')) { if (ch === '{') { tpl[tpl.length - 1] += 1; push('{'); i += 1; continue; } if (--tpl[tpl.length - 1] === 0) { tpl.pop(); c.push('}'); m.push(')+'); i += 1; scanTpl(); continue; } push('}'); i += 1; continue; }
    else if (lang === 'js' && ch === '/' && isJsRegexStart(lastTok || prevWord())) { let j = i + 1, cls = false; while (j < s.length && s[j] !== '\n') { if (s[j] === '\\' && j + 1 < s.length) { j += 2; continue; } if (s[j] === '[') cls = true; else if (s[j] === ']') cls = false; else if (s[j] === '/' && !cls) { j += 1; break; } j += 1; } c.push(s.slice(i, j)); m.push('/re/'); i = j; lineStart = false; lastTok = 'r'; continue; }
    if (ch === '"' || ch === '\'' || (lang === 'go' && ch === '`')) { let j = i + 1; while (j < s.length) { if (ch !== '`' && s[j] === '\\' && j + 1 < s.length) { j += 2; continue; } if (s[j] === ch) { j += 1; break; } if (ch !== '`' && s[j] === '\n') break; j += 1; } const raw = s.slice(i, j); c.push(raw); m.push(mask(raw)); i = j; lineStart = false; lastTok = 'q'; continue; }
    push(ch); if (ch === '\n') lineStart = true; else if (!/\s/.test(ch)) { lineStart = false; lastTok = /[\w$]/.test(ch) ? '' : ch; } i += 1;
  }
  return { code: c.join(''), masked: m.join('') };
}
export const stripCommentsAndDocstrings = (source, lang = 'js') => scanCode(source, lang).code;

export function classifyNativeOnlySurfaces({ modulePath = '', promptText = '', moduleSource = '' } = {}) {
  const pathStr = normPath(modulePath), code = stripCommentsAndDocstrings(moduleSource, detectLang(pathStr)), prompt = String(promptText ?? ''), s = [];
  if (HTTP_PATH_RE.test(pathStr) || HTTP_CODE_RE.test(code) || HTTP_PROMPT_RE.test(prompt)) s.push('http-auth-browser-mcp');
  if (PARSER_RE.test(pathStr) || PARSER_RE.test(code) || PARSER_RE.test(prompt)) s.push('binary-parser');
  if (STORAGE_RE.test(pathStr) || STORAGE_RE.test(code) || STORAGE_RE.test(prompt)) s.push('storage-dr');
  if (CLI_PATH_RE.test(pathStr) || CLI_CODE_PROMPT_RE.test(code) || CLI_CODE_PROMPT_RE.test(prompt)) s.push('cli-day0');
  return s.length ? s.sort() : ['general-native-boundary'];
}

function pyDecoratorsAbove(lines, at) {
  let i = at - 1, d = 0, out = [];
  while (i >= 0) { const t = lines[i].trim(); if (!t) { i -= 1; continue; } for (let k = t.length - 1; k >= 0; k -= 1) d = t[k] === ')' ? d + 1 : (t[k] === '(' ? Math.max(0, d - 1) : d); if (d > 0 || t.startsWith('@')) out.unshift(lines[i--]); else break; }
  return out.join('\n');
}

function extractPyFixtures(code, masked) {
  const map = new Map(), lines = code.split(/\r?\n/), mLines = masked.split(/\r?\n/);
  if (PRIMITIVE_SHADOW_RE.test(masked) || MOCK_CALL_RE.test(masked)) return map;
  for (let at = 0; at < mLines.length; at += 1) {
    const m = /^([ \t]*)(?:async\s+)?def\s+([A-Za-z_]\w*)\s*\(/.exec(mLines[at]);
    if (!m || !/@(?:pytest\.)?fixture\b/.test(pyDecoratorsAbove(mLines, at))) continue;
    const sEnd = scanBalancedEnd(mLines, at, '(', ')'), end = pyBlockEnd(mLines, sEnd, m[1].length), caps = detectCaps(lines.slice(sEnd + 1, end + 1).join('\n'), mLines.slice(sEnd + 1, end + 1).join('\n'), 'py');
    if (caps.size) map.set(m[2], caps);
  }
  return map;
}

function stripDeadCode(body, mBody, lang) {
  const lines = body.split(/\r?\n/), mLines = mBody.split(/\r?\n/), kept = [], keptM = [], out = [], outM = [];
  const calledElsewhere = (name, i, end) => new RegExp(`(?<![A-Za-z0-9_$.])${escRe(name)}\\s*\\(`).test([...mLines.slice(0, i), ...mLines.slice(end + 1)].join('\n'));
  let baseInd = null, brace = 0;
  for (let i = 0; i < lines.length; i += 1) {
    const mt = (mLines[i] ?? '').trim(); if (!mt || /^(?:void\s+)?\(*(?:""|\s*\+\s*)+\)*\s*;?$/.test(mt)) continue;
    if (lang === 'py') {
      const ind = /^\s*/.exec(mLines[i])[0].length; if (baseInd === null) baseInd = ind;
      if (ind === baseInd && /^return\b/.test(mt)) break;
      if (/^(?:(?:if|while)\s*\(?\s*(?:False|0|None|not\s+True)\s*\)?|with\s+(?:contextlib\.)?suppress\s*\([^)]*(?:AssertionError|Exception|BaseException)[^)]*\))\s*:/.test(mt)) { i = pyBlockEnd(mLines, i, ind); continue; }
      if (/^try\s*:/.test(mt)) {
        let excAt = pyBlockEnd(mLines, i, ind) + 1; while (excAt < mLines.length && !mLines[excAt].trim()) excAt += 1;
        if (excAt < mLines.length && /^\s*/.exec(mLines[excAt])[0].length === ind && /^except(?:\s*:|\s+(?:AssertionError|BaseException|Exception)\b|\s*\([^)]*(?:AssertionError|BaseException|Exception))/.test(mLines[excAt].trim())) { const eEnd = pyBlockEnd(mLines, excAt, ind); if (!/\b(?:raise|assert|fail)\b|assert(?:Equal|NotEqual|True|False|Is|In|Raises)/.test(`${mLines[excAt].replace(/^[^:]*:/, '')}\n${mLines.slice(excAt + 1, eEnd + 1).join('\n')}`)) { i = eEnd; continue; } }
      }
      if (/^lambda\b[^:]*:/.test(mt)) continue;
      const fnm = /^(?:([A-Za-z_]\w*)\s*=\s*lambda\b|(?:async\s+)?def\s+([A-Za-z_]\w*)\s*\()/.exec(mt);
      if (fnm) { const end = fnm[2] ? pyBlockEnd(mLines, i, ind) : i; if (!calledElsewhere(fnm[1] || fnm[2], i, end)) { i = end; continue; } }
    } else {
      if (brace === 0 && /^return\b/.test(mt)) break;
      if (/^(?:if|while)\s*\(\s*(?:false|0|null|undefined|!\s*true|!\s*1)\s*\)/.test(mt)) { i = mt.includes('{') ? scanBalancedEnd(mLines, i, '{', '}') : i + (mt.endsWith(';') ? 0 : 1); continue; }
      if (/^try\s*\{/.test(mt)) {
        const tEnd = scanBalancedEnd(mLines, i, '{', '}'), ci = mLines[tEnd].search(/\}\s*catch\b/), tail = ci >= 0 ? mLines[tEnd].slice(ci + 1) : '', cAt = ci >= 0 ? tEnd : (tEnd + 1 < mLines.length && /^\s*catch\b/.test(mLines[tEnd + 1]) ? tEnd + 1 : -1);
        if (cAt >= 0) { const tmp = [cAt === tEnd ? tail : mLines[cAt], ...mLines.slice(cAt + 1)], rEnd = scanBalancedEnd(tmp, 0, '{', '}'); if (!/\b(?:throw|assert|expect)\b/.test(tmp.slice(0, rEnd + 1).join('\n'))) { i = cAt + rEnd; continue; } }
      }
      const nf = /^(?:(?:async\s+)?function\s+([A-Za-z_$]\w*)\s*\(|(?:const|let|var)\s+([A-Za-z_$]\w*)\s*=\s*(?:async\s+)?(?:function\b|\([^)]*\)\s*=>|[A-Za-z_$]\w*\s*=>))/.exec(mt);
      if (nf) { const end = mt.includes('{') ? scanBalancedEnd(mLines, i, '{', '}') : i; if (!calledElsewhere(nf[1] || nf[2], i, end)) { i = end; continue; } }
      for (const ch of mt) { if (ch === '{') brace += 1; else if (ch === '}') brace = Math.max(0, brace - 1); }
    }
    kept.push(lines[i]); keptM.push(mLines[i]);
  }
  for (let i = 0; i < kept.length; i += 1) {
    const m = /^\s*(?:(?:const|let|var)\s+)?([A-Za-z_$][A-Za-z0-9_$]*)\s*=(?!=)\s*(.+)$/.exec(keptM[i]);
    if (m) {
      const rhs = m[2].trim(), open = rhs[0] === '{' ? ['{', '}'] : rhs[0] === '[' ? ['[', ']'] : (rhs[0] === '(' || /^(?:dict|list|set|tuple)\s*\(/.test(rhs)) ? ['(', ')'] : null, end = open ? scanBalancedEnd(keptM, i, open[0], open[1]) : i;
      if ((open || !/\(/.test(rhs)) && !detectCaps(kept.slice(i, end + 1).join('\n'), keptM.slice(i, end + 1).join('\n'), lang).size && !new RegExp(`(?<![A-Za-z0-9_$.])${escRe(m[1])}(?![A-Za-z0-9_$])`).test([...keptM.slice(0, i), ...keptM.slice(end + 1)].join('\n'))) { i = end; continue; }
    }
    out.push(kept[i]); outM.push(keptM[i]);
  }
  return { eff: out.join('\n'), maskedEff: outM.join('\n') };
}

function splitTestsAndHelpers(code, masked, lang) {
  const lines = code.split(/\r?\n/), mLines = masked.split(/\r?\n/), tests = [], helpers = new Map(), skipped = [];
  if (lang === 'py' && /\bpytestmark\s*=\s*(?:[^\n]*\bskip|\[[\s\S]{0,400}?\bskip)/.test(masked)) return { tests, helpers };
  const skipRe = lang === 'py' ? /@(?:pytest\.mark\.(?:skip|skipif|xfail)|unittest\.skip)|\b(?:pytest\.skip|(?:self\.)?skipTest)\s*\(|\braise\s+unittest\.SkipTest\b/ : lang === 'go' ? /\bt\.Skip(?:f|Now)?\s*\(/ : lang === 'rs' ? /#\[\s*ignore\b/ : /\b(?:test|it|t|ctx)\.(?:skip|todo)\s*\(/;
  const optSkipRe = /\{[^}]{0,200}\b(?:skip|todo)\s*:\s*(?:true|""|!)/, inSkip = (at) => skipped.some(([s, e]) => at >= s && at <= e), clsStack = [];
  const cbPos = (txt) => { const a = txt.indexOf('=>'), f = txt.search(/\bfunction\b/); return a >= 0 && f >= 0 ? Math.min(a, f) : Math.max(a, f); };
  for (let at = 0; at < mLines.length; at += 1) {
    if (lang === 'py') {
      const cm = /^([ \t]*)class\s+(\w+)/.exec(mLines[at]);
      if (cm) { const cEnd = pyBlockEnd(mLines, at, cm[1].length); clsStack.push([at, cEnd, cm[2]]); if (skipRe.test(pyDecoratorsAbove(mLines, at))) skipped.push([at, cEnd]); }
      const m = /^([ \t]*)(?:async\s+)?def\s+([A-Za-z_]\w*)\s*\(/.exec(mLines[at]); if (!m) continue;
      const sigEnd = scanBalancedEnd(mLines, at, '(', ')'), end = pyBlockEnd(mLines, sigEnd, m[1].length), pm = /\(([^)]*)\)/.exec(mLines.slice(at, sigEnd + 1).join(' '));
      const body = lines.slice(sigEnd + 1, end + 1).join('\n'), mBody = mLines.slice(sigEnd + 1, end + 1).join('\n'), cls = clsStack.findLast(([s, e]) => at > s && at <= e)?.[2] ?? null;
      if (/^test_/.test(m[2])) { if (!inSkip(at) && !skipRe.test(`${pyDecoratorsAbove(mLines, at)}\n${mBody}`)) tests.push({ name: m[2], cls, params: (pm?.[1] ?? '').split(',').map((p) => p.split(/[:=]/)[0].trim()).filter(Boolean), body, mBody }); }
      else if (m[1].length === 0) helpers.set(m[2], { body, mBody });
    } else if (lang === 'js') {
      if (/^\s*(?:(?:test\.)?describe|suite|context)(?:\.(?:skip|todo)\s*\(|\s*\([^;{}]*\{[^}]{0,200}\b(?:skip|todo)\s*:\s*(?:true|""|!))/.test(mLines.slice(at, at + 4).join('\n'))) skipped.push([at, scanBalancedEnd(mLines, at, '(', ')')]);
      const hm = /^\s*(?:async\s+)?function\s+([A-Za-z_$]\w*)\s*\(/.exec(mLines[at]), tm = /^\s*(?:await\s+)?(?:test|it)(?:\.(?:only|skip|todo))?\s*\(/.exec(mLines[at]); if (!hm && !tm) continue;
      const end = scanBalancedEnd(mLines, at, tm ? '(' : '{', tm ? ')' : '}'), raw = lines.slice(at, end + 1).join('\n'), mRaw = mLines.slice(at, end + 1).join('\n');
      const cbCol = (l, hasB) => { let q = ''; for (let k = 0; k < l.length; k += 1) { const ch = l[k]; if (q) { if (ch === '\\') k += 1; else if (ch === q) q = ''; continue; } if (ch === '\'' || ch === '"' || ch === '`') q = ch; else if ((ch === '=' && l[k + 1] === '>') || (l.startsWith('function', k) && !/[\w$]/.test(l[k - 1] ?? '') && !/[\w$]/.test(l[k + 8] ?? ''))) { const b = l.indexOf('{', k); return b >= 0 ? b + 1 : k + 2; } } return hasB ? l.indexOf('{') + 1 : 0; };
      if (tm) {
        const mIdx = cbPos(mRaw), head = mRaw.slice(0, mIdx >= 0 ? mIdx : mRaw.length), ms = mRaw.indexOf('{', mIdx >= 0 ? mIdx : 0), lo = mIdx >= 0 ? mRaw.slice(0, ms >= 0 ? ms : mIdx).split('\n').length - 1 : 0;
        const cut = (arr) => { const a = arr.slice(at + lo, end + 1); a[0] = a[0].slice(cbCol(a[0], ms >= 0)); const s = a.join('\n'), li = s.lastIndexOf('}'); return ms >= 0 && li >= 0 ? s.slice(0, li) : s; };
        if (!inSkip(at) && !skipRe.test(mRaw) && !optSkipRe.test(head)) tests.push({ name: '', cls: null, params: [], body: cut(lines), mBody: cut(mLines) });
      } else helpers.set(hm[1], { body: raw.slice(raw.indexOf('{') + 1, raw.lastIndexOf('}')), mBody: mRaw.slice(mRaw.indexOf('{') + 1, mRaw.lastIndexOf('}')) });
    } else {
      const m = (lang === 'go' ? /^\s*func\s+(Test\w*|[A-Za-z_]\w*)\s*\(/ : /^\s*(?:pub\s+)?(?:async\s+)?fn\s+([A-Za-z_]\w*)\s*\(/).exec(mLines[at]); if (!m) continue;
      let start = at; if (lang === 'rs') while (start > 0 && /^\s*#\[/.test(mLines[start - 1])) start -= 1;
      const isTest = lang === 'go' ? /^Test/.test(m[1]) : mLines.slice(start, at).some((l) => /#\[\s*(?:[\w:]*::)?test\b/.test(l)), end = scanBalancedEnd(mLines, at, '{', '}'), body = lines.slice(at + 1, end + 1).join('\n'), mBody = mLines.slice(at + 1, end + 1).join('\n');
      if (isTest) { if (!skipRe.test(`${mLines.slice(start, at).join('\n')}\n${mBody}`)) tests.push({ name: m[1], cls: null, params: [], body, mBody }); } else helpers.set(m[1], { body, mBody });
    }
  }
  return { tests, helpers };
}

const HTTP_PROBE_RULES = [
  ['auth-forged-access', (e, m, hr, er) => (hr && /\b(?:401|403)\b/.test(m)) || ((hr || er) && /\b(?:forged|unauth|tamper|revoke|revoked|invalid[_-]?token|bad[_-]?token|decision)\b/i.test(e))],
  ['clock-expiry', (e, _m, hr, er) => (hr || er) && /['"](?:now|expires?_at|exp|ttl|clock)['"]\s*[:=]|\b(?:expired|past_now|client_now|caller_now)\b/i.test(e)],
  ['csrf-origin', (e, _m, hr, er) => (hr || er) && /['"](?:origin|referer|x-csrf[^'"]*|csrf[^'"]*)['"]\s*[:=]|\b(?:evil\.|attacker\.|cross[_-]?origin|csrf)\b/i.test(e)],
  ['strict-coercion', (e, _m, hr, er, na) => (hr || er || na) && /(?:[:=]\s*['"](?:false|0|no|off)['"]|:\s*(?:None|null)\b|\b(?:bool_coercion|string_false|missing_key)\b)/i.test(e)],
  ['path-traversal', (e, _m, hr, er, _na, h4) => (hr || er || h4) && /(?:\.\.\/|\.\.\\\\|%2e%2e|\/etc\/passwd|escaped_pwned)/i.test(e)],
  ['ssrf-redirect', (e, _m, hr, er) => (hr || er) && /(?:%(?!20\b)[0-9a-f]{2}|169\.254\.169\.254|file:\/\/|gopher:\/\/|allow_redirects\s*=\s*False|ssrf|redirect[_-]?downgrade)/i.test(e)],
  ['interactive-csp-wire', (e, m, _hr, _er, _na, _h4, aa) => aa && ((/content-security-policy|script-src\s+'none'/i.test(e) && /<form|<input/i.test(e)) || (/(?:['"]initialize['"]|['"]tools\/list['"]|jsonrpc|\/\.well-known\/oauth|code_challenge|pkce)/i.test(e) && /\.(?:post|get|request)\s*\(|fetch\s*\(|urlopen\s*\(/i.test(m)))],
];

export function detectAdversarialProbesInTest(testPath, source, { hasRealHostSmoke = null, conftestFixtures = null, onlyTests = null } = {}) {
  const norm = normPath(testPath), lang = detectLang(norm), { code: clean, masked } = scanCode(source, lang), shadowed = PRIMITIVE_SHADOW_RE.test(masked) || (lang === 'js' && NON_BUILTIN_SHADOW_RE.test(clean));
  const allFixtures = new Map([...(conftestFixtures instanceof Map ? conftestFixtures : []), ...(lang === 'py' && !shadowed ? extractPyFixtures(clean, masked) : [])]);
  const hasRealExecFile = !shadowed && (hasRealHostSmoke !== null ? hasRealHostSmoke : (detectCaps(clean, masked, lang).size > 0 || allFixtures.size > 0));
  const { tests, helpers } = splitTestsAndHelpers(clean, masked, lang), probesBySurface = {}, add = (s, p) => { (probesBySurface[s] ??= new Set()).add(p); };
  for (const tc of tests) {
    if (onlyTests instanceof Set && !onlyTests.has(tc.name) && !(tc.cls && (onlyTests.has(tc.cls) || onlyTests.has(`${tc.cls}::${tc.name}`)))) continue;
    let { eff, maskedEff } = stripDeadCode(tc.body, tc.mBody, lang);
    for (const [h, hb] of helpers) if (new RegExp(`(?<![A-Za-z0-9_$.])${escRe(h)}\\s*\\(`).test(maskedEff)) { const d = stripDeadCode(hb.body, hb.mBody, lang); eff += `\n${d.eff}`; maskedEff += `\n${d.maskedEff}`; }
    if (!ACTIVE_CALL_RE.test(maskedEff) || PRIMITIVE_SHADOW_RE.test(maskedEff) || MOCK_CALL_RE.test(maskedEff)) continue;
    const tcCaps = hasRealExecFile ? detectCaps(eff, maskedEff, lang) : new Set();
    if (hasRealExecFile && lang === 'py') for (const p of tc.params) if (allFixtures.has(p) && new RegExp(`(?<![A-Za-z0-9_$.])${escRe(p)}\\s*[.(]|\\([^)\\n]*\\b${escRe(p)}\\b`).test(maskedEff)) for (const c of allFixtures.get(p)) tcCaps.add(c);
    const stim = stripAssertMsgs(eff), sLines = stim.split(/\r?\n/), mLines = maskedEff.split(/\r?\n/), mNoTaut = maskedEff.replace(TAUT_RE, '');
    const httpRej = mLines.some((l) => { const n = l.replace(TAUT_RE, ''); return ASSERT_OR_THROW_RE.test(n) && HTTP_REJ_RE.test(n) && !PERMISSIVE_2XX_RE.test(n); });
    const has404 = mLines.some((l) => { const n = l.replace(TAUT_RE, ''); return ASSERT_OR_THROW_RE.test(n) && HTTP_404_RE.test(n) && !PERMISSIVE_2XX_RE.test(n); });
    const errAssert = ERR_INTRINSIC_RE.test(mNoTaut) || mLines.some((l) => { const n = l.replace(TAUT_RE, ''); return ASSERT_OR_THROW_RE.test(n) && EXIT_NONZERO_RE.test(n); });
    const negDomain = mLines.some((l, idx) => NEG_DOMAIN_RE.test(l.replace(TAUT_RE, '')) && !HAPPY_NEG_KEY_RE.test(sLines[idx] ?? '')), negAssert = httpRej || errAssert || negDomain, anyAssert = negAssert || ANY_ASSERT_RE.test(mNoTaut);
    if (tcCaps.has('http')) for (const [id, fn] of HTTP_PROBE_RULES) if (fn(stim, mNoTaut, httpRej, errAssert, negAssert, has404, anyAssert)) add('http-auth-browser-mcp', id);
    if (tcCaps.has('db') || tcCaps.has('http') || (/\b(?:create_app|open_store|openTrustStore)\s*\(/.test(maskedEff) && PROD_IMPORT_RE[lang].test(clean))) {
      if (anyAssert && /(?:\.|(?<![A-Za-z0-9_$]))(?:write_bytes|writeFileSync|truncate(?:Sync)?)\s*\(|open\s*\([^)]*['"]wb['"]/.test(eff) && /(?:\.sqlite|\.db|corrupt|garbage|not\s+a\s+valid\s+sqlite)/i.test(stim) && /\b(?:create_app|connect|open|init|load|recover|DatabaseSync|sqlite3)\b/i.test(maskedEff)) add('storage-dr', 'corrupt-db-recovery');
      if (negAssert && /\b(?:rollback|audit[_-]?fail|503|atomic|sqlite_busy|BEGIN\s+IMMEDIATE)\b/i.test(stim) && /\b(?:SELECT|execute|sqlite|DatabaseSync|conn|cursor|count|rows|fetchall|prepare)\b/i.test(stim)) add('storage-dr', 'rollback-atomicity');
      if (anyAssert && (/\b(?:ThreadPoolExecutor|asyncio\.gather|Promise\.all(?:Settled)?|multiprocessing|worker_threads)\b/.test(maskedEff) || (negAssert && /\b(?:SQLITE_BUSY|OperationalError|database\s+is\s+locked)\b/i.test(stim)) || (/\bThread\s*\(/.test(maskedEff) && !/Thread\s*\([^)]*serve_forever/.test(eff) && /\b(?:join\s*\(|for\s+[^:\n]+:\s*[\s\S]{0,120}Thread\s*\()/.test(maskedEff))) && /\b(?:sqlite|DatabaseSync|sql\.Open|Connection::open|execute|insert|update|commit)\b/i.test(stim)) add('storage-dr', 'concurrent-transactions');
    }
    if (tcCaps.has('subproc') && /\bHOME\b|XDG_CONFIG_HOME|mkdtempSync|tmp_path|TemporaryDirectory|t\.TempDir/.test(stim) && (negAssert || (anyAssert && countNonTrivialSubproc(eff, maskedEff, lang) >= 2))) add('cli-day0', 'clean-home-walkthrough');
    if (tcCaps.size > 0 && negAssert) add('general-native-boundary', 'negative-real-host-probe');
    if (tcCaps.has('http') || (!MOCK_CALL_RE.test(masked) && BINARY_CONSTRUCT_RE.test(eff) && PROD_IMPORT_RE[lang].test(clean))) {
      const pAssert = negAssert || (anyAssert && mLines.some((l, idx) => { const n = l.replace(TAUT_RE, ''); return ANY_ASSERT_RE.test(n) && /\b(?:findings|blocked|redacted|unsafe|violations?|rejected|detected|malicious|macros?|formula|xxe)\b/i.test(sLines[idx] ?? '') && !/(?:===?\s*(?:\[\]|(?:0|false|null|None)\b)|\bis\s+(?:False|None)\b|\blength\s*===?\s*0\b|len\s*\([^)]*\)\s*===?\s*0\b|assertFalse\b|assertEqual\s*\([^,\n]+,\s*(?:\[\]|(?:0|False|None)\b)|strictEqual\s*\([^,\n]+,\s*(?:0|false|null)\b|\bassert\s+not\b)/i.test(n); }));
      if (pAssert && /(?:\/ObjStm|\/Fl#61teDecode|\/ASCIIHexDecode|\/ASCII85Decode|\/JavaScript|\/Launch|\/OpenAction|x:xmpmeta|\/Annot|\/XFA|\/Encrypt|\bTJ\b|(?:malformed|corrupt|truncated)[^\n]{0,30}pdf)/i.test(stim)) add('binary-parser', 'pdf-adversarial');
      if (pAssert && /(?:<!ENTITY|<!DOCTYPE|=HYPERLINK|=CMD|=IMPORTXML|vbaProject|xl\/macrosheets|zip[_-]?bomb|BadZipFile|(?:malformed|corrupt)[^\n]{0,30}(?:xlsx|xml|zip|archive)|\.\.\/[^\n]{0,40}\.(?:xml|txt|py|sh))/i.test(stim)) add('binary-parser', 'xlsx-archive-adversarial');
      if (negAssert && /\b(?:redos|timeout|bomb|oversized|decompression)\b/i.test(stim) && /(?:\.repeat\s*\(|\*\s*\d{3,}|zlib\.compress|zipfile)/i.test(eff)) add('binary-parser', 'parser-timeout-redos');
    }
  }
  const outBySurface = {}, probes = new Set(), coveredSurfaces = [];
  for (const [surf, set] of Object.entries(probesBySurface).sort()) { const arr = [...set].sort(); outBySurface[surf] = arr; if (surf !== 'http-auth-browser-mcp' || arr.some((p) => HTTP_NEG_PROBES.has(p))) { coveredSurfaces.push(surf); for (const p of arr) probes.add(p); } }
  return { hasRealHostSmoke: Boolean(hasRealExecFile), hasAdversarialProbes: probes.size > 0, happyPathOnly: Boolean(hasRealExecFile && probes.size === 0), surfaces: coveredSurfaces.sort(), probes: [...probes].sort(), probesBySurface: outBySurface };
}

function listRepoFilesSafe(realRoot, provided) {
  if (Array.isArray(provided)) return [...new Set(provided.map(normPath).filter(canonicalRepoPath))].sort();
  try { const t = gitFiles(realRoot); if (Array.isArray(t) && t.length) return [...new Set(t.map(normPath).filter(canonicalRepoPath))].sort(); } catch {}
  const found = [], walk = (abs, rel, d) => { if (d > 8 || found.length >= 10_000) return; let es; try { es = readdirSync(abs, { withFileTypes: true }); } catch { return; } for (const e of es) { if (found.length >= 10_000 || e.isSymbolicLink() || ['.git', 'node_modules', '.venv', 'venv', '__pycache__', 'target'].includes(e.name)) continue; const p = rel ? `${rel}/${e.name}` : e.name; if (e.isDirectory()) walk(join(abs, e.name), p, d + 1); else if (e.isFile() && canonicalRepoPath(p)) found.push(p); } };
  walk(realRoot, '', 0); return found.sort();
}

function resolveTouchedNativeOnlyModules(realRoot, repoFiles, touchedFiles) {
  const nativePrompts = new Map(), proseClaims = new Map(), bindingMap = new Map(), out = [], seen = new Set();
  for (const rel of repoFiles) { if (!rel.endsWith('.prompt.md')) continue; const text = readSafeUtf8(realRoot, rel); if (typeof text !== 'string' || !isNativeOnlyPrompt(text)) continue; const entry = { path: rel, content: text }; nativePrompts.set(rel.toLowerCase(), entry); for (const c of promptClaims(rel, text)) { const k = normPath(c).toLowerCase(); if (k && !proseClaims.has(k)) proseClaims.set(k, entry); } }
  if (!nativePrompts.size) return [];
  try { for (const item of JSON.parse(readSafeUtf8(realRoot, 'pdd-bindings.json') ?? '{}')?.modules ?? []) { const m = normPath(item?.module).toLowerCase(), p = normPath(item?.prompt).toLowerCase(); if (m && p && nativePrompts.has(p)) bindingMap.set(m, nativePrompts.get(p)); } } catch {}
  for (const raw of touchedFiles) {
    const rel = normPath(raw), lower = rel.toLowerCase(); if (!rel || seen.has(lower) || NON_PROD_RE.test(lower) || !CODE_EXT_RE.test(lower) || isTestOwnedPath(rel)) continue;
    const hKey = headerPrompts(readSafeHeadUtf8(realRoot, rel, 4096) ?? '').map((r) => normPath(r).toLowerCase()).find((k) => nativePrompts.has(k)), entry = bindingMap.get(lower) ?? (hKey ? nativePrompts.get(hKey) : proseClaims.get(lower));
    if (entry) { seen.add(lower); out.push({ module: rel, prompt: entry.path, surfaces: classifyNativeOnlySurfaces({ modulePath: rel, promptText: entry.content, moduleSource: readSafeUtf8(realRoot, rel) ?? '' }) }); }
  }
  return out.sort((a, b) => a.module.localeCompare(b.module));
}

function executedTestFilter(rel, lang, commands, pkgScripts) {
  if (!commands.length) return true;
  const segs = [], q = commands.flatMap((c) => String(c ?? '').split(/\s*(?:&&|\|\||;)\s*/));
  for (let d = 0; q.length && d < 24; d += 1) { const s = q.shift().trim().replace(/^(?:[A-Za-z_]\w*=(?:'[^']*'|"[^"]*"|\S+)\s+)+/, ''), sm = /^(?:npm|pnpm|yarn)\s+(?:run(?:-script)?\s+)?([A-Za-z0-9:._-]+)(?:\s+(.*))?$/.exec(s); if (sm && typeof pkgScripts?.[sm[1]] === 'string') { const ex = (sm[2] ?? '').replace(/^--\s*/, '').trim(); for (const sub of pkgScripts[sm[1]].split(/\s*(?:&&|\|\||;)\s*/)) q.push(ex ? `${sub} ${ex}` : sub); } else if (s) segs.push(s); }
  const onlySet = new Set(); let matchedAll = false;
  for (const cmd of segs) {
    const toks = [...cmd.matchAll(/'([^']*)'|"([^"]*)"|(\S+)/g)].map((m) => m[1] ?? m[2] ?? m[3]);
    if (lang === 'py' ? (/\bpython3?\s+-c\b/i.test(cmd) || (!/\b(?:pytest|unittest)\b/i.test(cmd) && !(/\bpython3?\b/i.test(cmd) && !/\s-m\b/.test(cmd) && toks.some((t) => /\.py$/i.test(t))))) : !(lang === 'go' ? /\bgo\s+test\b/i : lang === 'rs' ? /\bcargo\s+test\b/i : /\b(?:vitest|jest|mocha|bun\s+test|deno\s+test|node\b[^\n]*--test)\b/i).test(cmd)) continue;
    const files = [], dirs = [], globs = [], dotted = [], isDiscover = toks.includes('discover'); let afterUnit = false, pat = null;
    for (let i = 1; i < toks.length; i += 1) {
      const t = toks[i];
      if (t === '-m') { if (toks[++i] === 'unittest') afterUnit = true; continue; }
      if (t === '-s' || t === '--start-directory') { dirs.push(normPath(toks[++i]).replace(/\/$/, '')); continue; }
      if (t.startsWith('--start-directory=')) { dirs.push(normPath(t.slice(18)).replace(/\/$/, '')); continue; }
      if (t === '-p' || t === '--pattern') { pat = toks[++i]; continue; }
      if (VALUE_FLAGS.has(t)) { i += 1; continue; }
      if (t.startsWith('-') || /^(?:discover|run|test|pytest|unittest|vitest|jest|mocha|bun|deno|node|python3?)$/i.test(t)) continue;
      const [rawF, ...nodeParts] = t.split('::'), cl = normPath(rawF).replace(/\/$/, ''), nid = nodeParts.filter(Boolean).join('::'); if (!cl) continue;
      if (cl.includes('*')) globs.push(cl); else if (/\.(?:py|mjs|cjs|js|ts|tsx|go|rs)$/i.test(cl)) files.push([cl, nid]); else if (lang === 'py' && afterUnit && !isDiscover && /^[A-Za-z_][\w.]*$/.test(cl)) dotted.push(cl.replace(/\./g, '/')); else if (cl.includes('/') || /^(?:tests?|__tests__|spec|src)$/i.test(cl)) dirs.push(cl);
    }
    if (pat && !globMatch(pat, rel.split('/').pop())) continue;
    if ((!files.length && !dirs.length && !globs.length && !dotted.length) || dirs.some((d) => d === '.' || rel === d || rel.startsWith(`${d}/`)) || globs.some((g) => globMatch(g, rel))) { matchedAll = true; break; }
    const noExt = rel.replace(/\.py$/i, '');
    for (const [f, nid] of files) if (f === rel || rel.endsWith(`/${f}`)) { if (nid) onlySet.add(nid); else matchedAll = true; }
    for (const p of dotted) if (rel === `${p}.py` || rel.startsWith(`${p}/`)) matchedAll = true; else if (p.startsWith(`${noExt}/`)) onlySet.add(p.slice(noExt.length + 1).replace(/\//g, '::'));
  }
  return matchedAll ? true : (onlySet.size ? onlySet : null);
}
function testBindsModule(cleanTest, relTest, modPath) {
  const normMod = normPath(modPath), stem = normMod.replace(/\.(?:[cm]?[jt]sx?|py|go|rs|sh|sql)$/i, ''), parts = stem.split('/').filter(Boolean), base = parts.at(-1) ?? '', parent = parts.length >= 2 ? parts.at(-2) : '';
  const impRe = detectLang(relTest) === 'go' ? /^\s*(?:import\b|"[^"\n]+\/[^"\n]+")/ : /^\s*(?:import|\}?\s*from|export\b[^\n]*\bfrom|use)\b|\b(?:require|import)\s*\(/;
  const imp = cleanTest.split(/[\r\n;]+/).filter((l) => impRe.test(l)).join('\n'), has = (hay, tok) => new RegExp(`(?<![A-Za-z0-9_])${escRe(tok)}(?![A-Za-z0-9_])`, 'i').test(hay);
  if ([normMod, stem, stem.replace(/^src\//, '').replace(/\//g, '.')].some((t) => has(imp, t) || (CLI_PATH_RE.test(normMod) && has(cleanTest, t)))) return true;
  return [...(parent && !GENERIC_DIRS.has(parent.toLowerCase()) ? [parent] : []), ...(base && !GENERIC_BASES.has(base.toLowerCase()) ? [base] : [])].some((t) => has(imp, t) || relTest.toLowerCase().includes(t.toLowerCase()));
}
export function inspectAdversarialBoundaryEvidence({ root, touchedFiles = [], repoFiles = null, testResult = null, pathResults = [] } = {}) {
  const realRoot = realpathSync(root), normTouched = [...new Set((Array.isArray(touchedFiles) ? touchedFiles : []).map(normPath).filter(canonicalRepoPath))].sort();
  const allFiles = [...new Set([...listRepoFilesSafe(realRoot, repoFiles), ...normTouched])].sort(), vectorFiles = allFiles.filter((f) => SIMULATED_VECTOR_RE.test(f));
  const simulated_vectors = { totalFiles: vectorFiles.length, touchedFiles: normTouched.filter((f) => SIMULATED_VECTOR_RE.test(f)), executesNativeOnlyBoundaries: false, status: vectorFiles.length > 0 ? 'simulated-only' : 'none' };
  const nativeModules = resolveTouchedNativeOnlyModules(realRoot, allFiles, normTouched);
  if (!nativeModules.length) return { simulated_vectors, adversarial_real_host: { applicable: false, status: 'not-applicable', nativeOnlyModules: [], requiredSurfaces: [], coveredSurfaces: [], missingSurfaces: [], probesBySurface: {}, happyPathOnlyFiles: [], adversarialTestFiles: [], checklist: {}, summary: 'Adversarial real-host: not-applicable', notProvedReasons: [] } };
  const requiredSurfaces = [...new Set(nativeModules.flatMap((m) => m.surfaces))].sort(), conftestByDir = new Map();
  for (const rel of allFiles) if (/(?:^|\/)conftest\.py$/i.test(rel)) { const t = readSafeUtf8(realRoot, rel); if (t) { const sc = scanCode(t, 'py'); conftestByDir.set(dirname(rel), extractPyFixtures(sc.code, sc.masked)); } }
  const executedCommands = [testResult?.ok ? testResult.command : null, ...(Array.isArray(pathResults) ? pathResults.filter((p) => p?.ok && p.run).map((p) => p.run) : [])].filter(Boolean);
  let pkgScripts = {}; try { pkgScripts = JSON.parse(readSafeUtf8(realRoot, 'package.json') ?? '{}')?.scripts ?? {}; } catch {}
  const probesBySurface = {}, modCovered = new Map(nativeModules.map((m) => [m.module, new Set()])), happyPathOnlyFiles = [], adversarialTestFiles = [];
  for (const rel of allFiles) {
    if (!NATIVE_TEST_RE.test(rel) || SKIP_TEST_SUBDIR_RE.test(rel)) continue;
    const execFilter = testResult?.ok ? executedTestFilter(rel, detectLang(rel), executedCommands, pkgScripts) : true, text = execFilter ? readSafeUtf8(realRoot, rel) : null;
    if (typeof text !== 'string') continue;
    const dir = dirname(rel), fixtures = new Map(); for (const [d, fMap] of conftestByDir) if (d === '.' || d === dir || dir.startsWith(`${d}/`)) for (const [k, v] of fMap) fixtures.set(k, v);
    const res = detectAdversarialProbesInTest(rel, text, { conftestFixtures: fixtures, onlyTests: execFilter instanceof Set ? execFilter : null });
    if (res.hasAdversarialProbes) {
      const clean = stripCommentsAndDocstrings(text, detectLang(rel)); adversarialTestFiles.push(rel);
      for (const [surf, list] of Object.entries(res.probesBySurface)) { probesBySurface[surf] ??= new Set(); for (const p of list) probesBySurface[surf].add(p); }
      for (const m of nativeModules) if (testBindsModule(clean, rel, m.module)) for (const s of res.surfaces) modCovered.get(m.module).add(s);
    } else if (res.happyPathOnly) happyPathOnlyFiles.push(rel);
  }
  const uncoveredModules = nativeModules.map((m) => ({ module: m.module, missing: m.surfaces.filter((s) => !modCovered.get(m.module).has(s)) })).filter((x) => x.missing.length > 0);
  const missingSurfaces = [...new Set(uncoveredModules.flatMap((x) => x.missing))].sort(), coveredSurfaces = requiredSurfaces.filter((s) => !missingSurfaces.includes(s));
  const serializedProbes = Object.fromEntries(Object.entries(probesBySurface).sort().map(([k, v]) => [k, [...v].sort()])), checklist = Object.fromEntries(requiredSurfaces.map((s) => [s, { covered: coveredSurfaces.includes(s), requiredChecks: ADVERSARIAL_SURFACE_CHECKLISTS[s] }]));
  const status = !testResult ? 'not-run' : (testResult.ok === false ? 'failed' : (uncoveredModules.length ? (happyPathOnlyFiles.length && !adversarialTestFiles.length ? 'happy-path-only' : 'missing-adversarial-probes') : 'proved'));
  const notProvedReasons = testResult?.ok && uncoveredModules.length ? [`${uncoveredModules[0].module}:1 [native-only-adversarial-missing] ${formatTeachingDetail({ invariant: `Touched kind: native-only module(s) lack executed adversarial real-host boundary probes: ${uncoveredModules.map((u) => `${u.module} [${u.missing.join(', ')}]`).join('; ')} (simulated_vectors=${simulated_vectors.totalFiles}, happy_path_only_tests=${happyPathOnlyFiles.length})`, fix: `Add executed non-mocked adversarial real-host tests targeting the module(s) covering ${missingSurfaces.map((s) => `${s} (${ADVERSARIAL_SURFACE_CHECKLISTS[s]})`).join('; ')}`, rerun: 'pdd prove' })}`] : [];
  return { simulated_vectors, adversarial_real_host: { applicable: true, status, nativeOnlyModules: nativeModules.map((m) => m.module), requiredSurfaces, coveredSurfaces, missingSurfaces, probesBySurface: serializedProbes, happyPathOnlyFiles: happyPathOnlyFiles.sort(), adversarialTestFiles: adversarialTestFiles.sort(), checklist, summary: `Adversarial real-host: ${status} (${coveredSurfaces.length}/${requiredSurfaces.length} surface(s) covered${missingSurfaces.length ? `; missing: ${missingSurfaces.join(', ')}` : ''})`, notProvedReasons } };
}
