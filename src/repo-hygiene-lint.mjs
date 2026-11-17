// Prompt: prompts/cli/repo-hygiene-lint.prompt.md
import { closeSync, constants, fstatSync, lstatSync, openSync, readSync, realpathSync } from 'node:fs';
import { isAbsolute, join, posix } from 'node:path';
import { isTestOwnedPath } from './file-owner.mjs';
import { isLintableStoryPath, lintStory } from './story-lint.mjs';
import { gitFiles, isSecretPath, workspace } from './runtime-seam.mjs';

const MAX_FILE_BYTES = 2 * 1024 * 1024;
const PROMPT_FENCE_LINE_LIMIT = 15;
const PROMPT_FENCE_TOTAL_LIMIT = 30;
const TEST_CODE_EXT = /\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|cs|swift)$/i;
const SRC_CODE_PATH = /^src\/.+\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|cs|swift)$/i;
const SEAM_TEST_FILE = /(?:^|\/)[^/]*seam\.test\.[A-Za-z0-9]+$/i;
const SKIP_TEST_SUBDIR = /(?:^|\/)(?:fixtures|helpers)\//i;
const FIXTURE_DIR = /(?:^|\/)fixtures(?:\/|$)/i;

const IMPERATIVE_PATTERNS = [
  /(?<![\w$-])(?:export|const|let|def|impl)\s+/,
  /(?<![\w$-])function(?:\s+[A-Za-z_$]|\s*\(|\*)/,
  /(?<![\w$-])(?:if|for|while)\s*\(/,
  /(?<![\w$-])return(?:\s+|;|$)/,
  /(?<![\w$-])try\s*\{/,
  /=>/,
];

const canonicalRepoPath = value => typeof value === 'string' && value.trim().length > 0 && value.length <= 1000 && !isAbsolute(value)
  && !/[\\\x00-\x1f\x7f]/.test(value) && !value.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');

function readSafeUtf8(realRoot, relPath, maxBytes = MAX_FILE_BYTES) {
  if (!canonicalRepoPath(relPath)) return null;
  const parts = relPath.split('/');
  let cur = realRoot;
  try {
    for (let i = 0; i < parts.length; i++) {
      cur = join(cur, parts[i]);
      const st = lstatSync(cur);
      if (st.isSymbolicLink()) return null;
      if (i < parts.length - 1 && !st.isDirectory()) return null;
      if (i === parts.length - 1 && (!st.isFile() || st.size > maxBytes)) return null;
    }
  } catch {
    return null;
  }
  let fd;
  try {
    fd = openSync(cur, constants.O_RDONLY | (constants.O_NOFOLLOW ?? 0));
    const fst = fstatSync(fd);
    if (!fst.isFile() || fst.size > maxBytes) return null;
    const buf = Buffer.alloc(fst.size);
    let offset = 0;
    while (offset < buf.length) {
      const n = readSync(fd, buf, offset, buf.length - offset, offset);
      if (!n) break;
      offset += n;
    }
    return buf.subarray(0, offset).toString('utf8');
  } catch {
    return null;
  } finally {
    if (fd !== undefined) {
      try { closeSync(fd); } catch {}
    }
  }
}

const blankPreservingLines = segment => segment.replace(/[^\r\n]/g, ' ');

function stripPromptMetadataPreservingLines(raw) {
  let text = String(raw ?? '');
  text = text.replace(/^---\r?\n[\s\S]*?\r?\n---(?:\r?\n|$)/, blankPreservingLines);
  text = text.replace(
    /<details\b[^>]*>\s*<summary\b[^>]*>[^\r\n]*runtime\s+interface[^\r\n]*<\/summary>[\s\S]*?<\/details>/gi,
    blankPreservingLines,
  );
  text = text.replace(
    /^#{2,6}[ \t]+runtime[ \t]+interface[ \t]*\r?\n[\s\S]*?(?=^#{1,6}[ \t]+\S|\s*$)/gim,
    blankPreservingLines,
  );
  return text;
}

function isDeclarativeJson(lang, bodyText) {
  const trimmed = bodyText.trim();
  if (!trimmed) return true;
  if (lang !== 'json' && lang !== 'jsonc' && !trimmed.startsWith('{') && !trimmed.startsWith('[')) return false;
  try {
    const parsed = JSON.parse(trimmed);
    return typeof parsed === 'object' && parsed !== null;
  } catch {
    return false;
  }
}

function findImperativeToken(lineText) {
  for (const pattern of IMPERATIVE_PATTERNS) {
    const match = pattern.exec(lineText);
    if (match) return match[0].trim();
  }
  return null;
}

export function lintPromptCodeBlocks(text, { path = 'prompts/module.prompt.md' } = {}) {
  const cleaned = stripPromptMetadataPreservingLines(text);
  const lines = cleaned.split(/\r?\n/);
  const fences = [];
  let inComment = false;
  let activeFence = null;

  for (let i = 0; i < lines.length; i++) {
    let line = lines[i];
    const lineNo = i + 1;

    if (activeFence) {
      const closeMatch = line.match(/^ {0,3}(`{3,}|~{3,})\s*$/);
      if (closeMatch && closeMatch[1][0] === activeFence.char && closeMatch[1].length >= activeFence.len) {
        fences.push(activeFence);
        activeFence = null;
      } else {
        activeFence.bodyLines.push({ lineNo, text: line });
      }
      continue;
    }

    if (inComment) {
      const endIdx = line.indexOf('-->');
      if (endIdx < 0) continue;
      inComment = false;
      line = ' '.repeat(endIdx + 3) + line.slice(endIdx + 3);
    }

    while (true) {
      const openIdx = line.indexOf('<!--');
      if (openIdx < 0) break;
      const closeIdx = line.indexOf('-->', openIdx + 4);
      if (closeIdx < 0) {
        line = line.slice(0, openIdx);
        inComment = true;
        break;
      }
      line = line.slice(0, openIdx) + ' '.repeat(closeIdx + 3 - openIdx) + line.slice(closeIdx + 3);
    }

    const openMatch = line.match(/^ {0,3}(`{3,}|~{3,})(.*)$/);
    if (openMatch && !(openMatch[1][0] === '`' && openMatch[2].includes('`'))) {
      const info = openMatch[2].trim();
      const lang = (info.split(/[\s{`~]/)[0] ?? '').toLowerCase();
      activeFence = {
        openLine: lineNo,
        char: openMatch[1][0],
        len: openMatch[1].length,
        lang,
        bodyLines: [],
      };
    }
  }
  if (activeFence) fences.push(activeFence);

  const nonMermaid = fences.filter(f => f.lang !== 'mermaid' && f.lang !== 'pdd-boundary');
  if (!nonMermaid.length) return [];

  const records = [];
  let totalBodyLines = 0;

  for (const fence of nonMermaid) {
    const count = fence.bodyLines.length;
    totalBodyLines += count;
    if (count > PROMPT_FENCE_LINE_LIMIT) {
      records.push({
        line: fence.openLine,
        order: 1,
        warning: `Warning: prompt code block: ${path}:${fence.openLine} [prompt-code-fence-length] Non-mermaid code fence spans ${count} lines (recommended <= ${PROMPT_FENCE_LINE_LIMIT}). Replace long code or schema blocks with plain-English rules, a Markdown table, or a mermaid diagram.`,
      });
    }
    const rawBody = fence.bodyLines.map(item => item.text).join('\n');
    if (!isDeclarativeJson(fence.lang, rawBody)) {
      for (const item of fence.bodyLines) {
        const token = findImperativeToken(item.text);
        if (token) {
          records.push({
            line: item.lineNo,
            order: 2,
            warning: `Warning: prompt code block: ${path}:${item.lineNo} [prompt-imperative-code] Fenced block contains imperative code ("${token}"). Describe observable inputs, outputs and failure rules in prose instead of embedding code in prompts.`,
          });
          break;
        }
      }
    }
  }

  if (totalBodyLines > PROMPT_FENCE_TOTAL_LIMIT) {
    const firstLine = nonMermaid[0].openLine;
    records.push({
      line: firstLine,
      order: 0,
      warning: `Warning: prompt code block: ${path}:${firstLine} [prompt-code-fence-total] Prompt contains ${totalBodyLines} non-mermaid fenced lines across ${nonMermaid.length} blocks (recommended <= ${PROMPT_FENCE_TOTAL_LIMIT} total). Move implementation details to tests or summarize contracts in prose and tables.`,
    });
  }

  records.sort((a, b) => a.line - b.line || a.order - b.order);
  return records.map(r => r.warning);
}

function decodeSimpleEscapes(raw) {
  return raw.replace(/\\(.)/gs, (_, ch) => {
    if (ch === 'n') return '\n';
    if (ch === 'r') return '\r';
    if (ch === 't') return '\t';
    return ch;
  });
}

const newlinesIn = str => {
  let n = 0;
  for (let i = 0; i < str.length; i++) if (str[i] === '\n') n++;
  return '\n'.repeat(n);
};

// Mask comments and string/template bodies into __STR_k__ placeholders while keeping 1-based line numbers intact.
function tokenizeTestCode(source, { hashComments = false } = {}) {
  const literals = [];
  const addLit = (val, rawSpan) => {
    const id = literals.length;
    literals.push(val);
    return `__STR_${id}__${newlinesIn(rawSpan)}`;
  };

  let out = '';
  let i = 0;
  let prevToken = '';
  const templateStack = [];
  const canStartRegex = () => !prevToken || [
    '(', ',', '=', ':', '[', '!', '&', '|', '?', '{', '}', ';', '+', '-', '*', '%', '<', '>', '^', '~',
    'return', 'throw', 'case', 'in', 'of', 'typeof', 'void', 'delete', 'await', 'yield',
  ].includes(prevToken);

  const consumeTemplateChunk = startIdx => {
    let j = startIdx;
    while (j < source.length && source[j] !== '`') {
      if (source[j] === '\\') { j += 2; continue; }
      if (source[j] === '$' && source[j + 1] === '{') {
        const rawChunk = source.slice(startIdx, j);
        const tok = addLit(decodeSimpleEscapes(rawChunk), rawChunk);
        templateStack.push({ depth: 1 });
        prevToken = '(';
        return { text: `(${tok} + (`, next: j + 2 };
      }
      j++;
    }
    const rawChunk = source.slice(startIdx, j);
    const tok = addLit(decodeSimpleEscapes(rawChunk), rawChunk);
    prevToken = 'str';
    return { text: `${tok})`, next: j < source.length ? j + 1 : j };
  };

  while (i < source.length) {
    const ch = source[i];
    const next = source[i + 1];

    if (ch === '/' && next === '/') {
      const end = source.indexOf('\n', i + 2);
      if (end < 0) break;
      out += '\n';
      i = end + 1;
      continue;
    }
    if (hashComments && ch === '#') {
      const end = source.indexOf('\n', i + 1);
      if (end < 0) break;
      out += '\n';
      i = end + 1;
      continue;
    }
    if (ch === '/' && next === '*') {
      const end = source.indexOf('*/', i + 2);
      const body = end < 0 ? source.slice(i + 2) : source.slice(i + 2, end);
      out += newlinesIn(body);
      i = end < 0 ? source.length : end + 2;
      continue;
    }
    if (ch === "'" || ch === '"') {
      if (hashComments && source.slice(i, i + 3) === ch.repeat(3)) {
        const delim = ch.repeat(3);
        const end = source.indexOf(delim, i + 3);
        const body = end < 0 ? source.slice(i + 3) : source.slice(i + 3, end);
        out += addLit(body, body);
        prevToken = 'str';
        i = end < 0 ? source.length : end + 3;
        continue;
      }
      let j = i + 1;
      while (j < source.length && source[j] !== ch && source[j] !== '\n') {
        if (source[j] === '\\') j += 2;
        else j++;
      }
      const rawBody = source.slice(i + 1, j);
      out += addLit(decodeSimpleEscapes(rawBody), rawBody);
      prevToken = 'str';
      i = j < source.length && source[j] === ch ? j + 1 : j;
      continue;
    }
    if (ch === '`') {
      let j = i + 1;
      let hasInterp = false;
      while (j < source.length && source[j] !== '`') {
        if (source[j] === '\\') { j += 2; continue; }
        if (source[j] === '$' && source[j + 1] === '{') { hasInterp = true; break; }
        j++;
      }
      if (!hasInterp) {
        const rawBody = source.slice(i + 1, j);
        out += addLit(decodeSimpleEscapes(rawBody), rawBody);
        prevToken = 'str';
        i = j < source.length ? j + 1 : j;
      } else {
        const step = consumeTemplateChunk(i + 1);
        out += step.text;
        i = step.next;
      }
      continue;
    }
    if (templateStack.length) {
      if (ch === '{') {
        templateStack.at(-1).depth++;
        out += ch;
        prevToken = '{';
        i++;
        continue;
      }
      if (ch === '}' && --templateStack.at(-1).depth === 0) {
        templateStack.pop();
        out += ') + ';
        const step = consumeTemplateChunk(i + 1);
        out += step.text;
        i = step.next;
        continue;
      }
    }
    if (!hashComments && ch === '/' && next !== '/' && next !== '*' && canStartRegex()) {
      let j = i + 1;
      let inClass = false;
      let closed = false;
      while (j < source.length && source[j] !== '\n') {
        if (source[j] === '\\') { j += 2; continue; }
        if (source[j] === '[') inClass = true;
        else if (source[j] === ']') inClass = false;
        else if (source[j] === '/' && !inClass) { closed = true; j++; break; }
        j++;
      }
      if (closed) {
        while (j < source.length && /[A-Za-z]/.test(source[j])) j++;
        out += source.slice(i, j);
        prevToken = 'regex';
        i = j;
        continue;
      }
    }
    if (/\s/.test(ch)) {
      out += ch;
      i++;
      continue;
    }
    if (/[A-Za-z_$]/.test(ch)) {
      let j = i + 1;
      while (j < source.length && /[A-Za-z0-9_$]/.test(source[j])) j++;
      const word = source.slice(i, j);
      out += word;
      prevToken = word;
      i = j;
      continue;
    }
    out += ch;
    prevToken = ch;
    i++;
  }

  return { skeleton: out, literals };
}

function buildLineStarts(text) {
  const starts = [0];
  for (let i = 0; i < text.length; i++) if (text[i] === '\n') starts.push(i + 1);
  return starts;
}

function lineNumberAt(lineStarts, index) {
  let lo = 0, hi = lineStarts.length - 1;
  while (lo <= hi) {
    const mid = (lo + hi) >> 1;
    if (lineStarts[mid] <= index) lo = mid + 1;
    else hi = mid - 1;
  }
  return lo;
}

function parseCallArgs(skeleton, openParenIdx) {
  let depth = 1;
  let k = openParenIdx + 1;
  let argStart = k;
  const args = [];
  while (k < skeleton.length && depth > 0) {
    const ch = skeleton[k];
    if (ch === '(') depth++;
    else if (ch === ')') {
      depth--;
      if (depth === 0) {
        args.push(skeleton.slice(argStart, k));
        return { args, endIdx: k + 1 };
      }
    } else if (ch === ',' && depth === 1) {
      args.push(skeleton.slice(argStart, k));
      argStart = k + 1;
    }
    k++;
  }
  return null;
}

function normalizeCandidateRepoPath(rawCandidate, testDir) {
  if (!rawCandidate || typeof rawCandidate !== 'string') return null;
  let cleaned = rawCandidate.trim().replace(/^file:\/\//i, '').replace(/\\/g, '/');
  if (!cleaned || /[\r\n\0]/.test(cleaned)) return null;
  if (/(?:^|\/)(?:fixtures|harbor)(?:\/|$)/i.test(cleaned)) return null;

  let normalized;
  if (cleaned.startsWith('./') || cleaned.startsWith('../')) {
    normalized = posix.normalize(posix.join(testDir, cleaned));
  } else {
    const anchored = /(?:^|\/)((?:prompts|src)\/[A-Za-z0-9_./-]+)$/.exec(cleaned);
    normalized = anchored ? posix.normalize(anchored[1]) : posix.normalize(cleaned.replace(/^\/+/, ''));
  }

  if (!normalized || normalized.startsWith('..') || normalized.includes('/../')) return null;
  if (/(?:^|\/)(?:fixtures|harbor)(?:\/|$)/i.test(normalized)) return null;
  if (normalized.endsWith('.prompt.md') || normalized.startsWith('prompts/') || normalized.startsWith('src/')) {
    return normalized;
  }
  return null;
}

function referencesSandbox(expr, sandboxVars, literals) {
  if (/\b(?:tmpdir|mkdtempSync|mkdtemp)\s*\(/.test(expr)) return true;
  if (/\b(?:setup|f|w|ctx|env|fixture|sandbox|run)\s*\.\s*(?:repo|root|cwd|dir|worktree|mergeCheckout|primary|home|state)\b/.test(expr)) return true;
  for (const match of expr.matchAll(/__STR_(\d+)__/g)) {
    const val = literals?.[Number(match[1])] ?? '';
    if (/(?:^|\/)(?:fixtures|harbor)(?:\/|$)/i.test(val)) return true;
  }
  for (const match of expr.matchAll(/\b([A-Za-z_$][\w$]*)\b/g)) {
    const id = match[1];
    if (sandboxVars.has(id)) return true;
  }
  return false;
}

const IGNORED_PATH_HELPER_IDS = new Set([
  'join', 'resolve', 'posix', 'path', 'URL', 'new', 'fileURLToPath', 'import', 'meta', 'url', 'dirname',
  'process', 'cwd', 'root', 'packageRoot', 'repoRoot', 'String',
]);

function resolveTargetPath(argExpr, testDir, literals, pathVars, sandboxVars) {
  if (!argExpr || referencesSandbox(argExpr, sandboxVars, literals)) return null;

  const parts = [];
  const tokenRe = /__STR_(\d+)__|\b([A-Za-z_$][\w$]*)\b/g;
  for (const m of argExpr.matchAll(tokenRe)) {
    if (m[1] !== undefined) {
      const val = literals[Number(m[1])];
      if (typeof val === 'string' && !/^(?:utf-?8|ascii|latin1|r|rb)$/i.test(val)) {
        if (val.length > 0) parts.push({ kind: 'lit', val });
      }
    } else if (m[2]) {
      const id = m[2];
      if (pathVars.has(id)) parts.push({ kind: 'lit', val: pathVars.get(id) });
      else if (!IGNORED_PATH_HELPER_IDS.has(id)) parts.push({ kind: 'dyn', val: '*' });
    }
  }
  const litParts = parts.filter(p => p.kind === 'lit');
  if (!litParts.length) return null;

  const collapsed = [];
  for (const p of parts) {
    if (p.kind === 'dyn' && collapsed.at(-1)?.kind === 'dyn') continue;
    collapsed.push(p);
  }
  while (collapsed[0]?.kind === 'dyn') collapsed.shift();
  while (collapsed.at(-1)?.kind === 'dyn') collapsed.pop();
  if (!collapsed.length) return null;

  const isImportMetaRel = /\bimport\.meta\.(?:url|dirname)\b/.test(argExpr) && collapsed.length === 1 && !collapsed[0].val.startsWith('.');
  let joined = '';
  for (let idx = 0; idx < collapsed.length; idx++) {
    const cur = collapsed[idx];
    if (idx === 0) {
      joined = isImportMetaRel ? `./${cur.val}` : cur.val;
      continue;
    }
    const prev = collapsed[idx - 1];
    if (cur.kind === 'dyn' || prev.kind === 'dyn') {
      joined = `${joined}${cur.val}`;
    } else if (joined.endsWith('/') || cur.val.startsWith('/')) {
      joined = `${joined}${cur.val}`;
    } else {
      joined = `${joined}/${cur.val}`;
    }
  }

  return normalizeCandidateRepoPath(joined, testDir);
}

export function isInspectableTestCodePath(path) {
  return isTestOwnedPath(path)
    && TEST_CODE_EXT.test(path)
    && !SKIP_TEST_SUBDIR.test(path)
    && !SEAM_TEST_FILE.test(path);
}

function collectFakeTestWarnings(text, { path = 'test/example.test.mjs' } = {}) {
  if (!canonicalRepoPath(path) || SKIP_TEST_SUBDIR.test(path) || SEAM_TEST_FILE.test(path) || !TEST_CODE_EXT.test(path)) {
    return [];
  }
  const hashComments = /\.(?:py|rb)$/i.test(path);
  const testDir = posix.dirname(path) === '.' ? '' : posix.dirname(path);
  const { skeleton, literals } = tokenizeTestCode(String(text ?? ''), { hashComments });
  const lineStarts = buildLineStarts(skeleton);

  const sandboxVars = new Set(['harborDir', 'fixturesDir', 'fixtureDir']);
  for (const cb of skeleton.matchAll(/\bharbor\s*\([^,)]+,\s*(?:async\s+)?\(?([A-Za-z_$][\w$]*)\)?\s*=>/g)) {
    sandboxVars.add(cb[1]);
  }
  const sandboxInitRe = /(?:\b(?:const|let|var)\s+|,\s*)(?:\{([^}]+)\}|([A-Za-z_$][\w$]*))\s*=\s*(?:await\s+)?(?:[A-Za-z_$][\w$.]*\s*\(\s*)*(?:mkdtempSync|mkdtemp|temp|harbor|fixture|nativeFixture|layoutFixture|makeRepo|createTempRepo|setupRepo|fix2World)\s*\(/g;
  for (const m of skeleton.matchAll(sandboxInitRe)) {
    if (m[2]) sandboxVars.add(m[2]);
    else if (m[1]) {
      for (const part of m[1].split(',')) {
        const name = part.split(':').pop().split('=')[0].trim();
        if (/^[A-Za-z_$][\w$]*$/.test(name)) sandboxVars.add(name);
      }
    }
  }
  // Extract individual ident = rhs assignments across multi-declarator statements (respecting paren depth).
  const assignments = [];
  const assignHeadRe = /(?:\b(?:const|let|var)\s+|,\s*)([A-Za-z_$][\w$]*)\s*=\s*(?!=)/g;
  for (const m of skeleton.matchAll(assignHeadRe)) {
    const ident = m[1];
    let k = m.index + m[0].length;
    let depth = 0;
    while (k < skeleton.length) {
      const ch = skeleton[k];
      if (ch === '(' || ch === '[' || ch === '{') depth++;
      else if (ch === ')' || ch === ']' || ch === '}') {
        if (depth === 0) break;
        depth--;
      } else if (depth === 0 && (ch === ',' || ch === ';' || ch === '\n')) {
        break;
      }
      k++;
    }
    assignments.push([ident, skeleton.slice(m.index + m[0].length, k)]);
  }
  for (let pass = 0; pass < 4; pass++) {
    for (const [ident, rhs] of assignments) {
      if (!sandboxVars.has(ident) && referencesSandbox(rhs, sandboxVars, literals)) sandboxVars.add(ident);
    }
  }

  const pathVars = new Map();
  for (let pass = 0; pass < 2; pass++) {
    for (const [ident, rhs] of assignments) {
      if (sandboxVars.has(ident) || pathVars.has(ident)) continue;
      if (/\b(?:readFileSync|readFile|existsSync|statSync|lstatSync)\b/.test(rhs)) continue;
      if (/^\s*[\[{]/.test(rhs) || /[\]}]/.test(rhs)) continue;
      const resolved = resolveTargetPath(rhs, testDir, literals, pathVars, sandboxVars);
      if (resolved) pathVars.set(ident, resolved);
    }
  }

  const findings = [];
  const sourceTextVars = new Map();
  const callRe = /(?:^|[^\w$])(?:(?:fs|fsPromises|promises)\s*\.\s*)?(readFileSync|readFile|existsSync|statSync|lstatSync|accessSync)\s*\(/g;

  for (const match of skeleton.matchAll(callRe)) {
    const fnName = match[1];
    const fnOffset = match.index + match[0].lastIndexOf(fnName);
    const openParenIdx = skeleton.indexOf('(', fnOffset + fnName.length);
    if (openParenIdx < 0) continue;
    const parsed = parseCallArgs(skeleton, openParenIdx);
    if (!parsed || !parsed.args.length) continue;

    const target = resolveTargetPath(parsed.args[0], testDir, literals, pathVars, sandboxVars);
    if (!target) continue;
    const callLine = lineNumberAt(lineStarts, fnOffset);

    if (fnName === 'existsSync' || fnName === 'statSync' || fnName === 'lstatSync' || fnName === 'accessSync') {
      if (target.startsWith('prompts/') || target.startsWith('src/')) {
        findings.push({
          line: callLine,
          order: 1,
          target,
          warning: `Warning: fake test: ${path}:${callLine} [fake-test-exists-check] Test checks file existence on "${target}" instead of exercising behavior. Import the module or run the CLI command and assert its observable output.`,
        });
      }
      continue;
    }

    if (target.endsWith('.prompt.md')) {
      findings.push({
        line: callLine,
        order: 0,
        target,
        warning: `Warning: fake test: ${path}:${callLine} [fake-test-prompt-read] Test reads prompt file "${target}" directly. Call exported module functions or CLI commands to verify observable behavior instead of asserting on prompt prose.`,
      });
      continue;
    }

    if (SRC_CODE_PATH.test(target)) {
      const before = skeleton.slice(Math.max(0, match.index - 120), match.index + 1);
      const after = skeleton.slice(parsed.endIdx, Math.min(skeleton.length, parsed.endIdx + 160));
      const inlineChained = /^\s*\.\s*(?:includes|match|matchAll|search|indexOf|startsWith|endsWith)\s*\(/.test(after);
      const inlineWrapped = /(?:\.test|\bassert\s*\.\s*(?:match|doesNotMatch)|\bexpect)\s*\(\s*(?:await\s+)?$/.test(before);
      if (inlineChained || inlineWrapped) {
        findings.push({
          line: callLine,
          order: 2,
          target,
          warning: `Warning: fake test: ${path}:${callLine} [fake-test-source-match] Test reads "${target}" as text and matches source strings instead of testing behavior. Import "${target}" (or run the CLI) and assert outputs, state changes or exit codes.`,
        });
      } else {
        const assignMatch = /(?:const|let|var)\s+([A-Za-z_$][\w$]*)\s*=\s*(?:await\s+)?$/.exec(before);
        if (assignMatch && !sourceTextVars.has(assignMatch[1])) {
          sourceTextVars.set(assignMatch[1], { target, afterIdx: parsed.endIdx });
        }
      }
    }
  }

  for (const [ident, { target, afterIdx }] of sourceTextVars.entries()) {
    const rest = skeleton.slice(afterIdx);
    const escapedIdent = ident.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const assertPatterns = [
      new RegExp(`\\b${escapedIdent}\\s*\\.\\s*(?:includes|match|matchAll|search|indexOf|startsWith|endsWith)\\s*\\(`),
      new RegExp(`\\.test\\s*\\(\\s*${escapedIdent}\\b`),
      new RegExp(`\\bassert\\s*\\.\\s*(?:match|doesNotMatch)\\s*\\(\\s*${escapedIdent}\\b`),
      new RegExp(`\\bexpect\\s*\\(\\s*${escapedIdent}\\s*\\)\\s*\\.(?:not\\s*\\.)?(?:toMatch|toContain)\\s*\\(`),
    ];
    let earliestOffset = null;
    for (const re of assertPatterns) {
      const m = re.exec(rest);
      if (m && (earliestOffset === null || m.index < earliestOffset)) {
        earliestOffset = m.index;
      }
    }
    if (earliestOffset !== null) {
      const matchLine = lineNumberAt(lineStarts, afterIdx + earliestOffset);
      findings.push({
        line: matchLine,
        order: 2,
        target,
        warning: `Warning: fake test: ${path}:${matchLine} [fake-test-source-match] Test reads "${target}" as text and matches source strings instead of testing behavior. Import "${target}" (or run the CLI) and assert outputs, state changes or exit codes.`,
      });
    }
  }

  findings.sort((a, b) => a.line - b.line || a.order - b.order);
  const seen = new Set();
  return findings.filter(item => {
    if (seen.has(item.warning)) return false;
    seen.add(item.warning);
    return true;
  });
}

export function lintFakeTests(text, { path = 'test/example.test.mjs' } = {}) {
  return collectFakeTestWarnings(text, { path }).map(item => item.warning);
}

function scenarioPromptRefs(doc) {
  if (!doc || typeof doc !== 'object') return [];
  const refs = [];
  if (Array.isArray(doc.entry_paths)) {
    for (const p of doc.entry_paths) if (typeof p === 'string') refs.push(p.replace(/^\.\//, ''));
  }
  if (Array.isArray(doc.steps)) {
    for (const step of doc.steps) {
      if (typeof step?.entry_path === 'string') refs.push(step.entry_path.replace(/^\.\//, ''));
    }
  }
  if (Array.isArray(doc.context)) {
    for (const item of doc.context) {
      if (typeof item === 'string') refs.push(item.replace(/^\.\//, ''));
      else if (typeof item?.prompt_path === 'string') refs.push(item.prompt_path.replace(/^\.\//, ''));
    }
  }
  return refs;
}

export function lintRepoAntiPatterns({ root, files, promptPaths, tests } = {}) {
  if (!root || typeof root !== 'string') return [];
  let realRoot, policy;
  try {
    realRoot = realpathSync(root);
    policy = workspace.policy({ root });
  } catch {
    return [];
  }

  let rawFiles;
  try {
    rawFiles = Array.isArray(files) ? files : gitFiles(root);
  } catch {
    return [];
  }

  const allowedFiles = [...new Set(rawFiles)]
    .filter(path => canonicalRepoPath(path) && !isSecretPath(path) && workspace.allows(policy, path))
    .sort();

  const selectedInputs = [
    ...(Array.isArray(promptPaths) ? promptPaths : []).filter(p => typeof p === 'string').map(p => p.replace(/^\.\//, '')),
    ...(Array.isArray(tests) ? tests : []).map(t => (typeof t === 'string' ? t : t?.path)).filter(p => typeof p === 'string').map(p => p.replace(/^\.\//, '')),
  ];
  const allowFixtures = selectedInputs.some(p => FIXTURE_DIR.test(p));
  const scopedFiles = allowFixtures ? allowedFiles : allowedFiles.filter(p => !FIXTURE_DIR.test(p));
  const scopedSet = new Set(scopedFiles);

  const records = [];
  const addRecord = (filePath, line, warning) => records.push({ filePath, line, warning });

  // 1. Prompt code fences and imperative code blocks
  const targetPrompts = Array.isArray(promptPaths)
    ? [...new Set(promptPaths.filter(p => typeof p === 'string').map(p => p.replace(/^\.\//, '')).filter(p => scopedSet.has(p) && p.endsWith('.prompt.md')))].sort()
    : scopedFiles.filter(p => p.endsWith('.prompt.md'));

  for (const promptPath of targetPrompts) {
    const content = readSafeUtf8(realRoot, promptPath);
    if (typeof content !== 'string') continue;
    for (const warning of lintPromptCodeBlocks(content, { path: promptPath })) {
      const lineMatch = /:(\d+)\s+\[/.exec(warning);
      addRecord(promptPath, lineMatch ? Number(lineMatch[1]) : 1, warning);
    }
  }

  // 2. Story criteria and quality hygiene
  let targetStories = [];
  if (promptPaths === undefined && tests === undefined) {
    targetStories = scopedFiles.filter(isLintableStoryPath);
  } else {
    const storyCandidates = new Set();
    if (Array.isArray(tests)) {
      for (const entry of tests) {
        if (entry && typeof entry === 'object' && typeof entry.storyPath === 'string') {
          storyCandidates.add(entry.storyPath.replace(/^\.\//, ''));
        }
        const tPath = typeof entry === 'string' ? entry.replace(/^\.\//, '') : entry?.path?.replace(/^\.\//, '');
        if (tPath && scopedSet.has(tPath) && tPath.endsWith('.json')) {
          const raw = readSafeUtf8(realRoot, tPath);
          if (raw) {
            try {
              const doc = JSON.parse(raw);
              if (typeof doc?.story_path === 'string') storyCandidates.add(doc.story_path.replace(/^\.\//, ''));
            } catch {}
          }
        }
      }
    } else if (Array.isArray(promptPaths) && targetPrompts.length > 0) {
      const promptSet = new Set(targetPrompts);
      for (const scenarioPath of scopedFiles.filter(p => /^(?:tests?|__tests__)\/.*\.json$/i.test(p))) {
        const raw = readSafeUtf8(realRoot, scenarioPath);
        if (!raw) continue;
        try {
          const doc = JSON.parse(raw);
          if (typeof doc?.story_path === 'string' && scenarioPromptRefs(doc).some(ref => promptSet.has(ref))) {
            storyCandidates.add(doc.story_path.replace(/^\.\//, ''));
          }
        } catch {}
      }
    }
    targetStories = [...storyCandidates].filter(p => scopedSet.has(p) && isLintableStoryPath(p)).sort();
  }

  for (const storyPath of targetStories) {
    const content = readSafeUtf8(realRoot, storyPath);
    if (typeof content !== 'string') continue;
    const res = lintStory(content, { path: storyPath, criteriaHygiene: true });
    for (const problem of res.problems) {
      addRecord(
        storyPath,
        problem.line,
        `Warning: Story hygiene: ${problem.path}:${problem.line} [${problem.code}] ${problem.message}`,
      );
    }
  }

  // 3. Fake source-matching / prompt-reading / file-existence tests
  const promptFilterSet = Array.isArray(promptPaths) ? new Set(targetPrompts) : null;
  if (!promptFilterSet || promptFilterSet.size > 0) {
    for (const testPath of scopedFiles.filter(isInspectableTestCodePath)) {
      const content = readSafeUtf8(realRoot, testPath);
      if (typeof content !== 'string') continue;
      for (const item of collectFakeTestWarnings(content, { path: testPath })) {
        if (promptFilterSet && !promptFilterSet.has(item.target)) continue;
        addRecord(testPath, item.line, item.warning);
      }
    }
  }

  records.sort((a, b) => a.filePath.localeCompare(b.filePath) || a.line - b.line || a.warning.localeCompare(b.warning));
  return [...new Set(records.map(r => r.warning))];
}
