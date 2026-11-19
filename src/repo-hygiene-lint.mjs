// Generated from prompts/cli/repo-hygiene-lint.prompt.md.
import { closeSync, constants, fstatSync, lstatSync, openSync, readdirSync, readSync, realpathSync } from 'node:fs';
import { isAbsolute, join, posix } from 'node:path';
import { detectRealE2eKindsInTest, inspectTestBoundaryTargets, lintValidationCode } from './autopilot-validator.mjs';
import { isTestOwnedPath, resolveOwners } from './file-owner.mjs';
import { isLintableStoryPath, lintStory } from './story-lint.mjs';
import { gitFiles, isSecretPath, workspace } from './runtime-seam.mjs';

const MAX_FILE_BYTES = 2 * 1024 * 1024;
const HEAD_BYTES = 4096;
const PROMPT_FENCE_LINE_LIMIT = 15;
const PROMPT_FENCE_TOTAL_LIMIT = 30;
const DIAGRAM_MIN_PROSE_LINES = 18;
const DIAGRAM_MIN_BRANCH_LINES = 5;
const CODE_FILE_EXT = /\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|cs|swift|c|cc|cpp|h|hpp|php|scala|lua|sh)$/i;
const TEST_CODE_EXT = /\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|cs|swift)$/i;
const SRC_CODE_PATH = /^src\/.+\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|cs|swift)$/i;
const SEAM_TEST_FILE = /(?:^|\/)[^/]*seam\.test\.[A-Za-z0-9]+$/i;
const SKIP_TEST_SUBDIR = /(?:^|\/)(?:fixtures|helpers)\//i;
const FIXTURE_DIR = /(?:^|\/)fixtures(?:\/|$)/i;
const EXAMPLE_DIR = /(?:^|\/)examples(?:\/|$)/i;
const NON_CODE_DIR = /^(?:user_stories|docs?|\.github)\//i;
const RULE_ID_RE = /^[A-Za-z0-9][A-Za-z0-9_.-]{0,63}$/;
const PRIVATE_MODULE_SEGMENT_RE = /(?:^|\/|\.)(?:internal|_internal|private|_private|impl|_impl)(?:\/|\.|$)/i;
const PRIVATE_MODULE_BASENAME_RE = /(?:^|\/)_[A-Za-z0-9][\w.-]*$/;
const DUNDER_BASENAME_RE = /(?:^|\/)__[A-Za-z0-9_]+__(?:\.[A-Za-z0-9]+)?$/;
const PRIVATE_SYMBOL_RE = /^_[A-Za-z0-9][\w$]*$/;

const IMPERATIVE_PATTERNS = [
  /(?<![\w$-])(?:export|const|let|def|impl)\s+/,
  /(?<![\w$-])function(?:\s+[A-Za-z_$]|\s*\(|\*)/,
  /(?<![\w$-])(?:if|for|while)\s*\(/,
  /(?<![\w$-])return(?:\s+|;|$)/,
  /(?<![\w$-])try\s*\{/,
  /=>/,
];

const TEST_FRAMEWORK_PACKAGES = new Set([
  'vitest', 'jest', '@jest/globals', 'mocha', 'chai', 'sinon', 'ava', 'tap', 'uvu',
  'playwright', '@playwright/test', 'pytest', 'unittest',
]);

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

function hasRuntimeInterfaceMetadata(raw) {
  const text = String(raw ?? '');
  return /<details\b[^>]*>\s*<summary\b[^>]*>[^\r\n]*runtime\s+interface[^\r\n]*<\/summary>[\s\S]*?<\/details>/i.test(text)
    || /^#{2,6}[ \t]+runtime[ \t]+interface[ \t]*\r?\n/im.test(text);
}

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

export function stripPromptMetadata(raw) {
  let text = String(raw ?? '');
  text = text.replace(/^---\r?\n[\s\S]*?\r?\n---(?:\r?\n|$)/, '');
  text = text.replace(
    /<details\b[^>]*>\s*<summary\b[^>]*>[^\r\n]*runtime\s+interface[^\r\n]*<\/summary>[\s\S]*?<\/details>/gi,
    '',
  );
  text = text.replace(
    /^#{2,6}[ \t]+runtime[ \t]+interface[ \t]*\r?\n[\s\S]*?(?=^#{1,6}[ \t]+\S|\s*$)/gim,
    '',
  );
  return text;
}

function countPromptProseLines(raw) {
  const cleaned = stripPromptMetadata(raw).replace(/\s+$/, '');
  return cleaned ? cleaned.split(/\r?\n/).length : 0;
}

function countFileLines(raw) {
  const text = String(raw ?? '').replace(/\r?\n$/, '');
  return text ? text.split(/\r?\n/).length : 0;
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

function scanMarkdownLinesAndFences(cleanedText) {
  const lines = cleanedText.split(/\r?\n/);
  const fences = [];
  const proseLines = [];
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
      continue;
    }

    proseLines.push({ lineNo, text: line });
  }
  if (activeFence) fences.push(activeFence);
  return { fences, proseLines };
}

function collectPromptCodeBlockFindings(text, { path = 'prompts/module.prompt.md' } = {}) {
  const cleaned = stripPromptMetadataPreservingLines(text);
  const { fences } = scanMarkdownLinesAndFences(cleaned);
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
        code: 'prompt-code-fence-length',
        category: 'prompt code block',
        detail: `Non-mermaid code fence spans ${count} lines (recommended <= ${PROMPT_FENCE_LINE_LIMIT}). Replace long code or schema blocks with plain-English rules, a Markdown table, or a mermaid diagram.`,
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
            code: 'prompt-imperative-code',
            category: 'prompt code block',
            detail: `Fenced block contains imperative code ("${token}"). Describe observable inputs, outputs and failure rules in prose instead of embedding code in prompts.`,
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
      code: 'prompt-code-fence-total',
      category: 'prompt code block',
      detail: `Prompt contains ${totalBodyLines} non-mermaid fenced lines across ${nonMermaid.length} blocks (recommended <= ${PROMPT_FENCE_TOTAL_LIMIT} total). Move implementation details to tests or summarize contracts in prose and tables.`,
    });
  }

  records.sort((a, b) => a.line - b.line || a.order - b.order);
  return records.map(r => ({
    ...r,
    filePath: path,
    warning: `Warning: ${r.category}: ${path}:${r.line} [${r.code}] ${r.detail}`,
  }));
}

export function lintPromptCodeBlocks(text, { path = 'prompts/module.prompt.md' } = {}) {
  return collectPromptCodeBlockFindings(text, { path }).map(r => r.warning);
}

function collectPromptSizeFindings(promptText, codeFiles, { path = 'prompts/module.prompt.md' } = {}) {
  const rawList = Array.isArray(codeFiles) ? codeFiles : (codeFiles !== undefined && codeFiles !== null ? [codeFiles] : []);
  const entries = rawList
    .map(item => (typeof item === 'string' ? { path: '', text: item } : item))
    .filter(item => item && typeof item.text === 'string');
  if (!entries.length) return [];

  const promptLines = countPromptProseLines(promptText);
  const codeLines = entries.reduce((sum, item) => sum + countFileLines(item.text), 0);
  if (promptLines < codeLines) return [];

  const targetPaths = entries.map(item => item.path).filter(Boolean).join(', ') || 'owned code';
  const detail = `Prompt spans ${promptLines} lines while generated code (${targetPaths}) spans ${codeLines} lines. Keep prompt lines strictly smaller than generated code lines (< ${codeLines}) by stating domain decisions concisely instead of implementation detail.`;
  return [{
    filePath: path,
    line: 1,
    order: 0,
    code: 'prompt-larger-than-code',
    category: 'prompt size',
    detail,
    warning: `Warning: prompt size: ${path}:1 [prompt-larger-than-code] ${detail}`,
  }];
}

export function lintPromptSize(promptText, codeFiles, { path = 'prompts/module.prompt.md' } = {}) {
  return collectPromptSizeFindings(promptText, codeFiles, { path }).map(r => r.warning);
}

function collectPromptStructureFindings(text, { path = 'prompts/module.prompt.md', hasOwnedCode = false } = {}) {
  const raw = String(text ?? '');
  const hasRuntimeInterface = hasRuntimeInterfaceMetadata(raw);
  const cleaned = stripPromptMetadataPreservingLines(raw);
  const { fences, proseLines } = scanMarkdownLinesAndFences(cleaned);

  let hasTitle = false;
  let hasDependenciesHeading = false;
  let nonAppearanceH2Count = 0;
  let hasPeerPromptLink = false;
  let hasSvgDrawing = false;
  let hasMarkdownTable = false;
  let nonEmptyProseCount = 0;
  const branchLines = [];
  const stateTransitionLines = [];

  for (let idx = 0; idx < proseLines.length; idx++) {
    const { lineNo, text: line } = proseLines[idx];
    const trimmed = line.trim();
    if (!trimmed) continue;

    if (/^ {0,3}#\s+\S/.test(line)) {
      hasTitle = true;
      continue;
    }

    const h2 = /^ {0,3}##\s+(.+)$/.exec(line);
    if (h2) {
      const headingTitle = h2[1].trim();
      if (/^dependencies\b/i.test(headingTitle)) hasDependenciesHeading = true;
      else if (!/^appearance\b/i.test(headingTitle)) nonAppearanceH2Count++;
      continue;
    }

    if (/^ {0,3}#{3,6}\s+/.test(line)) continue;

    nonEmptyProseCount++;
    if (/\]\([^)\s]*\.prompt\.md(?:#[^)\s]*)?\)/i.test(line)) hasPeerPromptLink = true;
    if (/!\[[^\]]*\]\([^)\s]*\.ui\.svg[^)\s]*\)/i.test(line)) hasSvgDrawing = true;

    if (line.includes('|') && idx + 1 < proseLines.length) {
      const nextTrimmed = proseLines[idx + 1].text.trim();
      if (/^\|?\s*:?-{2,}:?\s*(?:\|\s*:?-{2,}:?\s*)+\|?$/.test(nextTrimmed)) {
        hasMarkdownTable = true;
      }
    }

    if (/\b(?:if|when|whenever|unless|otherwise)\b/i.test(trimmed)) {
      branchLines.push(lineNo);
    }
    if (/\b(?:transitions?\s+(?:from|to)|moves?\s+from\s+\S+\s+to\s+\S+|state\s+machine)\b/i.test(trimmed)) {
      stateTransitionLines.push(lineNo);
    }
  }

  const hasMermaidFence = fences.some(f => f.lang === 'mermaid');
  const findings = [];

  if (!hasTitle) {
    const detail = 'Prompt has no top-level "# <Title>" heading. Start every prompt with "# <Title>" and a plain-English opening sentence.';
    findings.push({
      filePath: path,
      line: 1,
      order: 0,
      code: 'prompt-missing-title',
      category: 'prompt structure',
      detail,
      warning: `Warning: prompt structure: ${path}:1 [prompt-missing-title] ${detail}`,
    });
  }

  if (!hasDependenciesHeading && (hasOwnedCode || hasRuntimeInterface || hasPeerPromptLink || nonAppearanceH2Count >= 2)) {
    const detail = 'Prompt has no "## Dependencies" section. Add "## Dependencies" listing peer prompt links (or "None." when standalone).';
    findings.push({
      filePath: path,
      line: 1,
      order: 1,
      code: 'prompt-missing-dependencies',
      category: 'prompt structure',
      detail,
      warning: `Warning: prompt structure: ${path}:1 [prompt-missing-dependencies] ${detail}`,
    });
  }

  if (
    !hasMermaidFence
    && !hasSvgDrawing
    && !hasMarkdownTable
    && ((nonEmptyProseCount >= DIAGRAM_MIN_PROSE_LINES && branchLines.length >= DIAGRAM_MIN_BRANCH_LINES) || stateTransitionLines.length >= 3)
  ) {
    const lineNo = stateTransitionLines[0] ?? branchLines[0] ?? 1;
    const detail = 'Prompt describes multi-branch or state-transition rules without a diagram or decision table. Add a ```mermaid``` diagram or Markdown table where applicable.';
    findings.push({
      filePath: path,
      line: lineNo,
      order: 2,
      code: 'prompt-missing-diagram',
      category: 'prompt structure',
      detail,
      warning: `Warning: prompt structure: ${path}:${lineNo} [prompt-missing-diagram] ${detail}`,
    });
  }

  findings.sort((a, b) => a.line - b.line || a.order - b.order);
  return findings;
}

export function lintPromptStructure(text, { path = 'prompts/module.prompt.md', hasOwnedCode = false } = {}) {
  return collectPromptStructureFindings(text, { path, hasOwnedCode }).map(r => r.warning);
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
        const detail = `Test checks file existence on "${target}" instead of exercising behavior. Import the module or run the CLI command and assert its observable output.`;
        findings.push({
          filePath: path,
          line: callLine,
          order: 1,
          code: 'fake-test-exists-check',
          category: 'fake test',
          target,
          detail,
          warning: `Warning: fake test: ${path}:${callLine} [fake-test-exists-check] ${detail}`,
        });
      }
      continue;
    }

    if (target.endsWith('.prompt.md')) {
      const detail = `Test reads prompt file "${target}" directly. Call exported module functions or CLI commands to verify observable behavior instead of asserting on prompt prose.`;
      findings.push({
        filePath: path,
        line: callLine,
        order: 0,
        code: 'fake-test-prompt-read',
        category: 'fake test',
        target,
        detail,
        warning: `Warning: fake test: ${path}:${callLine} [fake-test-prompt-read] ${detail}`,
      });
      continue;
    }

    if (SRC_CODE_PATH.test(target)) {
      const before = skeleton.slice(Math.max(0, match.index - 120), match.index + 1);
      const after = skeleton.slice(parsed.endIdx, Math.min(skeleton.length, parsed.endIdx + 160));
      const inlineChained = /^\s*\.\s*(?:includes|match|matchAll|search|indexOf|startsWith|endsWith)\s*\(/.test(after);
      const inlineWrapped = /(?:\.test|\bassert\s*\.\s*(?:match|doesNotMatch)|\bexpect)\s*\(\s*(?:await\s+)?$/.test(before);
      if (inlineChained || inlineWrapped) {
        const detail = `Test reads "${target}" as text and matches source strings instead of testing behavior. Import "${target}" (or run the CLI) and assert outputs, state changes or exit codes.`;
        findings.push({
          filePath: path,
          line: callLine,
          order: 2,
          code: 'fake-test-source-match',
          category: 'fake test',
          target,
          detail,
          warning: `Warning: fake test: ${path}:${callLine} [fake-test-source-match] ${detail}`,
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
      const detail = `Test reads "${target}" as text and matches source strings instead of testing behavior. Import "${target}" (or run the CLI) and assert outputs, state changes or exit codes.`;
      findings.push({
        filePath: path,
        line: matchLine,
        order: 2,
        code: 'fake-test-source-match',
        category: 'fake test',
        target,
        detail,
        warning: `Warning: fake test: ${path}:${matchLine} [fake-test-source-match] ${detail}`,
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

function isTestOrBuiltinSpecifier(spec, testDir) {
  if (!spec || typeof spec !== 'string') return true;
  const clean = spec.trim().split('?')[0].split('#')[0];
  if (!clean || clean.startsWith('node:') || TEST_FRAMEWORK_PACKAGES.has(clean)) return true;
  if (clean.startsWith('./') || clean.startsWith('../')) {
    const resolved = posix.normalize(posix.join(testDir, clean));
    if (
      /^(?:tests?|__tests__|fixtures|helpers)\//i.test(resolved)
      || /(?:^|\/)(?:fixtures|helpers|harbor)\//i.test(resolved)
      || isTestOwnedPath(resolved)
    ) {
      return true;
    }
    return false;
  }
  if (/^(?:tests?|__tests__|fixtures|helpers)(?:\/|\.|$)/i.test(clean)) return true;
  return false;
}

function resolveProductionModuleTarget(spec, testDir) {
  if (!spec || typeof spec !== 'string') return null;
  const clean = spec.trim().split('?')[0].split('#')[0];
  if (clean.startsWith('./') || clean.startsWith('../')) {
    const resolved = posix.normalize(posix.join(testDir, clean));
    if (resolved && !resolved.startsWith('..') && !resolved.includes('/../')) return resolved;
  }
  return null;
}

function isPrivateModuleSpecifier(spec) {
  const clean = spec.trim().split('?')[0].split('#')[0];
  if (PRIVATE_MODULE_SEGMENT_RE.test(clean)) return true;
  const slashPath = clean.replace(/\\/g, '/');
  if (!DUNDER_BASENAME_RE.test(slashPath) && PRIVATE_MODULE_BASENAME_RE.test(slashPath)) return true;
  if (!slashPath.includes('/') && clean.includes('.')) {
    const segments = clean.split('.');
    if (segments.some(seg => PRIVATE_SYMBOL_RE.test(seg) && !/^__.*__$/.test(seg))) return true;
  }
  return false;
}

function parseBindingClause(clause) {
  const importedSymbols = [];
  const localBindings = [];
  const trimmed = clause.trim().replace(/^type\s+/, '');
  if (!trimmed) return { importedSymbols, localBindings };

  const nsMatch = /\*\s+as\s+([A-Za-z_$][\w$]*)/.exec(trimmed);
  if (nsMatch) localBindings.push(nsMatch[1]);

  const braceStart = trimmed.indexOf('{');
  const braceEnd = trimmed.lastIndexOf('}');
  if (braceStart >= 0 && braceEnd > braceStart) {
    const before = trimmed.slice(0, braceStart).replace(/,\s*$/, '').trim();
    if (before && /^[A-Za-z_$][\w$]*$/.test(before)) {
      localBindings.push(before);
    }
    const inner = trimmed.slice(braceStart + 1, braceEnd);
    for (const part of inner.split(',')) {
      const piece = part.trim().replace(/^type\s+/, '');
      if (!piece) continue;
      const asMatch = /^([A-Za-z_$][\w$]*)\s+(?:as|:)\s+([A-Za-z_$][\w$]*)(?:\s*=.*)?$/.exec(piece);
      if (asMatch) {
        importedSymbols.push(asMatch[1]);
        localBindings.push(asMatch[2]);
      } else {
        const simple = /^([A-Za-z_$][\w$]*)(?:\s*=.*)?$/.exec(piece);
        if (simple) {
          importedSymbols.push(simple[1]);
          localBindings.push(simple[1]);
        }
      }
    }
  } else if (!nsMatch && /^[A-Za-z_$][\w$]*$/.test(trimmed)) {
    localBindings.push(trimmed);
  }
  return { importedSymbols, localBindings };
}

function collectPublicInterfaceTestWarnings(text, { path = 'test/example.test.mjs' } = {}) {
  if (!canonicalRepoPath(path) || SKIP_TEST_SUBDIR.test(path) || SEAM_TEST_FILE.test(path) || !TEST_CODE_EXT.test(path)) {
    return [];
  }
  const isPython = /\.py$/i.test(path);
  const hashComments = /\.(?:py|rb)$/i.test(path);
  const testDir = posix.dirname(path) === '.' ? '' : posix.dirname(path);
  const { skeleton, literals } = tokenizeTestCode(String(text ?? ''), { hashComments });
  const lineStarts = buildLineStarts(skeleton);

  const findings = [];
  const prodBindings = new Map(); // localIdent -> resolved target path | null

  const recordImport = (spec, clause, offset) => {
    if (!spec || isTestOrBuiltinSpecifier(spec, testDir)) return;
    const line = lineNumberAt(lineStarts, offset);
    const target = resolveProductionModuleTarget(spec, testDir);

    if (isPrivateModuleSpecifier(spec)) {
      const detail = `Test imports private module path "${spec}". Import only the module's public entry interface so internal refactors do not break tests.`;
      findings.push({
        filePath: path,
        line,
        order: 0,
        code: 'test-private-import',
        category: 'public-interface test',
        target,
        detail,
        warning: `Warning: public-interface test: ${path}:${line} [test-private-import] ${detail}`,
      });
    }

    if (clause) {
      const { importedSymbols, localBindings } = parseBindingClause(clause);
      for (const sym of importedSymbols) {
        if (PRIVATE_SYMBOL_RE.test(sym) && !/^__.*__$/.test(sym)) {
          const detail = `Test imports private internal symbol "${sym}" from "${spec}". Test observable behavior through public exports instead of private helpers.`;
          findings.push({
            filePath: path,
            line,
            order: 1,
            code: 'test-private-import',
            category: 'public-interface test',
            target,
            detail,
            warning: `Warning: public-interface test: ${path}:${line} [test-private-import] ${detail}`,
          });
        }
      }
      for (const local of localBindings) {
        if (!prodBindings.has(local)) prodBindings.set(local, target);
      }
    }
  };

  // 1. Static ESM imports: import ... from 'spec'
  for (const m of skeleton.matchAll(/\bimport\s+([\s\S]*?)\s+from\s+__STR_(\d+)__/g)) {
    const spec = literals[Number(m[2])];
    recordImport(spec, m[1], m.index);
  }
  // Bare side-effect imports: import 'spec'
  for (const m of skeleton.matchAll(/\bimport\s+__STR_(\d+)__/g)) {
    const spec = literals[Number(m[1])];
    recordImport(spec, '', m.index);
  }
  // Assigned dynamic import / require: const X = await import('spec') / const X = require('spec')
  for (const m of skeleton.matchAll(/\b(?:const|let|var)\s+([^=;]+?)\s*=\s*(?:await\s+)?(?:import|require)\s*\(\s*__STR_(\d+)__\s*\)/g)) {
    const spec = literals[Number(m[2])];
    recordImport(spec, m[1], m.index);
  }
  // Unassigned dynamic import('spec') / require('spec')
  for (const m of skeleton.matchAll(/(?<![\w$.])(?:import|require)\s*\(\s*__STR_(\d+)__\s*\)/g)) {
    const before = skeleton.slice(Math.max(0, m.index - 80), m.index);
    if (/=\s*(?:await\s+)?$/.test(before)) continue;
    const spec = literals[Number(m[1])];
    recordImport(spec, '', m.index);
  }

  // Python imports: from pkg.mod import a, _b  /  import pkg._internal
  if (isPython) {
    for (const m of skeleton.matchAll(/^[ \t]*from\s+([A-Za-z0-9_.]+)\s+import\s+([^\n;#]+)/gm)) {
      const modSpec = m[1];
      if (isTestOrBuiltinSpecifier(modSpec, testDir)) continue;
      const line = lineNumberAt(lineStarts, m.index);
      if (isPrivateModuleSpecifier(modSpec)) {
        const detail = `Test imports private module path "${modSpec}". Import only the module's public entry interface so internal refactors do not break tests.`;
        findings.push({
          filePath: path,
          line,
          order: 0,
          code: 'test-private-import',
          category: 'public-interface test',
          target: null,
          detail,
          warning: `Warning: public-interface test: ${path}:${line} [test-private-import] ${detail}`,
        });
      }
      for (const rawPart of m[2].replace(/[()]/g, '').split(',')) {
        const piece = rawPart.trim();
        if (!piece) continue;
        const [orig, alias] = piece.split(/\s+as\s+/);
        const sym = orig.trim();
        const local = (alias ?? orig).trim();
        if (PRIVATE_SYMBOL_RE.test(sym) && !/^__.*__$/.test(sym)) {
          const detail = `Test imports private internal symbol "${sym}" from "${modSpec}". Test observable behavior through public exports instead of private helpers.`;
          findings.push({
            filePath: path,
            line,
            order: 1,
            code: 'test-private-import',
            category: 'public-interface test',
            target: null,
            detail,
            warning: `Warning: public-interface test: ${path}:${line} [test-private-import] ${detail}`,
          });
        }
        if (/^[A-Za-z_]\w*$/.test(local)) prodBindings.set(local, null);
      }
    }
    for (const m of skeleton.matchAll(/^[ \t]*import\s+([A-Za-z0-9_., \t]+)$/gm)) {
      const line = lineNumberAt(lineStarts, m.index);
      for (const item of m[1].split(',')) {
        const [modName, alias] = item.trim().split(/\s+as\s+/);
        if (!modName || isTestOrBuiltinSpecifier(modName, testDir)) continue;
        if (isPrivateModuleSpecifier(modName)) {
          const detail = `Test imports private module path "${modName}". Import only the module's public entry interface so internal refactors do not break tests.`;
          findings.push({
            filePath: path,
            line,
            order: 0,
            code: 'test-private-import',
            category: 'public-interface test',
            target: null,
            detail,
            warning: `Warning: public-interface test: ${path}:${line} [test-private-import] ${detail}`,
          });
        }
        const local = (alias ?? modName.split('.')[0]).trim();
        if (/^[A-Za-z_]\w*$/.test(local)) prodBindings.set(local, null);
      }
    }
  }

  // Propagate instances constructed or returned from imported production factories/classes:
  // e.g. const svc = new OrderService(...) or const store = createStore(...)
  for (let pass = 0; pass < 2; pass++) {
    for (const m of skeleton.matchAll(/\b(?:const|let|var)?\s*([A-Za-z_$][\w$]*)\s*=\s*(?:await\s+)?(?:new\s+)?([A-Za-z_$][\w$]*)\s*\(/g)) {
      const lhs = m[1];
      const callee = m[2];
      if (!prodBindings.has(lhs) && prodBindings.has(callee)) {
        prodBindings.set(lhs, prodBindings.get(callee));
      }
    }
  }

  // 2. Private member access on imported production modules or their instances: mod._secret / instance._cache
  for (const m of skeleton.matchAll(/\b([A-Za-z_$][\w$]*)\s*(?:\?\.|\.)\s*(_[A-Za-z0-9][\w$]*)\b/g)) {
    const obj = m[1];
    const member = m[2];
    if (!prodBindings.has(obj)) continue;
    if (/^__.*__$/.test(member)) continue;
    const line = lineNumberAt(lineStarts, m.index);
    const target = prodBindings.get(obj) ?? null;
    const detail = `Test accesses private member "${obj}.${member}". Exercise only public methods and properties instead of reaching into module internals.`;
    findings.push({
      filePath: path,
      line,
      order: 2,
      code: 'test-private-access',
      category: 'public-interface test',
      target,
      detail,
      warning: `Warning: public-interface test: ${path}:${line} [test-private-access] ${detail}`,
    });
  }

  // 3. Rewire and private introspection hooks anywhere in test code
  for (const m of skeleton.matchAll(/(?:\.\s*(__get__|__set__|__Rewire__|__ResetDependency__|__private|__internal)\b|\b(rewire)\s*\(\s*__STR_(\d+)__\s*\))/g)) {
    const hook = m[1] ?? m[2];
    const target = m[3] !== undefined ? resolveProductionModuleTarget(literals[Number(m[3])], testDir) : null;
    const line = lineNumberAt(lineStarts, m.index);
    const detail = `Test reaches into private module internals via "${hook}". Test the module through its public interface and injected ports.`;
    findings.push({
      filePath: path,
      line,
      order: 3,
      code: 'test-private-access',
      category: 'public-interface test',
      target,
      detail,
      warning: `Warning: public-interface test: ${path}:${line} [test-private-access] ${detail}`,
    });
  }

  // 4. VM evaluation of production src/ files to extract unexported internals
  const srcReadVars = new Map();
  for (const m of skeleton.matchAll(/\b(?:const|let|var)\s+([A-Za-z_$][\w$]*)\s*=\s*(?:await\s+)?(?:fs\s*\.\s*)?(?:readFileSync|readFile)\s*\(\s*__STR_(\d+)__/g)) {
    const candidate = normalizeCandidateRepoPath(literals[Number(m[2])], testDir);
    if (candidate && SRC_CODE_PATH.test(candidate)) srcReadVars.set(m[1], candidate);
  }
  if (srcReadVars.size > 0) {
    for (const m of skeleton.matchAll(/\b(?:runInNewContext|runInContext|runInThisContext|Script)\s*\(\s*([A-Za-z_$][\w$]*)\b/g)) {
      const target = srcReadVars.get(m[1]);
      if (!target) continue;
      const line = lineNumberAt(lineStarts, m.index);
      const detail = `Test evaluates raw source from "${target}" to reach unexported internals. Import "${target}" through its public exports instead.`;
      findings.push({
        filePath: path,
        line,
        order: 4,
        code: 'test-private-access',
        category: 'public-interface test',
        target,
        detail,
        warning: `Warning: public-interface test: ${path}:${line} [test-private-access] ${detail}`,
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

export function lintPublicInterfaceTests(text, { path = 'test/example.test.mjs' } = {}) {
  return collectPublicInterfaceTestWarnings(text, { path }).map(item => item.warning);
}

const VALIDATION_WARNING_RE = /^Warning: validation lint: (.+):(\d+) \[([^\]]+)\] (.+)$/;

function parseValidationWarnings(rawWarnings, fallbackPath) {
  return rawWarnings.map((warning, idx) => {
    const match = VALIDATION_WARNING_RE.exec(warning);
    if (!match) {
      return {
        filePath: fallbackPath,
        line: 1,
        order: 30 + idx,
        code: 'silent-validation-skip',
        category: 'validation lint',
        detail: warning,
        warning,
      };
    }
    return {
      filePath: match[1],
      line: Number(match[2]) || 1,
      order: 30 + idx,
      code: match[3],
      category: 'validation lint',
      detail: match[4],
      warning,
    };
  });
}

function collectValidationCodeFindings(text, { path = 'test/example.test.mjs', kind = 'test', hasRealE2eCoverage = false } = {}) {
  const { warnings } = lintValidationCode({ path, kind, text, hasRealE2eCoverage });
  return parseValidationWarnings(warnings, path);
}

/**
 * Flag silent validation bypasses (such as real-binding-unavailable local skips or unconditional E2E skips).
 */
export function lintValidationSkips(text, { path = 'src/module.mjs', kind = 'code' } = {}) {
  return collectValidationCodeFindings(text, { path, kind, hasRealE2eCoverage: true })
    .filter(item => item.code === 'silent-validation-skip')
    .map(item => item.warning);
}

/**
 * Flag mock-only tests targeting runtime boundaries when no real E2E coverage exists.
 */
export function lintBoundaryMockOnlyTests(text, { path = 'test/example.test.mjs', hasRealE2eCoverage = false } = {}) {
  return collectValidationCodeFindings(text, { path, kind: 'test', hasRealE2eCoverage })
    .filter(item => item.code === 'boundary-mock-only-test')
    .map(item => item.warning);
}

const MAX_GLOB_WILDCARDS = 12;
const MAX_REGEX_GROUP_DEPTH = 16;

function encodeGlobSegment(segment) {
  let out = '';
  for (const ch of segment) {
    if (ch === '*') out += '[^/]*';
    else if (ch === '?') out += '[^/]';
    else if ('+^$()[]{}|.\\'.includes(ch)) out += `\\${ch}`;
    else out += ch;
  }
  return out;
}

function globToRegExp(glob) {
  const clean = String(glob ?? '').trim().replace(/\\/g, '/').replace(/^\.\//, '').replace(/\/+/g, '/').replace(/^\/+|\/+$/g, '');
  if (!clean || clean.length > 256) return null;
  const rawSegments = clean.split('/');
  const segments = [];
  for (const rawSeg of rawSegments) {
    const collapsed = /^\*+$/.test(rawSeg)
      ? (rawSeg.length >= 2 ? '**' : '*')
      : rawSeg.replace(/\*+/g, '*');
    if (collapsed === '**' && segments.at(-1) === '**') continue;
    segments.push(collapsed);
  }
  let wildcardCount = 0;
  for (const seg of segments) {
    if (seg === '**') wildcardCount += 1;
    else wildcardCount += (seg.match(/[*?]/g) ?? []).length;
  }
  if (wildcardCount > MAX_GLOB_WILDCARDS) return null;

  let re = '^';
  for (let idx = 0; idx < segments.length; idx++) {
    const seg = segments[idx];
    if (seg === '**') {
      if (segments.length === 1) re += '.*';
      else if (idx === 0) re += '(?:.*/)?';
      else if (idx === segments.length - 1) re += '/.*';
      else re += '(?:/.*)?';
      continue;
    }
    if (idx > 0 && segments[idx - 1] !== '**') re += '/';
    else if (idx > 0 && segments[idx - 1] === '**' && idx - 1 > 0) re += '/';
    re += encodeGlobSegment(seg);
  }
  re += '$';
  return new RegExp(re);
}

function readRegexQuantifier(pattern, pos) {
  if (pos >= pattern.length) return null;
  const ch = pattern[pos];
  if (ch === '*' || ch === '+') {
    const lazy = pattern[pos + 1] === '?' ? 1 : 0;
    return { len: 1 + lazy, unbounded: true, repeats: true };
  }
  if (ch === '?') {
    const lazy = pattern[pos + 1] === '?' ? 1 : 0;
    return { len: 1 + lazy, unbounded: false, repeats: false };
  }
  if (ch === '{') {
    const m = /^\{(\d+)(?:,(\d*))?\}(\?)?/.exec(pattern.slice(pos));
    if (!m) return null;
    const min = Number(m[1]);
    const hasComma = m[2] !== undefined;
    const max = hasComma ? (m[2] === '' ? Infinity : Number(m[2])) : min;
    if (max < min) return null;
    return { len: m[0].length, unbounded: max === Infinity, repeats: max > 1 };
  }
  return null;
}

function isSafeRegexPattern(pattern, cleanFlags) {
  const ignoreCase = cleanFlags.includes('i');
  const normChar = ch => (ignoreCase ? ch.toLowerCase() : ch);
  const stack = [];
  const newBranch = () => ({ firstChar: null, pureLiteralPrefix: true, len: 0 });
  const recordAtomOnTop = (literalChar = null) => {
    if (!stack.length) return;
    const branch = stack.at(-1).branches.at(-1);
    if (branch.len === 0) {
      if (literalChar !== null && branch.pureLiteralPrefix) branch.firstChar = normChar(literalChar);
      else branch.pureLiteralPrefix = false;
    }
    branch.len += 1;
  };
  const markQuantifierOnTop = quant => {
    if (!stack.length) return;
    const top = stack.at(-1);
    top.hasInnerQuantifier = true;
    if (quant.unbounded) top.hasUnboundedQuantifier = true;
  };

  let inCharClass = false;
  let i = 0;
  while (i < pattern.length) {
    const ch = pattern[i];
    if (inCharClass) {
      if (ch === '\\') { i += 2; continue; }
      if (ch === ']') {
        inCharClass = false;
        i += 1;
        const q = readRegexQuantifier(pattern, i);
        if (q) { markQuantifierOnTop(q); i += q.len; }
        continue;
      }
      i += 1;
      continue;
    }

    if (ch === '\\') {
      const esc = pattern[i + 1];
      if (!esc) return false;
      if (/^[1-9]$/.test(esc) || esc === 'k') return false;
      let step = 2;
      if ((esc === 'p' || esc === 'P' || esc === 'u') && pattern[i + 2] === '{') {
        const close = pattern.indexOf('}', i + 3);
        if (close < 0) return false;
        step = close - i + 1;
      }
      if (esc === 'b' || esc === 'B') {
        i += step;
        continue;
      }
      const isClassEscape = /^[dDwWsSpP]$/.test(esc);
      recordAtomOnTop(isClassEscape ? null : esc);
      i += step;
      const q = readRegexQuantifier(pattern, i);
      if (q) { markQuantifierOnTop(q); i += q.len; }
      continue;
    }

    if (ch === '[') {
      inCharClass = true;
      recordAtomOnTop(null);
      i += 1;
      continue;
    }

    if (ch === '(') {
      if (stack.length >= MAX_REGEX_GROUP_DEPTH) return false;
      let kind = 'normal';
      let step = 1;
      if (pattern[i + 1] === '?') {
        const rest = pattern.slice(i + 2);
        if (rest.startsWith(':')) { step = 3; }
        else if (rest.startsWith('=') || rest.startsWith('!')) { kind = 'lookaround'; step = 3; }
        else if (rest.startsWith('<=') || rest.startsWith('<!')) { kind = 'lookaround'; step = 4; }
        else if (rest.startsWith('<')) {
          const close = rest.indexOf('>');
          if (close <= 1) return false;
          step = 2 + close + 1;
        } else {
          return false;
        }
      }
      if (kind === 'normal') recordAtomOnTop(null);
      stack.push({ kind, hasInnerQuantifier: false, hasUnboundedQuantifier: false, branches: [newBranch()] });
      i += step;
      continue;
    }

    if (ch === '|') {
      if (stack.length) stack.at(-1).branches.push(newBranch());
      i += 1;
      continue;
    }

    if (ch === ')') {
      if (!stack.length) return false;
      const frame = stack.pop();
      if (frame.kind === 'lookaround' && frame.hasUnboundedQuantifier) return false;
      i += 1;
      const q = readRegexQuantifier(pattern, i);
      if (q) {
        if (frame.kind === 'lookaround') return false;
        if (frame.hasInnerQuantifier) return false;
        if (q.repeats && frame.branches.length > 1) {
          const starts = [];
          for (const br of frame.branches) {
            if (br.len === 0 || !br.pureLiteralPrefix || br.firstChar === null) return false;
            starts.push(br.firstChar);
          }
          if (new Set(starts).size !== frame.branches.length) return false;
        }
        markQuantifierOnTop(q);
        i += q.len;
      }
      if (stack.length && frame.kind === 'normal') {
        if (frame.hasInnerQuantifier) stack.at(-1).hasInnerQuantifier = true;
        if (frame.hasUnboundedQuantifier) stack.at(-1).hasUnboundedQuantifier = true;
      }
      continue;
    }

    if (ch === '^' || ch === '$') {
      i += 1;
      continue;
    }

    const strayQuant = readRegexQuantifier(pattern, i);
    if (strayQuant) {
      markQuantifierOnTop(strayQuant);
      i += strayQuant.len;
      continue;
    }

    recordAtomOnTop(ch === '.' ? null : ch);
    i += 1;
    const q = readRegexQuantifier(pattern, i);
    if (q) { markQuantifierOnTop(q); i += q.len; }
  }

  return !inCharClass && stack.length === 0;
}

function parseRegexSafe(pattern, flags = '') {
  if (typeof pattern !== 'string' || !pattern.length || pattern.length > 512) return null;
  if (typeof flags !== 'string' || flags.length > 8) return null;
  const cleanFlags = [...new Set(flags.replace(/[gy]/g, '').split(''))].join('');
  if (!/^[imsu]*$/.test(cleanFlags)) return null;
  if (!isSafeRegexPattern(pattern, cleanFlags)) return null;
  try {
    return new RegExp(pattern, cleanFlags);
  } catch {
    return null;
  }
}

const VALID_TARGETS = new Set(['prompt', 'story', 'test', 'code', 'all']);
const VALID_SEVERITIES = new Set(['off', 'warn', 'error']);

function mergeLintConfigSection(rawLint, { sourcePath, disabledRules, ruleSeverities, customRules, configErrors }) {
  const addConfigError = detail => configErrors.push({
    filePath: sourcePath,
    line: 1,
    order: 0,
    code: 'lint-config-invalid',
    category: 'lint config',
    detail,
  });

  if (typeof rawLint !== 'object' || rawLint === null || Array.isArray(rawLint)) {
    addConfigError(`"lint" in ${sourcePath} must be a JSON object.`);
    return;
  }

  if (rawLint.disable !== undefined) {
    if (!Array.isArray(rawLint.disable) || rawLint.disable.some(id => typeof id !== 'string' || !RULE_ID_RE.test(id))) {
      addConfigError(`"lint.disable" in ${sourcePath} must be an array of valid rule IDs.`);
    } else {
      for (const id of rawLint.disable) disabledRules.add(id);
    }
  }

  if (rawLint.rules !== undefined) {
    if (!rawLint.rules || typeof rawLint.rules !== 'object' || Array.isArray(rawLint.rules)) {
      addConfigError(`"lint.rules" in ${sourcePath} must be an object mapping rule IDs to "off", "warn", or "error".`);
    } else {
      for (const [id, spec] of Object.entries(rawLint.rules)) {
        if (!RULE_ID_RE.test(id)) {
          addConfigError(`Invalid rule ID "${id}" in "lint.rules".`);
          continue;
        }
        const sev = typeof spec === 'string' ? spec : (spec && typeof spec === 'object' && !Array.isArray(spec) ? spec.severity : null);
        if (!VALID_SEVERITIES.has(sev)) {
          addConfigError(`Rule "${id}" in "lint.rules" must use severity "off", "warn", or "error".`);
          continue;
        }
        ruleSeverities.set(id, sev);
        if (sev === 'off') disabledRules.add(id);
        else disabledRules.delete(id);
      }
    }
  }

  if (rawLint.custom_rules !== undefined) {
    if (!Array.isArray(rawLint.custom_rules)) {
      addConfigError(`"lint.custom_rules" in ${sourcePath} must be an array of rule objects.`);
    } else {
      for (let idx = 0; idx < rawLint.custom_rules.length; idx++) {
        const rawRule = rawLint.custom_rules[idx];
        if (!rawRule || typeof rawRule !== 'object' || Array.isArray(rawRule)) {
          addConfigError(`Entry ${idx} in "lint.custom_rules" must be an object.`);
          continue;
        }
        const id = rawRule.id;
        if (typeof id !== 'string' || !RULE_ID_RE.test(id)) {
          addConfigError(`Entry ${idx} in "lint.custom_rules" requires a valid "id" (letters, digits, "-", "_", ".").`);
          continue;
        }
        const rawTarget = rawRule.target ?? (rawRule.include ? 'all' : 'prompt');
        const targetList = Array.isArray(rawTarget) ? rawTarget : [rawTarget];
        if (!targetList.length || targetList.some(t => typeof t !== 'string' || !VALID_TARGETS.has(t))) {
          addConfigError(`Custom rule "${id}" has invalid "target" (choose "prompt", "story", "test", "code", or "all").`);
          continue;
        }
        const severity = rawRule.severity ?? 'warn';
        if (!VALID_SEVERITIES.has(severity)) {
          addConfigError(`Custom rule "${id}" has invalid "severity" (choose "off", "warn", or "error").`);
          continue;
        }

        const toGlobs = (val, fieldName) => {
          if (val === undefined) return [];
          const arr = typeof val === 'string' ? [val] : (Array.isArray(val) ? val : null);
          if (!arr || arr.some(g => typeof g !== 'string')) {
            addConfigError(`Custom rule "${id}" field "${fieldName}" must be a glob string or array of strings.`);
            return null;
          }
          const compiled = arr.map(globToRegExp);
          if (compiled.some(r => r === null)) {
            addConfigError(`Custom rule "${id}" field "${fieldName}" contains an invalid glob.`);
            return null;
          }
          return compiled;
        };

        const includeMatchers = toGlobs(rawRule.include, 'include');
        const excludeMatchers = toGlobs(rawRule.exclude, 'exclude');
        if (includeMatchers === null || excludeMatchers === null) continue;

        let forbidRegex = null;
        if (rawRule.forbid_pattern !== undefined) {
          forbidRegex = parseRegexSafe(rawRule.forbid_pattern, rawRule.flags ?? '');
          if (!forbidRegex) {
            addConfigError(`Custom rule "${id}" has an invalid "forbid_pattern" regular expression.`);
            continue;
          }
        }

        let requireRegex = null;
        if (rawRule.require_pattern !== undefined) {
          requireRegex = parseRegexSafe(rawRule.require_pattern, rawRule.flags ?? '');
          if (!requireRegex) {
            addConfigError(`Custom rule "${id}" has an invalid "require_pattern" regular expression.`);
            continue;
          }
        }

        let requireHeading = null;
        if (rawRule.require_heading !== undefined) {
          if (typeof rawRule.require_heading !== 'string' || !rawRule.require_heading.trim()) {
            addConfigError(`Custom rule "${id}" field "require_heading" must be a nonblank string.`);
            continue;
          }
          requireHeading = rawRule.require_heading.trim();
        }

        let maxLines = null;
        if (rawRule.max_lines !== undefined) {
          if (!Number.isInteger(rawRule.max_lines) || rawRule.max_lines < 1) {
            addConfigError(`Custom rule "${id}" field "max_lines" must be a positive integer.`);
            continue;
          }
          maxLines = rawRule.max_lines;
        }

        if (!forbidRegex && !requireRegex && !requireHeading && maxLines === null) {
          addConfigError(`Custom rule "${id}" must specify at least one check ("forbid_pattern", "require_pattern", "require_heading", or "max_lines").`);
          continue;
        }

        const message = typeof rawRule.message === 'string' && rawRule.message.trim()
          ? rawRule.message.trim()
          : `Custom project lint rule "${id}" failed.`;

        customRules.push({
          id,
          targets: new Set(targetList),
          severity,
          includeMatchers,
          excludeMatchers,
          forbidRegex,
          requireRegex,
          requireHeading,
          maxLines,
          message,
        });
      }
    }
  }
}

function loadWorkspaceLintRuleFiles(realRoot, target) {
  let loadedAny = false;
  for (const relDir of ['rules', 'rules/lint']) {
    try {
      const st = lstatSync(join(realRoot, relDir));
      if (st.isSymbolicLink() || !st.isDirectory()) return false;
    } catch {
      return false;
    }
  }

  let entries;
  try {
    entries = readdirSync(join(realRoot, 'rules/lint')).filter(name => name.endsWith('.json')).sort();
  } catch {
    return false;
  }

  for (const name of entries) {
    const relPath = `rules/lint/${name}`;
    const rawText = readSafeUtf8(realRoot, relPath);
    if (rawText === null) continue;
    loadedAny = true;
    let parsed;
    try {
      parsed = JSON.parse(rawText);
    } catch {
      target.configErrors.push({
        filePath: relPath,
        line: 1,
        order: 0,
        code: 'lint-config-invalid',
        category: 'lint config',
        detail: `${relPath} contains invalid JSON.`,
      });
      continue;
    }
    const section = Array.isArray(parsed)
      ? { custom_rules: parsed }
      : (parsed && typeof parsed === 'object' && typeof parsed.id === 'string'
        && !Object.hasOwn(parsed, 'disable') && !Object.hasOwn(parsed, 'rules') && !Object.hasOwn(parsed, 'custom_rules')
        ? { custom_rules: [parsed] }
        : parsed);
    mergeLintConfigSection(section, { sourcePath: relPath, ...target });
  }
  return loadedAny;
}

export function loadProjectLintConfig(rootOrObject) {
  const empty = {
    configured: false,
    disabledRules: new Set(),
    ruleSeverities: new Map(),
    customRules: [],
    configErrors: [],
  };
  if (!rootOrObject) return empty;

  const target = {
    disabledRules: new Set(),
    ruleSeverities: new Map(),
    customRules: [],
    configErrors: [],
  };
  let configured = false;

  if (typeof rootOrObject === 'string') {
    let realRoot;
    try { realRoot = realpathSync(rootOrObject); } catch { return empty; }
    // Workspace-local rules/lint/*.json load first; explicit pdd.json "lint" overrides below.
    if (loadWorkspaceLintRuleFiles(realRoot, target)) configured = true;

    const rawText = readSafeUtf8(realRoot, 'pdd.json');
    if (rawText !== null) {
      let parsed;
      try {
        parsed = JSON.parse(rawText);
      } catch {
        target.configErrors.push({
          filePath: 'pdd.json',
          line: 1,
          order: 0,
          code: 'lint-config-invalid',
          category: 'lint config',
          detail: 'pdd.json contains invalid JSON.',
        });
        return { configured: true, ...target };
      }
      if (parsed && typeof parsed === 'object' && !Array.isArray(parsed) && Object.hasOwn(parsed, 'lint') && parsed.lint !== undefined && parsed.lint !== null) {
        configured = true;
        mergeLintConfigSection(parsed.lint, { sourcePath: 'pdd.json', ...target });
      }
    }
    return configured ? { configured: true, ...target } : empty;
  }

  if (typeof rootOrObject === 'object' && !Array.isArray(rootOrObject)) {
    const rawLint = Object.hasOwn(rootOrObject, 'lint') ? rootOrObject.lint : rootOrObject;
    if (rawLint === undefined || rawLint === null) return empty;
    mergeLintConfigSection(rawLint, { sourcePath: 'pdd.json', ...target });
    return { configured: true, ...target };
  }

  return empty;
}

function headingMatches(contentText, requiredHeading) {
  const hasHashes = /^#{1,6}\s+/.test(requiredHeading);
  const lines = contentText.split(/\r?\n/);
  for (const line of lines) {
    if (hasHashes) {
      if (line.trim().toLowerCase() === requiredHeading.toLowerCase()) return true;
    } else {
      const m = /^ {0,3}#{1,6}\s+(.+)$/.exec(line);
      if (m && m[1].trim().toLowerCase() === requiredHeading.toLowerCase()) return true;
    }
  }
  return false;
}

function evaluateCustomRulesOnFile(customRules, { filePath, kind, rawText }) {
  const findings = [];
  const inspectText = kind === 'prompt' ? stripPromptMetadataPreservingLines(rawText) : rawText;
  const lineCount = kind === 'prompt' ? countPromptProseLines(rawText) : countFileLines(rawText);
  const lineStarts = buildLineStarts(inspectText);

  for (let idx = 0; idx < customRules.length; idx++) {
    const rule = customRules[idx];
    if (rule.severity === 'off') continue;
    if (!rule.targets.has('all') && !rule.targets.has(kind)) continue;
    if (rule.includeMatchers.length && !rule.includeMatchers.some(re => re.test(filePath))) continue;
    if (rule.excludeMatchers.some(re => re.test(filePath))) continue;

    if (rule.forbidRegex) {
      const m = rule.forbidRegex.exec(inspectText);
      if (m) {
        const line = lineNumberAt(lineStarts, m.index);
        findings.push({
          filePath,
          line,
          order: 50 + idx,
          code: rule.id,
          category: 'custom rule',
          defaultSeverity: rule.severity,
          detail: rule.message,
        });
      }
    }

    if (rule.requireRegex && !rule.requireRegex.test(inspectText)) {
      findings.push({
        filePath,
        line: 1,
        order: 50 + idx,
        code: rule.id,
        category: 'custom rule',
        defaultSeverity: rule.severity,
        detail: rule.message,
      });
    }

    if (rule.requireHeading && !headingMatches(inspectText, rule.requireHeading)) {
      findings.push({
        filePath,
        line: 1,
        order: 50 + idx,
        code: rule.id,
        category: 'custom rule',
        defaultSeverity: rule.severity,
        detail: rule.message,
      });
    }

    if (rule.maxLines !== null && lineCount > rule.maxLines) {
      findings.push({
        filePath,
        line: 1,
        order: 50 + idx,
        code: rule.id,
        category: 'custom rule',
        defaultSeverity: rule.severity,
        detail: `${rule.message} (${lineCount} lines > max ${rule.maxLines}).`,
      });
    }
  }
  return findings;
}

function isEligibleProductionCodeFile(path) {
  return canonicalRepoPath(path)
    && CODE_FILE_EXT.test(path)
    && !path.endsWith('.prompt.md')
    && !isTestOwnedPath(path)
    && !FIXTURE_DIR.test(path)
    && !EXAMPLE_DIR.test(path)
    && !NON_CODE_DIR.test(path);
}

function scenarioPromptRefs(doc) {
  if (!doc || typeof doc !== 'object') return [];
  const refs = [];
  if (typeof doc.entry_path === 'string') refs.push(doc.entry_path.replace(/^\.\//, ''));
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

function buildStoriesByStem(scopedFiles) {
  const storiesByStem = new Map();
  for (const file of scopedFiles) {
    if (!isLintableStoryPath(file)) continue;
    const stem = posix.basename(file).replace(/\.md$/i, '');
    if (!storiesByStem.has(stem)) storiesByStem.set(stem, []);
    storiesByStem.get(stem).push(file);
  }
  return storiesByStem;
}

function inferScenarioStoryPath(doc, scenarioPath, storiesByStem) {
  if (typeof doc?.story_path === 'string' && doc.story_path.trim()) {
    return doc.story_path.trim().replace(/^\.\//, '');
  }
  if (!doc || typeof doc !== 'object' || Array.isArray(doc)) return null;
  const base = posix.basename(scenarioPath, '.json');
  const owners = storiesByStem.has(base) ? [base] : [];
  for (let at = base.lastIndexOf('.'); at > 0; at = base.lastIndexOf('.', at - 1)) {
    if (storiesByStem.has(base.slice(0, at))) owners.push(base.slice(0, at));
  }
  if (owners.length === 1) {
    const matches = storiesByStem.get(owners[0]) ?? [];
    if (matches.length === 1) return matches[0];
  }
  return null;
}

export function lintRepoProject({ root, files, promptPaths, tests, config } = {}) {
  const empty = { ok: true, configured: false, warnings: [], errors: [], findings: [] };
  if (!root || typeof root !== 'string') return empty;
  let realRoot, policy;
  try {
    realRoot = realpathSync(root);
    policy = workspace.policy({ root: realRoot });
  } catch {
    return empty;
  }

  let rawFiles;
  try {
    rawFiles = Array.isArray(files) ? files : gitFiles(realRoot);
  } catch {
    return empty;
  }

  const lintConfig = loadProjectLintConfig(config !== undefined ? config : realRoot);
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

  // Build prompt <-> production code ownership map across the repository so prompt size, structure, and scoped test checks have ownership facts.
  const allPrompts = scopedFiles.filter(p => p.endsWith('.prompt.md'));
  const prodCodePaths = scopedFiles.filter(isEligibleProductionCodeFile);
  const promptTextCache = new Map();
  const getPromptText = p => {
    if (!promptTextCache.has(p)) promptTextCache.set(p, readSafeUtf8(realRoot, p));
    return promptTextCache.get(p);
  };

  const ownedCodeByPrompt = new Map();
  const promptOwnersByCode = new Map();
  if (allPrompts.length && prodCodePaths.length) {
    const rawBindings = scopedSet.has('pdd-bindings.json') ? readSafeUtf8(realRoot, 'pdd-bindings.json') : null;
    const heads = prodCodePaths.map(p => {
      const txt = readSafeUtf8(realRoot, p);
      return { path: p, content: typeof txt === 'string' ? txt.slice(0, HEAD_BYTES + 1) : null, fullText: txt };
    });
    const codeTextByPath = new Map(heads.filter(h => typeof h.fullText === 'string').map(h => [h.path, h.fullText]));
    const promptRows = allPrompts.map(p => ({ path: p, content: getPromptText(p) })).filter(r => typeof r.content === 'string');
    const ownership = resolveOwners({
      paths: prodCodePaths,
      allPaths: scopedFiles,
      bindings: rawBindings,
      heads: heads.map(({ path: p, content }) => ({ path: p, content })),
      prompts: promptRows,
    });
    for (const row of ownership.files) {
      if (!row.owners.length || !codeTextByPath.has(row.path)) continue;
      promptOwnersByCode.set(row.path, row.owners);
      for (const owner of row.owners) {
        if (!ownedCodeByPrompt.has(owner)) ownedCodeByPrompt.set(owner, []);
        ownedCodeByPrompt.get(owner).push({ path: row.path, text: codeTextByPath.get(row.path) });
      }
    }
  }

  const rawFindings = [...lintConfig.configErrors.map(err => ({ ...err, defaultSeverity: 'error' }))];

  // 1. Prompts: code fences, structure/diagrams, prompt-vs-code size, and custom prompt rules
  const targetPrompts = Array.isArray(promptPaths)
    ? [...new Set(promptPaths.filter(p => typeof p === 'string').map(p => p.replace(/^\.\//, '')).filter(p => scopedSet.has(p) && p.endsWith('.prompt.md')))].sort()
    : allPrompts;

  for (const promptPath of targetPrompts) {
    const content = getPromptText(promptPath);
    if (typeof content !== 'string') continue;
    const ownedCode = ownedCodeByPrompt.get(promptPath) ?? [];

    for (const f of collectPromptCodeBlockFindings(content, { path: promptPath })) {
      rawFindings.push({ ...f, defaultSeverity: 'warn' });
    }
    for (const f of collectPromptStructureFindings(content, { path: promptPath, hasOwnedCode: ownedCode.length > 0 })) {
      rawFindings.push({ ...f, defaultSeverity: 'warn' });
    }
    for (const f of collectPromptSizeFindings(content, ownedCode, { path: promptPath })) {
      rawFindings.push({ ...f, defaultSeverity: 'warn' });
    }
    if (lintConfig.customRules.length) {
      rawFindings.push(...evaluateCustomRulesOnFile(lintConfig.customRules, {
        filePath: promptPath,
        kind: 'prompt',
        rawText: content,
      }));
    }
  }

  // 2. Stories: criteria/quality hygiene and custom Story rules
  let targetStories = [];
  if (promptPaths === undefined && tests === undefined) {
    targetStories = scopedFiles.filter(isLintableStoryPath);
  } else {
    const storyCandidates = new Set();
    const storiesByStem = buildStoriesByStem(scopedFiles);
    if (Array.isArray(tests)) {
      for (const entry of tests) {
        if (entry && typeof entry === 'object' && typeof entry.storyPath === 'string') {
          storyCandidates.add(entry.storyPath.replace(/^\.\//, ''));
        }
        const tPath = typeof entry === 'string' ? entry.replace(/^\.\//, '') : entry?.path?.replace(/^\.\//, '');
        if (tPath && scopedSet.has(tPath)) {
          if (isLintableStoryPath(tPath)) storyCandidates.add(tPath);
          else if (tPath.endsWith('.json')) {
            const raw = readSafeUtf8(realRoot, tPath);
            if (raw) {
              try {
                const doc = JSON.parse(raw);
                const sPath = inferScenarioStoryPath(doc, tPath, storiesByStem);
                if (sPath) storyCandidates.add(sPath);
              } catch {}
            }
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
          const sPath = inferScenarioStoryPath(doc, scenarioPath, storiesByStem);
          if (sPath && scenarioPromptRefs(doc).some(ref => promptSet.has(ref))) {
            storyCandidates.add(sPath);
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
      rawFindings.push({
        filePath: storyPath,
        line: problem.line,
        order: 10,
        code: problem.code,
        category: 'Story hygiene',
        defaultSeverity: 'warn',
        detail: problem.message,
      });
    }
    if (lintConfig.customRules.length) {
      rawFindings.push(...evaluateCustomRulesOnFile(lintConfig.customRules, {
        filePath: storyPath,
        kind: 'story',
        rawText: content,
      }));
    }
  }

  // 3. Tests: fake tests, public-interface-only tests, and custom test rules
  const promptFilterSet = Array.isArray(promptPaths) ? new Set(targetPrompts) : null;
  const targetMatchesPromptFilter = target => {
    if (!promptFilterSet) return true;
    if (!target) return false;
    if (promptFilterSet.has(target)) return true;
    const owners = promptOwnersByCode.get(target);
    return Array.isArray(owners) && owners.some(owner => promptFilterSet.has(owner));
  };

  if (!promptFilterSet || promptFilterSet.size > 0) {
    const testEntries = [];
    const realE2eTargets = new Set();
    for (const testPath of scopedFiles.filter(isInspectableTestCodePath)) {
      const content = readSafeUtf8(realRoot, testPath);
      if (typeof content !== 'string') continue;
      const { boundaryTargets } = inspectTestBoundaryTargets(testPath, content);
      const realKinds = detectRealE2eKindsInTest(testPath, content);
      if (realKinds.some(k => k !== 'real-execution')) {
        for (const target of boundaryTargets) {
          if (!target.startsWith('test-stem:')) realE2eTargets.add(target);
        }
      }
      testEntries.push({ testPath, content, boundaryTargets });
    }

    for (const { testPath, content, boundaryTargets } of testEntries) {
      for (const item of collectFakeTestWarnings(content, { path: testPath })) {
        if (!targetMatchesPromptFilter(item.target)) continue;
        rawFindings.push({ ...item, defaultSeverity: 'warn' });
      }
      for (const item of collectPublicInterfaceTestWarnings(content, { path: testPath })) {
        if (!targetMatchesPromptFilter(item.target)) continue;
        rawFindings.push({ ...item, defaultSeverity: 'warn' });
      }
      const hasRealE2eCoverage = boundaryTargets.length > 0
        && boundaryTargets.every(target => !target.startsWith('test-stem:') && realE2eTargets.has(target));
      if (!promptFilterSet) {
        for (const item of collectValidationCodeFindings(content, { path: testPath, kind: 'test', hasRealE2eCoverage })) {
          rawFindings.push({ ...item, defaultSeverity: 'warn' });
        }
      }
      if (!promptFilterSet && lintConfig.customRules.length) {
        rawFindings.push(...evaluateCustomRulesOnFile(lintConfig.customRules, {
          filePath: testPath,
          kind: 'test',
          rawText: content,
        }));
      }
    }
  }

  // 4. Production code: silent validation skip checks and custom code rules
  const hasCustomCodeRules = lintConfig.customRules.some(r => r.severity !== 'off' && (r.targets.has('code') || r.targets.has('all')));
  const targetCodePaths = promptFilterSet
    ? prodCodePaths.filter(codePath => (promptOwnersByCode.get(codePath) ?? []).some(owner => promptFilterSet.has(owner)))
    : prodCodePaths;
  for (const codePath of targetCodePaths) {
    const content = readSafeUtf8(realRoot, codePath);
    if (typeof content !== 'string') continue;
    for (const item of collectValidationCodeFindings(content, { path: codePath, kind: 'code', hasRealE2eCoverage: true })) {
      rawFindings.push({ ...item, defaultSeverity: 'warn' });
    }
    if (hasCustomCodeRules) {
      rawFindings.push(...evaluateCustomRulesOnFile(lintConfig.customRules, {
        filePath: codePath,
        kind: 'code',
        rawText: content,
      }));
    }
  }

  rawFindings.sort((a, b) => a.filePath.localeCompare(b.filePath) || a.line - b.line || (a.order ?? 0) - (b.order ?? 0) || a.code.localeCompare(b.code));

  const warnings = [];
  const errors = [];
  const findings = [];
  const seenFormatted = new Set();

  for (const item of rawFindings) {
    if (item.code !== 'lint-config-invalid') {
      if (lintConfig.disabledRules.has(item.code)) continue;
    }
    const severity = item.code === 'lint-config-invalid'
      ? 'error'
      : (lintConfig.ruleSeverities.get(item.code) ?? item.defaultSeverity ?? 'warn');
    if (severity === 'off') continue;

    const prefix = severity === 'error' ? 'Error' : 'Warning';
    const formatted = `${prefix}: ${item.category}: ${item.filePath}:${item.line} [${item.code}] ${item.detail}`;
    if (seenFormatted.has(formatted)) continue;
    seenFormatted.add(formatted);

    findings.push({
      path: item.filePath,
      line: item.line,
      code: item.code,
      category: item.category,
      severity,
      message: item.detail,
      formatted,
    });
    if (severity === 'error') errors.push(formatted);
    else warnings.push(formatted);
  }

  return {
    ok: errors.length === 0,
    configured: lintConfig.configured,
    warnings,
    errors,
    findings,
  };
}

export function lintRepoAntiPatterns({ root, files, promptPaths, tests, config } = {}) {
  return lintRepoProject({ root, files, promptPaths, tests, config }).warnings;
}
