// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// Built-in deterministic prompt hygiene rules: code fences, size, structure, dependency links & cycles.
import { formatTeachingDetail } from './diagnostics.mjs';
import {
  countFileLines,
  countPromptProseLines,
  extractDependencyLinks,
  hasNativeOnlyFrontmatter,
  hasRuntimeInterfaceMetadata,
  isMarkdownTableSeparator,
  scanMarkdownLinesAndFences,
  stripPromptMetadataPreservingLines,
} from './prompt-metadata.mjs';

const PROMPT_FENCE_LINE_LIMIT = 15;
const PROMPT_FENCE_TOTAL_LIMIT = 30;
const DIAGRAM_MIN_PROSE_LINES = 18;
const DIAGRAM_MIN_BRANCH_LINES = 5;

export const DECLARATIVE_SCHEMA_FENCE_LANGS = new Set([
  'sql', 'ddl', 'sqlite', 'postgres', 'postgresql', 'mysql',
  'openapi', 'yaml', 'yml', 'json', 'jsonc', 'jsonschema', 'json-schema',
  'protobuf', 'proto', 'graphql', 'gql', 'http', 'idl', 'schema',
  'avro', 'avsc', 'thrift', 'toml', 'xml', 'xsd', 'prisma',
]);

const IMPERATIVE_PATTERNS = [
  /(?<![\w$-])(?:export|const|let|def|impl)\s+/,
  /(?<![\w$-])function(?:\s+[A-Za-z_$]|\s*\(|\*)/,
  /(?<![\w$-])(?:if|for|while)\s*\(/,
  /(?<![\w$-])return(?:\s+|;|$)/,
  /(?<![\w$-])try\s*\{/,
  /=>/,
];

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

export function collectPromptCodeBlockFindings(text, { path = 'prompts/module.prompt.md' } = {}) {
  const isNativeOnly = hasNativeOnlyFrontmatter(text);
  const cleaned = stripPromptMetadataPreservingLines(text);
  const { fences } = scanMarkdownLinesAndFences(cleaned);
  const nonMermaid = fences.filter(f => f.lang !== 'mermaid' && f.lang !== 'pdd-boundary');
  if (!nonMermaid.length) return [];

  const records = [];
  const countedFences = [];
  let totalBodyLines = 0;

  for (const fence of nonMermaid) {
    if (isNativeOnly && DECLARATIVE_SCHEMA_FENCE_LANGS.has(fence.lang)) continue;
    countedFences.push(fence);
    const count = fence.bodyLines.length;
    totalBodyLines += count;
    if (count > PROMPT_FENCE_LINE_LIMIT) {
      records.push({
        line: fence.openLine,
        order: 1,
        code: 'prompt-code-fence-length',
        category: 'prompt code block',
        detail: `Non-mermaid code fence spans ${count} lines (recommended <= ${PROMPT_FENCE_LINE_LIMIT}). Replace long code or schema blocks with plain-English rules, a Markdown table, or a mermaid diagram.`,
        fix: `Trim the fenced block at ${path}:${fence.openLine} to <= ${PROMPT_FENCE_LINE_LIMIT} lines or replace it with a concise prose table`,
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
            fix: `Replace imperative code ("${token}") at ${path}:${item.lineNo} with observable behavioral rules in prose`,
          });
          break;
        }
      }
    }
  }

  if (totalBodyLines > PROMPT_FENCE_TOTAL_LIMIT && countedFences.length > 0) {
    const firstLine = countedFences[0].openLine;
    records.push({
      line: firstLine,
      order: 0,
      code: 'prompt-code-fence-total',
      category: 'prompt code block',
      detail: `Prompt contains ${totalBodyLines} non-mermaid fenced lines across ${countedFences.length} blocks (recommended <= ${PROMPT_FENCE_TOTAL_LIMIT} total). Move implementation details to tests or summarize contracts in prose and tables.`,
      fix: `Reduce total non-mermaid fenced lines in ${path} to <= ${PROMPT_FENCE_TOTAL_LIMIT}`,
    });
  }

  records.sort((a, b) => a.line - b.line || a.order - b.order);
  return records.map(r => ({
    ...r,
    filePath: path,
    defaultSeverity: 'warn',
    warning: `Warning: ${r.category}: ${path}:${r.line} [${r.code}] ${r.detail}`,
  }));
}

export const lintPromptCodeBlocks = (text, opts = {}) => collectPromptCodeBlockFindings(text, opts).map(r => r.warning);

export function collectPromptSizeFindings(promptText, codeFiles, { path = 'prompts/module.prompt.md', minCodeLines = 0 } = {}) {
  const rawList = Array.isArray(codeFiles) ? codeFiles : (codeFiles !== undefined && codeFiles !== null ? [codeFiles] : []);
  const entries = rawList
    .map(item => (typeof item === 'string' ? { path: '', text: item } : item))
    .filter(item => item && typeof item.text === 'string');
  if (!entries.length) return [];

  const promptLines = countPromptProseLines(promptText);
  const codeLines = entries.reduce((sum, item) => sum + countFileLines(item.text), 0);
  if (codeLines < minCodeLines || promptLines < codeLines) return [];

  const targetPaths = entries.map(item => item.path).filter(Boolean).join(', ') || 'owned code';
  const detail = `Prompt spans ${promptLines} lines while generated code (${targetPaths}) spans ${codeLines} lines. Keep prompt lines strictly smaller than generated code lines (< ${codeLines}) by stating domain decisions concisely instead of implementation detail.`;
  return [{
    filePath: path,
    line: 1,
    order: 0,
    code: 'prompt-larger-than-code',
    category: 'prompt size',
    defaultSeverity: 'warn',
    detail,
    fix: `Condense ${path} below ${codeLines} prose lines by removing implementation detail`,
    warning: `Warning: prompt size: ${path}:1 [prompt-larger-than-code] ${detail}`,
  }];
}

export const lintPromptSize = (promptText, codeFiles, opts = {}) => collectPromptSizeFindings(promptText, codeFiles, opts).map(r => r.warning);

export function collectPromptStructureFindings(text, { path = 'prompts/module.prompt.md', hasOwnedCode = false } = {}) {
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
    if (/^ {0,3}#\s+\S/.test(line)) { hasTitle = true; continue; }
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
    if (line.includes('|') && idx + 1 < proseLines.length && isMarkdownTableSeparator(proseLines[idx + 1].text)) hasMarkdownTable = true;
    if (/\b(?:if|when|whenever|unless|otherwise)\b/i.test(trimmed)) branchLines.push(lineNo);
    if (/\b(?:transitions?\s+(?:from|to)|moves?\s+from\s+\S+\s+to\s+\S+|state\s+machine)\b/i.test(trimmed)) stateTransitionLines.push(lineNo);
  }

  const hasMermaidFence = fences.some(f => f.lang === 'mermaid');
  const findings = [];
  if (!hasTitle) {
    const detail = 'Prompt has no top-level "# <Title>" heading. Start every prompt with "# <Title>" and a plain-English opening sentence.';
    findings.push({ filePath: path, line: 1, order: 0, code: 'prompt-missing-title', category: 'prompt structure', defaultSeverity: 'warn', detail, fix: `Add a top-level "# <Title>" heading to line 1 of ${path}`, warning: `Warning: prompt structure: ${path}:1 [prompt-missing-title] ${detail}` });
  }
  if (!hasDependenciesHeading && (hasOwnedCode || hasRuntimeInterface || hasPeerPromptLink || nonAppearanceH2Count >= 2)) {
    const detail = 'Prompt has no "## Dependencies" section. Add "## Dependencies" listing peer prompt links (or "None." when standalone).';
    findings.push({ filePath: path, line: 1, order: 1, code: 'prompt-missing-dependencies', category: 'prompt structure', defaultSeverity: 'warn', detail, fix: `Add a "## Dependencies" section to ${path}`, warning: `Warning: prompt structure: ${path}:1 [prompt-missing-dependencies] ${detail}` });
  }
  if (!hasMermaidFence && !hasSvgDrawing && !hasMarkdownTable && ((nonEmptyProseCount >= DIAGRAM_MIN_PROSE_LINES && branchLines.length >= DIAGRAM_MIN_BRANCH_LINES) || stateTransitionLines.length >= 3)) {
    const lineNo = stateTransitionLines[0] ?? branchLines[0] ?? 1;
    const detail = 'Prompt describes multi-branch or state-transition rules without a diagram or decision table. Add a ```mermaid``` diagram or Markdown table where applicable.';
    findings.push({ filePath: path, line: lineNo, order: 2, code: 'prompt-missing-diagram', category: 'prompt structure', defaultSeverity: 'warn', detail, fix: `Add a mermaid flowchart or decision table near ${path}:${lineNo}`, warning: `Warning: prompt structure: ${path}:${lineNo} [prompt-missing-diagram] ${detail}` });
  }
  findings.sort((a, b) => a.line - b.line || a.order - b.order);
  return findings;
}

export const lintPromptStructure = (text, opts = {}) => collectPromptStructureFindings(text, opts).map(r => r.warning);

export function collectPromptDependencyFindings({ targetPrompts, allVisibleFiles, getPromptText }) {
  const fileSet = new Set(allVisibleFiles);
  const dirSet = new Set();
  for (const file of allVisibleFiles) {
    let idx = file.indexOf('/');
    while (idx > 0) {
      dirSet.add(file.slice(0, idx));
      idx = file.indexOf('/', idx + 1);
    }
  }

  const findings = [];
  const adj = new Map();
  const edgeLine = new Map();
  const targetSet = new Set(targetPrompts);

  for (const promptPath of targetPrompts) {
    const content = getPromptText(promptPath);
    if (typeof content !== 'string') continue;
    const links = extractDependencyLinks(content, promptPath);
    const nextPrompts = [];
    for (const link of links) {
      const targetClean = link.target.replace(/\/+$/, '');
      const exists = link.canonical && (fileSet.has(targetClean) || dirSet.has(targetClean));
      if (!exists) {
        findings.push({
          filePath: promptPath,
          line: link.line,
          order: 2,
          code: 'broken-dependency-link',
          category: 'prompt dependency',
          defaultSeverity: 'error',
          detail: formatTeachingDetail({
            invariant: `Dependency link "${link.rawTarget}" resolves to "${targetClean}", which is not a Git-visible file or directory in this repository`,
            fix: `Update or remove the link "${link.rawTarget}" under "## Dependencies" in ${promptPath}`,
            rerun: 'pdd lint',
          }),
        });
      } else if (targetClean.endsWith('.prompt.md') && targetClean !== promptPath) {
        nextPrompts.push(targetClean);
        if (!edgeLine.has(`${promptPath}->${targetClean}`)) edgeLine.set(`${promptPath}->${targetClean}`, link.line);
      }
    }
    adj.set(promptPath, [...new Set(nextPrompts)].sort());
  }

  const state = new Map();
  const stack = [];
  const reported = new Set();
  const dfs = u => {
    state.set(u, 1);
    stack.push(u);
    for (const v of adj.get(u) ?? []) {
      if (!targetSet.has(v)) continue;
      if (state.get(v) === 1) {
        const cyclePath = [...stack.slice(stack.indexOf(v)), v];
        const key = `${u}->${v}`;
        if (!reported.has(key)) {
          reported.add(key);
          findings.push({
            filePath: u,
            line: edgeLine.get(key) ?? 1,
            order: 3,
            code: 'prompt-dependency-cycle',
            category: 'prompt dependency',
            defaultSeverity: 'warn',
            detail: `Prompt dependency cycle detected (${cyclePath.join(' -> ')}). Break the cycle by extracting a shared contract or inverting the dependency over an injected port.`,
            fix: `Break the dependency cycle "${u} -> ${v}" by extracting a shared contract or injecting a <port>.<op> interface`,
          });
        }
      } else if (!state.get(v)) dfs(v);
    }
    stack.pop();
    state.set(u, 2);
  };
  for (const promptPath of targetPrompts) if (!state.get(promptPath)) dfs(promptPath);
  return findings;
}
