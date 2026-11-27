// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// Pure structural & graph rules for prompts and Stories:
// # Title, ## Dependencies, exact-case relative CommonMark links, dependency cycles, and truncated fences/tables.
import { readdirSync } from 'node:fs';
import { join } from 'node:path';
import { formatTeachingDetail } from './diagnostics.mjs';
import {
  extractRelativeMarkdownLinks,
  hasRuntimeInterfaceMetadata,
  isMarkdownTableSeparator,
  isNativeOnlyPrompt,
  scanMarkdownLinesAndFences,
  splitMarkdownTableRow,
  stripFrontmatterPreservingLines,
  stripPromptMetadataPreservingLines,
} from './prompt-metadata.mjs';

function findExactCaseOnDisk(realRoot, relPath, dirCache) {
  if (!realRoot || !relPath) return { existsExact: false, actualCase: null };
  const parts = relPath.split('/');
  let cur = realRoot;
  const resolvedParts = [];
  let hadCaseMismatch = false;
  for (const part of parts) {
    let entries = dirCache.get(cur);
    if (!entries) {
      try { entries = readdirSync(cur); } catch { return { existsExact: false, actualCase: null }; }
      dirCache.set(cur, entries);
    }
    if (entries.includes(part)) {
      resolvedParts.push(part);
      cur = join(cur, part);
    } else {
      const lower = part.toLowerCase();
      const ci = entries.find(e => e.toLowerCase() === lower);
      if (!ci) return { existsExact: false, actualCase: null };
      hadCaseMismatch = true;
      resolvedParts.push(ci);
      cur = join(cur, ci);
    }
  }
  return { existsExact: !hadCaseMismatch, actualCase: hadCaseMismatch ? resolvedParts.join('/') : relPath };
}

/**
 * Detect truncated Markdown structures (unclosed fenced code blocks and truncated pipe table rows)
 * caused by CLI timeouts or partial writes.
 */
export function collectMarkdownIntegrityFindings(text, { path = 'prompts/module.prompt.md' } = {}) {
  const raw = String(text ?? '');
  const cleaned = stripFrontmatterPreservingLines(raw);
  const { fences, proseLines } = scanMarkdownLinesAndFences(cleaned);
  const findings = [];

  for (const fence of fences) {
    if (fence.closed === false) {
      const closer = fence.char.repeat(fence.len);
      const detail = `Unclosed fenced code block opened at line ${fence.openLine} (missing closing ${closer} before end of file; file may be truncated)`;
      findings.push({
        filePath: path,
        line: fence.openLine,
        order: 0,
        code: 'truncated-markdown-fence',
        category: 'markdown integrity',
        defaultSeverity: 'error',
        detail,
        fix: `Add a matching closing ${closer} fence or restore the truncated content in ${path}`,
      });
    }
  }

  for (let i = 0; i < proseLines.length - 1; i++) {
    const headerRow = proseLines[i];
    const sepRow = proseLines[i + 1];
    if (sepRow.lineNo !== headerRow.lineNo + 1) continue;
    if (!headerRow.text.includes('|') || !isMarkdownTableSeparator(sepRow.text)) continue;
    const sepCols = splitMarkdownTableRow(sepRow.text);
    if (!sepCols || sepCols.length < 2) continue;
    const headerTrimmed = headerRow.text.trim();
    const headerHasOuterPipes = headerTrimmed.startsWith('|') && headerTrimmed.endsWith('|') && !headerTrimmed.endsWith('\\|');
    let j = i + 2;
    let prevLine = sepRow.lineNo;
    while (j < proseLines.length) {
      const row = proseLines[j];
      const trimmed = row.text.trim();
      if (row.lineNo !== prevLine + 1 || !trimmed || /^#{1,6}[ \t]+/.test(trimmed) || !trimmed.startsWith('|')) break;
      const endsWithPipe = trimmed.endsWith('|') && !trimmed.endsWith('\\|');
      if (headerHasOuterPipes && !endsWithPipe) {
        const excerpt = trimmed.length <= 80 ? trimmed : `${trimmed.slice(0, 79)}…`;
        const detail = `Truncated Markdown pipe table row at line ${row.lineNo} ("${excerpt}") is missing its closing "|"`;
        findings.push({
          filePath: path,
          line: row.lineNo,
          order: 1,
          code: 'truncated-markdown-table',
          category: 'markdown integrity',
          defaultSeverity: 'error',
          detail,
          fix: `Complete or restore the truncated table row at ${path}:${row.lineNo} and close it with "|"`,
        });
      }
      prevLine = row.lineNo;
      j++;
    }
    i = j - 1;
  }

  findings.sort((a, b) => a.line - b.line || a.order - b.order);
  return findings;
}

/**
 * Flag malformed Operations table cells (Calls / Error codes) and inline Calls: entries
 * containing trailing parenthetical prose (e.g. `None (unknown inputs...)` or `` `store.save` (writes disk) ``)
 * that cause runtime Calls/Operations parsers to fail closed.
 */
export function collectOperationsTableIntegrityFindings(text, { path = 'prompts/module.prompt.md' } = {}) {
  const raw = String(text ?? '');
  const cleaned = stripFrontmatterPreservingLines(raw);
  const { proseLines } = scanMarkdownLinesAndFences(cleaned);
  const findings = [];
  let inOpsSection = false;

  const pushCellFinding = (lineNo, colHeader, rawCell) => {
    const excerpt = rawCell.length <= 80 ? rawCell : `${rawCell.slice(0, 79)}…`;
    const detail = `Malformed Operations "${colHeader}" cell "${excerpt}" contains trailing parenthetical prose; use plain syntax such as \`None\` or comma-separated identifiers (runtime Calls/Operations parsers reject extra words in parentheses).`;
    findings.push({
      filePath: path,
      line: lineNo,
      order: 2,
      code: 'prompt-malformed-operations-cell',
      category: 'operations integrity',
      defaultSeverity: 'error',
      detail,
      fix: `Remove the parenthetical prose from the "${colHeader}" cell at ${path}:${lineNo} (write plain \`None\` or comma-separated names, and move behavioral notes to prose below the table)`,
    });
  };

  for (let i = 0; i < proseLines.length; i++) {
    const cur = proseLines[i];
    const h2 = /^ {0,3}##\s+(.+)$/.exec(cur.text);
    if (h2) {
      const title = h2[1].trim();
      inOpsSection = /^(?:public\s+)?operations\b|^ports\b/i.test(title);
      continue;
    }

    if (i < proseLines.length - 1) {
      const sepRow = proseLines[i + 1];
      if (sepRow.lineNo === cur.lineNo + 1 && cur.text.includes('|') && isMarkdownTableSeparator(sepRow.text)) {
        const headerCols = splitMarkdownTableRow(cur.text);
        const sepCols = splitMarkdownTableRow(sepRow.text);
        if (headerCols && sepCols && sepCols.length >= 2) {
          const isOpsTable = inOpsSection || /^operation$/i.test(headerCols[0].trim());
          const callsCols = [];
          const errorCols = [];
          if (isOpsTable) {
            for (let c = 0; c < headerCols.length; c++) {
              const h = headerCols[c].trim();
              if (/^calls$/i.test(h)) callsCols.push({ idx: c, header: h });
              else if (/^errors?$|^error\s+codes?$/i.test(h)) errorCols.push({ idx: c, header: h });
            }
          }
          let j = i + 2;
          let prevLine = sepRow.lineNo;
          while (j < proseLines.length) {
            const row = proseLines[j];
            const trimmed = row.text.trim();
            if (row.lineNo !== prevLine + 1 || !trimmed || /^#{1,6}[ \t]+/.test(trimmed) || !trimmed.startsWith('|')) break;
            if (callsCols.length || errorCols.length) {
              const cells = splitMarkdownTableRow(row.text);
              if (cells) {
                for (const { idx, header } of callsCols) {
                  const cell = (cells[idx] ?? '').trim();
                  if (!cell) continue;
                  const cleanedCell = cell.replace(/\[[^\]]+\]\([^)\s]+\)/g, 'LINK').replace(/`[^`]*`/g, 'CODE');
                  if (/\(\s*[^()\s][^()]*\)/.test(cleanedCell)) pushCellFinding(row.lineNo, header, cell);
                }
                for (const { idx, header } of errorCols) {
                  const cell = (cells[idx] ?? '').trim();
                  if (!cell) continue;
                  if (/^(?:`?none`?|`?n\/a`?)\s*\(\s*[^()\s]/i.test(cell)) pushCellFinding(row.lineNo, header, cell);
                }
              }
            }
            prevLine = row.lineNo;
            j++;
          }
          i = j - 1;
          continue;
        }
      }
    }

    const inlineCalls = /^\s*(?:[-*+]\s+)?(?:\*\*)?Calls(?:\*\*)?:\s*(.+)$/i.exec(cur.text);
    if (inlineCalls) {
      const val = inlineCalls[1].trim();
      const cleanedVal = val.replace(/\[[^\]]+\]\([^)\s]+\)/g, 'LINK').replace(/`[^`]*`/g, 'CODE');
      if (/^(?:none|n\/a)\s*\(\s*[^()\s]|(?:CODE|[a-zA-Z_][\w-]*\.[a-zA-Z_][\w-]*)\s+\(\s*[^()\s]/i.test(cleanedVal)) {
        pushCellFinding(cur.lineNo, 'Calls', val);
      }
    }
  }

  findings.sort((a, b) => a.line - b.line || a.order - b.order);
  return findings;
}

export function collectPromptStructureFindings(text, { path = 'prompts/module.prompt.md', hasOwnedCode = false } = {}) {
  const raw = String(text ?? '');
  const hasRuntimeInterface = hasRuntimeInterfaceMetadata(raw);
  const cleaned = stripPromptMetadataPreservingLines(raw);
  const { proseLines } = scanMarkdownLinesAndFences(cleaned);

  let hasTitle = false;
  let hasDependenciesHeading = false;
  let nonAppearanceH2Count = 0;
  let hasPeerPromptLink = false;

  for (const { text: line } of proseLines) {
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
    if (/\]\([^)\s]*\.prompt\.md(?:#[^)\s]*)?\)/i.test(line)) hasPeerPromptLink = true;
  }

  const findings = [];
  if (!hasTitle) {
    const detail = 'Prompt has no top-level "# <Title>" heading. Start every prompt with "# <Title>" and a plain-English opening sentence.';
    findings.push({ filePath: path, line: 1, order: 0, code: 'prompt-missing-title', category: 'prompt structure', defaultSeverity: 'warn', detail, fix: `Add a top-level "# <Title>" heading to line 1 of ${path}`, warning: `Warning: prompt structure: ${path}:1 [prompt-missing-title] ${detail}` });
  }
  if (!hasDependenciesHeading && (hasOwnedCode || hasRuntimeInterface || hasPeerPromptLink || nonAppearanceH2Count >= 2)) {
    const detail = 'Prompt has no "## Dependencies" section. Add "## Dependencies" listing peer prompt links (or "None." when standalone).';
    findings.push({ filePath: path, line: 1, order: 1, code: 'prompt-missing-dependencies', category: 'prompt structure', defaultSeverity: 'warn', detail, fix: `Add a "## Dependencies" section to ${path}`, warning: `Warning: prompt structure: ${path}:1 [prompt-missing-dependencies] ${detail}` });
  }
  findings.sort((a, b) => a.line - b.line || a.order - b.order);
  return findings;
}

export const lintPromptStructure = (text, opts = {}) => collectPromptStructureFindings(text, opts).map(r => r.warning);

export function collectPromptDependencyFindings({ targetPrompts, allVisibleFiles, getPromptText, realRoot = null }) {
  const fileSet = new Set(allVisibleFiles);
  const lowerFileMap = new Map();
  const dirSet = new Set();
  const lowerDirMap = new Map();
  for (const file of allVisibleFiles) {
    const lf = file.toLowerCase();
    if (!lowerFileMap.has(lf)) lowerFileMap.set(lf, file);
    let idx = file.indexOf('/');
    while (idx > 0) {
      const dir = file.slice(0, idx);
      dirSet.add(dir);
      const ld = dir.toLowerCase();
      if (!lowerDirMap.has(ld)) lowerDirMap.set(ld, dir);
      idx = file.indexOf('/', idx + 1);
    }
  }
  const dirCache = new Map();

  const findings = [];
  const adj = new Map();
  const edgeLine = new Map();
  const targetSet = new Set(targetPrompts);
  const nativeOnlyCache = new Map();
  const isPromptNativeOnly = p => {
    if (nativeOnlyCache.has(p)) return nativeOnlyCache.get(p);
    const raw = getPromptText(p);
    const res = typeof raw === 'string' ? isNativeOnlyPrompt(raw) : false;
    nativeOnlyCache.set(p, res);
    return res;
  };

  for (const promptPath of targetPrompts) {
    const content = getPromptText(promptPath);
    if (typeof content !== 'string') continue;
    const links = extractRelativeMarkdownLinks(content, promptPath);
    const nextPrompts = [];
    const seenInvertedTargets = new Set();
    for (const link of links) {
      const targetClean = link.target.replace(/\/+$/, '');
      const inIndex = link.canonical && (fileSet.has(targetClean) || dirSet.has(targetClean));
      let diskCheck = null;
      if (inIndex && realRoot) {
        diskCheck = findExactCaseOnDisk(realRoot, targetClean, dirCache);
      }
      const exactOk = inIndex && (!diskCheck || diskCheck.existsExact);
      if (!exactOk) {
        const ciMatch = diskCheck?.actualCase
          ?? (link.canonical ? (lowerFileMap.get(targetClean.toLowerCase()) ?? lowerDirMap.get(targetClean.toLowerCase()) ?? null) : null)
          ?? (link.canonical && realRoot ? findExactCaseOnDisk(realRoot, targetClean, dirCache).actualCase : null);
        const isDep = link.inDependencies;
        const code = isDep ? 'broken-dependency-link' : 'broken-relative-link';
        const category = isDep ? 'prompt dependency' : 'prompt link';
        const invariant = ciMatch && ciMatch !== targetClean
          ? `${isDep ? 'Dependency' : 'Relative'} link "${link.rawTarget}" resolves to "${targetClean}", which has wrong letter case (actual path on disk is "${ciMatch}"; fails on case-sensitive Linux CI)`
          : `${isDep ? 'Dependency' : 'Relative'} link "${link.rawTarget}" resolves to "${targetClean}", which is not a Git-visible file or directory in this repository`;
        const fix = ciMatch && ciMatch !== targetClean
          ? `Fix the letter case of "${link.rawTarget}" in ${promptPath}:${link.line} to match "${ciMatch}"`
          : `Update or remove the broken link "${link.rawTarget}" in ${promptPath}:${link.line}`;
        findings.push({
          filePath: promptPath,
          line: link.line,
          order: 2,
          code,
          category,
          defaultSeverity: 'error',
          detail: formatTeachingDetail({ invariant, fix, rerun: 'pdd lint' }),
        });
      } else if (targetClean.endsWith('.prompt.md') && targetClean !== promptPath) {
        if (
          link.inDependencies
          && !seenInvertedTargets.has(targetClean)
          && !isPromptNativeOnly(promptPath)
          && isPromptNativeOnly(targetClean)
        ) {
          seenInvertedTargets.add(targetClean);
          findings.push({
            filePath: promptPath,
            line: link.line,
            order: 3,
            code: 'inverted-native-only-dependency',
            category: 'prompt dependency',
            defaultSeverity: 'warn',
            detail: formatTeachingDetail({
              invariant: `Checkable prompt "${promptPath}" depends on native-only prompt "${targetClean}" (layering inversion: pure/checkable domain prompts must not import native-only host/IO adapters)`,
              fix: `Invert the dependency by declaring an injected port in ${promptPath} and having ${targetClean} depend on ${promptPath} instead, or mark ${promptPath} with \`kind: native-only\` if it genuinely owns host IO`,
              rerun: 'pdd lint',
            }),
          });
        }
        if (!link.inCallerNavigation) {
          nextPrompts.push(targetClean);
          const key = `${promptPath}->${targetClean}`;
          if (!edgeLine.has(key) || link.inDependencies) edgeLine.set(key, link.line);
        }
      }
    }
    adj.set(promptPath, [...new Set(nextPrompts)].sort());
  }

  const getAdj = u => {
    if (adj.has(u)) return adj.get(u);
    const content = getPromptText(u);
    if (typeof content !== 'string') { adj.set(u, []); return []; }
    const next = [];
    for (const link of extractRelativeMarkdownLinks(content, u)) {
      if (link.inCallerNavigation || !link.canonical) continue;
      const targetClean = link.target.replace(/\/+$/, '');
      if (!targetClean.endsWith('.prompt.md') || targetClean === u || !fileSet.has(targetClean)) continue;
      next.push(targetClean);
      const key = `${u}->${targetClean}`;
      if (!edgeLine.has(key) || link.inDependencies) edgeLine.set(key, link.line);
    }
    const deduped = [...new Set(next)].sort();
    adj.set(u, deduped);
    return deduped;
  };

  const state = new Map();
  const stack = [];
  const reported = new Set();
  const dfs = u => {
    state.set(u, 1);
    stack.push(u);
    for (const v of getAdj(u)) {
      if (state.get(v) === 1) {
        const cyclePath = [...stack.slice(stack.indexOf(v)), v];
        if (!cyclePath.some(node => targetSet.has(node))) continue;
        let reportFrom = u;
        let reportTo = v;
        if (!targetSet.has(reportFrom)) {
          const idx = cyclePath.findIndex(node => targetSet.has(node));
          reportFrom = cyclePath[idx];
          reportTo = cyclePath[idx + 1] ?? v;
        }
        const key = `${reportFrom}->${reportTo}`;
        if (!reported.has(key)) {
          reported.add(key);
          findings.push({
            filePath: reportFrom,
            line: edgeLine.get(key) ?? 1,
            order: 4,
            code: 'prompt-dependency-cycle',
            category: 'prompt dependency',
            defaultSeverity: 'warn',
            detail: `Prompt dependency cycle detected (${cyclePath.join(' -> ')}). Break the cycle by extracting a shared contract or inverting the dependency over an injected port.`,
            fix: `Break the dependency cycle "${reportFrom} -> ${reportTo}" by extracting a shared contract or injecting a <port>.<op> interface`,
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
