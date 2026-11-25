// Prompt: prompts/cli/rule-coverage.prompt.md

// Layer-1 mechanical Rule-to-Proof traceability for diff-changed ## Domain decisions and ## Rules to check.
import { spawnSync } from 'node:child_process';
import { realpathSync } from 'node:fs';
import { posix } from 'node:path';
import { isTestOwnedPath, isTestPromptPath } from '../file-owner.mjs';
import { isLintableStoryPath } from '../story-lint.mjs';
import { gitFiles } from '../shared/git-context.mjs';
import { TEST_SCENARIO_JSON_RE } from '../shared/test-paths.mjs';
import { FORMAL_TEST_FILE_RE } from './formal-verify.mjs';
import { canonicalRepoPath, formatTeachingDetail, readSafeUtf8, resolveDefaultBaseRef } from './lint/diagnostics.mjs';
import {
  isMarkdownTableSeparator,
  scanMarkdownLinesAndFences,
  stripPromptMetadataPreservingLines,
} from './lint/prompt-metadata.mjs';

const FIXTURE_OR_UTIL_DIR_RE = /(?:^|\/)(?:fixtures|__fixtures__|mocks|__mocks__|helpers|__snapshots__|node_modules|\.git)\//i;
const FIXTURE_DOC_DIR_RE = /(?:^|\/)(?:fixtures|__fixtures__)\//i;
const TEST_CODE_EXT_RE = /\.(?:mjs|cjs|js|ts|tsx|jsx|py|go|rs|java|kt|rb|c|cc|cpp|cs|swift|scala|php|sh)$/i;
const TOOLING_CONFIG_JSON = new Set([
  'jsconfig.json', 'package.json', 'package-lock.json', 'npm-shrinkwrap.json', 'composer.json',
  'biome.json', 'deno.json', 'jsr.json', 'eslint.json', 'prettier.json', 'vitest.json', 'jest.json', 'babel.json',
]);

const EXCLUDED_STANDARD_TOKEN_RE = /^(?:UTF-(?:8|16|32)|SHA-(?:1|256|384|512)|ISO-8601|RFC-\d+|TLS-\d+|ECMA-\d+)$/;
const HYPHEN_RULE_ID_RE = /^[A-Z]{1,12}(?:-[A-Z0-9]{1,8})+$/;
const UNDERSCORE_RULE_ID_RE = /^[A-Z]{1,10}(?:_[A-Z0-9]{1,8})+$/;
const COMPACT_RULE_ID_RE = /^[A-Z]{1,6}\d{1,5}$/;

const DOMAIN_DECISIONS_HEADING_RE = /^ {0,3}##[ \t]+Domain[ \t]+decisions[ \t]*#*$/i;
const RULES_TO_CHECK_HEADING_RE = /^ {0,3}##[ \t]+Rules[ \t]+to[ \t]+check[ \t]*#*$/i;
const LEVEL_1_OR_2_HEADING_RE = /^ {0,3}#{1,2}[ \t]+\S/;
const LIST_ITEM_RE = /^([ \t]*)(?:[-*+]|\d+[.)])[ \t]+(.+)$/;
const TABLE_ID_PRIMARY_COL_RE = /^(?:rule\s*id|id|code|ref|key)$/;
const TABLE_ID_SECONDARY_COL_RE = /^rule$/;

const TIER_ORDER = Object.freeze(['formal', 'scenario', 'native']);
const TIER_RANK = Object.freeze({ formal: 0, scenario: 1, native: 2 });
const SUBSTANTIVE_REASON_RE = /[\p{L}\p{N}]{2,}/u;
const MAX_DISPLAY_TEXT_CHARS = 240;

const escapeRegex = value => String(value).replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
const collapseSpaces = value => String(value ?? '').replace(/\s+/g, ' ').trim();
const isPlainObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);

function splitTableRowEscaped(line) {
  let trimmed = String(line ?? '').trim();
  if (!trimmed.includes('|')) return null;
  if (trimmed.startsWith('|')) trimmed = trimmed.slice(1);
  if (trimmed.endsWith('|') && !trimmed.endsWith('\\|')) trimmed = trimmed.slice(0, -1);
  const cells = [];
  let cur = '';
  for (let i = 0; i < trimmed.length; i++) {
    if (trimmed[i] === '\\' && trimmed[i + 1] === '|') {
      cur += '|';
      i += 1;
      continue;
    }
    if (trimmed[i] === '|') {
      cells.push(cur.trim());
      cur = '';
      continue;
    }
    cur += trimmed[i];
  }
  cells.push(cur.trim());
  return cells;
}

function unwrapRuleToken(raw) {
  let text = String(raw ?? '').trim().replace(/:+$/, '').trim();
  for (let i = 0; i < 4; i++) {
    const prev = text;
    if (text.startsWith('**') && text.endsWith('**') && text.length > 4) text = text.slice(2, -2).trim();
    else if (text.startsWith('__') && text.endsWith('__') && text.length > 4) text = text.slice(2, -2).trim();
    else if (text.startsWith('`') && text.endsWith('`') && text.length > 2) text = text.slice(1, -1).trim();
    else if (text.startsWith('*') && text.endsWith('*') && text.length > 2) text = text.slice(1, -1).trim();
    else if (text.startsWith('[') && text.endsWith(']') && text.length > 2) text = text.slice(1, -1).trim();
    text = text.replace(/:+$/, '').trim();
    if (text === prev) break;
  }
  return text;
}

export function isExplicitRuleId(token) {
  const clean = unwrapRuleToken(token);
  if (!clean || clean.length > 32 || EXCLUDED_STANDARD_TOKEN_RE.test(clean)) return false;
  if (HYPHEN_RULE_ID_RE.test(clean)) {
    const segments = clean.split('-').slice(1);
    return segments.some(seg => /\d/.test(seg) || /^[A-Z]$/.test(seg));
  }
  if (UNDERSCORE_RULE_ID_RE.test(clean)) {
    return /\d/.test(clean);
  }
  return COMPACT_RULE_ID_RE.test(clean);
}

function isInsideBackticksOrDoubleQuotes(text, index) {
  let backtickRun = 0;
  let inDoubleQuote = false;
  let i = 0;
  while (i < index) {
    const ch = text[i];
    if (ch === '`' && !inDoubleQuote) {
      let runEnd = i;
      while (runEnd < text.length && text[runEnd] === '`') runEnd += 1;
      const runLen = runEnd - i;
      if (runEnd > index) return true;
      if (backtickRun === 0) backtickRun = runLen;
      else if (runLen === backtickRun) backtickRun = 0;
      i = runEnd;
      continue;
    }
    if (ch === '"' && backtickRun === 0 && (i === 0 || text[i - 1] !== '\\')) {
      inDoubleQuote = !inDoubleQuote;
    }
    i += 1;
  }
  return backtickRun > 0 || inDoubleQuote;
}

function sliceBalancedParenContent(raw) {
  let depth = 1;
  for (let i = 0; i < raw.length; i++) {
    if (raw[i] === '(') depth += 1;
    else if (raw[i] === ')') {
      depth -= 1;
      if (depth === 0) return raw.slice(0, i);
    }
  }
  return raw;
}

function cleanNotProvedReason(raw, openedWithParen = false) {
  let reason = openedWithParen ? sliceBalancedParenContent(String(raw ?? '')) : String(raw ?? '');
  reason = collapseSpaces(reason)
    .replace(/^\*{1,2}\s*/, '')
    .replace(/^[-—–:,;]+\s*/, '')
    .replace(/\s*[.;,]+$/, '')
    .replace(/^\*{1,2}|\*{1,2}$/g, '')
    .trim();
  return SUBSTANTIVE_REASON_RE.test(reason) ? reason : null;
}

function extractInlineNotProvedReason(text) {
  const raw = String(text ?? '');
  const re = /\bNot\s+proved\s*:\s*\*{0,2}\s*([^\r\n|]*)/gi;
  let match;
  while ((match = re.exec(raw)) !== null) {
    if (isInsideBackticksOrDoubleQuotes(raw, match.index)) continue;
    const before = raw.slice(0, match.index).replace(/\*{1,2}\s*$/, '').trimEnd();
    const openedWithParen = before.endsWith('(');
    const reason = cleanNotProvedReason(match[1], openedWithParen);
    if (reason) return reason;
  }
  return null;
}

function extractInlineIdPrefix(text) {
  const body = String(text ?? '').trim();
  if (!body) return null;

  const patterns = [
    /^\*\*`?([^`*:\r\n]+?)`?:?\*\*(?:\s*(?::|—|–|-\s+)\s*|\s+)(.*)$/,
    /^`([^`\r\n]+)`\s*(?::|—|–|-\s+)\s*(.*)$/,
    /^\[([^\]\r\n]+)\]\s*(?:(?::|—|–|-)\s*)?(.*)$/,
    /^([A-Za-z0-9_-]+)\s*(?::|—|–|\s+-\s+)\s*(.*)$/,
  ];

  for (const re of patterns) {
    const match = re.exec(body);
    if (!match) continue;
    const candidate = unwrapRuleToken(match[1]);
    if (isExplicitRuleId(candidate)) {
      return { id: candidate, rest: collapseSpaces(match[2]) };
    }
  }
  return null;
}

function normalizeHeaderCell(cell) {
  return collapseSpaces(String(cell ?? '').replace(/[`*_~]/g, '')).toLowerCase();
}

function pickTableIdColumn(headerCells) {
  const normalized = headerCells.map(normalizeHeaderCell);
  const primary = normalized.findIndex(h => TABLE_ID_PRIMARY_COL_RE.test(h));
  if (primary >= 0) return primary;
  const secondary = normalized.findIndex(h => TABLE_ID_SECONDARY_COL_RE.test(h));
  if (secondary >= 0) return secondary;
  return 0;
}

function extractDocLevelNotProvedMap(proseLines) {
  const map = new Map();
  const re = /\b[Nn][Oo][Tt]\s+[Pp][Rr][Oo][Vv][Ee][Dd]\s*:\s*(?:\*\*|`)?([A-Z][A-Z0-9_-]{1,31})(?:\*\*|`)?\s*(?:\(([^)\r\n]+)\)|(?::|—|–|\s+-\s+)\s*([^\r\n]+))/g;
  for (const { text } of proseLines) {
    re.lastIndex = 0;
    let match;
    while ((match = re.exec(text)) !== null) {
      if (isInsideBackticksOrDoubleQuotes(text, match.index)) continue;
      const id = unwrapRuleToken(match[1]);
      if (!isExplicitRuleId(id)) continue;
      const reason = cleanNotProvedReason(match[2] ?? match[3] ?? '', false);
      if (reason && !map.has(id)) map.set(id, reason);
    }
  }
  return map;
}

function resolveDocKind(sourcePath, fileKind) {
  if (fileKind === 'prompt' || fileKind === 'story') return fileKind;
  if (typeof sourcePath === 'string' && sourcePath.endsWith('.prompt.md')) return 'prompt';
  if (isLintableStoryPath(sourcePath)) return 'story';
  return null;
}

function extractRulesInternal(markdown, { sourcePath = '', fileKind } = {}) {
  const resolvedKind = resolveDocKind(sourcePath, fileKind);
  if (!resolvedKind || typeof markdown !== 'string' || !markdown.trim()) return [];

  const targetHeadingRe = resolvedKind === 'prompt' ? DOMAIN_DECISIONS_HEADING_RE : RULES_TO_CHECK_HEADING_RE;
  const sectionName = resolvedKind === 'prompt' ? 'Domain decisions' : 'Rules to check';
  const cleaned = resolvedKind === 'prompt' ? stripPromptMetadataPreservingLines(markdown) : markdown;
  const { proseLines } = scanMarkdownLinesAndFences(cleaned);
  const docNotProved = extractDocLevelNotProvedMap(proseLines);

  const rawRules = [];
  let inSection = false;
  let i = 0;

  while (i < proseLines.length) {
    const cur = proseLines[i];
    const trimmed = cur.text.trim();

    if (LEVEL_1_OR_2_HEADING_RE.test(cur.text)) {
      inSection = targetHeadingRe.test(cur.text);
      i += 1;
      continue;
    }

    if (!inSection || !trimmed) {
      i += 1;
      continue;
    }

    // Markdown table: header row immediately followed by separator row.
    if (
      cur.text.includes('|')
      && i + 1 < proseLines.length
      && proseLines[i + 1].lineNo === cur.lineNo + 1
      && isMarkdownTableSeparator(proseLines[i + 1].text)
    ) {
      const headerCells = splitTableRowEscaped(cur.text) ?? [];
      const idCol = pickTableIdColumn(headerCells);
      let prevLineNo = proseLines[i + 1].lineNo;
      i += 2;
      while (i < proseLines.length) {
        const row = proseLines[i];
        const rowTrimmed = row.text.trim();
        if (row.lineNo !== prevLineNo + 1 || !rowTrimmed || LEVEL_1_OR_2_HEADING_RE.test(row.text) || !row.text.includes('|')) break;
        prevLineNo = row.lineNo;
        if (isMarkdownTableSeparator(row.text)) {
          i += 1;
          continue;
        }
        const cells = splitTableRowEscaped(row.text) ?? [];
        const idCell = cells[idCol] ?? '';
        const directId = unwrapRuleToken(idCell);
        let id = null;
        let inlineRest = '';
        if (isExplicitRuleId(directId)) {
          id = directId;
        } else {
          const prefixed = extractInlineIdPrefix(idCell);
          if (prefixed) {
            id = prefixed.id;
            inlineRest = prefixed.rest;
          }
        }
        if (id) {
          let notProvedReason = null;
          const descParts = [];
          if (inlineRest) descParts.push(inlineRest);
          for (let c = 0; c < cells.length; c++) {
            const cellText = collapseSpaces(cells[c]);
            if (!notProvedReason) {
              const found = extractInlineNotProvedReason(cellText);
              if (found) notProvedReason = found;
            }
            if (c === idCol || !cellText) continue;
            if (/^\(?Not\s+proved\s*:/i.test(cellText)) continue;
            descParts.push(cellText);
          }
          const fullText = collapseSpaces(descParts.join(' — '));
          rawRules.push({
            id,
            source: sourcePath,
            line: row.lineNo,
            section: sectionName,
            text: fullText.slice(0, MAX_DISPLAY_TEXT_CHARS),
            fullText,
            not_proved_reason: notProvedReason,
          });
        }
        i += 1;
      }
      continue;
    }

    // List item bullet with explicit leading rule ID.
    const bulletMatch = LIST_ITEM_RE.exec(cur.text);
    if (bulletMatch) {
      const baseIndent = bulletMatch[1].replace(/\t/g, '  ').length;
      const prefixed = extractInlineIdPrefix(bulletMatch[2]);
      if (prefixed) {
        const textParts = [prefixed.rest];
        let notProvedReason = extractInlineNotProvedReason(bulletMatch[2]);
        let prevLineNo = cur.lineNo;
        let nextIdx = i + 1;
        while (nextIdx < proseLines.length) {
          const nxt = proseLines[nextIdx];
          if (nxt.lineNo !== prevLineNo + 1 || !nxt.text.trim()) break;
          if (LEVEL_1_OR_2_HEADING_RE.test(nxt.text)) break;
          const indent = (/^[ \t]*/.exec(nxt.text)?.[0] ?? '').replace(/\t/g, '  ').length;
          if (indent <= baseIndent) break;
          prevLineNo = nxt.lineNo;
          const stripped = nxt.text.trim().replace(/^(?:[-*+]|\d+[.)])\s+/, '');
          if (!notProvedReason) notProvedReason = extractInlineNotProvedReason(stripped);
          textParts.push(stripped);
          nextIdx += 1;
        }
        const fullText = collapseSpaces(textParts.join(' '));
        rawRules.push({
          id: prefixed.id,
          source: sourcePath,
          line: cur.lineNo,
          section: sectionName,
          text: fullText.slice(0, MAX_DISPLAY_TEXT_CHARS),
          fullText,
          not_proved_reason: notProvedReason,
        });
        i = nextIdx;
        continue;
      }
    }

    i += 1;
  }

  // Deduplicate by ID per file (preserving first line; merging later substantive Not proved reason).
  const byId = new Map();
  for (const rule of rawRules) {
    const existing = byId.get(rule.id);
    if (!existing) {
      const reason = rule.not_proved_reason ?? docNotProved.get(rule.id) ?? null;
      byId.set(rule.id, { ...rule, not_proved_reason: reason });
    } else if (!existing.not_proved_reason && rule.not_proved_reason) {
      existing.not_proved_reason = rule.not_proved_reason;
    }
  }
  return [...byId.values()];
}

const stripInternalRuleFields = ({ fullText: _fullText, ...pub }) => pub;

export function extractRulesFromMarkdown(markdown, opts = {}) {
  return extractRulesInternal(markdown, opts).map(stripInternalRuleFields);
}

export function diffChangedRules(changedDocs = []) {
  if (!Array.isArray(changedDocs) || changedDocs.length === 0) return [];
  const changed = [];

  for (const doc of changedDocs) {
    if (!doc || typeof doc !== 'object') continue;
    const sourcePath = typeof doc.path === 'string' ? doc.path.trim().replace(/^\.\//, '') : '';
    if (!sourcePath) continue;
    const explicitKind = doc.fileKind === 'prompt' || doc.fileKind === 'story' ? doc.fileKind : undefined;
    if (!explicitKind && (FIXTURE_DOC_DIR_RE.test(sourcePath) || (sourcePath.endsWith('.prompt.md') && isTestPromptPath(sourcePath)))) {
      continue;
    }
    const afterText = typeof doc.after === 'string' ? doc.after : '';
    if (!afterText.trim()) continue;

    const afterRules = extractRulesInternal(afterText, { sourcePath, fileKind: explicitKind });
    if (afterRules.length === 0) continue;

    const beforeText = typeof doc.before === 'string' ? doc.before : '';
    const beforeRules = beforeText.trim()
      ? extractRulesInternal(beforeText, { sourcePath, fileKind: explicitKind })
      : [];
    const beforeById = new Map(beforeRules.map(r => [r.id, r]));

    for (const rule of afterRules) {
      const prev = beforeById.get(rule.id);
      if (!prev || prev.fullText !== rule.fullText || prev.not_proved_reason !== rule.not_proved_reason) {
        changed.push(stripInternalRuleFields(rule));
      }
    }
  }

  changed.sort((a, b) => a.source.localeCompare(b.source) || a.line - b.line || a.id.localeCompare(b.id));
  return changed;
}

export function classifyTestFileKind(filePath) {
  if (!canonicalRepoPath(filePath)) return null;
  if (FIXTURE_OR_UTIL_DIR_RE.test(filePath)) return null;
  if (/\.(?:snap|md|txt)$/i.test(filePath)) return null;
  if (FORMAL_TEST_FILE_RE.test(filePath)) return 'formal';
  if (TEST_SCENARIO_JSON_RE.test(filePath)) {
    const base = posix.basename(filePath).toLowerCase();
    if (TOOLING_CONFIG_JSON.has(base) || base.startsWith('tsconfig') || base === 'cases.json' || base.endsWith('-cases.json')) {
      return null;
    }
    return 'scenario';
  }
  if (isTestOwnedPath(filePath) && TEST_CODE_EXT_RE.test(filePath)) return 'native';
  return null;
}

function buildRuleMatcher(ruleId) {
  if (ruleId.includes('-') || ruleId.includes('_')) {
    const parts = ruleId.split(/[-_]/).map(escapeRegex);
    return new RegExp(`(?<![A-Za-z0-9])${parts.join('[-_]')}(?![A-Za-z0-9])`, 'i');
  }
  return new RegExp(`(?<![A-Za-z0-9])${escapeRegex(ruleId)}(?![A-Za-z0-9])`);
}

function collectScenarioTraceableStrings(doc) {
  if (!isPlainObject(doc) || !Array.isArray(doc.steps)) return null;
  const strings = [];
  const pushStr = val => {
    if (typeof val === 'string' && val.trim()) strings.push(val);
  };
  const pushList = list => {
    if (!Array.isArray(list)) return;
    for (const item of list) pushStr(item);
  };

  pushStr(doc.description);
  pushStr(doc.name);
  pushStr(doc.title);
  pushList(doc.rules);
  pushList(doc.rule_ids);

  if (Array.isArray(doc.criteria)) {
    for (const crit of doc.criteria) {
      if (typeof crit === 'string') pushStr(crit);
      else if (isPlainObject(crit)) {
        pushStr(crit.id);
        pushStr(crit.text);
        pushStr(crit.rule_id);
        pushStr(crit.description);
      }
    }
  }

  for (const step of doc.steps) {
    if (!isPlainObject(step)) continue;
    pushStr(step.id);
    pushStr(step.step_id);
    pushStr(step.name);
    pushStr(step.description);
    pushStr(step.rule_id);
    pushList(step.rule_ids);
    pushList(step.rules);
    pushList(step.tags);

    if (isPlainObject(step.checks)) {
      for (const [key, val] of Object.entries(step.checks)) {
        pushStr(key);
        if (Array.isArray(val)) {
          for (const check of val) {
            if (isPlainObject(check)) {
              pushStr(check.criterion_id);
              pushStr(check.rule_id);
              pushStr(check.description);
              pushStr(check.note);
              pushStr(check.label);
            }
          }
        }
      }
    } else if (Array.isArray(step.checks)) {
      for (const check of step.checks) {
        if (isPlainObject(check)) {
          pushStr(check.criterion_id);
          pushStr(check.rule_id);
          pushStr(check.description);
          pushStr(check.note);
          pushStr(check.label);
        }
      }
    }
  }

  return strings;
}

function findFirstMatchingLine(lines, matcher, preferredStrings = null) {
  if (Array.isArray(preferredStrings) && preferredStrings.length > 0) {
    for (let i = 0; i < lines.length; i++) {
      if (matcher.test(lines[i]) && preferredStrings.some(s => lines[i].includes(s))) {
        return i + 1;
      }
    }
  }
  for (let i = 0; i < lines.length; i++) {
    if (matcher.test(lines[i])) return i + 1;
  }
  return 1;
}

export function findRuleReferencesInFiles(ruleIds = [], testFiles = []) {
  const uniqueIds = [...new Set((Array.isArray(ruleIds) ? ruleIds : []).filter(id => typeof id === 'string' && id.trim()))];
  const evidenceById = Object.fromEntries(uniqueIds.map(id => [id, []]));
  if (uniqueIds.length === 0 || !Array.isArray(testFiles) || testFiles.length === 0) return evidenceById;

  const matchers = uniqueIds.map(id => ({ id, re: buildRuleMatcher(id) }));

  for (const file of testFiles) {
    if (!file || typeof file !== 'object') continue;
    const filePath = typeof file.path === 'string' ? file.path.trim().replace(/^\.\//, '') : '';
    const content = typeof file.content === 'string' ? file.content : '';
    if (!filePath || !content) continue;

    // Production source files, prompts, Stories, fixtures, and docs MUST never count as test evidence.
    const detectedKind = classifyTestFileKind(filePath);
    if (!detectedKind) continue;
    const kind = file.kind === 'formal' || file.kind === 'scenario' || file.kind === 'native'
      ? file.kind
      : detectedKind;

    const lines = content.split(/\r?\n/);

    if (kind === 'scenario') {
      let parsed = null;
      try { parsed = JSON.parse(content); } catch { parsed = null; }
      const traceable = collectScenarioTraceableStrings(parsed);
      if (!traceable) continue;
      for (const { id, re } of matchers) {
        const matchedStrings = traceable.filter(s => re.test(s));
        if (matchedStrings.length === 0) continue;
        const line = findFirstMatchingLine(lines, re, matchedStrings);
        evidenceById[id].push({ path: filePath, line, kind: 'scenario' });
      }
      continue;
    }

    for (const { id, re } of matchers) {
      if (!re.test(content)) continue;
      const line = findFirstMatchingLine(lines, re);
      evidenceById[id].push({ path: filePath, line, kind });
    }
  }

  for (const id of uniqueIds) {
    const seen = new Set();
    const deduped = [];
    for (const entry of evidenceById[id]) {
      const key = `${entry.kind}\0${entry.path}`;
      if (seen.has(key)) continue;
      seen.add(key);
      deduped.push(entry);
    }
    deduped.sort((a, b) => (TIER_RANK[a.kind] - TIER_RANK[b.kind]) || a.path.localeCompare(b.path) || (a.line - b.line));
    evidenceById[id] = deduped;
  }

  return evidenceById;
}

export function formatRuleCoverageWarnings(rules = []) {
  if (!Array.isArray(rules) || rules.length === 0) return [];
  const warnings = [];
  for (const row of rules) {
    if (!row || row.status !== 'uncovered') continue;
    const detail = formatTeachingDetail({
      invariant: `Changed rule "${row.id}" in "## ${row.section}" has no traceable formal, scenario, or native test and no "Not proved:" rationale`,
      fix: `Reference "${row.id}" in a formal, scenario, or native test or add "Not proved: <reason>" to ${row.source}:${row.line}`,
      rerun: 'pdd lint --diff',
    });
    warnings.push(`Warning: rule coverage: ${row.source}:${row.line} [rule-coverage-uncovered] ${detail}`);
  }
  return warnings;
}

export function formatRuleCoverageSummary(result) {
  if (!result || !Array.isArray(result.rules) || result.rules.length === 0) return '';
  const summary = result.summary ?? {
    total: result.rules.length,
    covered: result.rules.filter(r => r.status === 'covered').length,
    not_proved: result.rules.filter(r => r.status === 'not_proved').length,
    uncovered: result.rules.filter(r => r.status === 'uncovered').length,
  };
  const traced = summary.covered + summary.not_proved;
  const uncoveredIds = result.rules.filter(r => r.status === 'uncovered').map(r => r.id);
  if (uncoveredIds.length > 0) {
    const listed = uncoveredIds.slice(0, 6).join(', ');
    const more = uncoveredIds.length > 6 ? `, +${uncoveredIds.length - 6} more` : '';
    return `Rule coverage: ${traced}/${summary.total} traced (${summary.covered} covered, ${summary.not_proved} not proved, ${summary.uncovered} uncovered: ${listed}${more})`;
  }
  return `Rule coverage: ${traced}/${summary.total} traced (${summary.covered} covered, ${summary.not_proved} not proved, 0 uncovered)`;
}

export function evaluateRuleCoverage({ changedDocs = [], testFiles = [] } = {}) {
  const empty = { rules: [], summary: { total: 0, covered: 0, not_proved: 0, uncovered: 0 }, warnings: [] };
  const changedRules = diffChangedRules(changedDocs);
  if (changedRules.length === 0) return empty;

  const refsById = findRuleReferencesInFiles(changedRules.map(r => r.id), testFiles);
  let covered = 0;
  let notProved = 0;
  let uncovered = 0;

  const rules = changedRules.map(rule => {
    const evidence = refsById[rule.id] ?? [];
    const tiers = TIER_ORDER.filter(tier => evidence.some(e => e.kind === tier));
    const status = evidence.length > 0 ? 'covered' : (rule.not_proved_reason ? 'not_proved' : 'uncovered');
    if (status === 'covered') covered += 1;
    else if (status === 'not_proved') notProved += 1;
    else uncovered += 1;

    return {
      id: rule.id,
      source: rule.source,
      line: rule.line,
      section: rule.section,
      text: rule.text,
      status,
      tiers,
      evidence,
      not_proved_reason: rule.not_proved_reason,
    };
  });

  const summary = { total: rules.length, covered, not_proved: notProved, uncovered };
  const warnings = formatRuleCoverageWarnings(rules);
  return { rules, summary, warnings };
}

function resolveMergeBaseSha(realRoot, baseRef) {
  const target = baseRef || resolveDefaultBaseRef(realRoot);
  if (!target) return null;
  const rev = spawnSync('git', ['rev-parse', '--verify', `${target}^{commit}`], {
    cwd: realRoot,
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  if (rev.status !== 0 || !rev.stdout.trim()) return null;
  const mb = spawnSync('git', ['merge-base', 'HEAD', rev.stdout.trim()], {
    cwd: realRoot,
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  return mb.status === 0 && mb.stdout.trim() ? mb.stdout.trim() : null;
}

function collectChangedEntriesFromGit(realRoot, baseSha) {
  const entries = [];
  const seenNew = new Set();
  const diffRes = spawnSync(
    'git',
    ['diff', '--no-ext-diff', '--no-textconv', '--name-status', '-z', '--find-renames', baseSha, '--'],
    { cwd: realRoot, maxBuffer: 32 * 1024 * 1024 },
  );
  if (diffRes.status === 0 && diffRes.stdout) {
    const fields = diffRes.stdout.toString('utf8').replace(/\0$/, '').split('\0').filter(Boolean);
    for (let i = 0; i < fields.length;) {
      const status = fields[i++];
      const first = fields[i++];
      const second = status.startsWith('R') || status.startsWith('C') ? fields[i++] : first;
      const oldPath = status === 'A' ? '' : first;
      const newPath = status === 'D' ? '' : second;
      entries.push({ status, oldPath, newPath });
      if (newPath) seenNew.add(newPath);
    }
  }
  const untracked = spawnSync('git', ['ls-files', '--others', '--exclude-standard', '-z'], {
    cwd: realRoot,
    maxBuffer: 16 * 1024 * 1024,
  });
  if (untracked.status === 0 && untracked.stdout) {
    for (const rel of untracked.stdout.toString('utf8').split('\0').filter(Boolean)) {
      if (seenNew.has(rel)) continue;
      seenNew.add(rel);
      entries.push({ status: 'A', oldPath: '', newPath: rel });
    }
  }
  return entries;
}

export function analyzeRepoRuleCoverage({ root, baseRef, baseSha, changedEntries = null, allFiles = null, filterPaths = null } = {}) {
  const empty = { rules: [], summary: { total: 0, covered: 0, not_proved: 0, uncovered: 0 }, warnings: [] };
  if (typeof root !== 'string' || !root.trim()) return empty;
  let realRoot;
  try { realRoot = realpathSync(root); } catch { return empty; }

  const resolvedBaseSha = baseSha || resolveMergeBaseSha(realRoot, baseRef);
  if (!resolvedBaseSha) return empty;

  const entries = Array.isArray(changedEntries) ? changedEntries : collectChangedEntriesFromGit(realRoot, resolvedBaseSha);
  if (entries.length === 0) return empty;

  const filterSet = filterPaths ? new Set(filterPaths) : null;
  const changedDocs = [];

  for (const entry of entries) {
    if (!entry || typeof entry !== 'object') continue;
    const newPath = typeof entry.newPath === 'string' ? entry.newPath.trim().replace(/^\.\//, '') : '';
    const oldPath = typeof entry.oldPath === 'string' ? entry.oldPath.trim().replace(/^\.\//, '') : '';
    if (!newPath || !canonicalRepoPath(newPath)) continue;
    if (filterSet && !filterSet.has(newPath) && (!oldPath || !filterSet.has(oldPath))) continue;
    if (FIXTURE_DOC_DIR_RE.test(newPath)) continue;

    const isPrompt = newPath.endsWith('.prompt.md') && !isTestPromptPath(newPath);
    const isStory = !isPrompt && isLintableStoryPath(newPath);
    if (!isPrompt && !isStory) continue;

    const after = typeof entry.after === 'string' ? entry.after : readSafeUtf8(realRoot, newPath);
    if (typeof after !== 'string') continue;

    let before = typeof entry.before === 'string' ? entry.before : '';
    if (entry.before === undefined && oldPath && canonicalRepoPath(oldPath)) {
      const show = spawnSync('git', ['show', `${resolvedBaseSha}:${oldPath}`], {
        cwd: realRoot,
        encoding: 'utf8',
        maxBuffer: 8 * 1024 * 1024,
        stdio: ['ignore', 'pipe', 'ignore'],
      });
      before = show.status === 0 && typeof show.stdout === 'string' ? show.stdout : '';
    }

    changedDocs.push({ path: newPath, before, after });
  }

  // Fast short-circuit: zero test file reads when zero explicit rules changed.
  if (diffChangedRules(changedDocs).length === 0) return empty;

  let repoFiles = Array.isArray(allFiles) ? allFiles : null;
  if (!repoFiles) {
    try { repoFiles = gitFiles(realRoot); } catch { repoFiles = []; }
  }

  const testFiles = [];
  for (const rel of repoFiles) {
    const kind = classifyTestFileKind(rel);
    if (!kind) continue;
    const content = readSafeUtf8(realRoot, rel);
    if (typeof content !== 'string') continue;
    testFiles.push({ path: rel, kind, content });
  }

  return evaluateRuleCoverage({ changedDocs, testFiles });
}
