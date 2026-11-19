// Generated from prompts/cli/human-boundary-card.prompt.md (sha256: 40aaabceb5015fdd1fd1f75fa132aaf8e38bbaa6fda5a829d9911ff05aeabe9f).
import { spawnSync } from 'node:child_process';
import { lstatSync, readdirSync, readFileSync, realpathSync } from 'node:fs';
import { homedir } from 'node:os';
import { basename, dirname, join, posix, resolve, sep } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { findOwners, isTestOwnedPath, isTestPromptPath } from './file-owner.mjs';
import {
  TEST_SCHEMA,
  findTests,
  gitFiles,
  interfaceBlocks,
  parseScenarioJson,
  promptMarkdownTargets,
  readPrompt,
  storyCriteria,
} from './runtime-seam.mjs';
import { isLintableStoryPath } from './story-lint.mjs';
import { hasAcceptance, isStoryPath } from './test-selection.mjs';

export const BOUNDARY_CARD_MAX_LINES = 25;

const BATCH_NAME = /^\d{8}-\d{6}-[a-z0-9]{4}$/;
const UUID_RE = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
const EFFECT_SEGMENT_RE = /(?:^|[_-])(effects?|side_effects?|actions?|commands?|calls?|dispatched|dispatch|emitted|emit|sent|notifications?|alerts?|events?|writes?|mutations?|invocations?|executed|outbound)(?:$|[_-])/i;
const EFFECT_KEY_RE = /^(effect|side_effect|action|command|call|port|tool|dispatch|dispatched|emit|emitted|sent|alert|notification|event)$/i;
const EXCLUDED_STORY_HEADING_RE = /^(?:Out\s+of\s+scope|What\s+must\s+not\s+change|Non-goals?|Not\s+in\s+scope)\b/i;

const STOPWORDS = new Set([
  'about', 'above', 'across', 'after', 'again', 'against', 'allow', 'allows', 'allowed', 'already', 'also', 'always',
  'among', 'another', 'applies', 'apply', 'array', 'assert', 'asserts', 'back', 'because', 'been', 'before', 'being',
  'below', 'between', 'boolean', 'both', 'call', 'called', 'calls', 'cannot', 'case', 'cases', 'change', 'changed',
  'changes', 'check', 'checked', 'checks', 'code', 'contain', 'contains', 'context', 'count', 'criteria', 'criterion',
  'current', 'data', 'default', 'does', 'done', 'during', 'each', 'either', 'else', 'empty', 'entry', 'equal', 'equals',
  'error', 'errors', 'even', 'every', 'exact', 'expect', 'expected', 'fail', 'failed', 'fails', 'false', 'field',
  'fields', 'file', 'files', 'first', 'follow', 'follows', 'forbid', 'forbidden', 'from', 'full', 'give', 'given',
  'gives', 'have', 'having', 'hold', 'holds', 'include', 'includes', 'initial', 'input', 'inputs', 'integer', 'into',
  'item', 'items', 'json', 'keep', 'keeps', 'kept', 'kind', 'last', 'least', 'less', 'line', 'lines', 'list', 'lists',
  'load', 'loaded', 'make', 'makes', 'match', 'matches', 'model', 'more', 'most', 'must', 'name', 'named', 'names',
  'need', 'needs', 'never', 'next', 'none', 'null', 'number', 'object', 'objects', 'once', 'only', 'operation',
  'operations', 'optional', 'other', 'otherwise', 'outcome', 'outcomes', 'output', 'outputs', 'over', 'pass', 'passed',
  'passes', 'path', 'paths', 'person', 'plain', 'policy', 'port', 'ports', 'preserve', 'preserves', 'prompt', 'prompts',
  'read', 'reads', 'reason', 'record', 'records', 'report', 'reported', 'reports', 'require', 'required', 'requires',
  'resource', 'resources', 'response', 'result', 'results', 'retain', 'retains', 'return', 'returned', 'returns',
  'route', 'rule', 'rules', 'same', 'save', 'saved', 'scenario', 'scenarios', 'schema', 'section', 'select', 'selected',
  'send', 'sends', 'sent', 'shall', 'should', 'show', 'shown', 'shows', 'simulate', 'simulated', 'simulation',
  'simulator', 'since', 'single', 'slice', 'some', 'source', 'sources', 'state', 'states', 'status', 'stay', 'stays',
  'step', 'steps', 'still', 'stories', 'story', 'string', 'such', 'supplied', 'system', 'target', 'test', 'tested',
  'tests', 'text', 'than', 'that', 'their', 'them', 'then', 'there', 'these', 'they', 'this', 'those', 'through',
  'true', 'type', 'types', 'unchanged', 'under', 'until', 'update', 'updated', 'updates', 'used', 'user', 'users',
  'using', 'valid', 'validate', 'value', 'values', 'verify', 'version', 'want', 'wants', 'when', 'where', 'whether',
  'which', 'while', 'with', 'within', 'without', 'word', 'words', 'work', 'works', 'world', 'write', 'writes',
]);

const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const cleanOneLine = value => String(value ?? '')
  .replace(/\x1b\[[0-9;?]*[ -/]*[@-~]/g, '')
  .replace(/[\x00-\x1f\x7f-\x9f\u2028\u2029]+/g, ' ')
  .replace(/\s+/g, ' ')
  .trim();

function clipText(value, max = 96) {
  const flat = cleanOneLine(value);
  const chars = [...flat];
  if (chars.length <= max) return flat;
  const cut = chars.slice(0, max - 2).join('');
  const word = cut.replace(/\s+\S*$/, '');
  return `${(word.length >= cut.length / 2 ? word : cut).trimEnd()} …`;
}

const NON_CODE_DIR_RE = /^(?:user_stories|docs?|\.github)\//i;
const CONFIG_FILE_RE = /(?:^|\/)(?:package(?:-lock)?\.json|pdd(?:-bindings)?\.json|tsconfig[^/]*\.json|jsconfig\.json|Makefile|GNUmakefile|Dockerfile|Containerfile|Procfile|Justfile|Vagrantfile|Rakefile|Gemfile)$/i;
const NON_CODE_EXT_RE = /\.(?:mdx?|rst|txt|json|jsonl|ndjson|ya?ml|toml|ini|cfg|conf|lock|csv|tsv|xml|svg|png|jpe?g|gif|webp|ico|pdf|woff2?)$/i;

const trimNonBlank = value => (typeof value === 'string' && value.trim() ? value.trim() : null);
const trimStringList = values => (Array.isArray(values) ? values.map(trimNonBlank).filter(Boolean) : []);

function uniqueInOrder(values) {
  const seen = new Set();
  const out = [];
  for (const item of values) {
    if (!seen.has(item)) {
      seen.add(item);
      out.push(item);
    }
  }
  return out;
}

function isProductionCodePath(filePath) {
  if (typeof filePath !== 'string' || !filePath || filePath.endsWith('.prompt.md')) return false;
  if (isStoryPath(filePath) || isTestOwnedPath(filePath)) return false;
  if (NON_CODE_DIR_RE.test(filePath) || CONFIG_FILE_RE.test(filePath) || NON_CODE_EXT_RE.test(filePath)) return false;
  if (/(?:^|\/)\.[^/]+$/.test(filePath)) return false;
  return posix.extname(posix.basename(filePath)).length > 1;
}

function sanitizeBoundaryLine(text) {
  const indent = /^ +/.exec(String(text ?? ''))?.[0] ?? '';
  const scrubbed = cleanOneLine(text)
    .replace(/Acceptance\s+criteria/gi, 'Criteria')
    .replace(/Agent\s+note/gi, 'note')
    .replace(/<\/?details\b[^>]*>|<details/gi, 'details')
    .replace(/\bbatch(?:es)?\b/gi, 'check-set')
    .replace(/\brequests?(?:ed|ing)?\b/gi, 'call');
  const cleaned = `${indent}${scrubbed}`;
  return /^(?:Text|Approve\s)/.test(cleaned) ? `  ${cleaned}` : cleaned;
}

function createEvidenceEntry({
  kind,
  label,
  source,
  scope,
  exitCode = null,
  ownerPrompt = null,
  loadedPrompts = [],
  passedAssertions = [],
  receiptId = null,
  creditsPromptRules = false,
  creditsModeledAssertions = false,
  creditsNativeBehavior = false,
  note = '',
}) {
  return {
    kind,
    label,
    source,
    scope,
    exitCode,
    ownerPrompt,
    loadedPrompts,
    passedAssertions,
    receiptId,
    creditsPromptRules,
    creditsModeledAssertions,
    creditsNativeBehavior,
    note,
  };
}

function buildOwnerResolutionEntry(item) {
  const targetPath = cleanOneLine(item?.targetPath ?? '');
  const ownerPrompt = trimNonBlank(item?.ownerPrompt);
  const rawSource = trimNonBlank(item?.source) ?? 'none';
  const certain = Boolean(item?.certain);
  return createEvidenceEntry({
    kind: 'owner-resolution',
    label: ownerPrompt ? 'resolved' : 'unmapped',
    source: rawSource === 'none' ? 'pdd owner' : `pdd owner (${rawSource})`,
    scope: ownerPrompt
      ? `ownership lookup: ${targetPath} -> ${ownerPrompt}${certain ? ' (certain)' : ' (uncertain)'}`
      : `ownership lookup: ${targetPath} -> no owner`,
    ownerPrompt,
    note: 'ownership lookup only; checks no prompt rules or behavior',
  });
}

function buildLocalLintEntry(item) {
  const localOnly = Boolean(item?.localOnly);
  const exitCode = Number.isInteger(item?.exitCode) ? item.exitCode : null;
  const rawState = trimNonBlank(item?.state) ?? 'unknown';
  const cleanScope = trimNonBlank(item?.scope) ?? 'SVG layout only';
  const incompleteSave = Boolean(item?.incompleteSave);
  return createEvidenceEntry({
    kind: 'local-lint',
    label: localOnly ? 'partial' : rawState,
    source: localOnly ? 'pdd lint --local' : 'pdd lint',
    scope: localOnly
      ? `${cleanScope}${incompleteSave ? '; incomplete local save' : ''}; prompt rules not checked`
      : cleanScope,
    exitCode,
    note: localOnly ? 'partial local lint; no credit for checking prompt rules' : '',
  });
}

function buildHostedStoryEntry(item) {
  const storyPath = cleanOneLine(item?.storyPath ?? '');
  const loadedPrompts = trimStringList(item?.loadedPrompts);
  const passedAssertions = trimStringList(item?.passedAssertions);
  const missingOwnerConnection = Boolean(item?.missingOwnerConnection);
  const rawState = trimNonBlank(item?.state) ?? 'unknown';
  const totalAssertions = Number.isInteger(item?.totalAssertions) ? item.totalAssertions : passedAssertions.length;
  const connectedPass = !missingOwnerConnection
    && rawState === 'passed'
    && loadedPrompts.length >= 1
    && passedAssertions.length >= 1;
  return createEvidenceEntry({
    kind: 'hosted-story',
    label: missingOwnerConnection ? 'unconnected' : connectedPass ? 'passed' : rawState,
    source: `pdd test (hosted): ${storyPath}`,
    scope: `modeled policy assertions (${passedAssertions.length}/${totalAssertions}) via ${loadedPrompts.length ? loadedPrompts.join(', ') : 'none'}`,
    loadedPrompts,
    passedAssertions,
    creditsPromptRules: connectedPass,
    creditsModeledAssertions: connectedPass,
    note: missingOwnerConnection
      ? 'missing owner connection; no credit for unexercised owner'
      : connectedPass
        ? 'modeled assertions only; native host behavior requires a native receipt'
        : 'hosted run did not pass modeled assertions',
  });
}

function buildNativeCheckEntry(item) {
  const trimmedBehavior = trimNonBlank(item?.behavior) ?? '';
  const targetHost = trimNonBlank(item?.targetHost) ?? 'target-host';
  const runner = trimNonBlank(item?.runner) ?? 'native-check';
  const receipt = isObject(item?.receipt) ? item.receipt : null;
  const receiptId = receipt ? trimNonBlank(receipt.receiptId) : null;
  const receiptSource = receipt ? trimNonBlank(receipt.source) : null;
  const receiptStatus = receipt ? (trimNonBlank(receipt.status) ?? 'unverified') : null;
  const verifiedBehaviors = receipt ? trimStringList(receipt.verifiedBehaviors) : [];
  const hasMeta = Boolean(receipt && receiptId && receiptSource);
  const validReceipt = Boolean(
    hasMeta && receiptStatus === 'passed' && trimmedBehavior && verifiedBehaviors.includes(trimmedBehavior),
  );
  let note;
  if (validReceipt) note = 'credited via native receipt';
  else if (!hasMeta) note = 'no native receipt; native behavior credit withheld';
  else if (receiptStatus === 'failed') note = 'native receipt failed; native behavior credit withheld';
  else if (receiptStatus !== 'passed') note = `native receipt status is ${receiptStatus}; native behavior credit withheld`;
  else note = 'behavior not listed in native receipt; native behavior credit withheld';
  return {
    behavior: trimmedBehavior,
    entry: createEvidenceEntry({
      kind: 'native-check',
      label: validReceipt ? 'verified' : receipt !== null && receiptStatus === 'failed' ? 'failed' : 'unverified',
      source: hasMeta
        ? `${runner} on ${targetHost} (receipt ${receiptId}, ${receiptSource})`
        : `${runner} on ${targetHost} (no native receipt)`,
      scope: `target-host native behavior: ${trimmedBehavior}`,
      receiptId,
      creditsNativeBehavior: validReceipt,
      note,
    }),
  };
}

function formatEvidenceEntryPlain(entry) {
  const kindLabel = entry.kind === 'local-lint' ? 'local lint' : entry.kind;
  const exitPart = entry.kind === 'local-lint' && Number.isInteger(entry.exitCode) ? ` (exit ${entry.exitCode})` : '';
  const parts = [`${kindLabel} [${entry.label}]${exitPart}: ${clipText(entry.scope, 96)}`];
  if (entry.kind === 'hosted-story' && entry.creditsModeledAssertions && entry.passedAssertions.length) {
    const shown = entry.passedAssertions.slice(0, 3).map(a => clipText(a, 54)).join('; ');
    const more = entry.passedAssertions.length > 3 ? ` (+${entry.passedAssertions.length - 3} more)` : '';
    parts.push(`passed=[${shown}${more}]`);
  }
  parts.push(`source=${clipText(entry.source, 120)}`);
  if (entry.note) parts.push(clipText(entry.note, 84));
  return `    - ${parts.join(' · ')}`;
}

/**
 * Pure deterministic review-summary evidence provenance calculator.
 * Keeps pdd owner, pdd lint --local, hosted Story checks, and native receipts
 * separate with explicit scope, source, label, and credit limits.
 */
export function summarizeBoundaryEvidence({
  ownerLookups = [],
  localLint = null,
  hostedStoryRuns = [],
  nativeChecks = [],
} = {}) {
  const entries = [];
  for (const item of Array.isArray(ownerLookups) ? ownerLookups : []) {
    if (isObject(item)) entries.push(buildOwnerResolutionEntry(item));
  }
  if (isObject(localLint)) {
    entries.push(buildLocalLintEntry(localLint));
  }
  for (const item of Array.isArray(hostedStoryRuns) ? hostedStoryRuns : []) {
    if (isObject(item)) entries.push(buildHostedStoryEntry(item));
  }
  const nativePairs = [];
  for (const item of Array.isArray(nativeChecks) ? nativeChecks : []) {
    if (isObject(item)) {
      const pair = buildNativeCheckEntry(item);
      nativePairs.push(pair);
      entries.push(pair.entry);
    }
  }

  const credits = {
    resolvedOwners: [...new Set(entries.filter(e => e.kind === 'owner-resolution' && e.ownerPrompt).map(e => e.ownerPrompt))].sort(),
    localLintPartial: entries.some(e => e.kind === 'local-lint' && e.label === 'partial'),
    localLintCreditsPromptRules: entries.some(e => e.kind === 'local-lint' && e.creditsPromptRules === true),
    hostedPassedAssertions: uniqueInOrder(
      entries.filter(e => e.kind === 'hosted-story' && e.creditsModeledAssertions === true).flatMap(e => e.passedAssertions),
    ),
    nativeVerifiedBehaviors: uniqueInOrder(
      nativePairs.filter(p => p.entry.creditsNativeBehavior === true && p.behavior).map(p => p.behavior),
    ),
    nativeUnverifiedBehaviors: uniqueInOrder(
      nativePairs.filter(p => p.entry.creditsNativeBehavior === false && p.behavior).map(p => p.behavior),
    ),
  };

  let rawLines;
  if (!entries.length) {
    rawLines = ['Human boundary card (advisory):', '  Evidence: none'];
  } else {
    const header = ['Human boundary card (advisory):', '  Evidence:'];
    const entryLines = entries.map(formatEvidenceEntryPlain);
    const room = BOUNDARY_CARD_MAX_LINES - header.length;
    rawLines = entryLines.length <= room
      ? [...header, ...entryLines]
      : [
          ...header,
          ...entryLines.slice(0, room - 1),
          `  … +${entryLines.length - (room - 1)} more evidence entries omitted`,
        ];
  }

  return {
    advisory: true,
    entries,
    credits,
    lines: rawLines.map(sanitizeBoundaryLine),
  };
}

/**
 * Compaction priority for evidence entries so gaps (unconnected hosted runs,
 * partial local lint, unverified/failed native checks) stay above the fold.
 */
export function evidenceEntryPriority(entry) {
  if (entry?.kind === 'hosted-story' && entry.label === 'unconnected') return 0;
  if (entry?.kind === 'local-lint' && entry.label === 'partial') return 0;
  if (entry?.kind === 'native-check' && entry.creditsNativeBehavior === false) return 0;
  return 2;
}

function renderBoundedSection(heading, rows, budget, omitLine, emptyLine = null) {
  if (budget <= 0) return [];
  if (!rows.length) return emptyLine ? [emptyLine] : [];
  if (budget === 1) return [omitLine(rows.length)];
  if (1 + rows.length <= budget) return [heading, ...rows];
  if (budget === 2) return [heading, omitLine(rows.length)];
  const shown = budget - 2;
  return [heading, ...rows.slice(0, shown), omitLine(rows.length - shown)];
}

/**
 * Shared 1-screen (<= 25-line) fitter for cards with optional Evidence and
 * Provenance sections. Preserves header/footer lines and prioritizes critical
 * rows from both sections when compacting.
 */
export function fitSectionedBoundaryLines({
  headerLines,
  footerLines,
  evidenceHeading,
  evidenceItems = [],
  evidenceOmit,
  provenanceHeading,
  provenanceItems = [],
  provenanceEmpty,
  provenanceOmit,
  maxLines = BOUNDARY_CARD_MAX_LINES,
}) {
  const totalFixed = headerLines.length + footerLines.length;
  if (totalFixed >= maxLines) return [...headerLines, ...footerLines].slice(0, maxLines);
  const room = maxLines - totalFixed;
  const provSorted = [...provenanceItems].sort((a, b) => (a.priority ?? 3) - (b.priority ?? 3));

  if (!evidenceItems.length) {
    const provBody = renderBoundedSection(
      provenanceHeading,
      provSorted.map(item => item.line),
      room,
      provenanceOmit,
      provenanceEmpty,
    );
    return [...headerLines, ...provBody, ...footerLines];
  }

  const evTotal = 1 + evidenceItems.length;
  const provTotal = provSorted.length ? 1 + provSorted.length : 1;
  if (evTotal + provTotal <= room) {
    const evBody = [evidenceHeading, ...evidenceItems.map(item => item.line)];
    const provBody = provSorted.length
      ? [provenanceHeading, ...provSorted.map(item => item.line)]
      : [provenanceEmpty];
    return [...headerLines, ...evBody, ...provBody, ...footerLines];
  }

  if (room === 1) {
    return [...headerLines, evidenceOmit(evidenceItems.length + provSorted.length), ...footerLines];
  }

  const evSorted = [...evidenceItems].sort((a, b) => (a.priority ?? 2) - (b.priority ?? 2));
  const half = Math.floor(room / 2);
  let evBudget;
  if (evTotal <= half) {
    evBudget = evTotal;
  } else if (provTotal <= half) {
    evBudget = Math.max(1, room - provTotal);
  } else {
    const evCritical = evSorted.filter(item => (item.priority ?? 2) <= 1).length;
    const minProv = provSorted.length ? Math.min(provTotal, Math.max(2, provSorted.filter(item => (item.priority ?? 3) <= 1).length + 1)) : 1;
    const maxEv = Math.max(1, room - minProv);
    evBudget = Math.min(evTotal, maxEv, Math.max(2, Math.min(room - 1, Math.max(evCritical + 2, half))));
  }
  const provBudget = Math.max(1, room - evBudget);
  const evBody = renderBoundedSection(evidenceHeading, evSorted.map(item => item.line), evBudget, evidenceOmit);
  const provBody = renderBoundedSection(
    provenanceHeading,
    provSorted.map(item => item.line),
    provBudget,
    provenanceOmit,
    provenanceEmpty,
  );
  return [...headerLines, ...evBody, ...provBody, ...footerLines].slice(0, maxLines);
}

function canonicalRoot(root) {
  try { return realpathSync(root); } catch { return resolve(root); }
}

function normalizeRelPromptPath(rawPath) {
  if (typeof rawPath !== 'string') return '';
  return posix.normalize(rawPath.trim().replace(/^\.\//, ''));
}

function readSafeText(rootReal, relPath) {
  if (typeof relPath !== 'string' || !relPath || relPath.startsWith('/') || relPath.includes('\\')) return null;
  const normalized = posix.normalize(relPath.replace(/^\.\//, ''));
  if (!normalized || normalized === '.' || normalized.startsWith('..') || normalized.split('/').includes('..')) return null;
  const full = join(rootReal, normalized);
  try {
    const stat = lstatSync(full);
    if (!stat.isFile()) return null;
    const real = realpathSync(full);
    if (real !== rootReal && !real.startsWith(`${rootReal}${sep}`)) return null;
    return readFileSync(real, 'utf8');
  } catch {
    return null;
  }
}

function stripHtmlComments(text) {
  const raw = String(text ?? '');
  let out = '', pos = 0;
  while (pos < raw.length) {
    const open = raw.indexOf('<!--', pos);
    if (open < 0) { out += raw.slice(pos); break; }
    out += raw.slice(pos, open);
    const close = raw.indexOf('-->', open + 4);
    const end = close < 0 ? raw.length : close + 3;
    for (let i = open; i < end; i += 1) out += raw[i] === '\n' || raw[i] === '\r' ? raw[i] : ' ';
    pos = end;
  }
  return out;
}

function maskFencedCodeBlocks(text) {
  const lines = String(text ?? '').split('\n');
  let fence = null;
  const masked = lines.map(line => {
    const trimmed = line.replace(/\r$/, '');
    const closeMatch = fence ? /^ {0,3}(`{3,}|~{3,})[ \t]*$/.exec(trimmed) : null;
    if (fence) {
      if (closeMatch && closeMatch[1][0] === fence[0] && closeMatch[1].length >= fence.length) fence = null;
      return '';
    }
    const openMatch = /^ {0,3}(?:(`{3,})[^`]*|(~{3,}).*)$/.exec(trimmed);
    if (openMatch) {
      fence = openMatch[1] ?? openMatch[2];
      return '';
    }
    return line;
  });
  return masked.join('\n');
}

function maskInlineCodeSpans(text) {
  const raw = String(text ?? '');
  const unclosedLengths = new Set();
  let out = '', i = 0;
  while (i < raw.length) {
    if (raw[i] === '\\' && i + 1 < raw.length) {
      out += raw.slice(i, i + 2);
      i += 2;
      continue;
    }
    if (raw[i] !== '`') {
      out += raw[i];
      i += 1;
      continue;
    }
    let ticks = 1;
    while (i + ticks < raw.length && raw[i + ticks] === '`') ticks += 1;
    if (unclosedLengths.has(ticks)) {
      out += raw.slice(i, i + ticks);
      i += ticks;
      continue;
    }
    let j = i + ticks, closeAt = -1;
    while (j < raw.length) {
      if (raw[j] !== '`') { j += 1; continue; }
      let run = 1;
      while (j + run < raw.length && raw[j + run] === '`') run += 1;
      if (run === ticks) { closeAt = j + run; break; }
      j += run;
    }
    if (closeAt < 0) {
      unclosedLengths.add(ticks);
      out += raw.slice(i, i + ticks);
      i += ticks;
    } else {
      for (let k = i; k < closeAt; k += 1) out += raw[k] === '\n' || raw[k] === '\r' ? raw[k] : ' ';
      i = closeAt;
    }
  }
  return out;
}

function maskCodeAndComments(text) {
  const withoutComments = stripHtmlComments(text);
  const withoutFences = maskFencedCodeBlocks(withoutComments);
  return maskInlineCodeSpans(withoutFences);
}

function proseWithoutInterface(text) {
  if (typeof text !== 'string') return '';
  let out = '', at = 0;
  for (const block of interfaceBlocks(text)) {
    out += text.slice(at, block.index);
    at = block.index + block[0].length;
  }
  const rest = out + text.slice(at);
  return rest.replace(/^---\r?\n[\s\S]*?\r?\n---\r?\n?/, '');
}

function countProseLines(text) {
  const prose = proseWithoutInterface(text).replace(/\r\n/g, '\n').replace(/\n+$/, '');
  return prose ? prose.split('\n').length : 0;
}

function headingSlug(rawHeading) {
  let text = String(rawHeading ?? '')
    .replace(/`([^`]*)`/g, '$1')
    .replace(/\[([^\][]*)\]\([^()]*\)/g, '$1');
  while (/<[^<>]*>/.test(text)) text = text.replace(/<[^<>]*>/g, '');
  return text
    .replace(/[<>]/g, '')
    .toLowerCase()
    .trim()
    .replace(/[^\p{L}\p{N}\s_-]+/gu, '')
    .replace(/\s+/g, '-');
}

function parsePromptHeadingsAndSections(text) {
  const headings = new Set();
  const sections = new Map();
  if (typeof text !== 'string') return { headings, sections };
  const prose = proseWithoutInterface(text);
  const maskedForHeadings = maskFencedCodeBlocks(stripHtmlComments(prose));
  const proseLines = prose.split('\n');
  const maskedLines = maskedForHeadings.split('\n');

  const lineStarts = [];
  let offset = 0;
  for (const l of proseLines) {
    lineStarts.push(offset);
    offset += l.length + 1;
  }

  const found = [];
  for (let i = 0; i < maskedLines.length; i += 1) {
    const m = /^(#{1,6})[ \t]+(.+?)[ \t]*\r?$/.exec(maskedLines[i]);
    if (!m) continue;
    const rawTitle = proseLines[i].replace(/^#{1,6}[ \t]+/, '').replace(/[ \t]*\r?$/, '');
    const slug = headingSlug(rawTitle);
    if (!slug) continue;
    headings.add(slug);
    found.push({
      level: m[1].length,
      slug,
      headingText: rawTitle,
      startOffset: lineStarts[i],
      bodyStartOffset: Math.min(prose.length, lineStarts[i] + proseLines[i].length + 1),
    });
  }

  for (let i = 0; i < found.length; i += 1) {
    const cur = found[i];
    let endOffset = prose.length;
    for (let j = i + 1; j < found.length; j += 1) {
      if (found[j].level <= cur.level) {
        endOffset = found[j].startOffset;
        break;
      }
    }
    const rawBody = prose.slice(cur.bodyStartOffset, endOffset);
    const cleanBody = stripHtmlComments(rawBody).trim();
    const prev = sections.get(cur.slug);
    sections.set(cur.slug, {
      slug: cur.slug,
      level: cur.level,
      headingText: cur.headingText,
      bodyText: prev?.bodyText ? `${prev.bodyText}\n${cleanBody}`.trim() : cleanBody,
    });
  }

  for (const match of stripHtmlComments(prose).matchAll(/<a\s+[^<>]*?\bid=(?:"([^"<>]+)"|'([^'<>]+)')/gi)) {
    const anchor = match[1] ?? match[2];
    if (anchor) headings.add(anchor.toLowerCase());
  }
  return { headings, sections };
}

function dependenciesSection(text) {
  const prose = proseWithoutInterface(text);
  const heading = /^##[ \t]+Dependencies[ \t]*\r?$/im.exec(prose);
  if (!heading) return '';
  const rest = prose.slice(heading.index + heading[0].length);
  const end = /^#{1,2}[ \t]+/m.exec(rest);
  return end ? rest.slice(0, end.index) : rest;
}

function resolvePromptHref(rawHref, fromPath, visible) {
  if (typeof rawHref !== 'string') return null;
  const trimmed = rawHref.trim().replace(/^<|>$/g, '');
  if (!trimmed || /^[a-z]+:/i.test(trimmed) || trimmed.startsWith('#')) return null;
  const hashAt = trimmed.indexOf('#');
  const rawPath = (hashAt >= 0 ? trimmed.slice(0, hashAt) : trimmed).trim();
  const fragment = hashAt >= 0 ? trimmed.slice(hashAt + 1).trim().toLowerCase() : null;
  if (!rawPath.endsWith('.prompt.md')) return null;
  const baseDir = posix.dirname(fromPath);
  const relResolved = posix.normalize(baseDir === '.' ? rawPath : posix.join(baseDir, rawPath));
  if (!relResolved.startsWith('..') && visible.has(relResolved)) {
    return { target: relResolved, fragment: fragment || null };
  }
  const rootResolved = normalizeRelPromptPath(rawPath);
  if (rootResolved && !rootResolved.startsWith('..') && visible.has(rootResolved)) {
    return { target: rootResolved, fragment: fragment || null };
  }
  return null;
}

function extractFragmentLinks(sectionText, fromPath, visible) {
  const links = [];
  if (typeof sectionText !== 'string' || !sectionText) return links;
  const masked = maskCodeAndComments(sectionText);
  for (const match of masked.matchAll(/\[[^\]\n\[]*\]\(([^()\n]+)\)/g)) {
    const resolved = resolvePromptHref(match[1], fromPath, visible);
    if (resolved) links.push({ from: fromPath, ...resolved });
  }
  return links;
}

function stripExcludedStorySections(storyText) {
  if (typeof storyText !== 'string' || !storyText) return '';
  const lines = stripHtmlComments(storyText).split('\n');
  let fence = null;
  let skippingSection = false;
  const kept = [];
  for (const line of lines) {
    const trimmed = line.replace(/\r$/, '');
    const closeMatch = fence ? /^ {0,3}(`{3,}|~{3,})[ \t]*$/.exec(trimmed) : null;
    if (fence) {
      if (closeMatch && closeMatch[1][0] === fence[0] && closeMatch[1].length >= fence.length) fence = null;
      if (!skippingSection) kept.push(line);
      continue;
    }
    const openMatch = /^ {0,3}(?:(`{3,})[^`]*|(~{3,}).*)$/.exec(trimmed);
    if (openMatch) {
      fence = openMatch[1] ?? openMatch[2];
      if (!skippingSection) kept.push(line);
      continue;
    }
    const h2 = /^(#{1,2})[ \t]+(.+?)[ \t]*$/.exec(trimmed);
    if (h2) {
      skippingSection = h2[1].length === 2 && EXCLUDED_STORY_HEADING_RE.test(h2[2]);
    }
    if (!skippingSection) kept.push(line);
  }
  return kept.join('\n');
}

function parseStorySectionLines(storyText, headingPattern) {
  if (typeof storyText !== 'string') return [];
  const cleanStory = stripHtmlComments(storyText);
  const match = headingPattern.exec(cleanStory);
  if (!match) return [];
  const rest = cleanStory.slice(match.index + match[0].length);
  const end = /^##[ \t]+/m.exec(rest);
  const body = (end ? rest.slice(0, end.index) : rest).trim();
  if (!body) return [];
  const items = [];
  let current = null;
  for (const raw of body.split(/\r?\n/)) {
    const trimmed = raw.trim();
    if (!trimmed) {
      if (current) { items.push(current.join(' ')); current = null; }
      continue;
    }
    const bullet = /^(?:[-*+]|[1-9][0-9]*[.)])[ \t]+(.+)$/.exec(trimmed);
    if (bullet) {
      if (current) items.push(current.join(' '));
      current = [bullet[1].trim()];
    } else if (current) {
      current.push(trimmed);
    } else {
      items.push(trimmed);
    }
  }
  if (current) items.push(current.join(' '));
  return items.filter(line => !/^none\.?$/i.test(line));
}

function parseStoryBoundaryPrompts(storyText, storyPath, visible) {
  if (typeof storyText !== 'string') return [];
  const found = new Set();
  const addCandidate = candidate => {
    if (typeof candidate !== 'string') return;
    const norm = normalizeRelPromptPath(candidate);
    if (norm.endsWith('.prompt.md') && visible.has(norm)) {
      found.add(norm);
      return;
    }
    const resolved = resolvePromptHref(candidate, storyPath, visible);
    if (resolved) found.add(resolved.target);
  };

  for (const match of storyText.matchAll(/^[ \t]*`{3,}[ \t]*pdd-boundary\b[^\n]*\r?\n([\s\S]*?)\r?\n[ \t]*`{3,}[ \t]*(?=\r?\n|$)/gm)) {
    for (const raw of match[1].split(/\r?\n/)) addCandidate(raw);
  }
  for (const match of storyText.matchAll(/`{3,}json[ \t]+pdd-boundary[ \t]*\r?\n([\s\S]*?)`{3,}/gi)) {
    try {
      const parsed = JSON.parse(match[1]);
      for (const p of Array.isArray(parsed?.prompts) ? parsed.prompts : []) addCandidate(p);
    } catch { /* advisory reader never fails on malformed blocks */ }
  }

  const inScopeStory = stripExcludedStorySections(storyText);
  for (const link of extractFragmentLinks(inScopeStory, storyPath, visible)) found.add(link.target);
  const withoutFences = maskFencedCodeBlocks(inScopeStory);
  for (const match of withoutFences.matchAll(/(?:^|[\s`"'([])([A-Za-z0-9_./-]+\.prompt\.md)(?=$|[\s`"'),.:;#\]])/gm)) {
    addCandidate(match[1]);
  }
  return [...found].sort();
}

function stemToken(word) {
  let w = word.toLowerCase();
  for (const suffix of ['ations', 'ation', 'ments', 'ment', 'ities', 'ity', 'iness', 'ning', 'ings', 'ing', 'edly', 'ed', 'ies', 'ves', 'ses', 'ers', 'er', 'es', 's']) {
    if (w.length - suffix.length >= 4 && w.endsWith(suffix)) {
      if (suffix === 'ies') w = `${w.slice(0, -3)}y`;
      else if (suffix === 'ves') w = `${w.slice(0, -3)}f`;
      else if (suffix === 'ses') w = `${w.slice(0, -2)}`;
      else w = w.slice(0, -suffix.length);
      break;
    }
  }
  return w.length >= 5 ? w.slice(0, 5) : w;
}

function salientRuleTokens(text, excludedPromptPaths = []) {
  const excludedStems = new Set();
  for (const p of excludedPromptPaths) {
    const base = basename(p, '.prompt.md').toLowerCase();
    for (const part of base.split(/[^a-z0-9]+/)) {
      if (part.length >= 4) excludedStems.add(stemToken(part));
    }
  }
  const rawWords = String(text ?? '')
    .replace(/`[^`]*`/g, ' ')
    .replace(/[A-Za-z0-9_./-]+\.(?:prompt\.md|md|json|mjs|js|ts|py)/gi, ' ')
    .replace(/([a-z])([A-Z])/g, '$1 $2')
    .toLowerCase()
    .split(/[^a-z0-9]+/)
    .filter(token => token.length >= 4 && !/^\d+$/.test(token) && !STOPWORDS.has(token));
  const allStems = [...new Set(rawWords.map(stemToken))];
  const withoutTopic = allStems.filter(stem => !excludedStems.has(stem));
  return withoutTopic.length >= 2 ? withoutTopic : allStems;
}

function explicitIdentifiers(text) {
  const ids = [];
  for (const match of String(text ?? '').matchAll(/`([^`\n]{3,64})`/g)) {
    const token = match[1].trim();
    if (!token || /\s/.test(token) || token.endsWith('.md') || token.endsWith('.json')) continue;
    if (/[_-]|[A-Z0-9]|^\//.test(token)) ids.push(token.replace(/^\//, ''));
  }
  return [...new Set(ids)];
}

function proseStemsOf(proseText) {
  const words = String(proseText ?? '')
    .replace(/([a-z])([A-Z])/g, '$1 $2')
    .toLowerCase()
    .split(/[^a-z0-9]+/)
    .filter(token => token.length >= 4);
  return new Set(words.map(stemToken));
}

function effectiveProseForRecord(rec, targetedFragmentsMap = null) {
  const targeted = targetedFragmentsMap?.get(rec.path);
  if (!targeted || !targeted.size) return rec.proseText;
  const parts = [];
  for (const slug of targeted) {
    const sec = rec.sections?.get(slug);
    if (sec) parts.push(`${sec.headingText}\n${sec.bodyText}`);
    else parts.push(rec.proseText);
  }
  return parts.join('\n');
}

function ruleConnectedToSources(ruleText, loadedPromptRecords, targetedFragmentsMap = null) {
  if (!loadedPromptRecords.length) return { connected: false, reason: 'no prompt source loaded' };
  const combinedProse = loadedPromptRecords.map(item => effectiveProseForRecord(item, targetedFragmentsMap)).join('\n');
  const combinedLower = combinedProse.toLowerCase();
  const identifiers = explicitIdentifiers(ruleText);
  const matchedIds = identifiers.filter(id => combinedLower.includes(id.toLowerCase()));
  const missingIds = identifiers.filter(id => !combinedLower.includes(id.toLowerCase()));
  const stems = salientRuleTokens(ruleText, loadedPromptRecords.map(item => item.path));
  const corpusStems = proseStemsOf(combinedProse);
  const matchedStems = stems.filter(stem => corpusStems.has(stem));

  const totalSignals = identifiers.length + stems.length;
  if (totalSignals === 0) return { connected: true, reason: null };
  const matchedSignals = matchedIds.length + matchedStems.length;
  const requiredSignals = totalSignals >= 2 ? Math.max(2, Math.ceil(totalSignals * 0.5)) : 1;
  if (matchedSignals < requiredSignals) {
    if (missingIds.length) {
      return { connected: false, reason: `missing \`${missingIds[0]}\` in selected source` };
    }
    return { connected: false, reason: 'owning rule absent from selected source prose' };
  }
  return { connected: true, reason: null };
}

function inspectFragmentLink(link, rootReal, visible, promptCache) {
  if (!link?.fragment) return { broken: null, validFragment: null };
  const targetRec = readPromptRecord(rootReal, visible, link.target, promptCache);
  if (!targetRec) return { broken: null, validFragment: null };
  if (!targetRec.headings.has(link.fragment)) {
    return { broken: { from: link.from, target: link.target, fragment: link.fragment, empty: false }, validFragment: null };
  }
  const sec = targetRec.sections.get(link.fragment);
  if (sec && !sec.bodyText) {
    return { broken: { from: link.from, target: link.target, fragment: link.fragment, empty: true }, validFragment: null };
  }
  return { broken: null, validFragment: { from: link.from, target: link.target, fragment: link.fragment } };
}

const unescapePointer = token => token.replace(/~([01])/g, (_, d) => (d === '1' ? '/' : '~'));

function pointerGet(rootValue, pointer) {
  if (typeof pointer !== 'string') return { found: false, value: undefined };
  if (pointer === '') return { found: rootValue !== undefined, value: rootValue };
  if (!pointer.startsWith('/')) return { found: false, value: undefined };
  let cur = rootValue;
  for (const rawPart of pointer.slice(1).split('/')) {
    const part = unescapePointer(rawPart);
    if (Array.isArray(cur)) {
      const idx = Number(part);
      if (!Number.isInteger(idx) || idx < 0 || idx >= cur.length) return { found: false, value: undefined };
      cur = cur[idx];
    } else if (isObject(cur) && Object.hasOwn(cur, part)) {
      cur = cur[part];
    } else {
      return { found: false, value: undefined };
    }
  }
  return { found: true, value: cur };
}

function pointerSetClone(targetObj, pointer, val) {
  if (!isObject(targetObj) || typeof pointer !== 'string' || !pointer.startsWith('/')) return;
  const parts = pointer.slice(1).split('/').map(unescapePointer);
  let cur = targetObj;
  for (let i = 0; i < parts.length - 1; i += 1) {
    const key = parts[i];
    if (!isObject(cur[key])) cur[key] = {};
    cur = cur[key];
  }
  if (parts.length) cur[parts.at(-1)] = val;
}

function resolveInitialWorld(doc, rootReal, visible, seedCache) {
  const raw = doc?.initial_world;
  if (!isObject(raw)) return {};
  let merged = {};
  if (typeof raw.$seed === 'string') {
    const seedPath = normalizeRelPromptPath(raw.$seed);
    if (!seedCache.has(seedPath)) {
      const seedText = visible.has(seedPath) ? readSafeText(rootReal, seedPath) : null;
      let parsed = null;
      if (seedText) {
        try { parsed = JSON.parse(seedText); } catch { parsed = null; }
      }
      seedCache.set(seedPath, isObject(parsed) ? parsed : null);
    }
    const baseSeed = seedCache.get(seedPath);
    if (baseSeed) merged = structuredClone(baseSeed);
  }
  for (const [k, v] of Object.entries(raw)) {
    if (k === '$seed' || k === 'set') continue;
    merged[k] = structuredClone(v);
  }
  if (isObject(raw.set)) {
    for (const [ptr, v] of Object.entries(raw.set)) {
      pointerSetClone(merged, ptr, structuredClone(v));
    }
  }
  return merged;
}

function nodeReferencesInput(node) {
  if (!node || typeof node !== 'object') return false;
  if (Array.isArray(node)) return node.some(nodeReferencesInput);
  if (node.ref_target === 'input') return true;
  return Object.values(node).some(nodeReferencesInput);
}

function checkReferencesInput(check) {
  if (!isObject(check)) return false;
  if (check.ref_target === 'input') return true;
  if (isObject(check.value) && check.value.ref_target === 'input') return true;
  if (check.op === 'integer_relation' && isObject(check.value) && nodeReferencesInput(check.value)) return true;
  return false;
}

function valueAppearsSupplied(expected, supplied, checkPath) {
  if (expected === undefined || expected === null || typeof expected === 'boolean') return false;
  if (typeof expected === 'number' && (expected === 0 || expected === 1)) return false;
  if (typeof expected === 'string' && expected.length === 0) return false;
  if ((Array.isArray(expected) && expected.length === 0) || (isObject(expected) && Object.keys(expected).length === 0)) {
    if (typeof checkPath === 'string' && checkPath.startsWith('/')) {
      const direct = pointerGet(supplied, checkPath);
      return direct.found && isDeepStrictEqual(direct.value, expected);
    }
    return false;
  }
  if (typeof checkPath === 'string' && checkPath.startsWith('/')) {
    const direct = pointerGet(supplied, checkPath);
    if (direct.found && isDeepStrictEqual(direct.value, expected)) return true;
  }
  const leaf = typeof checkPath === 'string' && checkPath.includes('/') ? checkPath.split('/').filter(Boolean).at(-1) : null;
  let matched = false;
  const visit = (node, keyName = null) => {
    if (matched || node === null || node === undefined) return;
    if (isDeepStrictEqual(node, expected)) {
      if (typeof expected === 'object' || !leaf || keyName === leaf || (typeof expected === 'string' && expected.length >= 3)) {
        matched = true;
        return;
      }
    }
    if (Array.isArray(node)) for (const item of node) visit(item, keyName);
    else if (isObject(node)) for (const [k, v] of Object.entries(node)) visit(v, k);
  };
  visit(supplied, null);
  return matched;
}

function looksLikeReturnedEffectClaim(check) {
  if (!isObject(check) || !['result', 'world'].includes(check.target)) return false;
  const segments = String(check.path ?? '').split('/').filter(Boolean);
  if (segments.some(seg => EFFECT_SEGMENT_RE.test(seg))) return true;
  const val = check.value;
  if (Array.isArray(val) && val.length > 0 && val.some(item => isObject(item) && Object.keys(item).some(k => EFFECT_KEY_RE.test(k)))) {
    return true;
  }
  if (isObject(val) && Object.keys(val).some(k => EFFECT_KEY_RE.test(k))) return true;
  return false;
}

function isZeroCallCheck(check) {
  if (!isObject(check) || check.target !== 'calls') return false;
  if ((check.op === 'equals' || check.op === 'count' || check.op === 'at_most' || check.op === 'lte') && check.value === 0) return true;
  if (check.op === 'equals' && Array.isArray(check.value) && check.value.length === 0) return true;
  return false;
}

function instrumentedPortsForStep(doc, step, loadedPromptRecords) {
  const ports = new Set();
  for (const rec of loadedPromptRecords) {
    for (const res of Array.isArray(rec.interface?.resources) ? rec.interface.resources : []) {
      if (typeof res?.name === 'string' && res.name) {
        const ops = Array.isArray(res.operations) ? res.operations : [];
        if (ops.length) for (const op of ops) { if (typeof op?.name === 'string') ports.add(`${res.name}.${op.name}`); }
        else ports.add(res.name);
      }
    }
    for (const call of Array.isArray(rec.interface?.calls) ? rec.interface.calls : []) {
      if (typeof call?.target === 'string' && call?.target_operation) ports.add(`${basename(call.target, '.prompt.md')}.${call.target_operation}`);
    }
  }
  for (const sim of [doc?.simulation, step?.simulation_overrides]) {
    if (!isObject(sim)) continue;
    for (const [k, v] of Object.entries(sim)) {
      if ((k === 'resources' || k === 'calls' || k === 'ports') && isObject(v)) {
        for (const sub of Object.keys(v)) ports.add(sub);
      } else if (k !== '$simulation') {
        ports.add(k);
      }
    }
  }
  return [...ports].sort();
}

function classifyStepCheck(check, doc, step, effectiveWorld, receiptCheck = null) {
  if (!isObject(check)) return { kind: 'model-returned value', zeroCalls: false, needsPortOrNative: false, portPath: null };
  if (check.target === 'calls') {
    const zero = isZeroCallCheck(check) || receiptCheck?.actual === 0 || (Array.isArray(receiptCheck?.actual) && receiptCheck.actual.length === 0);
    const portLabel = typeof check.path === 'string' && check.path ? check.path.replace(/^\/(?:resources|internal)\//, '').replace(/^\//, '') : 'port';
    return { kind: 'observed simulated port call', zeroCalls: zero, needsPortOrNative: false, portPath: portLabel || 'port' };
  }
  if (checkReferencesInput(check)) {
    return { kind: 'supplied fact', zeroCalls: false, needsPortOrNative: false, portPath: null };
  }
  const worldSet = isObject(doc?.initial_world?.set) ? doc.initial_world.set : null;
  if (check.target === 'world' && Object.hasOwn(check, 'value') && ['equals', 'equals_ignore_case', 'contains'].includes(check.op)) {
    if (worldSet && typeof check.path === 'string' && Object.hasOwn(worldSet, check.path) && isDeepStrictEqual(worldSet[check.path], check.value)) {
      return { kind: 'supplied fact', zeroCalls: false, needsPortOrNative: false, portPath: null };
    }
    const initial = pointerGet(effectiveWorld, check.path ?? '');
    if (initial.found && isDeepStrictEqual(initial.value, check.value)) {
      return { kind: 'supplied fact', zeroCalls: false, needsPortOrNative: false, portPath: null };
    }
  }
  if (['result', 'world'].includes(check.target) && Object.hasOwn(check, 'value') && ['equals', 'equals_ignore_case', 'contains'].includes(check.op)) {
    if (valueAppearsSupplied(check.value, step?.input, check.path) || (check.target === 'result' && valueAppearsSupplied(check.value, effectiveWorld, check.path))) {
      return { kind: 'supplied fact', zeroCalls: false, needsPortOrNative: false, portPath: null };
    }
  }
  return {
    kind: 'model-returned value',
    zeroCalls: false,
    needsPortOrNative: looksLikeReturnedEffectClaim(check),
    portPath: null,
  };
}

function gitChangedPaths(rootReal, visible) {
  const head = spawnSync('git', ['rev-parse', '--verify', 'HEAD^{commit}'], { cwd: rootReal, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  if (head.status !== 0) return [...visible].sort();
  const paths = new Set();
  const collect = args => {
    const out = spawnSync('git', args, { cwd: rootReal, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
    if (out.status === 0 && out.stdout) {
      for (const item of out.stdout.split('\0')) if (item && visible.has(item)) paths.add(item);
    }
  };
  collect(['diff', '--no-color', '--no-renames', '--name-only', '-z', 'HEAD']);
  collect(['ls-files', '--others', '--exclude-standard', '-z']);
  let comparedBase = false;
  for (const baseRef of ['refs/remotes/origin/main', 'refs/heads/main']) {
    const mb = spawnSync('git', ['merge-base', 'HEAD', baseRef], { cwd: rootReal, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
    const sha = mb.status === 0 ? mb.stdout.trim() : '';
    if (sha) {
      if (sha !== head.stdout.trim()) { collect(['diff', '--no-color', '--no-renames', '--name-only', '-z', sha]); comparedBase = true; }
      break;
    }
  }
  if (!comparedBase) {
    const parent = spawnSync('git', ['rev-parse', '--verify', 'HEAD~1^{commit}'], { cwd: rootReal, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
    if (parent.status !== 0) for (const item of visible) paths.add(item);
  }
  return [...paths].sort();
}

function resolveNativeRecordStatus(native, receiptId) {
  const explicit = trimNonBlank(native.status);
  if (explicit && ['passed', 'failed', 'skipped', 'unverified'].includes(explicit)) return explicit;
  if (isObject(native.intake) && typeof native.intake.admission === 'string') {
    return native.intake.admission === 'verified' ? 'passed' : 'unverified';
  }
  if (Array.isArray(native.checks) && native.checks.length > 0) {
    const states = native.checks.map(c => trimNonBlank(c?.state));
    if (states.some(s => s === 'failed')) return 'failed';
    if (states.every(s => s === 'checked' || s === 'passed')) return 'passed';
    return 'unverified';
  }
  return receiptId && trimNonBlank(native.profileId) && trimNonBlank(native.storyPath) ? 'passed' : 'unverified';
}

function readSavedNativeEvidenceRecords(rootReal) {
  const receiptedPassingStories = new Set();
  const records = [];
  try {
    const out = spawnSync('git', ['rev-parse', '--git-common-dir'], { cwd: rootReal, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
    if (out.status !== 0 || !out.stdout.trim()) return { receiptedPassingStories, records };
    const commonDir = resolve(rootReal, out.stdout.trim());
    const runsDir = join(commonDir, 'pdd', 'runs');
    let entries = [];
    try { entries = readdirSync(runsDir).sort(); } catch { return { receiptedPassingStories, records }; }
    for (const entry of entries) {
      let run;
      try { run = JSON.parse(readFileSync(join(runsDir, entry, 'status.json'), 'utf8')); } catch { continue; }
      if (!isObject(run) || typeof run.root !== 'string' || canonicalRoot(run.root) !== rootReal) continue;
      for (const ev of Array.isArray(run.evidence) ? run.evidence : []) {
        const native = ev?.native;
        if (!isObject(native) || native.schema !== 'pdd.native-evidence-record.v1' || typeof native.storyPath !== 'string') continue;
        const storyPath = normalizeRelPromptPath(native.storyPath);
        if (!storyPath) continue;
        const receiptId = trimNonBlank(native.receiptId) ?? trimNonBlank(native.runId) ?? trimNonBlank(run.runId);
        const profileId = trimNonBlank(native.profileId) ?? 'native-profile';
        const targetHost = trimNonBlank(native.targetHost) ?? 'target-host';
        const runner = trimNonBlank(native.runner) ?? profileId;
        const status = resolveNativeRecordStatus(native, receiptId);
        const explicitVerified = Array.isArray(native.verifiedBehaviors) ? trimStringList(native.verifiedBehaviors) : null;
        const explicitBehavior = trimNonBlank(native.behavior);
        const defaultBehavior = `native validation for ${storyPath} (${profileId})`;
        const behaviors = explicitBehavior
          ? [explicitBehavior]
          : explicitVerified && explicitVerified.length
            ? explicitVerified
            : [defaultBehavior];
        if (receiptId && status === 'passed') receiptedPassingStories.add(storyPath);
        for (const behavior of behaviors) {
          records.push({
            storyPath,
            check: {
              behavior,
              targetHost,
              runner,
              receipt: receiptId
                ? {
                    receiptId,
                    source: 'pdd.native-evidence-record.v1',
                    status,
                    verifiedBehaviors: explicitVerified ?? (status === 'passed' ? [behavior] : []),
                  }
                : null,
            },
          });
        }
      }
    }
  } catch { /* ignore unreadable git run state */ }
  return { receiptedPassingStories, records };
}

function parseSavedLocalLintRecord(folder, name, batch, since) {
  if (batch.version !== 1 || batch.batch !== name || batch.intent !== 'lint-only' || batch.local_only !== true) return null;
  if (!isObject(batch.local_scope) || !Array.isArray(batch.local_scope.tests) || !Array.isArray(batch.local_scope.prompts)) return null;
  if (!isObject(batch.lint) || batch.lint.state !== 'partial' || batch.lint.reason?.code !== 'local-only') return null;
  const createdAt = Date.parse(batch.created_at) || 0;
  if (since > 0 && createdAt > 0 && createdAt < since) return null;
  let summary = null;
  try { summary = JSON.parse(readFileSync(join(folder, 'summary.json'), 'utf8')); } catch { summary = null; }
  const expectedSummary = {
    batch: batch.batch,
    repo: batch.root,
    exit_code: batch.exit_code,
    state: 'partial',
    lint_state: 'partial',
    reason: batch.lint.reason,
    local_only: true,
    local_scope: batch.local_scope,
    summary_line: batch.summary_line,
    warnings: batch.warnings,
    problems: batch.problems,
    rows: [],
    report_url: null,
  };
  const incompleteSave = !isDeepStrictEqual(summary, expectedSummary);
  return {
    at: createdAt,
    record: {
      exitCode: Number.isInteger(batch.exit_code) ? batch.exit_code : 2,
      state: 'partial',
      localOnly: true,
      scope: 'SVG layout only',
      warningCount: Array.isArray(batch.warnings) ? batch.warnings.length : 0,
      problemCount: Array.isArray(batch.problems) ? batch.problems.length : 0,
      incompleteSave,
      inspectedPrompts: trimStringList(batch.local_scope.prompts),
      inspectedTests: trimStringList(batch.local_scope.tests),
    },
  };
}

function countStepCalls(callsObj) {
  if (!isObject(callsObj)) return null;
  let sum = 0, seenNumber = false;
  const walk = obj => {
    for (const val of Object.values(obj)) {
      if (typeof val === 'number' && Number.isFinite(val)) { sum += val; seenNumber = true; }
      else if (Array.isArray(val)) { sum += val.length; seenNumber = true; }
      else if (isObject(val)) walk(val);
    }
  };
  walk(callsObj);
  return seenNumber || Object.keys(callsObj).length === 0 ? sum : null;
}

function readSavedBatchDiagnostics(rootReal, { since = 0, env = process.env, relevantTests = null } = {}) {
  const byTest = new Map();
  let latestLocalLint = null;
  const stateRoot = resolve(env?.PDD_STATE_DIR || join(env?.HOME || homedir(), '.pdd', 'runtime'));
  const batchesDir = join(stateRoot, 'batches');
  let names = [];
  try { names = readdirSync(batchesDir).filter(name => BATCH_NAME.test(name)).sort(); } catch { return { byTest, divergences: [], sampleSummary: null, localLint: null }; }
  for (const name of names) {
    const folder = join(batchesDir, name);
    let batch;
    try { batch = JSON.parse(readFileSync(join(folder, 'batch.json'), 'utf8')); } catch { continue; }
    if (!isObject(batch) || typeof batch.root !== 'string' || !Array.isArray(batch.rows)) continue;
    if (canonicalRoot(batch.root) !== rootReal) continue;
    if (batch.intent === 'lint-only' && batch.local_only === true) {
      const localParsed = parseSavedLocalLintRecord(folder, name, batch, since);
      if (localParsed && (!latestLocalLint || localParsed.at >= latestLocalLint.at)) latestLocalLint = localParsed;
      continue;
    }
    if (batch.intent && batch.intent !== 'check') continue;
    const createdAt = Date.parse(batch.created_at) || 0;
    const batchAt = Math.max(createdAt, ...batch.rows.map(r => Number.isFinite(r?.ended_at) ? r.ended_at : 0));
    if (since > 0 && batchAt > 0 && batchAt < since) continue;
    for (const row of batch.rows) {
      if (!isObject(row) || typeof row.test !== 'string' || !Array.isArray(row.request_ids) || !row.request_ids.length) continue;
      const reqId = row.request_ids.at(-1);
      if (typeof reqId !== 'string' || !UUID_RE.test(reqId)) continue;
      let answer;
      try { answer = JSON.parse(readFileSync(join(folder, `${reqId}.json`), 'utf8')); } catch { continue; }
      const report = answer?.result?.report;
      if (!isObject(report)) continue;
      const samples = Array.isArray(report.samples) ? report.samples.filter(isObject) : [];
      const rowDivergences = [];
      let rowAgreedSamples = 0;
      if (samples.length > 1) {
        const baseSteps = Array.isArray(samples[0].steps) ? samples[0].steps : [];
        let differed = false;
        for (let idx = 0; idx < baseSteps.length; idx += 1) {
          const first = baseSteps[idx];
          const stepId = cleanOneLine(first?.step_id || `step-${idx + 1}`);
          const surfaces = new Set();
          for (let s = 1; s < samples.length; s += 1) {
            const other = Array.isArray(samples[s].steps) ? samples[s].steps[idx] : null;
            if (!other) continue;
            if (!isDeepStrictEqual(first?.result, other?.result)) surfaces.add('result');
            if (!isDeepStrictEqual(first?.error, other?.error)) surfaces.add('error');
            if (!isDeepStrictEqual(first?.world, other?.world)) surfaces.add('world');
            if (!isDeepStrictEqual(first?.calls, other?.calls)) surfaces.add('calls');
            const passA = (Array.isArray(first?.checks) ? first.checks : []).map(c => Boolean(c?.passed));
            const passB = (Array.isArray(other?.checks) ? other.checks : []).map(c => Boolean(c?.passed));
            if (!isDeepStrictEqual(passA, passB)) surfaces.add('verdict');
          }
          if (surfaces.size) {
            differed = true;
            rowDivergences.push(`${stepId} varied across ${samples.length} samples (${[...surfaces].join(', ')})`);
          }
        }
        if (!differed) rowAgreedSamples = samples.length;
      }
      for (const rStep of Array.isArray(report?.rerun?.steps) ? report.rerun.steps : []) {
        if (!isObject(rStep)) continue;
        const stepId = cleanOneLine(rStep.step_id || 'step');
        if (Array.isArray(rStep.changed_paths) && rStep.changed_paths.length) {
          rowDivergences.push(`${stepId} rerun varied (${rStep.changed_paths.slice(0, 2).map(cleanOneLine).join(', ')})`);
        } else if (Number.isInteger(rStep.runs) && rStep.runs > 1 && Number.isInteger(rStep.failed) && rStep.failed > 0 && rStep.failed < rStep.runs) {
          rowDivergences.push(`${stepId} split across ${rStep.runs} reruns (${rStep.failed} failed)`);
        }
      }
      for (const div of Array.isArray(report?.divergences) ? report.divergences : []) {
        const note = typeof div === 'string' ? cleanOneLine(div) : isObject(div) ? cleanOneLine(div.summary || div.step_id || div.path || '') : '';
        if (note) rowDivergences.push(note);
      }

      const stepObservations = new Map();
      const stepObservationsByIndex = [];
      const unkeyedChecks = [];
      const primarySteps = Array.isArray(samples[0]?.steps) ? samples[0].steps : [];
      for (let sIdx = 0; sIdx < primarySteps.length; sIdx += 1) {
        const s = primarySteps[sIdx];
        if (!isObject(s)) {
          stepObservationsByIndex.push(null);
          continue;
        }
        const observedCallTotal = countStepCalls(s.calls);
        const checks = Array.isArray(s.checks) ? s.checks : [];
        const hasId = typeof s.step_id === 'string' && s.step_id.length > 0;
        const obs = { stepId: hasId ? s.step_id : null, observedCallTotal, checks };
        stepObservationsByIndex.push(obs);
        if (hasId) stepObservations.set(s.step_id, obs);
        else unkeyedChecks.push(...checks);
      }

      byTest.set(normalizeRelPromptPath(row.test), {
        state: answer?.state ?? row.state ?? null,
        storyPath: typeof row.story === 'string' ? normalizeRelPromptPath(row.story) : null,
        reportCriteria: Array.isArray(report.criteria) ? report.criteria.filter(isObject) : [],
        stepObservations,
        stepObservationsByIndex,
        unkeyedChecks,
        sampleCount: samples.length,
        agreedSamples: rowAgreedSamples,
        divergences: [...new Set(rowDivergences)],
      });
    }
  }

  const activeRecords = Array.isArray(relevantTests) && relevantTests.length > 0
    ? relevantTests.map(p => byTest.get(normalizeRelPromptPath(p))).filter(Boolean)
    : [...byTest.values()];
  const uniqueDivergences = [...new Set(activeRecords.flatMap(r => r.divergences))];
  const agreedMultiSample = activeRecords.reduce((best, r) => Math.max(best, r.agreedSamples), 0);
  const maxSamples = activeRecords.reduce((best, r) => Math.max(best, r.sampleCount), 0);
  const sampleSummary = uniqueDivergences.length
    ? `advisory divergence: ${uniqueDivergences.slice(0, 2).join('; ')}`
    : agreedMultiSample > 1
      ? `${agreedMultiSample}/${agreedMultiSample} samples agreed`
      : maxSamples === 1
        ? 'single-sample check'
        : null;
  return { byTest, divergences: uniqueDivergences, sampleSummary, localLint: latestLocalLint?.record ?? null };
}

function readPromptRecord(rootReal, visible, path, cache) {
  if (cache.has(path)) return cache.get(path);
  const rawText = readSafeText(rootReal, path);
  if (rawText === null) { cache.set(path, null); return null; }
  let parsed = null;
  try { parsed = readPrompt(rootReal, visible, path); } catch { parsed = null; }
  const iface = parsed?.interface ?? null;
  const proseText = proseWithoutInterface(rawText);
  const { headings, sections } = parsePromptHeadingsAndSections(rawText);
  const rec = {
    path,
    rawText,
    proseText,
    proseLoc: countProseLines(rawText),
    interface: iface,
    kind: iface?.kind === 'native-only' ? 'native-only' : parsed?.blocks?.length ? 'runtime' : 'plain',
    reason: iface?.kind === 'native-only' && typeof iface.reason === 'string' ? cleanOneLine(iface.reason) : null,
    operations: Array.isArray(iface?.entries)
      ? iface.entries.map(e => e?.operation).filter(op => typeof op === 'string' && op.trim())
      : [],
    headings,
    sections,
  };
  cache.set(path, rec);
  return rec;
}

function resolveScenarioClosure(doc, storyBoundaryPrompts, rootReal, visible, promptCache) {
  const normalizeVisiblePrompt = raw => {
    const norm = normalizeRelPromptPath(raw);
    return norm.endsWith('.prompt.md') && visible.has(norm) ? norm : null;
  };

  const entryCandidates = new Set([
    ...(typeof doc?.entry_path === 'string' ? [normalizeVisiblePrompt(doc.entry_path)] : []),
    ...(Array.isArray(doc?.entry_paths) ? doc.entry_paths.map(normalizeVisiblePrompt) : []),
    ...storyBoundaryPrompts,
  ].filter(Boolean));

  const seeds = new Set();
  for (const step of Array.isArray(doc?.steps) ? doc.steps : []) {
    const stepEntry = normalizeVisiblePrompt(step?.entry_path);
    if (stepEntry) {
      seeds.add(stepEntry);
      continue;
    }
    if (typeof step?.operation === 'string' && step.operation) {
      let matchedOwner = null;
      for (const candidate of entryCandidates) {
        const rec = readPromptRecord(rootReal, visible, candidate, promptCache);
        if (rec?.operations.includes(step.operation)) { matchedOwner = candidate; break; }
      }
      if (matchedOwner) seeds.add(matchedOwner);
      else if (entryCandidates.size === 1) seeds.add([...entryCandidates][0]);
    }
  }
  const addContextSeed = raw => {
    const p = normalizeVisiblePrompt(raw);
    if (p) seeds.add(p);
  };
  for (const ctx of Array.isArray(doc?.context) ? doc.context : []) {
    if (typeof ctx === 'string') addContextSeed(ctx);
    else if (isObject(ctx)) {
      addContextSeed(ctx.path);
      addContextSeed(ctx.prompt_path);
      if (Array.isArray(ctx.paths)) for (const p of ctx.paths) addContextSeed(p);
    }
  }

  const loaded = new Set();
  const brokenFragments = [];
  const validFragments = [];
  const queue = [...seeds];
  while (queue.length) {
    const current = queue.shift();
    if (!current || loaded.has(current) || !visible.has(current)) continue;
    const rec = readPromptRecord(rootReal, visible, current, promptCache);
    if (!rec) continue;
    loaded.add(current);
    const targets = promptMarkdownTargets(rec.rawText, current, visible);
    for (const target of targets) if (!loaded.has(target)) queue.push(target);
    const depLinks = extractFragmentLinks(dependenciesSection(rec.rawText), current, visible);
    for (const link of depLinks) {
      if (!loaded.has(link.target)) queue.push(link.target);
      const inspected = inspectFragmentLink(link, rootReal, visible, promptCache);
      if (inspected.broken) brokenFragments.push(inspected.broken);
      if (inspected.validFragment) validFragments.push(inspected.validFragment);
    }
    for (const call of Array.isArray(rec.interface?.calls) ? rec.interface.calls : []) {
      const target = normalizeVisiblePrompt(call?.target);
      if (target && !loaded.has(target)) queue.push(target);
    }
  }
  return {
    entryPrompts: [...seeds].sort(),
    loadedPrompts: [...loaded].sort(),
    loadedRecords: [...loaded].sort().map(p => readPromptRecord(rootReal, visible, p, promptCache)).filter(Boolean),
    brokenFragments,
    validFragments,
  };
}

function buildHostedRunSummary(scen, savedTest, storyText, missingOwnerConnection) {
  const storyPath = scen.storyPath ?? savedTest.storyPath ?? normalizeRelPromptPath(scen.testEntry.path);
  const docCriteria = Array.isArray(scen.testEntry.doc?.criteria)
    ? scen.testEntry.doc.criteria.filter(isObject)
    : [];
  const fallbackCriteria = storyText
    ? storyCriteria(storyText).map((text, idx) => ({ id: `AC${idx + 1}`, text }))
    : [];
  const criteriaList = docCriteria.length ? docCriteria : fallbackCriteria;
  const savedChecks = (savedTest.stepObservationsByIndex ?? [])
    .filter(Boolean)
    .flatMap(obs => (Array.isArray(obs.checks) ? obs.checks : []));
  const reportCritById = new Map(
    (savedTest.reportCriteria ?? []).filter(c => typeof c?.id === 'string').map(c => [c.id, c]),
  );
  const hasKeyedChecks = savedChecks.some(c => typeof c?.criterion_id === 'string' && c.criterion_id);
  const allSavedChecksPassed = savedChecks.length === 0 || savedChecks.every(c => c?.passed !== false);

  const passedAssertions = [];
  for (const [idx, crit] of criteriaList.entries()) {
    const id = trimNonBlank(crit?.id) ?? `AC${idx + 1}`;
    const text = cleanOneLine(crit?.text ?? '');
    const display = text ? (text.startsWith(`${id}:`) ? clipText(text, 88) : `${id}: ${clipText(text, 84)}`) : id;
    const matching = savedChecks.filter(c => c?.criterion_id === id);
    let passed = false;
    if (matching.length > 0) passed = matching.every(c => c?.passed === true);
    else if (reportCritById.has(id) && typeof reportCritById.get(id).passed === 'boolean') passed = reportCritById.get(id).passed;
    else if (savedTest.state === 'passed' && !hasKeyedChecks && allSavedChecksPassed) passed = true;
    if (passed) passedAssertions.push(display);
  }
  return {
    storyPath,
    testPath: normalizeRelPromptPath(scen.testEntry.path),
    loadedPrompts: [...scen.loadedPrompts],
    missingOwnerConnection,
    state: trimNonBlank(savedTest.state) ?? 'unknown',
    passedAssertions,
    totalAssertions: criteriaList.length || passedAssertions.length,
  };
}

function mergeByKey(baseItems, extraItems, keyOf) {
  const byKey = new Map();
  for (const item of baseItems) byKey.set(keyOf(item), item);
  for (const item of extraItems) byKey.set(keyOf(item), item);
  return [...byKey.values()];
}

function mergeEvidenceInputs(auto, explicit) {
  const exp = isObject(explicit) ? explicit : {};
  const ownerLookups = mergeByKey(
    auto.ownerLookups,
    Array.isArray(exp.ownerLookups) ? exp.ownerLookups.filter(isObject) : [],
    item => `${cleanOneLine(item?.targetPath ?? '')}\0${trimNonBlank(item?.ownerPrompt) ?? ''}\0${trimNonBlank(item?.source) ?? 'none'}`,
  );
  const localLint = Object.hasOwn(exp, 'localLint') && exp.localLint !== undefined
    ? exp.localLint
    : auto.localLint;
  const hostedStoryRuns = mergeByKey(
    auto.hostedStoryRuns,
    Array.isArray(exp.hostedStoryRuns) ? exp.hostedStoryRuns.filter(isObject) : [],
    item => `${cleanOneLine(item?.storyPath ?? '')}\0${cleanOneLine(item?.testPath ?? '')}`,
  );
  const nativeChecks = mergeByKey(
    auto.nativeChecks,
    Array.isArray(exp.nativeChecks) ? exp.nativeChecks.filter(isObject) : [],
    item => `${trimNonBlank(item?.behavior) ?? ''}\0${trimNonBlank(item?.targetHost) ?? ''}\0${trimNonBlank(item?.runner) ?? ''}\0${trimNonBlank(item?.receipt?.receiptId) ?? ''}`,
  );
  return { ownerLookups, localLint, hostedStoryRuns, nativeChecks };
}

export function buildHumanBoundaryCard({
  root,
  focusPrompt = null,
  promptPaths = [],
  storyPaths = [],
  changedPaths = null,
  since = 0,
  env = process.env,
  evidence = null,
} = {}) {
  if (!root || typeof root !== 'string') return null;
  const rootReal = canonicalRoot(root);
  let visibleList = [];
  try { visibleList = gitFiles(rootReal); } catch { return null; }
  const visible = new Set(visibleList.filter(path => !path.startsWith('test/fixtures/')));
  const promptCache = new Map();
  const seedCache = new Map();

  const normalizedFocus = typeof focusPrompt === 'string' && focusPrompt ? normalizeRelPromptPath(focusPrompt) : null;

  const sliceChanged = Array.isArray(changedPaths)
    ? changedPaths.map(normalizeRelPromptPath).filter(p => p && visible.has(p))
    : gitChangedPaths(rootReal, visible);

  // Resolve owning prompts for changed production code files via `pdd owner` (`findOwners`).
  const autoOwnerLookups = [];
  const ownerResolvedPrompts = [];
  const prodChangedPaths = sliceChanged.filter(isProductionCodePath);
  if (prodChangedPaths.length > 0) {
    try {
      const resolved = findOwners({ root: rootReal, paths: prodChangedPaths }, { files: () => [...visible] });
      for (const file of Array.isArray(resolved?.files) ? resolved.files : []) {
        autoOwnerLookups.push({
          targetPath: file.path,
          ownerPrompt: file.owner ?? null,
          source: file.source ?? 'none',
          certain: Boolean(file.certain),
        });
        for (const owner of Array.isArray(file.owners) ? file.owners : []) {
          const normOwner = normalizeRelPromptPath(owner);
          if (normOwner.endsWith('.prompt.md') && visible.has(normOwner) && !isTestPromptPath(normOwner)) {
            ownerResolvedPrompts.push(normOwner);
          }
        }
      }
    } catch { /* ignore owner lookup read errors */ }
  }

  let foundTests = { tests: [], stories: [], nativeSelections: [] };
  try {
    foundTests = findTests({ root: rootReal, files: [...visible], excludeFixtureProjects: true });
  } catch {
    foundTests = { tests: [], stories: [], nativeSelections: [] };
  }

  const validTests = [];
  for (const entry of foundTests.tests ?? []) {
    if (entry?.doc && isObject(entry.doc) && entry.doc.schema_version === TEST_SCHEMA) {
      validTests.push(entry);
      continue;
    }
    if (typeof entry?.path === 'string' && visible.has(entry.path)) {
      const raw = readSafeText(rootReal, entry.path);
      if (raw) {
        try {
          const parsed = parseScenarioJson(raw);
          if (isObject(parsed) && parsed.schema_version === TEST_SCHEMA) validTests.push({ ...entry, doc: parsed });
        } catch { /* ignore unreadable JSON */ }
      }
    }
  }

  const storyTextCache = new Map();
  const readStory = path => {
    if (storyTextCache.has(path)) return storyTextCache.get(path);
    const text = isStoryPath(path) && visible.has(path) ? readSafeText(rootReal, path) : null;
    storyTextCache.set(path, text);
    return text;
  };

  const scenarioClosures = new Map();
  for (const testEntry of validTests) {
    const rawStoryPath = typeof testEntry.doc?.story_path === 'string' ? testEntry.doc.story_path : testEntry.storyPath;
    const sPath = rawStoryPath ? normalizeRelPromptPath(rawStoryPath) : '';
    const sText = sPath ? readStory(sPath) : null;
    const boundaryPrompts = sText ? parseStoryBoundaryPrompts(sText, sPath, visible) : [];
    scenarioClosures.set(testEntry.path, {
      testEntry,
      storyPath: sPath || null,
      boundaryPrompts,
      ...resolveScenarioClosure(testEntry.doc, boundaryPrompts, rootReal, visible, promptCache),
    });
  }

  // Select relevant Stories for this slice (approve focusPrompt vs. PR 1 slice).
  const candidateStoryPaths = new Set();
  for (const s of storyPaths ?? []) {
    const norm = normalizeRelPromptPath(s);
    if (norm && isStoryPath(norm) && visible.has(norm)) candidateStoryPaths.add(norm);
  }

  if (normalizedFocus) {
    for (const info of scenarioClosures.values()) {
      if (info.loadedPrompts.includes(normalizedFocus) || info.boundaryPrompts.includes(normalizedFocus)) {
        if (info.storyPath) candidateStoryPaths.add(info.storyPath);
      }
    }
    for (const p of visible) {
      if (!isStoryPath(p)) continue;
      const text = readStory(p);
      if (text && hasAcceptance(text) && parseStoryBoundaryPrompts(text, p, visible).includes(normalizedFocus)) {
        candidateStoryPaths.add(p);
      }
    }
    const focusRec = readPromptRecord(rootReal, visible, normalizedFocus, promptCache);
    if (focusRec?.kind !== 'native-only') {
      for (const p of sliceChanged) {
        if (isLintableStoryPath(p) && readStory(p) && hasAcceptance(readStory(p))) candidateStoryPaths.add(p);
      }
      for (const info of scenarioClosures.values()) {
        if (sliceChanged.includes(info.testEntry.path) && info.storyPath) candidateStoryPaths.add(info.storyPath);
      }
    }
  } else {
    for (const p of sliceChanged) {
      if (isLintableStoryPath(p) && readStory(p) && hasAcceptance(readStory(p))) candidateStoryPaths.add(p);
    }
    for (const info of scenarioClosures.values()) {
      if (sliceChanged.includes(info.testEntry.path) && info.storyPath) candidateStoryPaths.add(info.storyPath);
    }
  }

  const selectedStories = [...candidateStoryPaths].sort().filter(p => readStory(p) !== null);
  const selectedScenarios = [...scenarioClosures.values()].filter(info =>
    (info.storyPath && selectedStories.includes(info.storyPath))
    || (!normalizedFocus && sliceChanged.includes(info.testEntry.path))
    || (normalizedFocus && info.loadedPrompts.includes(normalizedFocus)),
  );

  // Collect owning prompts in scope.
  const owningPromptSet = new Set();
  if (normalizedFocus && visible.has(normalizedFocus)) owningPromptSet.add(normalizedFocus);
  for (const rawPrompt of promptPaths ?? []) {
    const p = normalizeRelPromptPath(rawPrompt);
    if (p.endsWith('.prompt.md') && visible.has(p) && !isTestPromptPath(p)) owningPromptSet.add(p);
  }
  if (!normalizedFocus || selectedStories.length > 0 || selectedScenarios.length > 0) {
    for (const p of sliceChanged) {
      if (p.endsWith('.prompt.md') && visible.has(p) && !isTestPromptPath(p)) owningPromptSet.add(p);
    }
    for (const p of ownerResolvedPrompts) owningPromptSet.add(p);
  }
  for (const sPath of selectedStories) {
    const sText = readStory(sPath);
    for (const p of parseStoryBoundaryPrompts(sText, sPath, visible)) {
      if (!isTestPromptPath(p)) owningPromptSet.add(p);
    }
  }

  const owningRecords = [...owningPromptSet]
    .sort()
    .map(p => readPromptRecord(rootReal, visible, p, promptCache))
    .filter(Boolean);

  const allLoadedPaths = new Set(selectedScenarios.flatMap(s => s.loadedPrompts));
  const allRelevantPromptRecords = [...new Set([...owningPromptSet, ...allLoadedPaths])]
    .sort()
    .map(p => readPromptRecord(rootReal, visible, p, promptCache))
    .filter(Boolean);

  const nativeOnlyRecords = allRelevantPromptRecords.filter(r => r.kind === 'native-only');
  const checkableOwners = owningRecords.filter(r => r.kind !== 'native-only');
  const unloadedOwners = selectedScenarios.length > 0
    ? checkableOwners.map(r => r.path).filter(p => !allLoadedPaths.has(p))
    : [];

  const relevantTestPaths = selectedScenarios.map(s => s.testEntry.path);
  const batchDiag = readSavedBatchDiagnostics(rootReal, { since, env, relevantTests: relevantTestPaths });

  // Build policy items & per-rule/criterion provenance rows.
  const policyItems = [];
  const provenanceRows = [];
  const savedNativeEvidence = readSavedNativeEvidenceRecords(rootReal);
  const nativeDeclaredStories = new Set(
    (foundTests.nativeSelections ?? []).map(item => normalizeRelPromptPath(item.storyPath)).filter(Boolean),
  );
  const storyMissingConnection = new Map();

  for (const sPath of selectedStories) {
    const sText = readStory(sPath) ?? '';
    const title = cleanOneLine(sText.split(/\r?\n/).find(l => l.startsWith('# '))?.slice(2) || basename(sPath, '.md'));
    const criteriaTexts = storyCriteria(sText);
    const rulesTexts = parseStorySectionLines(sText, /^##[ \t]+Rules to check[ \t]*\r?$/im);
    const hasNativeReceipt = savedNativeEvidence.receiptedPassingStories.has(sPath);
    const hasNativeDeclaration = nativeDeclaredStories.has(sPath) || /^##[ \t]+Native validation[ \t]*\r?$/im.test(stripHtmlComments(sText));
    const inScopeStory = stripExcludedStorySections(sText);
    const storyLinks = extractFragmentLinks(inScopeStory, sPath, visible);
    const brokenStoryFragments = [];
    const validStoryFragments = [];
    for (const link of storyLinks) {
      const inspected = inspectFragmentLink(link, rootReal, visible, promptCache);
      if (inspected.broken) brokenStoryFragments.push(inspected.broken);
      if (inspected.validFragment) validStoryFragments.push(inspected.validFragment);
    }

    for (const rule of rulesTexts) policyItems.push({ kind: 'rule', story: title, text: clipText(rule, 88) });
    for (const [idx, crit] of criteriaTexts.entries()) {
      policyItems.push({ kind: 'criterion', id: `AC${idx + 1}`, story: title, text: clipText(crit, 88) });
    }

    const storyStartIndex = provenanceRows.length;
    const storyScenarios = selectedScenarios.filter(s => s.storyPath === sPath);
    if (!storyScenarios.length) {
      if (hasNativeReceipt || (nativeOnlyRecords.length > 0 && checkableOwners.length === 0)) {
        const ownerLabel = nativeOnlyRecords.map(r => r.path).join(', ') || `${sPath} (native receipt)`;
        for (const [idx, crit] of criteriaTexts.entries()) {
          provenanceRows.push({
            label: `AC${idx + 1}`,
            summary: clipText(crit, 54),
            owner: ownerLabel,
            missingConnection: false,
            missingReason: null,
            observations: ['native test'],
            needsPortOrNative: false,
            zeroPortCalls: false,
            priority: 3,
          });
        }
      } else if (hasNativeDeclaration) {
        const ownerLabel = `${sPath} (Native validation)`;
        for (const [idx, crit] of criteriaTexts.entries()) {
          provenanceRows.push({
            label: `AC${idx + 1}`,
            summary: clipText(crit, 54),
            owner: ownerLabel,
            missingConnection: false,
            missingReason: null,
            observations: ['unverified (native receipt required)'],
            needsPortOrNative: true,
            zeroPortCalls: false,
            priority: 1,
          });
        }
      } else {
        const unexercised = checkableOwners.map(r => r.path).join(', ') || 'owning prompt';
        for (const [idx, crit] of criteriaTexts.entries()) {
          provenanceRows.push({
            label: `AC${idx + 1}`,
            summary: clipText(crit, 54),
            owner: `missing owner connection (no scenario loads ${unexercised})`,
            missingConnection: true,
            missingReason: `no scenario loads ${unexercised}`,
            observations: ['none'],
            needsPortOrNative: false,
            zeroPortCalls: false,
            priority: 0,
          });
        }
      }
      storyMissingConnection.set(sPath, provenanceRows.slice(storyStartIndex).some(r => r.missingConnection));
      continue;
    }

    // Evaluate each criterion across the Story's scenarios.
    for (const [idx, critText] of criteriaTexts.entries()) {
      const fallbackId = `AC${idx + 1}`;
      const matchedChecks = [];
      const loadedForCrit = new Map();
      const brokenForCrit = [...brokenStoryFragments];
      const targetedFragments = new Map();
      const addTargetedFragment = item => {
        if (!item?.target || !item?.fragment) return;
        if (!targetedFragments.has(item.target)) targetedFragments.set(item.target, new Set());
        targetedFragments.get(item.target).add(item.fragment);
      };
      for (const vf of validStoryFragments) addTargetedFragment(vf);
      let instrumentedZeroCalls = false;

      for (const scen of storyScenarios) {
        const doc = scen.testEntry.doc;
        const effectiveWorld = resolveInitialWorld(doc, rootReal, visible, seedCache);
        const docCriteria = Array.isArray(doc?.criteria) ? doc.criteria : [];
        const docCrit = docCriteria.find(c => c?.text === critText) ?? docCriteria[idx];
        const critId = typeof docCrit?.id === 'string' && docCrit.id ? docCrit.id : fallbackId;
        const savedTest = batchDiag.byTest.get(normalizeRelPromptPath(scen.testEntry.path));
        brokenForCrit.push(...scen.brokenFragments);
        for (const vf of scen.validFragments) addTargetedFragment(vf);

        for (const [stepIdx, step] of (Array.isArray(doc?.steps) ? doc.steps : []).entries()) {
          const stepChecks = (Array.isArray(step?.checks) ? step.checks : []).filter(c => c?.criterion_id === critId);
          if (!stepChecks.length) continue;
          for (const rec of scen.loadedRecords) loadedForCrit.set(rec.path, rec);
          const byId = typeof step?.step_id === 'string' && step.step_id ? savedTest?.stepObservations?.get(step.step_id) : undefined;
          const byIdxCandidate = savedTest?.stepObservationsByIndex?.[stepIdx];
          const savedStep = byId ?? (byIdxCandidate && !byIdxCandidate.stepId ? byIdxCandidate : undefined);
          const instrumented = instrumentedPortsForStep(doc, step, scen.loadedRecords);
          const classified = stepChecks.map((chk, cIdx) => {
            const candidatePool = savedStep?.checks ?? savedTest?.unkeyedChecks ?? [];
            const receiptChk = candidatePool.find(rc => rc?.criterion_id === critId && rc?.target === chk?.target && rc?.path === chk?.path)
              ?? savedStep?.checks?.[cIdx]
              ?? null;
            return classifyStepCheck(chk, doc, step, effectiveWorld, receiptChk);
          });
          if (instrumented.length > 0 && !classified.some(c => c.kind === 'observed simulated port call')) {
            if (savedStep?.observedCallTotal === 0) instrumentedZeroCalls = true;
          }
          matchedChecks.push(...classified);
        }
      }

      const loadedRecords = [...loadedForCrit.values()];
      const obsSet = new Set(matchedChecks.map(c => c.kind));
      if (hasNativeReceipt) obsSet.add('native test');
      const hasPortOrNative = obsSet.has('observed simulated port call') || obsSet.has('native test');
      const needsPortOrNative = !hasPortOrNative && matchedChecks.some(c => c.needsPortOrNative);
      const explicitZeroCalls = matchedChecks.some(c => c.zeroCalls);
      const zeroPortCalls = explicitZeroCalls || instrumentedZeroCalls;

      // Determine owner connection for this criterion!
      let missingConnection = false;
      let missingReason = null;
      if (normalizedFocus && focusRecIsCheckable(normalizedFocus, owningRecords) && !loadedForCrit.has(normalizedFocus)) {
        missingConnection = true;
        const selectedLabel = loadedRecords.map(r => r.path).join(', ') || 'none';
        missingReason = `unloaded owning source ${normalizedFocus}; scenario selects ${selectedLabel}`;
      } else if (brokenForCrit.length > 0) {
        missingConnection = true;
        const b = brokenForCrit[0];
        missingReason = b.empty
          ? `empty section #${b.fragment} in ${b.target}`
          : `missing section #${b.fragment} in ${b.target}`;
      } else {
        const ruleConn = ruleConnectedToSources(critText, loadedRecords, targetedFragments);
        if (!ruleConn.connected) {
          missingConnection = true;
          const unloadedHint = unloadedOwners.length ? `; unloaded in slice: ${unloadedOwners.join(', ')}` : '';
          missingReason = `${ruleConn.reason}${unloadedHint}`;
        } else if (unloadedOwners.length > 0) {
          const unloadedRecords = unloadedOwners.map(p => readPromptRecord(rootReal, visible, p, promptCache)).filter(Boolean);
          const loadedPaths = loadedRecords.map(r => r.path);
          if (loadedPaths.length && loadedPaths.every(p => /simulat|mock|stub|fake|harness/i.test(basename(p)))) {
            const unloadedMatch = unloadedRecords.filter(rec => ruleConnectedToSources(critText, [rec]).connected);
            if (unloadedMatch.length) {
              missingConnection = true;
              missingReason = `unloaded owning source ${unloadedMatch.map(r => r.path).join(', ')}; scenario only runs ${loadedPaths.join(', ')}`;
            }
          }
        }
      }

      const observations = formatObservationList(obsSet, { needsPortOrNative, explicitZeroCalls, instrumentedZeroCalls });
      const ownerDisplay = missingConnection
        ? `missing owner connection (${missingReason})`
        : loadedRecords.map(r => r.path).join(' -> ') || 'unmapped';
      const priority = missingConnection ? 0 : needsPortOrNative ? 1 : zeroPortCalls ? 2 : 3;

      provenanceRows.push({
        label: fallbackId,
        summary: clipText(critText, 50),
        owner: ownerDisplay,
        missingConnection,
        missingReason,
        observations,
        needsPortOrNative,
        zeroPortCalls,
        priority,
      });
    }

    // Also check explicit `## Rules to check` invariants so removed owning rules are always caught!
    const allStoryLoadedRecords = [...new Map(storyScenarios.flatMap(s => s.loadedRecords.map(r => [r.path, r]))).values()];
    const allStoryTargetedFragments = new Map();
    for (const vf of [...validStoryFragments, ...storyScenarios.flatMap(s => s.validFragments)]) {
      if (!allStoryTargetedFragments.has(vf.target)) allStoryTargetedFragments.set(vf.target, new Set());
      allStoryTargetedFragments.get(vf.target).add(vf.fragment);
    }
    const allStoryBroken = [...brokenStoryFragments, ...storyScenarios.flatMap(s => s.brokenFragments)];

    for (const [rIdx, ruleText] of rulesTexts.entries()) {
      const conn = ruleConnectedToSources(ruleText, allStoryLoadedRecords, allStoryTargetedFragments);
      const focusUnloaded = normalizedFocus && focusRecIsCheckable(normalizedFocus, owningRecords) && !allStoryLoadedRecords.some(r => r.path === normalizedFocus);
      const brokenFrag = allStoryBroken[0] ?? null;
      if (!conn.connected || focusUnloaded || brokenFrag) {
        const selectedLabel = allStoryLoadedRecords.map(r => r.path).join(', ') || 'none';
        const reason = focusUnloaded
          ? `unloaded owning source ${normalizedFocus}; scenario selects ${selectedLabel}`
          : brokenFrag
            ? `${brokenFrag.empty ? 'empty' : 'missing'} section #${brokenFrag.fragment} in ${brokenFrag.target}`
            : `${conn.reason}${unloadedOwners.length ? `; unloaded: ${unloadedOwners.join(', ')}` : ''}`;
        provenanceRows.push({
          label: `Rule ${rIdx + 1}`,
          summary: clipText(ruleText, 50),
          owner: `missing owner connection (${reason})`,
          missingConnection: true,
          missingReason: reason,
          observations: hasNativeReceipt ? ['native test'] : ['unverified rule owner'],
          needsPortOrNative: false,
          zeroPortCalls: false,
          priority: 0,
        });
      }
    }
    storyMissingConnection.set(sPath, provenanceRows.slice(storyStartIndex).some(r => r.missingConnection));
  }

  // Fallback policy summary when no Story exists in the slice (e.g. standalone prompt approval).
  if (!selectedStories.length && owningRecords.length) {
    for (const rec of owningRecords) {
      if (rec.kind === 'native-only') {
        policyItems.push({ kind: 'prompt', story: rec.path, text: `native-only boundary (${rec.reason || 'deterministic native tests'})` });
        provenanceRows.push({
          label: basename(rec.path, '.prompt.md'),
          summary: 'native-only boundary',
          owner: rec.path,
          missingConnection: false,
          missingReason: null,
          observations: ['native test'],
          needsPortOrNative: false,
          zeroPortCalls: false,
          priority: 3,
        });
      } else if (rec.operations.length) {
        policyItems.push({ kind: 'prompt', story: rec.path, text: `operations: ${rec.operations.join(', ')}` });
      } else {
        policyItems.push({ kind: 'prompt', story: rec.path, text: 'plain module prompt (verified through referencing Story or native tests)' });
      }
    }
  }

  // Verification split summary.
  const runtimeOps = allRelevantPromptRecords
    .filter(r => r.kind !== 'native-only')
    .map(r => r.operations.length ? `${r.path} (${r.operations.join(', ')})` : `${r.path} (plain)`);
  const nativeSplit = [
    ...nativeOnlyRecords.map(r => `${r.path} (native-only: ${clipText(r.reason || 'native tests', 60)})`),
    ...selectedStories
      .filter(s =>
        savedNativeEvidence.receiptedPassingStories.has(s)
        || nativeDeclaredStories.has(s)
        || /^##[ \t]+Native validation[ \t]*\r?$/im.test(stripHtmlComments(readStory(s) ?? '')),
      )
      .map(s => `${s} (Native validation)`),
  ];

  // Assemble review-summary evidence provenance across owner lookups, local lint, hosted runs, and native receipts.
  const autoHostedStoryRuns = [];
  for (const scen of selectedScenarios) {
    const savedTest = batchDiag.byTest.get(normalizeRelPromptPath(scen.testEntry.path));
    if (!savedTest) continue;
    const sPath = scen.storyPath ?? savedTest.storyPath;
    const storyText = sPath ? readStory(sPath) : null;
    const missingOwnerConn = Boolean(
      (sPath && storyMissingConnection.get(sPath))
      || unloadedOwners.length > 0
      || scen.brokenFragments.length > 0,
    );
    autoHostedStoryRuns.push(buildHostedRunSummary(scen, savedTest, storyText, missingOwnerConn));
  }
  const selectedStorySet = new Set(selectedStories);
  const autoNativeChecks = savedNativeEvidence.records
    .filter(item => selectedStorySet.size === 0 || selectedStorySet.has(item.storyPath))
    .map(item => item.check);
  const evidenceSummary = summarizeBoundaryEvidence(
    mergeEvidenceInputs(
      {
        ownerLookups: autoOwnerLookups,
        localLint: batchDiag.localLint,
        hostedStoryRuns: autoHostedStoryRuns,
        nativeChecks: autoNativeChecks,
      },
      evidence,
    ),
  );

  // Complexity budget & advisory sample divergences.
  const scopedPrompts = normalizedFocus ? owningRecords.filter(r => r.path === normalizedFocus) : owningRecords;
  const budgetPrompts = scopedPrompts.length ? scopedPrompts : allRelevantPromptRecords;
  const maxPrompt = budgetPrompts.reduce((best, r) => (!best || r.proseLoc > best.proseLoc ? r : best), null);
  const oversizes = budgetPrompts.filter(r => r.proseLoc > 500).map(r =>
    `${r.path} ${r.proseLoc} prose LOC (${r.proseLoc > 1000 ? 'elevated >1000' : 'over 500 budget'})`,
  );
  const scenarioStepCounts = selectedScenarios.map(s => ({
    path: s.testEntry.path,
    steps: Array.isArray(s.testEntry.doc?.steps) ? s.testEntry.doc.steps.length : 0,
    lines: (readSafeText(rootReal, s.testEntry.path) ?? '').split('\n').length,
  }));
  const totalSteps = scenarioStepCounts.reduce((acc, item) => acc + item.steps, 0);
  const stepWarnings = scenarioStepCounts
    .filter(item => item.steps > 15 || item.lines > 1000)
    .map(item => `${item.path} (${item.steps > 15 ? `${item.steps} steps >15` : ''}${item.steps > 15 && item.lines > 1000 ? ', ' : ''}${item.lines > 1000 ? `${item.lines} lines >1000` : ''})`);

  const proseSummary = maxPrompt
    ? budgetPrompts.length === 1
      ? `prose ${maxPrompt.proseLoc} LOC${maxPrompt.proseLoc > 500 ? ' (over 500 budget)' : ' (<=500)'}`
      : `${budgetPrompts.length} prompts (max ${maxPrompt.proseLoc} prose LOC${maxPrompt.proseLoc > 500 ? ', over 500 budget' : ''})`
    : 'prose 0 LOC';
  const stepSummary = scenarioStepCounts.length
    ? `scenario steps ${totalSteps}${stepWarnings.length ? ` (advisory: ${stepWarnings.join('; ')})` : ' (<=15)'}`
    : 'scenario steps 0';

  return {
    advisory: true,
    stories: selectedStories,
    policyItems,
    unloadedOwners,
    selectedSources: [...allLoadedPaths].sort(),
    provenanceRows,
    evidenceSummary,
    verificationSplit: {
      runtime: runtimeOps,
      native: nativeSplit,
    },
    complexity: {
      proseSummary,
      stepSummary,
      warnings: [...oversizes, ...stepWarnings],
    },
    sampleSummary: batchDiag.sampleSummary,
    divergences: batchDiag.divergences,
  };
}

function focusRecIsCheckable(focusPrompt, owningRecords) {
  const rec = owningRecords.find(r => r.path === focusPrompt);
  return Boolean(rec && rec.kind !== 'native-only');
}

function formatObservationList(obsSet, { needsPortOrNative, explicitZeroCalls, instrumentedZeroCalls }) {
  const out = [];
  if (obsSet.has('observed simulated port call')) {
    out.push(explicitZeroCalls ? 'observed simulated port call (0 observed port calls)' : 'observed simulated port call');
  }
  if (obsSet.has('supplied fact')) out.push('supplied fact');
  if (obsSet.has('model-returned value')) {
    const notes = [];
    if (instrumentedZeroCalls) notes.push('0 observed port calls on instrumented port');
    if (needsPortOrNative) notes.push('port spy or native observation still needed');
    out.push(notes.length ? `model-returned value (${notes.join('; ')})` : 'model-returned value');
  } else if (instrumentedZeroCalls && !obsSet.has('observed simulated port call')) {
    out.push('0 observed port calls on instrumented port');
  }
  if (obsSet.has('native test')) out.push('native test');
  return out.length ? out : ['unverified'];
}

export function fitBoundaryLines(headerLines, bodyLines, footerLines, maxLines = BOUNDARY_CARD_MAX_LINES) {
  const totalFixed = headerLines.length + footerLines.length;
  if (totalFixed >= maxLines) return [...headerLines, ...footerLines].slice(0, maxLines);
  const room = maxLines - totalFixed;
  if (bodyLines.length <= room) return [...headerLines, ...bodyLines, ...footerLines];
  if (room === 1) return [...headerLines, `  … +${bodyLines.length} provenance rows omitted`, ...footerLines];
  return [
    ...headerLines,
    ...bodyLines.slice(0, room - 1),
    `  … +${bodyLines.length - (room - 1)} more checks omitted for 1-screen budget`,
    ...footerLines,
  ];
}

export function formatApproveBoundaryCard(card) {
  if (!isObject(card)) return [];

  const header = ['Human boundary card (advisory):'];
  const policies = Array.isArray(card.policyItems) ? card.policyItems : [];
  if (policies.length) {
    const shown = policies.slice(0, 3).map(p => `${p.id ? `${p.id}: ` : ''}${p.text}`);
    const extra = policies.length > 3 ? ` (+${policies.length - 3} more)` : '';
    header.push(`  Policy: ${shown.join(' | ')}${extra}`);
  }
  if (Array.isArray(card.unloadedOwners) && card.unloadedOwners.length) {
    const selected = Array.isArray(card.selectedSources) && card.selectedSources.length ? card.selectedSources.join(', ') : 'none';
    header.push(`  Owner gap: missing owner connection for ${card.unloadedOwners.join(', ')} (unloaded; scenario selects ${selected})`);
  }

  const evidenceEntries = Array.isArray(card.evidenceSummary?.entries) ? card.evidenceSummary.entries : [];
  const evidenceItems = evidenceEntries.map(entry => ({
    priority: evidenceEntryPriority(entry),
    line: formatEvidenceEntryPlain(entry),
  }));
  const provenanceItems = (Array.isArray(card.provenanceRows) ? card.provenanceRows : []).map(row => ({
    priority: row.priority ?? 3,
    line: `    - ${row.label} (${row.summary}): owner=${row.owner} · obs=${(row.observations ?? []).join(', ')}`,
  }));

  const rt = card.verificationSplit?.runtime ?? [];
  const nat = card.verificationSplit?.native ?? [];
  const rtText = rt.length ? rt.slice(0, 2).join(', ') + (rt.length > 2 ? ` (+${rt.length - 2} more)` : '') : 'none';
  const natText = nat.length ? nat.slice(0, 2).join(', ') + (nat.length > 2 ? ` (+${nat.length - 2} more)` : '') : 'code / unit tests';
  const samplePart = card.sampleSummary ? ` · ${card.sampleSummary}` : '';
  const footer = [
    `  Verification split: runtime=[${rtText}] · native=[${natText}]`,
    `  Budget & samples: ${card.complexity?.proseSummary ?? 'prose 0 LOC'} · ${card.complexity?.stepSummary ?? 'scenario steps 0'}${samplePart}`,
  ];

  return fitSectionedBoundaryLines({
    headerLines: header,
    footerLines: footer,
    evidenceHeading: '  Evidence:',
    evidenceItems,
    evidenceOmit: count => `  … +${count} more evidence entries omitted`,
    provenanceHeading: '  Provenance:',
    provenanceItems,
    provenanceEmpty: '  Provenance: no Story scenario checks in this slice (standalone / exploratory or native-tested).',
    provenanceOmit: count => `  … +${count} more checks omitted for 1-screen budget`,
    maxLines: BOUNDARY_CARD_MAX_LINES,
  }).map(sanitizeBoundaryLine);
}
