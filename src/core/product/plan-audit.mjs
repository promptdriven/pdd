// Generated from prompts/cli/product.prompt.md.
// Pure product plan prompt-inventory & boundary-wiring auditor (Layer 1 core).
import {
  EXAMPLE_DIR_RE, PROMPT_PATH_COLS, SIMPLE_ID_RE, VERSION_RE, buildPartLookups, clean, csv,
  findSectionLines, hasPromptFilenameStem, isIdentChar, isSeparatorRow, matchPartMentionInHeading,
  normalizeRepoPath, resolvePlanRelativePrompt, rowsWithMeta, scanMarkdownLinksLinear,
  stripMarkdownLinkTargetsLinear, stripUrlsLinear, tableCells,
} from './markdown-utils.mjs';

const NON_OP_EXTENSIONS = new Set([
  'md', 'mdx', 'json', 'jsonc', 'jsonl', 'mjs', 'cjs', 'js', 'jsx', 'ts', 'tsx', 'mts', 'cts',
  'py', 'pyi', 'go', 'rs', 'rb', 'java', 'kt', 'cs', 'swift', 'php', 'lua', 'sh', 'bash', 'zsh',
  'sql', 'ddl', 'db', 'sqlite', 'sqlite3', 'yaml', 'yml', 'toml', 'ini', 'cfg', 'conf', 'env',
  'xml', 'xsd', 'html', 'htm', 'css', 'scss', 'svg', 'png', 'jpg', 'jpeg', 'gif', 'webp', 'ico',
  'pdf', 'csv', 'tsv', 'txt', 'rst', 'log', 'lock', 'proto', 'graphql', 'gql', 'prisma',
  'prompt', 'test', 'spec', 'com', 'org', 'net', 'io', 'dev', 'app', 'ai', 'gov', 'edu', 'local', 'localhost', 'example', 'invalid',
]);

function extractPromptRefsFromLine(line, fallbackFolder) {
  const source = String(line ?? '');
  const rawRefs = [];
  const nonLinkChunks = [];
  let cursor = 0;

  scanMarkdownLinksLinear(source, (start, end, _label, rawTarget) => {
    nonLinkChunks.push(source.slice(cursor, start), ' ');
    cursor = end;
    let target = rawTarget.trim();
    if (target.startsWith('<') && target.endsWith('>')) target = target.slice(1, -1).trim();
    const space = target.search(/\s/);
    if (space >= 0) target = target.slice(0, space);
    if (target.includes('://') || /^mailto:/i.test(target)) return;
    const hash = target.indexOf('#');
    if (hash >= 0) target = target.slice(0, hash);
    if (hasPromptFilenameStem(target)) rawRefs.push(target);
  });
  nonLinkChunks.push(source.slice(cursor));

  const text = stripUrlsLinear(nonLinkChunks.join(''));
  let tokenStart = -1;
  const isDelim = ch => ' \t,;()[]{}"\'`<>|'.includes(ch);
  const flushToken = end => {
    if (tokenStart < 0) return;
    let tok = text.slice(tokenStart, end);
    tokenStart = -1;
    while (tok.length && (tok.endsWith('.') || tok.endsWith(':') || tok.endsWith('*'))) {
      if (tok.endsWith('.prompt.md')) break;
      tok = tok.slice(0, -1);
    }
    while (tok.length && tok.startsWith('*')) tok = tok.slice(1);
    const hash = tok.indexOf('#');
    if (hash >= 0) tok = tok.slice(0, hash);
    if (hasPromptFilenameStem(tok)) rawRefs.push(tok);
  };
  for (let i = 0; i < text.length; i++) {
    if (isDelim(text[i])) flushToken(i);
    else if (tokenStart < 0) tokenStart = i;
  }
  flushToken(text.length);

  const normalized = [];
  for (const ref of rawRefs) {
    const norm = resolvePlanRelativePrompt(ref, fallbackFolder);
    if (norm) normalized.push(norm);
  }
  return normalized;
}

export function parsePlanPrompts(planText, parts = []) {
  const sec = findSectionLines(planText, 'Prompts', { caseInsensitive: true });
  if (!sec) return { hasSection: false, prompts: [] };
  const { folderByPart, partsByFolderDesc, inferPart } = buildPartLookups(parts);
  const seen = new Map();
  let currentPart = '', currentFolder = '', tableHeader = null, partCol = -1, promptCols = [];
  const record = (path, hintPart, line) => {
    if (!seen.has(path)) seen.set(path, { path, part: inferPart(path, hintPart), line });
  };

  for (const item of sec.lines) {
    const trimmed = item.text.trim();
    if (!trimmed) { tableHeader = null; partCol = -1; promptCols = []; continue; }
    const sub = /^#{3,6}[ \t]+(.+)$/.exec(trimmed);
    if (sub) {
      tableHeader = null; partCol = -1; promptCols = [];
      const matched = matchPartMentionInHeading(sub[1], partsByFolderDesc, folderByPart);
      currentPart = matched ? matched.part : '';
      currentFolder = matched ? matched.folder : '';
      continue;
    }
    if (/^\s*\|/.test(item.text)) {
      const cells = tableCells(item.text);
      if (!tableHeader) {
        tableHeader = cells;
        partCol = cells.findIndex(c => ['part', 'owner'].includes(c.toLowerCase()));
        promptCols = cells.map((c, idx) => (PROMPT_PATH_COLS.has(c.toLowerCase()) ? idx : -1)).filter(idx => idx >= 0);
        continue;
      }
      if (isSeparatorRow(cells)) continue;
      const rowPart = partCol >= 0 ? clean(cells[partCol] ?? '') : '';
      const rowFolder = (rowPart && folderByPart.get(rowPart)) || currentFolder;
      const cellsToScan = promptCols.length > 0 ? promptCols.map(idx => cells[idx] ?? '') : cells;
      for (const cell of cellsToScan) {
        for (const path of extractPromptRefsFromLine(cell, rowFolder)) record(path, rowPart || currentPart, item.lineNo);
      }
      continue;
    }
    tableHeader = null; partCol = -1; promptCols = [];
    let linePart = currentPart, lineFolder = currentFolder;
    const leadText = trimmed.replace(/^(?:[-*+]|\d+[.)])\s+/, '').replace(/^\*\*([^*\r\n]+)\*\*/, '$1');
    const promptExtIdx = leadText.indexOf('.prompt.md');
    let leadPrefix = leadText;
    if (promptExtIdx >= 0) {
      let cut = promptExtIdx;
      while (cut > 0 && !/\s/.test(leadText[cut - 1])) cut--;
      leadPrefix = leadText.slice(0, cut).trim();
    }
    const leadMatch = leadPrefix ? matchPartMentionInHeading(leadPrefix, partsByFolderDesc, folderByPart) : null;
    if (leadMatch) { linePart = leadMatch.part; lineFolder = leadMatch.folder; }
    for (const path of extractPromptRefsFromLine(trimmed, lineFolder)) record(path, linePart, item.lineNo);
  }
  return { hasSection: true, prompts: [...seen.values()] };
}

function extractBoundaryOpsFromText(text, { requirePartPrefix = false, from = '', to = '', line = 1, knownParts = new Set() } = {}) {
  const withoutUrls = stripMarkdownLinkTargetsLinear(stripUrlsLinear(text));
  const ops = [];
  const isDelim = ch => ' \t,;()[]{}"\'`<>|'.includes(ch);
  let start = -1;

  const inspect = rawTok => {
    let tok = rawTok;
    while (tok.length && (tok.endsWith('.') || tok.endsWith(':') || tok.endsWith('*'))) tok = tok.slice(0, -1);
    while (tok.length && (tok.startsWith('*') || tok.startsWith('.'))) tok = tok.slice(1);
    if (!tok.includes('.')) return;
    const segs = tok.split('/');
    if (segs.length === 3 && segs[0] === 'prompts') segs.shift();
    if (segs.length !== 1 && segs.length !== 2) return;
    if (requirePartPrefix && segs.length !== 2) return;
    const explicitPart = segs.length === 2 ? segs[0] : '';
    const pair = segs[segs.length - 1];
    if (explicitPart && (!SIMPLE_ID_RE.test(explicitPart) || VERSION_RE.test(explicitPart))) return;
    const dot = pair.indexOf('.');
    if (dot <= 0 || dot !== pair.lastIndexOf('.')) return;
    const target = pair.slice(0, dot), op = pair.slice(dot + 1);
    if (target.length < 2 || op.length < 2 || !SIMPLE_ID_RE.test(target) || !SIMPLE_ID_RE.test(op)) return;
    if (VERSION_RE.test(target) || VERSION_RE.test(op) || NON_OP_EXTENSIONS.has(op.toLowerCase())) return;
    const toParts = csv(to);
    const inferredTo = toParts.length === 1 && (!knownParts.size || knownParts.has(toParts[0])) && !['*', 'all'].includes(toParts[0].toLowerCase()) ? toParts[0] : '';
    const part = explicitPart || inferredTo;
    const raw = explicitPart ? `${explicitPart}/${target}.${op}` : `${target}.${op}`;
    ops.push({ raw, explicitPart, part, target, op, shortName: `${target}.${op}`, from, to, line });
  };

  for (let i = 0; i < withoutUrls.length; i++) {
    if (isDelim(withoutUrls[i])) { if (start >= 0) { inspect(withoutUrls.slice(start, i)); start = -1; } }
    else if (start < 0) start = i;
  }
  if (start >= 0) inspect(withoutUrls.slice(start));
  return ops;
}

export function parsePlanBoundaryOperations(planText, parts = []) {
  const sec = findSectionLines(planText, 'Boundaries', { caseInsensitive: true });
  if (!sec) return { hasSection: false, operations: [] };
  const knownParts = new Set(parts.map(p => p.part).filter(Boolean));
  const seen = new Map();
  const addOp = item => {
    const key = `${item.part}\0${item.shortName}`, existing = seen.get(key);
    if (!existing) { seen.set(key, item); return; }
    if ((!existing.explicitPart && item.explicitPart) || (!existing.from && item.from)) {
      seen.set(key, { ...existing, ...item, explicitPart: existing.explicitPart || item.explicitPart, from: existing.from || item.from, to: existing.to || item.to });
    }
  };

  let heading = null, inNeverCrosses = false, neverCrossesSawBody = false;
  for (const item of sec.lines) {
    const trimmed = item.text.trim();
    if (!trimmed) {
      heading = null;
      if (inNeverCrosses && neverCrossesSawBody) { inNeverCrosses = false; neverCrossesSawBody = false; }
      continue;
    }
    if (/^\s*\|/.test(item.text)) {
      inNeverCrosses = false; neverCrossesSawBody = false;
      const cells = tableCells(item.text);
      if (!heading) { heading = cells; continue; }
      if (isSeparatorRow(cells)) continue;
      const fromIdx = heading.findIndex(c => c.toLowerCase() === 'from');
      const toIdx = heading.findIndex(c => c.toLowerCase() === 'to');
      const crossesIdx = heading.findIndex(c => c.toLowerCase() === 'what crosses');
      const opsIdx = heading.findIndex(c => ['operations', 'operation', 'ops'].includes(c.toLowerCase()));
      const from = fromIdx >= 0 ? (cells[fromIdx] ?? '') : '', to = toIdx >= 0 ? (cells[toIdx] ?? '') : '';
      for (const idx of [crossesIdx, opsIdx]) {
        if (idx < 0 || !cells[idx]) continue;
        for (const op of extractBoundaryOpsFromText(cells[idx], { requirePartPrefix: false, from, to, line: item.lineNo, knownParts })) addOp(op);
      }
      continue;
    }
    heading = null;
    const isSubheading = /^#{3,6}[ \t]+/.test(trimmed);
    const neverMatch = /^(?:#{3,6}[ \t]+|(?:[-*+]|\d+[.)])[ \t]+)?(?:\*\*)?never[ \t]+crosses\b/i.exec(trimmed);
    if (neverMatch) {
      const rest = trimmed.slice(neverMatch[0].length).replace(/^\*\*/, '').trim().replace(/^:/, '').trim().replace(/^\*\*/, '').trim();
      inNeverCrosses = true; neverCrossesSawBody = rest.length > 0;
      continue;
    }
    if (isSubheading) { inNeverCrosses = false; neverCrossesSawBody = false; }
    if (inNeverCrosses) { neverCrossesSawBody = true; continue; }
    for (const op of extractBoundaryOpsFromText(trimmed, { requirePartPrefix: true, line: item.lineNo, knownParts })) addOp(op);
  }
  return { hasSection: true, operations: [...seen.values()] };
}

function parseLenientMapParts(mapText) {
  if (!mapText || typeof mapText !== 'string') return [];
  const meta = rowsWithMeta(mapText, 'Parts', 'product/map.md', { required: false });
  if (!meta.heading || !meta.heading.includes('Part') || !meta.heading.includes('Folder')) return [];
  return meta.rows.map(item => ({ part: item.values.Part, folder: item.values.Folder })).filter(item => item.part && item.folder);
}

function stripFrontmatterAndComments(raw) {
  let text = String(raw ?? '');
  if (text.startsWith('---\n') || text.startsWith('---\r\n')) {
    let pos = text.startsWith('---\r\n') ? 5 : 4;
    while (pos <= text.length) {
      const nl = text.indexOf('\n', pos), end = nl < 0 ? text.length : nl;
      if (text.slice(pos, end).replace(/\r$/, '') === '---') { text = text.slice(nl < 0 ? text.length : nl + 1); break; }
      if (nl < 0) break;
      pos = nl + 1;
    }
  }
  const out = []; let cursor = 0;
  while (cursor < text.length) {
    const open = text.indexOf('<!--', cursor);
    if (open < 0) { out.push(text.slice(cursor)); break; }
    out.push(text.slice(cursor, open), ' ');
    const close = text.indexOf('-->', open + 4);
    if (close < 0) break;
    cursor = close + 3;
  }
  return out.join('');
}

function extractRuntimeInterfacesLinear(raw) {
  const text = String(raw ?? ''), lower = text.replace(/[A-Z]+/g, s => s.toLowerCase()), out = [];
  let pos = 0;
  while (pos < lower.length) {
    const det = lower.indexOf('<details', pos);
    if (det < 0) break;
    const detClose = lower.indexOf('</details>', det + 8);
    if (detClose < 0) break;
    const innerLower = lower.slice(det + 8, detClose);
    const relSum = innerLower.indexOf('<summary');
    const relSumClose = relSum >= 0 ? innerLower.indexOf('</summary>', relSum + 8) : -1;
    if (relSum >= 0 && relSumClose > relSum && /runtime\s+interface/i.test(text.slice(det + 8 + relSum, det + 8 + relSumClose))) {
      const inner = text.slice(det + 8 + relSumClose + 10, detClose);
      const fenceStart = inner.indexOf('```');
      if (fenceStart >= 0) {
        const nl = inner.indexOf('\n', fenceStart + 3), fenceEnd = nl >= 0 ? inner.indexOf('```', nl + 1) : -1;
        if (nl >= 0 && fenceEnd > nl) {
          try { const parsed = JSON.parse(inner.slice(nl + 1, fenceEnd)); if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) out.push(parsed); } catch {}
        }
      }
    }
    pos = detClose + 10;
  }
  return out;
}

function precedingSegmentBeforeSlash(text, slashIdx) {
  let start = slashIdx - 1;
  while (start >= 0 && isIdentChar(text[start])) start--;
  return text.slice(start + 1, slashIdx);
}

function containsBoundaryOpToken(text, needle, requiredPartPrefix = '') {
  if (!needle) return false;
  let from = 0;
  while (from <= text.length - needle.length) {
    const idx = text.indexOf(needle, from);
    if (idx < 0) return false;
    from = idx + 1;
    const after = text[idx + needle.length] ?? '', afterNext = text[idx + needle.length + 1] ?? '';
    if (isIdentChar(after) || (after === '.' && isIdentChar(afterNext))) continue;
    const before = idx > 0 ? text[idx - 1] : '';
    if (isIdentChar(before) || before === '.') continue;
    if (before === '/') {
      const seg = precedingSegmentBeforeSlash(text, idx - 1);
      if (needle.includes('/')) { if (seg && seg !== 'prompts') continue; }
      else if (requiredPartPrefix && seg !== requiredPartPrefix) continue;
    }
    return true;
  }
  return false;
}

function containsBraceBoundaryOp(text, target, op, requiredPartPrefix = '') {
  const prefix = `${target}.{`;
  let from = 0;
  while (from < text.length) {
    const idx = text.indexOf(prefix, from);
    if (idx < 0) return false;
    const bodyStart = idx + prefix.length, before = idx > 0 ? text[idx - 1] : '';
    if (isIdentChar(before) || before === '.' || (before === '/' && requiredPartPrefix && precedingSegmentBeforeSlash(text, idx - 1) !== requiredPartPrefix)) {
      from = bodyStart; continue;
    }
    let stop = bodyStart;
    while (stop < text.length && text[stop] !== '}' && text[stop] !== '{' && text[stop] !== '\n') stop++;
    if (stop >= text.length) return false;
    if (text[stop] !== '}') { from = text[stop] === '\n' ? stop + 1 : Math.max(bodyStart, stop - prefix.length + 1); continue; }
    if (text.slice(bodyStart, stop).split(',').map(s => s.trim()).includes(op)) return true;
    from = stop + 1;
  }
  return false;
}

const promptStemNormalized = path => {
  const slash = path.lastIndexOf('/');
  return (slash >= 0 ? path.slice(slash + 1) : path).replace(/\.prompt\.md$/i, '').toLowerCase().replace(/_/g, '-');
};

function runtimeInterfaceWiresOp(ifaces, boundaryOp) {
  const normTarget = boundaryOp.target.toLowerCase().replace(/_/g, '-');
  for (const iface of ifaces) {
    for (const call of Array.isArray(iface.calls) ? iface.calls : []) {
      if (call?.target_operation !== boundaryOp.op || typeof call?.target !== 'string') continue;
      if (promptStemNormalized(call.target) !== normTarget) continue;
      if (boundaryOp.explicitPart && !call.target.split('/').includes(boundaryOp.explicitPart)) continue;
      return true;
    }
    for (const res of Array.isArray(iface.resources) ? iface.resources : []) {
      if (typeof res?.name !== 'string' || !Array.isArray(res.operations)) continue;
      const rName = res.name.toLowerCase().replace(/_/g, '-');
      const namesMatch = rName === normTarget
        || (boundaryOp.part && (rName === `${boundaryOp.part.toLowerCase()}-${normTarget}` || rName === `${boundaryOp.part.toLowerCase()}/${normTarget}`));
      if (namesMatch && res.operations.some(item => item?.name === boundaryOp.op)) return true;
    }
  }
  return false;
}

export function auditProductPlan({ mapText = '', planText = '', promptFiles = [] } = {}) {
  const plan = String(planText ?? '');
  if (!plan.trim()) return { drift: [], unwiredBoundaries: [], findings: [], warnings: [] };
  const parts = parseLenientMapParts(mapText);
  const { folderByPart, inferPart } = buildPartLookups(parts);
  const knownParts = new Set(parts.map(p => p.part).filter(Boolean));
  const promptsInfo = parsePlanPrompts(plan, parts);
  const boundariesInfo = parsePlanBoundaryOperations(plan, parts);
  const allowExamples = [...folderByPart.values()].some(f => EXAMPLE_DIR_RE.test(f))
    || promptsInfo.prompts.some(item => EXAMPLE_DIR_RE.test(item.path));

  const normalizedPrompts = [], seenPromptPaths = new Set();
  for (const item of Array.isArray(promptFiles) ? promptFiles : []) {
    const path = normalizeRepoPath(item?.path ?? '');
    if (!path || !path.endsWith('.prompt.md') || typeof item?.content !== 'string' || seenPromptPaths.has(path)) continue;
    if (!allowExamples && EXAMPLE_DIR_RE.test(path)) continue;
    seenPromptPaths.add(path);
    normalizedPrompts.push({ path, content: item.content });
  }
  normalizedPrompts.sort((a, b) => a.path.localeCompare(b.path));

  const drift = [];
  if (promptsInfo.hasSection && promptsInfo.prompts.length > 0) {
    const declaredSet = new Set(promptsInfo.prompts.map(item => item.path));
    const actualSet = new Set(normalizedPrompts.map(item => item.path));
    const folderSet = new Set(folderByPart.values());
    for (const item of promptsInfo.prompts) { const slash = item.path.lastIndexOf('/'); if (slash > 0) folderSet.add(item.path.slice(0, slash)); }
    const trackedFolders = [...folderSet].sort((a, b) => b.length - a.length || a.localeCompare(b));
    for (const item of promptsInfo.prompts) {
      if (actualSet.has(item.path)) continue;
      drift.push({
        filePath: 'product/plan.md', line: item.line, order: 20, code: 'product-prompt-inventory-drift', category: 'product plan',
        relatedPrompts: [item.path],
        detail: `Declared prompt \`${item.path}\` in product/plan.md ## Prompts is missing on disk.`,
        statusWarning: `Warning: Prompt inventory drift: ${item.path} is declared in product/plan.md ## Prompts but missing on disk.`,
      });
    }
    for (const item of normalizedPrompts) {
      if (declaredSet.has(item.path)) continue;
      const folder = trackedFolders.find(dir => item.path.startsWith(`${dir}/`));
      if (!folder) continue;
      drift.push({
        filePath: item.path, line: 1, order: 21, code: 'product-prompt-inventory-drift', category: 'product plan',
        relatedPrompts: [item.path],
        detail: `Prompt file exists on disk under tracked folder \`${folder}\` but is not listed in product/plan.md ## Prompts.`,
        statusWarning: `Warning: Prompt inventory drift: ${item.path} exists under ${folder} but is not declared in product/plan.md ## Prompts.`,
      });
    }
  }

  const unwiredBoundaries = [];
  if (boundariesInfo.hasSection && boundariesInfo.operations.length > 0) {
    const indexedPrompts = normalizedPrompts.map(item => ({
      path: item.path, normStem: promptStemNormalized(item.path),
      cleaned: stripFrontmatterAndComments(item.content), ifaces: extractRuntimeInterfacesLinear(item.content),
    }));
    for (const b of boundariesInfo.operations) {
      const ownerPart = b.explicitPart || b.part;
      const ownerFolder = ownerPart ? (folderByPart.get(ownerPart) ?? `prompts/${ownerPart}`) : '';
      const normTarget = b.target.toLowerCase().replace(/_/g, '-');
      const isInOwnerPart = p => {
        if (!ownerPart) return false;
        const pPart = inferPart(p.path);
        return pPart ? pPart === ownerPart : (p.path.startsWith(`${ownerFolder}/`) || p.path.split('/').includes(ownerPart));
      };
      const definingPaths = new Set();
      let matchedByStem = false;
      for (const p of indexedPrompts) {
        if (p.normStem === normTarget && (!ownerPart || isInOwnerPart(p))) { definingPaths.add(p.path); matchedByStem = true; }
        if (p.ifaces.some(iface => Array.isArray(iface.entries) && iface.entries.some(e => e?.operation === b.shortName))) definingPaths.add(p.path);
        if (p.ifaces.some(iface => Array.isArray(iface.entries) && iface.entries.some(e => e?.operation === b.op)) && p.normStem === normTarget && (!ownerPart || isInOwnerPart(p))) {
          definingPaths.add(p.path); matchedByStem = true;
        }
      }
      if (!matchedByStem && ownerPart) {
        for (const p of indexedPrompts) if (isInOwnerPart(p) && p.ifaces.some(iface => Array.isArray(iface.entries) && iface.entries.some(e => e?.operation === b.op))) definingPaths.add(p.path);
      }
      if (!definingPaths.size && !b.explicitPart) {
        for (const p of indexedPrompts) if (p.normStem === normTarget) definingPaths.add(p.path);
      }
      const fromParts = csv(b.from);
      const isCrossPartBoundary = Boolean(ownerPart && knownParts.has(ownerPart) && fromParts.length > 0 && fromParts.some(fp => knownParts.has(fp)) && !fromParts.includes(ownerPart));
      const wired = indexedPrompts.some(p => {
        if (definingPaths.has(p.path)) return false;
        if (isCrossPartBoundary && isInOwnerPart(p)) return false;
        if (b.raw.includes('/') && containsBoundaryOpToken(p.cleaned, b.raw, '')) return true;
        if (containsBoundaryOpToken(p.cleaned, b.shortName, ownerPart)) return true;
        if (containsBraceBoundaryOp(p.cleaned, b.target, b.op, ownerPart)) return true;
        return runtimeInterfaceWiresOp(p.ifaces, b);
      });
      if (!wired) {
        unwiredBoundaries.push({
          filePath: 'product/plan.md', line: b.line, order: 25, code: 'product-boundary-unwired', category: 'product plan',
          relatedPrompts: [...definingPaths],
          detail: `Declared boundary operation \`${b.raw}\` in product/plan.md ## Boundaries is not referenced by any consumer prompt.`,
          statusWarning: `Warning: Unwired boundary operation: ${b.raw} declared in product/plan.md ## Boundaries is not referenced by any consumer prompt.`,
        });
      }
    }
  }
  const findings = [...drift, ...unwiredBoundaries];
  return { drift, unwiredBoundaries, findings, warnings: findings.map(f => f.statusWarning) };
}
