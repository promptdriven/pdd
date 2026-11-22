// Generated from prompts/cli/svg-layout.prompt.md.
// .ui.svg link/scoping parser and top-level lintSvgLayouts orchestrator.
import { dirname, relative, resolve, sep } from 'node:path';
import { workspace } from '../../shared/workspace-policy.mjs';
import { discoverTestAndAppMaps, lintAppMaps } from './app-map-lint.mjs';
import { lintScenarioFiles } from './scenario-lint.mjs';
import { decodeHtml, escaped, extractControls, mentioned, mentionedNormalized, normalize } from './svg-controls.mjs';
import { markupTokens, partsOf, safeRead } from './svg-xml.mjs';

const ROOT_PLACEHOLDER = '/__pdd_root__';

const REF_DEF_RE = /^\s*\[([^\]]+)\]:\s*<?([^\s>]+)>?(?:\s+(?:"[^"\n]*"|'[^'\n]*'|\([^)\n]*\)))?\s*$/gm;
const refDefs = text => new Map([...text.matchAll(REF_DEF_RE)].map(m => [normalize(m[1]), m[2]]));

function links(text, refs = refDefs(text), imagesOnly = false) {
  const inlineRe = imagesOnly
    ? /!\[[^\]]*\]\(\s*(?:<([^>]+)>|([^\s)]+))(?:\s+["'][^)]*)?\)/g
    : /!?\[[^\]]*\]\(\s*(?:<([^>]+)>|([^\s)]+))(?:\s+["'][^)]*)?\)/g;
  const refRe = imagesOnly ? /!\[([^\]]*)\]\[([^\]]*)\]/g : /!?\[([^\]]*)\]\[([^\]]*)\]/g;
  const shortRe = imagesOnly ? /!\[([^\]]+)\](?![\[(:])/g : /!?\[([^\]]+)\](?![\[(:])/g;
  return [...new Set([
    ...[...text.matchAll(inlineRe)].map(m => m[1] || m[2]),
    ...[...text.matchAll(refRe)].map(m => refs.get(normalize(m[2] || m[1]))),
    ...[...text.matchAll(shortRe)].map(m => refs.get(normalize(m[1]))),
  ].filter(value => value && !/^(?:[a-z][a-z\d+.-]*:|\/\/|#)/i.test(value) && /\.ui\.svg(?:#.*)?$/i.test(value)).map(value => value.split('#')[0]))];
}

function stripCodeFences(text) {
  const out = [];
  let fence = null;
  for (const line of text.replace(/\r\n?/g, '\n').split('\n')) {
    const fm = /^ {0,3}(`{3,}|~{3,})/.exec(line);
    if (fence) {
      if (fm && fm[1][0] === fence[0] && fm[1].length >= fence.length && /^ {0,3}(?:`+|~+)[ \t]*$/.test(line)) fence = null;
      out.push('');
      continue;
    }
    if (fm) { fence = fm[1]; out.push(''); continue; }
    out.push(line);
  }
  return out.join('\n');
}

function uploadCapturedSvgLinks(text, refs = refDefs(text)) {
  const depsBody = [...stripCodeFences(text).matchAll(/^##+[ \t]+Dependencies\b[^\n]*\n([\s\S]*?)(?=^##?[ \t]|$(?![\s\S]))/gim)].map(m => m[1]).join('\n');
  return [...new Set([...links(text, refs, true), ...links(depsBody, refs, false)])];
}

const resolveDrawing = (root, prompt, link) => {
  try { return relative(root, resolve(root, dirname(prompt), decodeURIComponent(link))).split(sep).join('/'); } catch { return link; }
};
const intersectTargets = (a, b) => {
  if (!a) return b;
  if (!b) return a;
  const both = new Set([...a].filter(item => b.has(item)));
  return both.size ? both : b;
};

function drawingTokenMap(drawings) {
  const states = drawings.map(d => normalize(d.split('/').at(-1).replace(/\.ui\.svg$/i, '').split('__')[0]).split(/[-_\s]+/).filter(Boolean));
  let prefix = 0;
  while (states.every(words => words.length > prefix + 1 && words[prefix] === states[0][prefix])) prefix++;
  const map = new Map();
  const add = (token, drawing) => {
    const clean = normalize(token);
    if (!clean || /^\d+$/.test(clean)) return;
    if (!map.has(clean)) map.set(clean, new Set());
    map.get(clean).add(drawing);
  };
  drawings.forEach((drawing, idx) => {
    const stem = drawing.split('/').at(-1).replace(/\.ui\.svg$/i, '');
    const [state, mode] = stem.split('__');
    const candidates = [stem, state, ...state.split('--'), ...(mode ? [mode, ...mode.split('--')] : [])];
    if (prefix > 0) candidates.push(states[idx].slice(prefix).join('-'));
    for (const candidate of candidates) { add(candidate, drawing); add(candidate.replace(/[-_]+/g, ' '), drawing); }
  });
  for (const [token, owners] of map) if (owners.size >= drawings.length) map.delete(token);
  return map;
}

function matchTokens(label, tokenMap, total) {
  if (!label) return null;
  const spaced = label.replace(/[-_]+/g, ' ');
  const matched = new Set();
  for (const [token, owners] of tokenMap) {
    if (mentioned(label, token) || mentioned(spaced, token)) for (const drawing of owners) matched.add(drawing);
  }
  return matched.size > 0 && matched.size < total ? matched : null;
}

function scopedSourcesByDrawing(source, root, prompt, drawings) {
  const refs = refDefs(source), allowed = new Set(drawings), tokenMap = drawingTokenMap(drawings);
  const resolvedAllowed = text => [...new Set(links(text, refs).map(link => resolveDrawing(root, prompt, link)).filter(d => allowed.has(d)))];
  const linkedIn = text => { const list = resolvedAllowed(text); return list.length > 0 && list.length < drawings.length ? new Set(list) : null; };
  const isStandaloneImages = text => {
    const stripped = text.replace(REF_DEF_RE, '').replace(/!\[[^\]]*\]\(\s*(?:<[^>]+>|[^\s)]+)(?:\s+(?:"[^"]*"|'[^']*'))?\s*\)/g, '')
      .replace(/!\[[^\]]*\]\[[^\]]*\]/g, '').replace(/!\[[^\]]+\](?![\[(:])/g, '').trim();
    return !stripped && resolvedAllowed(text).length > 0;
  };
  const listLead = line => {
    const rest = line.replace(/^ *(?:[-*+]|\d+[.)])[ \t]+/, '');
    let tick = false, quote = null;
    for (let i = 0; i < Math.min(rest.length, 200); i++) {
      const ch = rest[i];
      if (ch === '`') { tick = !tick; continue; }
      if (tick) continue;
      if (quote) { if (ch === quote) quote = null; continue; }
      if (ch === '"' || (ch === "'" && (i === 0 || !/[\p{L}\p{N}]/u.test(rest[i - 1])))) { quote = ch; continue; }
      if (ch === ':' || ch === '—' || (rest.slice(i, i + 2) === '--' && i > 0 && /\s/.test(rest[i - 1]) && /\s/.test(rest[i + 2] ?? ' '))) return rest.slice(0, i);
    }
    return '';
  };
  const lines = source.split('\n'), sections = [{ headings: [], blocks: [] }];
  let i = 0;
  const pushBlock = block => sections.at(-1).blocks.push(block);
  while (i < lines.length) {
    const line = lines[i];
    if (/^[ \t]*$/.test(line)) { i++; continue; }
    const fenceMatch = /^( *)(`{3,}|~{3,})/.exec(line);
    if (fenceMatch) {
      const indent = fenceMatch[1].length, marker = fenceMatch[2], start = i++;
      while (i < lines.length && !new RegExp(`^ *${marker[0]}{${marker.length},}[ \\t]*$`).test(lines[i])) i++;
      if (i < lines.length) i++;
      pushBlock({ kind: 'fence', indent, text: lines.slice(start, i).join('\n') });
      continue;
    }
    const headingMatch = /^ {0,3}(#{1,6})[ \t]+(.*)$/.exec(line);
    if (headingMatch) {
      const level = headingMatch[1].length, title = headingMatch[2].replace(/[ \t]+#+[ \t]*$/, '');
      const prev = sections.at(-1).headings.filter(h => h.level < level);
      const own = linkedIn(line) ?? matchTokens(title, tokenMap, drawings.length);
      const targets = intersectTargets(prev.at(-1)?.targets ?? null, own);
      sections.push({ headings: [...prev, { level, targets }], blocks: [{ kind: 'heading', indent: 0, text: line, ownTargets: targets }] });
      i++; continue;
    }
    const bulletMatch = /^( *)(?:[-*+]|\d+[.)])[ \t]+/.exec(line);
    if (bulletMatch) {
      const indent = bulletMatch[1].length, contentIndent = bulletMatch[0].length, start = i++;
      while (i < lines.length && !/^[ \t]*$/.test(lines[i]) && !/^(?: *(?:`{3,}|~{3,}|(?:[-*+]|\d+[.)])[ \t]+)| {0,3}#{1,6}[ \t]+)/.test(lines[i])) i++;
      pushBlock({ kind: 'list', indent, contentIndent, text: lines.slice(start, i).join('\n'), firstLine: line });
      continue;
    }
    const indent = /^( *)/.exec(line)[1].length, start = i++;
    while (i < lines.length && !/^[ \t]*$/.test(lines[i]) && !/^(?: *(?:`{3,}|~{3,}|(?:[-*+]|\d+[.)])[ \t]+)| {0,3}#{1,6}[ \t]+)/.test(lines[i])) i++;
    pushBlock({ kind: 'para', indent, text: lines.slice(start, i).join('\n') });
  }
  const scoped = new Map(drawings.map(d => [d, []]));
  for (const section of sections) {
    const sectionTargets = section.headings.at(-1)?.targets ?? null;
    const standalone = section.blocks.map(b => b.kind === 'para' && isStandaloneImages(b.text));
    const gallery = standalone.map((isImg, idx) => isImg && ((idx > 0 && standalone[idx - 1]) || (idx + 1 < standalone.length && standalone[idx + 1])));
    let imageScope = null;
    const listScopes = [];
    for (let idx = 0; idx < section.blocks.length; idx++) {
      const block = section.blocks[idx];
      if (standalone[idx]) { listScopes.length = 0; imageScope = gallery[idx] ? null : linkedIn(block.text); continue; }
      let targets = null;
      if (block.kind === 'heading') { listScopes.length = 0; targets = block.ownTargets ?? sectionTargets; }
      else if (block.kind === 'list') {
        while (listScopes.length && listScopes.at(-1).indent >= block.indent) listScopes.pop();
        const own = linkedIn(block.text) ?? matchTokens(listLead(block.firstLine), tokenMap, drawings.length);
        if (own) imageScope = null;
        const parentTargets = listScopes.at(-1)?.targets ?? null;
        targets = own ? intersectTargets(parentTargets ?? sectionTargets, own) : parentTargets ?? intersectTargets(sectionTargets, imageScope);
        listScopes.push({ indent: block.indent, contentIndent: block.contentIndent, targets });
      } else {
        while (listScopes.length && block.indent < listScopes.at(-1).contentIndent && block.indent <= listScopes.at(-1).indent) listScopes.pop();
        const activeListTargets = listScopes.length ? listScopes.at(-1).targets : undefined;
        targets = linkedIn(block.text) ?? (activeListTargets !== undefined ? activeListTargets : intersectTargets(sectionTargets, imageScope));
      }
      for (const drawing of drawings) if (!targets || targets.has(drawing)) scoped.get(drawing).push(block.text);
    }
  }
  return new Map([...scoped].map(([d, chunks]) => [d, chunks.join('\n\n')]));
}

const INTERFACE_SUMMARY_RE = /<details>\s*<summary>\s*Runtime interface\s*<\/summary>\s*```json\s*([\s\S]*?)```\s*<\/details>/gi;
function parsePromptMeta(text) {
  let fmKind = null, hasFrontmatter = false;
  const fm = text.match(/^---\r?\n([\s\S]*?)\r?\n---(?:\r?\n|$)/);
  if (fm) {
    hasFrontmatter = true;
    const km = fm[1].match(/^kind:\s*['"]?([A-Za-z0-9_-]+)['"]?\s*$/m);
    if (km) fmKind = km[1];
  }
  const blocks = [...text.matchAll(INTERFACE_SUMMARY_RE)];
  let iface = null;
  if (blocks.length === 1) { try { iface = JSON.parse(blocks[0][1]); } catch { iface = null; } }
  return { hasFrontmatter, hasEmbeddedInterface: blocks.length > 0, isNativeOnly: fmKind === 'native-only' || iface?.kind === 'native-only', iface, prose: text.replace(INTERFACE_SUMMARY_RE, '') };
}

function promptTargets(text, fromPrompt, visibleSet) {
  const noFences = stripCodeFences(text);
  const noCode = noFences.replace(/`+[^`\n]*`+/g, '');
  const refs = refDefs(noCode);
  const depsNoFences = [...noFences.matchAll(/^##[ \t]+Dependencies[ \t]*\n([\s\S]*?)(?=^#{1,2}[ \t]+|$(?![\s\S]))/gim)].map(m => m[1]).join('\n');
  const depsNoCode = depsNoFences.replace(/`+[^`\n]*`+/g, '');
  const candidates = [
    ...[...depsNoCode.matchAll(/!?\[[^\]]*\]\(\s*(?:<([^>]+)>|([^\s)]+))(?:\s+["'][^)]*)?\)/g)].map(m => m[1] || m[2]),
    ...[...depsNoCode.matchAll(/!?\[([^\]]*)\]\[([^\]]*)\]/g)].map(m => refs.get(normalize(m[2] || m[1]))),
    ...[...depsNoFences.matchAll(/^ {0,3}(?:[-+*]|[0-9]+[.)])[ \t]+`([^`\n]+)`(?=[ \t:]|$)/gm)].map(m => m[1]),
  ];
  const out = [];
  for (const raw of candidates) {
    if (!raw || /^(?:[a-z][a-z0-9+.-]*:|#|\/)/i.test(raw)) continue;
    const pathPart = raw.split('#')[0].split('?')[0];
    if (!pathPart || !pathPart.endsWith('.prompt.md')) continue;
    const rel = relative(ROOT_PLACEHOLDER, resolve(dirname(resolve(ROOT_PLACEHOLDER, fromPrompt)), pathPart)).split(sep).join('/');
    if (visibleSet.has(rel)) out.push(rel);
  }
  return [...new Set(out)];
}

export function lintSvgLayouts({ root, files, promptPaths }) {
  const policy = workspace.policy({ root });
  const allowedFiles = files.filter(path => workspace.allows(policy, path));
  const readRepoFile = (r, p) => safeRead(r, p, policy);
  const warnings = [];
  const promptRecords = [];
  const add = (prompt, drawing, part, reason) =>
    warnings.push({ key: `${prompt}\0${drawing}\0${part}\0${reason}`, text: `Warning: SVG layout ${prompt} -> ${drawing}: ${part}: ${reason}.` });

  const rawPromptCache = new Map();
  const readPromptCached = p => {
    if (!rawPromptCache.has(p)) rawPromptCache.set(p, readRepoFile(root, p));
    return rawPromptCache.get(p);
  };
  const drawingPartsCache = new Map();
  const getDrawingParts = drawing => {
    if (!drawingPartsCache.has(drawing)) {
      try { drawingPartsCache.set(drawing, { ok: true, parts: partsOf(readRepoFile(root, drawing)) }); }
      catch (error) { drawingPartsCache.set(drawing, { ok: false, message: error.message }); }
    }
    return drawingPartsCache.get(drawing);
  };

  for (const prompt of [...new Set(promptPaths ?? allowedFiles.filter(path => path.endsWith('.prompt.md')))].sort()) {
    let source;
    try { source = markupTokens(readPromptCached(prompt)).map(token => (token.startsWith('<!--') ? '\n' : token)).join('').replace(/\r\n?/g, '\n'); }
    catch (error) { add(prompt, '(unread)', 'source', error.message); continue; }
    source = source.replace(/<details\b[^>]*>\s*<summary[^>]*>[^\n]*Runtime interface[^\n]*<\/summary>[\s\S]*?<\/details>/gi, '')
      .replace(/(^##+ Runtime interface[^\n]*\n)[\s\S]*?(?=^##+ |$(?![\s\S]))/gmi, '');
    const decodedSource = decodeHtml(source), drawings = [], promptRefs = refDefs(source);
    const resolvedLinks = [...new Set(links(source, promptRefs).sort().map(link => resolveDrawing(root, prompt, link)))].sort();
    const capturedSet = new Set(uploadCapturedSvgLinks(source, promptRefs).map(link => resolveDrawing(root, prompt, link)));
    for (const drawing of resolvedLinks) {
      if (drawing && drawing !== '..' && !drawing.startsWith('../')) {
        drawings.push(drawing);
        if (!capturedSet.has(drawing)) {
          add(prompt, drawing, 'link syntax', 'plain Markdown link outside "## Dependencies" is skipped by scoped uploads (causes dependency-file-unreadable); use image syntax ![label](...) or link it under "## Dependencies"');
        }
      }
    }
    const scopedSources = drawings.length > 1 ? scopedSourcesByDrawing(source, root, prompt, drawings) : null;
    const normSource = resolvedLinks.length ? normalize(source) : '';
    const normDecoded = resolvedLinks.length ? normalize(decodedSource) : '';
    const appearance = resolvedLinks.length ? (source.match(/^##+ Appearance\b[^\n]*\n([\s\S]*?)(?=^##? |$(?![\s\S]))/m)?.[1] || '') : '';
    for (const drawing of resolvedLinks) {
      const cached = getDrawingParts(drawing);
      if (!cached.ok) { add(prompt, drawing, 'drawing', cached.message); continue; }
      const parts = cached.parts;
      for (const { kind, value } of parts) {
        if (kind === 'text' && !/^[\d\s.,+%-]+$/.test(value) && !mentionedNormalized(normSource, value) && !mentionedNormalized(normDecoded, value)) add(prompt, drawing, `label "${value}"`, 'drawing label absent from prompt');
        if (kind === 'id') {
          const name = escaped(value), words = escaped(value.replace(/[-_]/g, ' '));
          const declaration = new RegExp(`(?:\\b(?:region|id|part|container|bar|box)\\s*(?:=|:)?\\s*["'\x60]?${name}(?![\\w-])|(?<![\\w-])${name}["'\x60]?\\s+(?:region|box|bar|container|button|grid|heading|label)|(?<![\\w-])${words}\\s+(?:region|box|bar|container|button|grid|heading|label))`, 'i');
          if (!declaration.test(source) && !appearance.includes(`\`${value}\``)) add(prompt, drawing, `region #${value}`, 'drawing region layout unspecified in prompt');
        }
      }
      const controls = extractControls(scopedSources?.get(drawing) ?? source, parts);
      for (const control of controls) if (!parts.some(part => normalize(part.value) === normalize(control))) add(prompt, drawing, `control "${control}"`, 'prompt control absent from drawing');
    }
    promptRecords.push({ path: prompt, prose: source, drawings });
  }

  const visiblePromptSet = new Set(allowedFiles.filter(f => f.endsWith('.prompt.md')));
  const metaCache = new Map();
  const getMeta = p => {
    if (metaCache.has(p)) return metaCache.get(p);
    try { const meta = parsePromptMeta(readPromptCached(p)); metaCache.set(p, meta); return meta; }
    catch { metaCache.set(p, null); return null; }
  };
  const collectClosure = startPrompt => {
    const visited = new Set(), queue = [startPrompt];
    while (queue.length) {
      const cur = queue.shift();
      if (!cur || visited.has(cur) || !visiblePromptSet.has(cur)) continue;
      visited.add(cur);
      const meta = getMeta(cur);
      if (!meta) continue;
      for (const call of Array.isArray(meta.iface?.calls) ? meta.iface.calls : []) if (typeof call?.target === 'string') queue.push(call.target);
      if (!meta.hasEmbeddedInterface || meta.hasFrontmatter) for (const target of promptTargets(meta.prose, cur, visiblePromptSet)) queue.push(target);
    }
    return visited;
  };
  const promptFilter = promptPaths ? new Set(promptPaths) : null;
  const promptExists = promptPath => {
    if (typeof promptPath !== 'string' || !promptPath.endsWith('.prompt.md')) return false;
    if (visiblePromptSet.size > 0) return visiblePromptSet.has(promptPath);
    try { readPromptCached(promptPath); return true; } catch { return false; }
  };
  const promptDeclaresOp = (promptPath, op) => {
    const meta = getMeta(promptPath);
    if (!meta || typeof op !== 'string' || !op.trim()) return false;
    if (meta.hasEmbeddedInterface && Array.isArray(meta.iface?.entries)) return meta.iface.entries.some(entry => entry?.operation === op);
    return new RegExp(`(?<![A-Za-z0-9_-])${escaped(op)}(?![A-Za-z0-9_-])`).test(meta.prose);
  };

  // Single-pass disk scan for test*/**/*.json and app-map.json (replaces 3x redundant reads).
  const { testJsonPaths, parsedTests, mapPaths, parsedAppMaps, appMapParseErrors } = discoverTestAndAppMaps({
    root,
    files: allowedFiles,
    policy,
    safeRead: readRepoFile,
  });

  lintAppMaps({
    root,
    promptRecords,
    promptFilter,
    parsedAppMaps,
    appMapParseErrors,
    mapPaths,
    safeRead: readRepoFile,
    promptExists,
    promptDeclaresOp,
    warnings,
  });

  lintScenarioFiles({
    root,
    files: allowedFiles,
    policy,
    promptFilter,
    visiblePromptSet,
    testJsonPaths,
    parsedTests,
    parsedAppMaps,
    safeRead: readRepoFile,
    getMeta,
    collectClosure,
    warnings,
  });

  return [...new Map(warnings.sort((a, b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0)).map(w => [w.text, w.text])).values()];
}
