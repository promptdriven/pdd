// Generated from prompts/cli/svg-layout.prompt.md.
// Structural .ui.svg link/XML/viewBox validator and app-map/scenario lint orchestrator (zero prose regex matching).
import { dirname, relative, resolve, sep } from 'node:path';
import { workspace } from '../../shared/workspace-policy.mjs';
import { discoverTestAndAppMaps, lintAppMaps } from './app-map-lint.mjs';
import { lintScenarioFiles } from './scenario-lint.mjs';
import { safeRead, stripComments, validateSvgXml } from './svg-xml.mjs';

const ROOT_PLACEHOLDER = '/__pdd_root__';
const normalizeKey = text => String(text ?? '').trim().replace(/\s+/g, ' ').toLowerCase();
const REF_DEF_RE = /^\s*\[([^\]]+)\]:\s*<?([^\s>]+)>?(?:\s+(?:"[^"\n]*"|'[^'\n]*'|\([^)\n]*\)))?\s*$/gm;
const refDefs = text => new Map([...text.matchAll(REF_DEF_RE)].map(m => [normalizeKey(m[1]), m[2]]));

function stripCodeFencesOnly(text) {
  const out = [];
  let fence = null;
  for (const line of String(text ?? '').replace(/\r\n?/g, '\n').split('\n')) {
    const fm = /^ {0,3}(`{3,}|~{3,})(.*)$/.exec(line);
    if (fence) {
      if (fm && fm[1][0] === fence.char && fm[1].length >= fence.len && /^ {0,3}(?:`+|~+)[ \t]*$/.test(line)) fence = null;
      out.push('');
      continue;
    }
    if (fm && !(fm[1][0] === '`' && fm[2].includes('`'))) {
      fence = { char: fm[1][0], len: fm[1].length };
      out.push('');
      continue;
    }
    out.push(line);
  }
  return out.join('\n');
}

function stripCodeFencesAndComments(text) {
  const out = [];
  let fence = null;
  let inComment = false;
  for (let line of String(text ?? '').replace(/\r\n?/g, '\n').split('\n')) {
    const fm = /^ {0,3}(`{3,}|~{3,})(.*)$/.exec(line);
    if (fence) {
      if (fm && fm[1][0] === fence.char && fm[1].length >= fence.len && /^ {0,3}(?:`+|~+)[ \t]*$/.test(line)) fence = null;
      out.push('');
      continue;
    }
    if (fm && !(fm[1][0] === '`' && fm[2].includes('`'))) {
      fence = { char: fm[1][0], len: fm[1].length };
      out.push('');
      continue;
    }
    if (inComment) {
      const endIdx = line.indexOf('-->');
      if (endIdx < 0) { out.push(''); continue; }
      inComment = false;
      line = ' '.repeat(endIdx + 3) + line.slice(endIdx + 3);
    }
    while (true) {
      const openIdx = line.indexOf('<!--');
      if (openIdx < 0) break;
      const closeIdx = line.indexOf('-->', openIdx + 4);
      if (closeIdx < 0) { line = line.slice(0, openIdx); inComment = true; break; }
      line = line.slice(0, openIdx) + ' '.repeat(closeIdx + 3 - openIdx) + line.slice(closeIdx + 3);
    }
    out.push(line);
  }
  return out.join('\n');
}

function maskInlineCodeSpans(text) {
  if (!text.includes('`')) return text;
  const lines = text.split('\n');
  const out = [];
  let activeTicks = 0;
  for (const line of lines) {
    if (!line.trim() || /^ {0,3}#{1,6}[ \t]+/.test(line)) activeTicks = 0;
    if (activeTicks === 0 && !line.includes('`')) { out.push(line); continue; }
    if (activeTicks > 0 && !line.includes('`')) { out.push(' '.repeat(line.length)); continue; }
    const parts = [];
    let i = 0;
    while (i < line.length) {
      const next = line.indexOf('`', i);
      if (next < 0) {
        parts.push(activeTicks > 0 ? ' '.repeat(line.length - i) : line.slice(i));
        break;
      }
      if (next > i) parts.push(activeTicks > 0 ? ' '.repeat(next - i) : line.slice(i, next));
      let j = next + 1;
      while (j < line.length && line[j] === '`') j++;
      const run = j - next;
      if (activeTicks === 0) activeTicks = run;
      else if (run === activeTicks) activeTicks = 0;
      parts.push(' '.repeat(run));
      i = j;
    }
    out.push(parts.join(''));
  }
  return out.join('\n');
}

function links(text, refs = refDefs(text), imagesOnly = false) {
  const inlineRe = imagesOnly
    ? /!\[[^\]]*\]\(\s*(?:<([^>]+)>|([^\s)]+))(?:\s+["'][^)]*)?\)/g
    : /!?\[[^\]]*\]\(\s*(?:<([^>]+)>|([^\s)]+))(?:\s+["'][^)]*)?\)/g;
  const refRe = imagesOnly ? /!\[([^\]]*)\]\[([^\]]*)\]/g : /!?\[([^\]]*)\]\[([^\]]*)\]/g;
  const shortRe = imagesOnly ? /!\[([^\]]+)\](?![\[(:])/g : /!?\[([^\]]+)\](?![\[(:])/g;
  return [...new Set([
    ...[...text.matchAll(inlineRe)].map(m => m[1] || m[2]),
    ...[...text.matchAll(refRe)].map(m => refs.get(normalizeKey(m[2] || m[1]))),
    ...[...text.matchAll(shortRe)].map(m => refs.get(normalizeKey(m[1]))),
  ].filter(value => value && !/^(?:[a-z][a-z\d+.-]*:|\/\/|#)/i.test(value) && /\.ui\.svg(?:#.*)?$/i.test(value)).map(value => value.split('#')[0]))];
}

function uploadCapturedSvgLinks(text, refs = refDefs(text)) {
  const depsBody = [...text.matchAll(/^##+[ \t]+Dependencies\b[^\n]*\n([\s\S]*?)(?=^##?[ \t]|$(?![\s\S]))/gim)].map(m => m[1]).join('\n');
  return [...new Set([...links(text, refs, true), ...links(depsBody, refs, false)])];
}

const resolveDrawing = (root, prompt, link) => {
  try { return relative(root, resolve(root, dirname(prompt), decodeURIComponent(link))).split(sep).join('/'); } catch { return link; }
};

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
  const noFences = stripCodeFencesAndComments(text);
  const noCode = maskInlineCodeSpans(noFences);
  const refs = refDefs(noCode);
  const depsNoFences = [...noFences.matchAll(/^##[ \t]+Dependencies[ \t]*\n([\s\S]*?)(?=^#{1,2}[ \t]+|$(?![\s\S]))/gim)].map(m => m[1]).join('\n');
  const depsNoCode = maskInlineCodeSpans(depsNoFences);
  const candidates = [
    ...[...depsNoCode.matchAll(/!?\[[^\]]*\]\(\s*(?:<([^>]+)>|([^\s)]+))(?:\s+["'][^)]*)?\)/g)].map(m => m[1] || m[2]),
    ...[...depsNoCode.matchAll(/!?\[([^\]]*)\]\[([^\]]*)\]/g)].map(m => refs.get(normalizeKey(m[2] || m[1]))),
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

export function lintSvgLayouts({
  root,
  files,
  promptPaths,
  appMapPaths,
  scenarioPaths,
  tests,
  includeShortDiagnostics = false,
  readCache = null,
  statsOut = null,
}) {
  if (
    Array.isArray(promptPaths) && promptPaths.length === 0
    && Array.isArray(appMapPaths) && appMapPaths.length === 0
    && Array.isArray(scenarioPaths) && scenarioPaths.length === 0
    && (!Array.isArray(tests) || tests.length === 0)
  ) {
    if (statsOut && typeof statsOut === 'object') { statsOut.appMaps = 0; statsOut.drawings = 0; }
    return [];
  }
  const policy = workspace.policy({ root });
  const allowedFiles = files.filter(path => workspace.allows(policy, path));
  const allowedSet = new Set(allowedFiles);
  const lowerAllowedMap = new Map();
  for (const f of allowedFiles) {
    const low = f.toLowerCase();
    if (!lowerAllowedMap.has(low)) lowerAllowedMap.set(low, f);
  }
  const dirCache = new Map();
  const readRepoFile = (r, p) => {
    if (readCache && readCache.has(p)) {
      const cached = readCache.get(p);
      if (typeof cached === 'string') return cached;
    }
    const content = safeRead(r, p, policy, dirCache);
    if (readCache) readCache.set(p, content);
    return content;
  };
  const warnings = [];
  const validatedDrawings = new Set();
  const add = (prompt, drawing, part, reason) =>
    warnings.push({ key: `${prompt}\0${drawing}\0${part}\0${reason}`, text: `Warning: SVG layout ${prompt} -> ${drawing}: ${part}: ${reason}.` });

  const rawPromptCache = new Map();
  const readPromptCached = p => {
    if (!rawPromptCache.has(p)) rawPromptCache.set(p, readRepoFile(root, p));
    return rawPromptCache.get(p);
  };
  const drawingCheckCache = new Map();
  const checkDrawing = drawing => {
    if (!drawingCheckCache.has(drawing)) {
      try {
        if (allowedSet.size > 0 && !allowedSet.has(drawing)) {
          const ci = lowerAllowedMap.get(drawing.toLowerCase());
          if (ci && ci !== drawing) {
            drawingCheckCache.set(drawing, { ok: false, part: 'drawing', message: `case mismatch: linked as "${drawing}" but Git-visible file is "${ci}" (fails on case-sensitive Linux CI)` });
            return drawingCheckCache.get(drawing);
          }
        }
        const raw = safeRead(root, drawing, policy, dirCache);
        validateSvgXml(raw);
        drawingCheckCache.set(drawing, { ok: true });
      } catch (error) {
        drawingCheckCache.set(drawing, { ok: false, part: error?.part || 'drawing', message: error.message });
      }
    }
    return drawingCheckCache.get(drawing);
  };

  for (const prompt of [...new Set(promptPaths ?? allowedFiles.filter(path => path.endsWith('.prompt.md')))].sort()) {
    let rawPrompt;
    try { rawPrompt = readPromptCached(prompt); }
    catch (error) { add(prompt, '(unread)', 'source', error.message); continue; }
    if (!/\.ui\.svg/i.test(rawPrompt)) continue;
    const noMeta = rawPrompt
      .replace(/<details\b[^>]*>\s*<summary[^>]*>[^\n]*Runtime interface[^\n]*<\/summary>[\s\S]*?<\/details>/gi, '')
      .replace(/(^##+ Runtime interface[^\n]*\n)[\s\S]*?(?=^##+ |$(?![\s\S]))/gmi, '');
    const noFences = stripCodeFencesOnly(noMeta);
    let commentFree;
    try { commentFree = stripComments(noFences); }
    catch (error) { add(prompt, '(comment)', 'source', error.message); continue; }
    const cleanSource = maskInlineCodeSpans(commentFree);
    const promptRefs = refDefs(cleanSource);
    const resolvedLinks = [...new Set(links(cleanSource, promptRefs).sort().map(link => resolveDrawing(root, prompt, link)))].sort();
    const capturedSet = new Set(uploadCapturedSvgLinks(cleanSource, promptRefs).map(link => resolveDrawing(root, prompt, link)));
    for (const drawing of resolvedLinks) {
      if (drawing && drawing !== '..' && !drawing.startsWith('../')) {
        validatedDrawings.add(drawing);
        if (!capturedSet.has(drawing)) {
          add(prompt, drawing, 'link syntax', 'plain Markdown link outside "## Dependencies" is skipped by scoped uploads (causes dependency-file-unreadable); use image syntax ![label](...) or link it under "## Dependencies"');
        }
      }
      const checked = checkDrawing(drawing);
      if (!checked.ok) add(prompt, drawing, checked.part, checked.message);
    }
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
  const appMapFilter = appMapPaths !== undefined ? new Set(appMapPaths) : null;
  const scenarioFilter = scenarioPaths !== undefined ? new Set(scenarioPaths) : null;
  const testFilter = tests ? new Set(tests) : null;
  const promptExists = promptPath => {
    if (typeof promptPath !== 'string' || !promptPath.endsWith('.prompt.md')) return false;
    if (visiblePromptSet.size > 0) return visiblePromptSet.has(promptPath);
    try { readPromptCached(promptPath); return true; } catch { return false; }
  };
  // Check embedded Runtime interface JSON entries only — never regex-scrape plain-Markdown prose.
  const promptDeclaresOp = (promptPath, op) => {
    if (typeof op !== 'string' || !op.trim()) return false;
    const meta = getMeta(promptPath);
    if (!meta) return false;
    if (meta.hasEmbeddedInterface && Array.isArray(meta.iface?.entries)) {
      return meta.iface.entries.some(entry => entry?.operation === op);
    }
    return true;
  };

  const { testJsonPaths, parsedTests, mapPaths, parsedAppMaps, appMapParseErrors } = discoverTestAndAppMaps({
    root,
    files: allowedFiles,
    policy,
    safeRead: readRepoFile,
  });

  const inspectedAppMaps = lintAppMaps({
    root,
    safeRead: readRepoFile,
    promptFilter,
    appMapFilter,
    parsedAppMaps,
    appMapParseErrors,
    mapPaths,
    promptExists,
    promptDeclaresOp,
    warnings,
  });

  lintScenarioFiles({
    root,
    files: allowedFiles,
    policy,
    promptFilter,
    scenarioFilter,
    testFilter,
    includeShortDiagnostics,
    visiblePromptSet,
    testJsonPaths,
    parsedTests,
    parsedAppMaps,
    safeRead: readRepoFile,
    getMeta,
    collectClosure,
    warnings,
  });

  if (statsOut && typeof statsOut === 'object') {
    statsOut.appMaps = inspectedAppMaps;
    statsOut.drawings = validatedDrawings.size;
  }

  return [...new Map(warnings.sort((a, b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0)).map(w => [w.text, w.text])).values()];
}
