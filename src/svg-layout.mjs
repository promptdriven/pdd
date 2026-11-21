// Generated from prompts/cli/svg-layout.prompt.md (sha256: 4a5f7a6aedc2322ebbf3ee5f27621fefb0fd67950cff4d2a36e7ea1142885217).
import { lstatSync, readFileSync } from 'node:fs';
import { dirname, relative, resolve, sep } from 'node:path';
import { lintScreenDesign } from './screen-design-check.mjs';
import { compileScenario, isShortScenarioDoc, needsScenarioCompile, SHORT_SCENARIO_SCHEMA, V1_SCENARIO_SCHEMA } from './scenario-compile.mjs';
import { runtimeWorkspaceSlice, workspace } from './runtime-seam.mjs';

const { requireRuntimePath } = runtimeWorkspaceSlice();

const normalize = text => text.replace(/\s+/g, ' ').trim().toLowerCase();
const escaped = text => text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
function decode(text) {
  if (/&(?!(?:amp|lt|gt|quot|apos|#\d+|#x[\da-f]+);)/i.test(text)) throw Error('invalid XML entity');
  return text.replace(/&([^;\s]+);/g, (_, value) => {
    const named = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'" };
    if (value in named) return named[value];
    const number = /^#x[\da-f]+$/i.test(value) ? parseInt(value.slice(2), 16) : /^#\d+$/.test(value) ? Number(value.slice(1)) : NaN;
    if (!Number.isInteger(number) || number <= 0 || number > 0x10ffff || number >= 0xd800 && number <= 0xdfff) throw Error('invalid XML entity');
    return String.fromCodePoint(number);
  });
}
function decodeHtml(text) {
  return text.replace(/&(#x[\da-f]+|#\d+|amp|lt|gt|quot|apos|nbsp);/gi, (raw, entity) => {
    const named = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'", nbsp: ' ' }, lower = entity.toLowerCase();
    if (lower in named) return named[lower];
    const code = lower.startsWith('#x') ? parseInt(lower.slice(2), 16) : Number(lower.slice(1));
    return Number.isInteger(code) && code > 0 && code <= 0x10ffff && (code < 0xd800 || code > 0xdfff) ? String.fromCodePoint(code) : raw;
  });
}
function safeRead(root, path) {
  requireRuntimePath(workspace.policy({root}),{path,from:'SVG advice'});
  const full = resolve(root, path), rel = relative(resolve(root), full);
  if (!rel || rel === '..' || rel.startsWith(`..${sep}`) || resolve(root, rel) !== full) throw Error('path escapes repository');
  const parts = rel.split(sep);
  for (let i = 1; i <= parts.length; i++) {
    const stat = lstatSync(resolve(root, ...parts.slice(0, i)));
    if (stat.isSymbolicLink()) throw Error('symlink paths are not allowed');
    if (i === parts.length && !stat.isFile()) throw Error('not a regular file');
  }
  return readFileSync(full, 'utf8');
}

function markupTokens(source) {
  const tokens = source.match(/<!--[\s\S]*?(?:-->|$)|<!\[CDATA\[[\s\S]*?\]\]>|<[^>]*>|[^<]+|</g) || [];
  for (const token of tokens) if (token.startsWith('<!--') && (!token.endsWith('-->') || token.slice(4, -3).includes('--') || token.slice(4, -3).endsWith('-'))) throw Error('malformed or nested markup comment');
  return tokens;
}

// An inert XML reader: no document type, entity expansion, execution or resource loading.
function partsOf(source) {
  const tokens = markupTokens(source);
  const active = tokens.filter(token => !token.startsWith('<!--') && !token.startsWith('<![CDATA[')).join('\n');
  const styles = [...active.matchAll(/<style\b[^>]*>([\s\S]*?)<\/style>/g)].flatMap(match => [...match[1].replace(/\/\*[\s\S]*?\*\//g, '').matchAll(/([^{}]+)\{([^{}]*)\}/g)].flatMap(rule => rule[1].split(',').map(selector => ({ selector: selector.trim(), style: rule[2] }))));
  if (styles.some(rule => !/^(?:[\w-]+|[.#][\w-]+)$/.test(rule.selector))) throw Error('unsupported SVG stylesheet selector in static lint');
  for (const match of active.matchAll(/<style\b[^>]*>([\s\S]*?)<\/style>/g)) if (/@import|url\s*\(/i.test(match[1].replace(/url\(\s*(['"]?)#[^)'"\s]+\1\s*\)/gi, ''))) throw Error('external SVG stylesheet resources are not allowed');
  const stack = [], parts = [];
  let roots = 0;
  for (const token of tokens) {
    if (token.startsWith('<!--')) continue;
    if (token.startsWith('<?')) { if (!/^<\?xml\s[\s\S]*\?>$/.test(token)) throw Error('unsafe SVG processing instruction'); continue; }
    if (token.startsWith('</')) {
      const close = /^<\/([\w:-]+)\s*>$/.exec(token);
      if (!close || stack.pop()?.tag !== close[1]) throw Error('malformed XML closing tag');
    } else if (token.startsWith('<') && !token.startsWith('<![CDATA[')) {
      const match = /^<([\w:-]+)((?:\s+[\s\S]*?)?)\s*(\/?)>$/.exec(token);
      if (!match) throw Error('malformed XML element');
      const [, tag, raw, self] = match, attrs = {};
      if (['script', 'foreignobject', 'iframe', 'object', 'embed'].includes(tag.split(':').at(-1).toLowerCase())) throw Error('unsafe SVG content');
      let remainder = raw.trim();
      while (remainder) {
        const attr = /^([\w:-]+)\s*=\s*("[^"]*"|'[^']*')\s*/.exec(remainder);
        if (!attr || attr[1] in attrs) throw Error('malformed XML attributes');
        attrs[attr[1]] = decode(attr[2].slice(1, -1)); remainder = remainder.slice(attr[0].length);
      }
      if (Object.keys(attrs).some(name => /^on/i.test(name))) throw Error('unsafe SVG content');
      if (!stack.length && (tag !== 'svg' || roots++)) throw Error('expected one SVG root');
      const resourceValues = Object.values(attrs).join(' ').replace(/url\(\s*(['"]?)#[^)'"\s]+\1\s*\)/gi, '');
      if (Object.entries(attrs).some(([name, value]) => /^(?:href|xlink:href|src)$/i.test(name) && !value.startsWith('#')) || /(?:@import|url\s*\()/i.test(resourceValues)) throw Error('external SVG resources are not allowed');
      const simpleMatch = selector => selector === tag || selector === `#${attrs.id}` || selector.startsWith('.') && (attrs.class || '').split(/\s+/).includes(selector.slice(1));
      const declarations = new Map(['display', 'visibility', 'opacity'].filter(name => attrs[name] !== undefined).map(name => [name, { value: attrs[name], important: false }]));
      const specificity = rule => rule.selector.startsWith('#') ? 100 : rule.selector.startsWith('.') ? 10 : 1;
      for (const style of [...styles.filter(rule => simpleMatch(rule.selector)).sort((a, b) => specificity(a) - specificity(b)).map(rule => rule.style), attrs.style || '']) {
        for (const entry of style.split(';')) {
          const match = /^\s*([\w-]+)\s*:\s*(.*?)\s*(!important)?\s*$/i.exec(entry);
          if (!match) continue;
          const [, name, value, important] = match, previous = declarations.get(name.toLowerCase());
          if (!previous?.important || important) declarations.set(name.toLowerCase(), { value: value.toLowerCase().trim(), important: !!important });
        }
      }
      const css = Object.fromEntries([...declarations].map(([key, declaration]) => [key, declaration.value]));
      const hidden = stack.at(-1)?.hidden || ['title', 'desc', 'defs', 'metadata', 'style'].includes(tag) || attrs['data-context-only'] === 'true'
        || (attrs.class || '').split(/\s+/).includes('context-only') || css.display === 'none' || ['hidden', 'collapse'].includes(css.visibility)
        || css.opacity !== undefined && Number(css.opacity) === 0;
      const node = { tag, hidden, text: '', id: attrs.id };
      if (!hidden && attrs.id) parts.push({ kind: 'id', value: attrs.id });
      if (!hidden && tag === 'text') parts.push({ kind: 'text', node });
      if (!self) stack.push(node);
    } else {
      const text = token.startsWith('<![CDATA[') ? token.slice(9, -3) : decode(token);
      if (!stack.length && text.trim()) throw Error('text outside SVG root');
      if (!stack.at(-1)?.hidden) for (const node of stack) if (node.tag === 'text' && !node.hidden) node.text += text;
    }
  }
  if (stack.length || roots !== 1 || tokens.join('') !== source) throw Error('malformed SVG');
  return parts.map(part => ({ kind: part.kind, value: part.node ? part.node.text.replace(/\s+/g, ' ').trim() : part.value })).filter(part => part.value);
}
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
    if (fm) {
      fence = fm[1];
      out.push('');
      continue;
    }
    out.push(line);
  }
  return out.join('\n');
}
function uploadCapturedSvgLinks(text, refs = refDefs(text)) {
  const depsBody = [...stripCodeFences(text).matchAll(/^##+[ \t]+Dependencies\b[^\n]*\n([\s\S]*?)(?=^##?[ \t]|$(?![\s\S]))/gim)].map(m => m[1]).join('\n');
  return [...new Set([...links(text, refs, true), ...links(depsBody, refs, false)])];
}
const mentioned = (prose, value) => new RegExp(`(^|[^\\p{L}\\p{N}_])${escaped(normalize(value))}($|[^\\p{L}\\p{N}_])`, 'u').test(normalize(prose));
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
  const spaced = label.replace(/[-_]+/g, ' '), matched = new Set();
  for (const [token, owners] of tokenMap) {
    if (mentioned(label, token) || mentioned(spaced, token)) for (const drawing of owners) matched.add(drawing);
  }
  return matched.size > 0 && matched.size < total ? matched : null;
}

function scopedSourcesByDrawing(source, root, prompt, drawings) {
  const refs = refDefs(source), allowed = new Set(drawings), tokenMap = drawingTokenMap(drawings);
  const resolvedAllowed = text => [...new Set(links(text, refs).map(link => resolveDrawing(root, prompt, link)).filter(d => allowed.has(d)))];
  const linkedIn = text => {
    const list = resolvedAllowed(text);
    return list.length > 0 && list.length < drawings.length ? new Set(list) : null;
  };
  const isStandaloneImages = text => {
    const stripped = text
      .replace(REF_DEF_RE, '')
      .replace(/!\[[^\]]*\]\(\s*(?:<[^>]+>|[^\s)]+)(?:\s+(?:"[^"]*"|'[^']*'))?\s*\)/g, '')
      .replace(/!\[[^\]]*\]\[[^\]]*\]/g, '')
      .replace(/!\[[^\]]+\](?![\[(:])/g, '')
      .trim();
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
      if (ch === '"' || ch === "'" && (i === 0 || !/[\p{L}\p{N}]/u.test(rest[i - 1]))) { quote = ch; continue; }
      if (ch === ':' || ch === '—' || rest.slice(i, i + 2) === '--' && i > 0 && /\s/.test(rest[i - 1]) && /\s/.test(rest[i + 2] ?? ' ')) return rest.slice(0, i);
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
      const parentTargets = prev.at(-1)?.targets ?? null;
      const own = linkedIn(line) ?? matchTokens(title, tokenMap, drawings.length);
      const targets = intersectTargets(parentTargets, own);
      sections.push({ headings: [...prev, { level, targets }], blocks: [{ kind: 'heading', indent: 0, text: line, ownTargets: targets }] });
      i++;
      continue;
    }
    const bulletMatch = /^( *)(?:[-*+]|\d+[.)])[ \t]+/.exec(line);
    if (bulletMatch) {
      const indent = bulletMatch[1].length, contentIndent = bulletMatch[0].length, start = i++;
      while (i < lines.length) {
        const next = lines[i];
        if (/^[ \t]*$/.test(next) || /^(?: *(?:`{3,}|~{3,}|(?:[-*+]|\d+[.)])[ \t]+)| {0,3}#{1,6}[ \t]+)/.test(next)) break;
        i++;
      }
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
    const gallery = standalone.map((isImg, idx) => isImg && (idx > 0 && standalone[idx - 1] || idx + 1 < standalone.length && standalone[idx + 1]));
    let imageScope = null;
    const listScopes = [];
    for (let idx = 0; idx < section.blocks.length; idx++) {
      const block = section.blocks[idx];
      if (standalone[idx]) {
        listScopes.length = 0;
        imageScope = gallery[idx] ? null : linkedIn(block.text);
        continue;
      }
      let targets = null;
      if (block.kind === 'heading') {
        listScopes.length = 0;
        targets = block.ownTargets ?? sectionTargets;
      } else if (block.kind === 'list') {
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

const VOID_HTML = new Set(['area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'param', 'source', 'track', 'wbr']);
const BLOCK_HTML = new Set(['address', 'article', 'aside', 'blockquote', 'br', 'dd', 'details', 'dialog', 'div', 'dl', 'dt', 'fieldset', 'figcaption', 'figure', 'footer', 'form', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'header', 'hgroup', 'hr', 'li', 'main', 'nav', 'ol', 'p', 'pre', 'section', 'summary', 'table', 'tbody', 'td', 'tfoot', 'th', 'thead', 'tr', 'ul']);
const CONTROL_ATTRS = new Set(['id', 'ids', 'name', 'names', 'value', 'values']);
const NON_CONTROL_NAMES = /^(?:aria-[\w-]+|data-[\w-]+|class|role|style|type|placeholder|title|href|src|for|action|method|tabindex|disabled|readonly|required|checked|selected|hidden|multiple|autofocus)$/i;

function parseHtmlTag(token) {
  const head = /^<(\/?)([a-zA-Z][\w:-]*)(?=\s|\/?>)((?:"[^"]*"|'[^']*'|[^"'>])*)>$/.exec(token);
  if (!head) return null;
  const closing = head[1] === '/', tag = head[2].toLowerCase();
  if (closing) return { closing: true, tag, selfClosing: false, attrs: {} };
  let rest = head[3], selfClosing = VOID_HTML.has(tag);
  const attrs = {};
  while (rest) {
    rest = rest.replace(/^\s+/, '');
    if (!rest) break;
    if (rest === '/') { selfClosing = true; break; }
    const attr = /^([a-zA-Z_:][\w:.-]*)(?:\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s"'=<>`/]+(?:\/(?!\s*$)[^\s"'=<>`/]*)*)))?/.exec(rest);
    if (!attr) { rest = rest.slice(1); continue; }
    const name = attr[1].toLowerCase(), raw = attr[2] ?? attr[3] ?? attr[4];
    if (!(name in attrs)) attrs[name] = raw === undefined ? '' : decodeHtml(raw).replace(/\s+/g, ' ').trim();
    rest = rest.slice(attr[0].length);
  }
  return { closing: false, tag, selfClosing, attrs };
}

function extractHtmlControls(fragment, controls) {
  const add = value => { const trimmed = value?.replace(/\s+/g, ' ').trim(); if (trimmed) controls.add(trimmed); };
  const tagRe = /<\/?[a-zA-Z][\w:-]*(?=\s|\/?>)(?:"[^"]*"|'[^']*'|[^"'>])*>/g;
  let last = 0, button = null;
  for (const match of fragment.matchAll(tagRe)) {
    if (button && button.hiddenDepth === 0) button.text += decodeHtml(fragment.slice(last, match.index));
    last = match.index + match[0].length;
    const parsed = parseHtmlTag(match[0]);
    if (!parsed) continue;
    const { closing, tag, selfClosing, attrs } = parsed;
    if (closing) {
      if (tag === 'button' && button) { add(button.text); button = null; }
      else if (button && button.hiddenStack.at(-1) === tag) { button.hiddenStack.pop(); button.hiddenDepth = button.hiddenStack.length; }
      continue;
    }
    if (button) {
      if (tag === 'button') button = null;
      else if (tag === 'br' && button.hiddenDepth === 0) button.text += ' ';
      else if (!selfClosing && (['script', 'style', 'template'].includes(tag) || 'hidden' in attrs || /(?:^|;)\s*(?:display\s*:\s*none|visibility\s*:\s*(?:hidden|collapse))\b/i.test(attrs.style || ''))) {
        button.hiddenStack.push(tag); button.hiddenDepth = button.hiddenStack.length;
      }
      if (button) continue;
    }
    if (tag === 'button') {
      add(attrs.id); add(attrs.name); add(attrs.value);
      if (!selfClosing) button = { text: '', hiddenStack: [], hiddenDepth: 0 };
    } else if (tag === 'input') {
      const type = (attrs.type || 'text').toLowerCase();
      if (type !== 'hidden') {
        add(attrs.id); add(attrs.name);
        if (['button', 'submit', 'reset'].includes(type)) add(attrs.value);
      }
    } else if (tag === 'select' || tag === 'textarea') {
      add(attrs.id); add(attrs.name);
    }
  }
}

function splitClauses(sentence, escS, negModRe) {
  const initial = [];
  let start = 0, depth = 0;
  for (let i = 0; i < sentence.length; i++) {
    const ch = sentence[i];
    if (ch === '(') { depth++; continue; }
    if (ch === ')' && depth > 0) { depth--; continue; }
    if (depth > 0) continue;
    if (ch === ';' || ch === '—' || sentence.slice(i, i + 4) === ' -- ') {
      const step = ch === ';' || ch === '—' ? 1 : 4;
      initial.push(sentence.slice(start, i)); start = i + step; i += step - 1; continue;
    }
    if (ch === ':' && !/\b(?:buttons?|controls?|ids?|names?|values?|labels?|named|called)\s*$/i.test(sentence.slice(start, i))) {
      initial.push(sentence.slice(start, i)); start = i + 1; continue;
    }
    if (ch === ',') {
      const before = sentence.slice(start, i), after = sentence.slice(i + 1);
      const leadClause = /^\s*(?:when|whenever|if|unless|while|although|though|alongside|beside|besides|after|before|once|until|in\s+case)\b/i.test(before)
        || /^\s*(?:without|with\s+no|no)\b/i.test(before) && /\b(?:buttons?|controls?)\b/i.test(before) && (/\b(?:buttons?|controls?)\b/i.test(after) || /^\s*(?:explain|show|display|render)\b/i.test(after));
      const nextClause = /^\s*(?:while|whereas|but|although|though|except|instead|however|yet|when|whenever|if|unless|until|because|since|so\s+that|(?:(?:and|or)\s+)?(?:also\s+)?(?:show|shows|explain|explains|display|displays|render|renders|keep|keeps|set|sets|update|updates|leave|leaves|hide|hides|disable|disables|enable|enables|tell|tells|say|says|print|prints|note|notes|no|without))\b/i.test(after)
        || new RegExp(`^\\s*${escS}[CN]\\d+${escS}\\s+(?:says|shows|displays|explains|reads|is|are|has)\\b`, 'i').test(after);
      if (leadClause || nextClause) { initial.push(before); start = i + 1; }
    }
  }
  initial.push(sentence.slice(start));
  const midNeg = new RegExp(`(?=\\b(?:without\\s+(?:(?:a|an|any|the)\\s+)?|(?:and|or|with)\\s+no\\s+)${negModRe}(?:buttons?|controls?)\\b)`, 'i');
  return initial.flatMap(piece => piece.split(midNeg)).map(piece => piece.trim()).filter(Boolean);
}

function extractControls(source, parts) {
  const controls = new Set(), add = value => { const trimmed = value?.replace(/\s+/g, ' ').trim(); if (trimmed) controls.add(trimmed); };
  let S = '\x02';
  while (source.includes(S)) S += '\x02';
  const escS = escaped(S), items = [], sentences = [''];
  const put = (kind, value) => { const idx = items.length; items.push(value); return `${S}${kind}${idx}${S}`; };
  const push = text => { sentences[sentences.length - 1] += text; };
  const endSentence = () => { if (sentences.at(-1).trim()) sentences.push(''); };
  let pos = 0, inHeading = false;

  while (pos < source.length) {
    const rest = source.slice(pos), lineStart = pos === 0 || source[pos - 1] === '\n';
    if (lineStart) {
      const fence = /^ *(`{3,}|~{3,})[^\n]*\n([\s\S]*?)(?:\n *\1[~`]*[ \t]*(?=\n|$)|$)/.exec(rest);
      if (fence) { extractHtmlControls(fence[2], controls); endSentence(); pos += fence[0].length; continue; }
      const refDef = /^[ \t]*\[[^\]]+\]:[ \t]*<?[^\s>]+>?(?:[ \t]+(?:"[^"\n]*"|'[^'\n]*'|\([^)\n]*\)))?[ \t]*(?=\n|$)/.exec(rest);
      if (refDef) { endSentence(); pos += refDef[0].length; continue; }
      const blank = /^[ \t]*\n(?:[ \t]*\n)*/.exec(rest);
      if (blank) { inHeading = false; endSentence(); pos += blank[0].length; continue; }
      const hr = /^ {0,3}(?:[-*_][ \t]*){3,}(?=\n|$)/.exec(rest);
      if (hr) { endSentence(); pos += hr[0].length; continue; }
      const heading = /^ {0,3}#{1,6}[ \t]+/.exec(rest);
      if (heading) { endSentence(); inHeading = true; pos += heading[0].length; continue; }
      const bullet = /^ {0,3}(?:[-*+]|\d+[.)])[ \t]+/.exec(rest);
      if (bullet) { endSentence(); pos += bullet[0].length; continue; }
    }
    if (source[pos] === '`') {
      const ticks = /^`+/.exec(rest)[0], body = rest.slice(ticks.length);
      const close = new RegExp(`(?<!\`)${ticks}(?!\`)`).exec(body);
      if (close && !/\n[ \t]*\n/.test(body.slice(0, close.index))) {
        const inner = body.slice(0, close.index);
        if (/<\/?[a-zA-Z][\w:-]*(?=\s|\/?>)/.test(inner)) {
          extractHtmlControls(inner, controls); push(` ${S}H0${S} `);
        } else if (/=/.test(inner) && /^(?:[a-zA-Z_:][\w:.-]*(?:\s*=\s*(?:"[^"]*"|'[^']*'|[^\s"'=<>`]+))?\s*)+$/.test(inner.trim())) {
          for (const attrMatch of inner.trim().matchAll(/([a-zA-Z_:][\w:.-]*)(?:\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s"'=<>`]+)))?/g)) {
            const attr = attrMatch[1].toLowerCase(), val = (attrMatch[2] ?? attrMatch[3] ?? attrMatch[4] ?? '').replace(/\s+/g, ' ').trim();
            push(` ${CONTROL_ATTRS.has(attr) ? put('A', val) : put('N', val)} `);
          }
        } else {
          const val = inner.replace(/\s+/g, ' ').trim();
          push(put(/^[A-Za-z0-9][\w:-]*$/.test(val) && !NON_CONTROL_NAMES.test(val) ? 'C' : 'N', val));
        }
        pos += ticks.length + close.index + ticks.length; continue;
      }
      push(' '); pos += ticks.length; continue;
    }
    if (rest.startsWith('![')) {
      const img = /^!\[[^\]]*\]\(\s*(?:<[^>]+>|[^\s)]+)(?:\s+(?:"[^"]*"|'[^']*'))?\s*\)/.exec(rest)
        || /^!\[[^\]]*\]\[[^\]]*\]/.exec(rest);
      if (img) { endSentence(); pos += img[0].length; continue; }
    }
    if (source[pos] === '<') {
      const open = /^<(button|select|textarea|script|style)(?=\s|\/?>)((?:"[^"]*"|'[^']*'|[^"'>])*)>/i.exec(rest);
      if (open) {
        const parsed = parseHtmlTag(open[0]);
        if (parsed && !parsed.selfClosing) {
          const closeMatch = new RegExp(`^([\\s\\S]*?)<\\/${parsed.tag}\\s*>`, 'i').exec(rest.slice(open[0].length));
          const nestedSame = new RegExp(`<${parsed.tag}(?=\\s|\\/?\\s*>)`, 'i');
          if (closeMatch && !nestedSame.test(closeMatch[1])) {
            const full = open[0] + closeMatch[0];
            extractHtmlControls(full, controls); push(` ${S}H0${S} `); pos += full.length; continue;
          }
        }
      }
      const single = /^<\/?[a-zA-Z][\w:-]*(?=\s|\/?>)(?:"[^"]*"|'[^']*'|[^"'>])*>/.exec(rest);
      if (single) {
        const parsed = parseHtmlTag(single[0]);
        if (parsed) {
          if (!parsed.closing) extractHtmlControls(single[0], controls);
          if (BLOCK_HTML.has(parsed.tag)) endSentence(); else push(` ${S}H0${S} `);
          pos += single[0].length; continue;
        }
      }
    }
    if (pos === 0 || !/[\p{L}\p{N}_-]/u.test(source[pos - 1])) {
      const eqAttr = /^([a-zA-Z_:][\w:.-]*)\s*=\s*(?:"((?:[^"\n]|\n(?![ \t]*\n))*)"|'((?:[^'\n]|\n(?![ \t]*\n))*)'|`([^`\n]+)`|([\w:-]+))/.exec(rest);
      if (eqAttr) {
        const attr = eqAttr[1].toLowerCase(), val = (eqAttr[2] ?? eqAttr[3] ?? eqAttr[4] ?? eqAttr[5] ?? '').replace(/\s+/g, ' ').trim();
        if (CONTROL_ATTRS.has(attr)) push(put('A', val));
        else if (attr === 'label' || attr === 'labels') push(`${attr}=${put('Q', val)}`);
        else push(put('N', val));
        pos += eqAttr[0].length; continue;
      }
      const colonNonControl = /^(class|role|style|type|placeholder|title|href|aria-[\w-]+|data-[\w-]+)\s*:\s*(?:"((?:[^"\n]|\n(?![ \t]*\n))*)"|'((?:[^'\n]|\n(?![ \t]*\n))*)'|`([^`\n]+)`)/i.exec(rest);
      if (colonNonControl) {
        push(put('N', (colonNonControl[2] ?? colonNonControl[3] ?? colonNonControl[4] ?? '').replace(/\s+/g, ' ').trim()));
        pos += colonNonControl[0].length; continue;
      }
    }
    const quote = /^"((?:[^"\n]|\n(?![ \t]*\n))*)"/.exec(rest)
      || /^“((?:[^”\n]|\n(?![ \t]*\n))*)”/.exec(rest)
      || (pos === 0 || !/[\p{L}\p{N}]/u.test(source[pos - 1]) ? /^'((?:[^'\n]|'(?=[\p{L}\p{N}])|\n(?![ \t]*\n))*)'(?![\p{L}\p{N}])/u.exec(rest) : null);
    if (quote) {
      const rawInner = quote[1].replace(/\s*\n\s*/g, ' '), val = rawInner.replace(/\s+/g, ' ').trim();
      push(put('Q', val));
      const after = rest.slice(quote[0].length);
      if (/[.!?]$/.test(rawInner.trimEnd()) && /^(?:[ \t]*|[ \t]*\n[ \t]*)(?:[A-Z`"'“<]|$)/.test(after)) endSentence();
      pos += quote[0].length; continue;
    }
    if (source[pos] === '|') { endSentence(); pos++; continue; }
    if (source[pos] === '\n' && inHeading) { inHeading = false; endSentence(); pos++; continue; }
    const punct = /^[.!?]+(?=[)\]]*(?:[ \t]+|\n|$))/.exec(rest);
    if (punct) { endSentence(); pos += punct[0].length; continue; }
    push(source[pos] === '\n' ? ' ' : source[pos]);
    pos++;
  }

  const itemRe = `${escS}[QC](\\d+)${escS}`;
  const listRe = `${escS}[QC]\\d+${escS}(?:(?:\\s*,\\s*(?:and\\s+|or\\s+)?|\\s+(?:and|or)\\s+)${escS}[QC]\\d+${escS})*`;
  const negUnit = `(?:${listRe}|${escS}A\\d+${escS}|(?!\\b(?:a|an|the|show|shows|render|renders|use|uses|provide|provides|display|displays|items?|rows?|data|results?|tasks?|entries|records?|changes?|errors?|warnings?)\\b)[\\w-]+)`;
  const negMod = `(?:${negUnit}\\s+){0,3}`;
  const negatedRe = new RegExp(`\\b(?:no\\s+${negMod}|without\\s+(?:(?:a|an|any|the)\\s+)?${negMod})(?:buttons?|controls?)\\b`, 'i');
  const collectList = fragment => { for (const m of fragment.matchAll(new RegExp(itemRe, 'g'))) add(items[Number(m[1])]); };

  const attrTokenRe = new RegExp(`${escS}A(\\d+)${escS}`, 'g');
  const nonControlOwnerRe = /\b(?:region|container|box|bar|card|section|panel|grid|header|footer|banner)\s+$/i;
  const bindingListRe = new RegExp(`\\b(?:ids?|names?|values?)\\s*(?::|=)?\\s*(${listRe})`, 'gi');
  const nounMod = `(?:(?!\\b(?:a|an|the|in|on|for|with|to|from|of|by|at|into|under|after|before|when|while|if|its|their|this|that|show|shows|disable|disables|enable|enables|render|renders|click|use|is|are|says|has|and|or)\\b)[\\w-]+\\s+){0,2}`;
  const preNominalRe = new RegExp(`(${listRe})\\s+${nounMod}(?:buttons?|controls?)\\b`, 'gi');
  const postDirectRe = new RegExp(`\\b(?:buttons?|controls?)\\s*(?::\\s*|\\(\\s*)?(${listRe})`, 'gi');
  const postLabeledRe = new RegExp(`(?<![\\w-])(?:with\\s+(?:the\\s+)?(?:labels?|text|captions?)|labels?\\s*(?:=|:|is|are|of)|labeled|labelled|named|called)\\s*(${listRe})`, 'gi');

  for (const sentence of sentences) {
    for (const clause of splitClauses(sentence, escS, negMod)) {
      if (!/\b(?:buttons?|controls?)\b/i.test(clause) || negatedRe.test(clause)) continue;
      for (const m of clause.matchAll(attrTokenRe)) {
        if (!nonControlOwnerRe.test(clause.slice(0, m.index))) add(items[Number(m[1])]);
      }
      for (const m of clause.matchAll(bindingListRe)) {
        if (!nonControlOwnerRe.test(clause.slice(0, m.index))) collectList(m[1]);
      }
      for (const m of clause.matchAll(preNominalRe)) collectList(m[1]);
      for (const m of clause.matchAll(postDirectRe)) collectList(m[1]);
      for (const m of clause.matchAll(postLabeledRe)) collectList(m[1]);
      if (/\b(?:(?:four|4)\s+)?(?:touch-sized\s+)?direction(?:al)?\s+(?:buttons|controls)\b/i.test(clause)) {
        for (const direction of ['left', 'right', 'up', 'down']) if (!parts.some(part => mentioned(part.value.replace(/[-_]/g, ' '), direction))) controls.add(`move-${direction}`);
      }
    }
  }
  return controls;
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
  if (blocks.length === 1) {
    try { iface = JSON.parse(blocks[0][1]); } catch { iface = null; }
  }
  const hasEmbeddedInterface = blocks.length > 0;
  const isNativeOnly = fmKind === 'native-only' || iface?.kind === 'native-only';
  const prose = text.replace(INTERFACE_SUMMARY_RE, '');
  return { hasFrontmatter, hasEmbeddedInterface, isNativeOnly, iface, prose };
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
    const rel = relative(rootPlaceholder, resolve(dirname(resolve(rootPlaceholder, fromPrompt)), pathPart)).split(sep).join('/');
    if (visibleSet.has(rel)) out.push(rel);
  }
  return [...new Set(out)];
}
const rootPlaceholder = '/__pdd_root__';

function readPointer(obj, pointer) {
  if (typeof pointer !== 'string') return { found: false, value: undefined };
  if (pointer === '') return { found: obj !== undefined, value: obj };
  if (!pointer.startsWith('/')) return { found: false, value: undefined };
  let cur = obj;
  for (const seg of pointer.slice(1).split('/')) {
    if (cur === null || typeof cur !== 'object') return { found: false, value: undefined };
    const key = seg.replaceAll('~1', '/').replaceAll('~0', '~');
    if (Array.isArray(cur)) {
      const idx = Number(key);
      if (!Number.isInteger(idx) || idx < 0 || idx >= cur.length) return { found: false, value: undefined };
      cur = cur[idx];
    } else {
      if (!Object.hasOwn(cur, key)) return { found: false, value: undefined };
      cur = cur[key];
    }
  }
  return { found: true, value: cur };
}

function readSchemaPointer(stateSchema, pointer) {
  if (!stateSchema || typeof stateSchema !== 'object' || typeof pointer !== 'string' || !pointer.startsWith('/')) {
    return { exists: false, required: false, schema: null };
  }
  const segments = pointer.slice(1).split('/');
  const visit = (cur, idx, required) => {
    if (!cur || typeof cur !== 'object' || Array.isArray(cur)) {
      return { exists: false, required: false, schema: null };
    }
    if (typeof cur.$contract === 'string' || typeof cur.$ref === 'string') {
      return { exists: true, required: false, schema: cur };
    }
    if (idx >= segments.length) {
      return { exists: true, required, schema: cur };
    }
    const unions = [
      ...(Array.isArray(cur.oneOf) ? cur.oneOf : []),
      ...(Array.isArray(cur.anyOf) ? cur.anyOf : []),
      ...(Array.isArray(cur.allOf) ? cur.allOf : []),
    ];
    for (const branch of unions) {
      const branchHit = visit(branch, idx, false);
      if (branchHit.exists) return branchHit;
    }
    const key = segments[idx].replaceAll('~1', '/').replaceAll('~0', '~');
    const types = Array.isArray(cur.type) ? cur.type : typeof cur.type === 'string' ? [cur.type] : [];
    if (types.includes('array') || cur.items !== undefined || Array.isArray(cur.prefixItems)) {
      if (/^(?:0|[1-9][0-9]*|-)$/.test(key)) {
        if (Array.isArray(cur.prefixItems) && key !== '-' && Number(key) < cur.prefixItems.length) {
          return visit(cur.prefixItems[Number(key)], idx + 1, false);
        }
        if (cur.items && typeof cur.items === 'object' && !Array.isArray(cur.items)) {
          return visit(cur.items, idx + 1, false);
        }
        if (cur.items !== false) {
          return { exists: true, required: false, schema: null };
        }
      }
    }
    if (cur.properties && typeof cur.properties === 'object' && Object.hasOwn(cur.properties, key)) {
      const nextReq = required && Array.isArray(cur.required) && cur.required.includes(key);
      return visit(cur.properties[key], idx + 1, nextReq);
    }
    if (types.includes('object') || cur.additionalProperties !== undefined) {
      if (cur.additionalProperties === true) {
        return { exists: true, required: false, schema: null };
      }
      if (cur.additionalProperties && typeof cur.additionalProperties === 'object' && !Array.isArray(cur.additionalProperties)) {
        return visit(cur.additionalProperties, idx + 1, false);
      }
      if (!cur.properties && cur.additionalProperties !== false && types.includes('object')) {
        return { exists: true, required: false, schema: null };
      }
    }
    return { exists: false, required: false, schema: null };
  };
  return visit(stateSchema, 0, true);
}

function hasPointer(obj, pointer) {
  if (typeof pointer !== 'string') return false;
  if (pointer === '') return obj !== undefined;
  if (!pointer.startsWith('/')) return false;
  let cur = obj;
  for (const seg of pointer.slice(1).split('/')) {
    if (cur === null || typeof cur !== 'object') return false;
    const key = seg.replaceAll('~1', '/').replaceAll('~0', '~');
    if (Array.isArray(cur)) {
      const idx = Number(key);
      if (!Number.isInteger(idx) || idx < 0 || idx >= cur.length) return false;
      cur = cur[idx];
    } else {
      if (!Object.hasOwn(cur, key)) return false;
      cur = cur[key];
    }
  }
  return true;
}

function setPointer(obj, pointer, value) {
  if (!obj || typeof obj !== 'object' || typeof pointer !== 'string' || !pointer.startsWith('/')) return;
  const segs = pointer.slice(1).split('/').map(s => s.replaceAll('~1', '/').replaceAll('~0', '~'));
  let cur = obj;
  for (let i = 0; i < segs.length - 1; i++) {
    const key = segs[i];
    if (Array.isArray(cur)) {
      const idx = Number(key);
      if (!Number.isInteger(idx) || idx < 0 || idx >= cur.length || cur[idx] === null || typeof cur[idx] !== 'object') return;
      cur = cur[idx];
    } else {
      if (!Object.hasOwn(cur, key) || cur[key] === null || typeof cur[key] !== 'object') {
        Object.defineProperty(cur, key, { value: {}, writable: true, enumerable: true, configurable: true });
      }
      cur = cur[key];
    }
  }
  const last = segs.at(-1);
  if (Array.isArray(cur)) {
    const idx = Number(last);
    if (Number.isInteger(idx) && idx >= 0 && idx <= cur.length) cur[idx] = value;
  } else {
    Object.defineProperty(cur, last, { value, writable: true, enumerable: true, configurable: true });
  }
}

function resolveInitialWorld(root, testFile, initialWorld) {
  if (!initialWorld || typeof initialWorld !== 'object' || Array.isArray(initialWorld)) return { resolvable: true, world: initialWorld };
  if (typeof initialWorld.$seed !== 'string') return { resolvable: true, world: initialWorld };
  const rawSeed = initialWorld.$seed.trim();
  if (!rawSeed) return { resolvable: false, world: null };
  let seedDoc = null;
  const relCandidate = relative(rootPlaceholder, resolve(dirname(resolve(rootPlaceholder, testFile)), rawSeed)).split(sep).join('/');
  for (const candidate of [...new Set([rawSeed, relCandidate])]) {
    try {
      seedDoc = JSON.parse(safeRead(root, candidate));
      break;
    } catch { /* try fallback or mark unresolvable */ }
  }
  if (!seedDoc || typeof seedDoc !== 'object') return { resolvable: false, world: null };
  const world = structuredClone(seedDoc);
  if (initialWorld.set && typeof initialWorld.set === 'object' && !Array.isArray(initialWorld.set)) {
    for (const [ptr, val] of Object.entries(initialWorld.set)) {
      if (ptr === '') continue;
      setPointer(world, ptr, val);
    }
  }
  for (const [k, v] of Object.entries(initialWorld)) {
    if (k === '$seed' || k === 'set') continue;
    Object.defineProperty(world, k, { value: v, writable: true, enumerable: true, configurable: true });
  }
  return { resolvable: true, world };
}

const APP_MAP_PATH_RE = /(?:^|\/)(?:app-map\.json|app\/maps\/[^/]+\.json)$/;
const APP_MAP_SCHEMA_VERSIONS = new Set(['prompt-runtime.app-map.v1', 'prompt-runtime.app-map.v2']);
const isValidAppMapSchemaVersion = doc => !Object.hasOwn(doc, 'schema_version') || APP_MAP_SCHEMA_VERSIONS.has(doc.schema_version);
const isFixturePath = path => /(?:^|\/)fixtures\//.test(path);

function proseMentionsPortOp(prose, opKey) {
  if (prose.includes(opKey)) return true;
  const dot = opKey.indexOf('.');
  if (dot <= 0) return false;
  const port = opKey.slice(0, dot), op = opKey.slice(dot + 1);
  const portRe = new RegExp(`(?<![A-Za-z0-9_-])${escaped(port)}(?![A-Za-z0-9_-])`, 'i');
  const opRe = new RegExp(`(?<![A-Za-z0-9_-])${escaped(op)}(?![A-Za-z0-9_-])`, 'i');
  return portRe.test(prose) && opRe.test(prose);
}

export function lintSvgLayouts({ root, files, promptPaths }) {
  const policy=workspace.policy({root});files=files.filter(path=>workspace.allows(policy,path));
  const warnings = [], promptRecords = [], add = (prompt, drawing, part, reason) => warnings.push({ key: `${prompt}\0${drawing}\0${part}\0${reason}`, text: `Warning: SVG layout ${prompt} -> ${drawing}: ${part}: ${reason}.` });
  for (const prompt of [...new Set(promptPaths ?? files.filter(path => path.endsWith('.prompt.md')))].sort()) {
    let source;
    try { source = markupTokens(safeRead(root, prompt)).map(token => token.startsWith('<!--') ? '\n' : token).join('').replace(/\r\n?/g, '\n'); } catch (error) { add(prompt, '(unread)', 'source', error.message); continue; }
    source = source.replace(/<details\b[^>]*>\s*<summary[^>]*>[^\n]*Runtime interface[^\n]*<\/summary>[\s\S]*?<\/details>/gi, '')
      .replace(/(^##+ Runtime interface[^\n]*\n)[\s\S]*?(?=^##+ |$(?![\s\S]))/gmi, '');
    const decodedSource = decodeHtml(source), drawings = [];
    const promptRefs = refDefs(source);
    const resolvedLinks = [...new Set(links(source, promptRefs).sort().map(link => resolveDrawing(root, prompt, link)))].sort();
    const capturedSet = new Set(uploadCapturedSvgLinks(source, promptRefs).map(link => resolveDrawing(root, prompt, link)));
    for (const drawing of resolvedLinks) {
      if (drawing && drawing !== '..' && !drawing.startsWith('../')) {
        drawings.push(drawing);
        if (!capturedSet.has(drawing)) {
          add(
            prompt,
            drawing,
            'link syntax',
            'plain Markdown link outside "## Dependencies" is skipped by scoped uploads (causes dependency-file-unreadable); use image syntax ![label](...) or link it under "## Dependencies"',
          );
        }
      }
    }
    const scopedSources = drawings.length > 1 ? scopedSourcesByDrawing(source, root, prompt, drawings) : null;
    for (const drawing of resolvedLinks) {
      let parts;
      try { parts = partsOf(safeRead(root, drawing)); } catch (error) { add(prompt, drawing, 'drawing', error.message); continue; }
      const appearance = source.match(/^##+ Appearance\b[^\n]*\n([\s\S]*?)(?=^##? |$(?![\s\S]))/m)?.[1] || '';
      for (const { kind, value } of parts) {
        if (kind === 'text' && !/^[\d\s.,+%-]+$/.test(value) && !mentioned(source, value) && !mentioned(decodedSource, value)) add(prompt, drawing, `label "${value}"`, 'drawing label absent from prompt');
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
  if (promptRecords.some(record => record.drawings.length > 0)) {
    const mapPaths = new Set(files.filter(path => !isFixturePath(path) && APP_MAP_PATH_RE.test(path)));
    for (const testFile of files.filter(path => !isFixturePath(path) && /^(?:tests?|.*\/tests?)\/.*\.json$/.test(path))) {
      try {
        const doc = JSON.parse(safeRead(root, testFile));
        if (Array.isArray(doc?.app_maps)) for (const candidate of doc.app_maps) if (typeof candidate === 'string' && !isFixturePath(candidate) && workspace.allows(policy, candidate)) mapPaths.add(candidate);
      } catch { /* non-scenario or unreadable JSON */ }
    }
    const appMaps = [], cssPaths = new Set(), inspectedPrompts = new Set(promptRecords.map(record => record.path));
    for (const mapPath of [...mapPaths].sort()) {
      try {
        const doc = JSON.parse(safeRead(root, mapPath));
        if (
          !doc
          || typeof doc !== 'object'
          || Array.isArray(doc)
          || !isValidAppMapSchemaVersion(doc)
          || (Object.hasOwn(doc, 'name') && (typeof doc.name !== 'string' || !doc.name))
          || !Array.isArray(doc.screens)
        ) continue;
        const topSheets = Array.isArray(doc.stylesheets) ? doc.stylesheets.filter(item => typeof item === 'string') : [];
        const screens = doc.screens
          .filter(screen => screen && typeof screen === 'object' && typeof screen.prompt_path === 'string')
          .map((screen, idx) => {
            const source = typeof screen.source === 'string' ? screen.source : 'operation';
            const format = typeof screen.format === 'string' ? screen.format : (source === 'mockup' ? 'svg' : 'html');
            const id = typeof screen.id === 'string' && screen.id ? screen.id : (idx === 0 ? 'main' : `screen-${idx + 1}`);
            return {
              id,
              prompt_path: screen.prompt_path,
              source,
              format,
              stylesheets: Array.isArray(screen.stylesheets) ? screen.stylesheets.filter(item => typeof item === 'string') : [],
            };
          });
        for (const screen of screens) {
          if (screen.source === 'operation' && screen.format === 'html' && inspectedPrompts.has(screen.prompt_path)) {
            for (const cssPath of [...topSheets, ...screen.stylesheets]) cssPaths.add(cssPath);
          }
        }
        appMaps.push({ path: mapPath, stylesheets: topSheets, screens });
      } catch { /* unreadable or non-app-map JSON */ }
    }
    if (appMaps.length) {
      const stylesheets = [...cssPaths].sort().map(cssPath => {
        try { return { path: cssPath, content: safeRead(root, cssPath), error: null }; }
        catch (error) { return { path: cssPath, content: null, error: error.message }; }
      });
      for (const text of lintScreenDesign({ appMaps, stylesheets, prompts: promptRecords }).warnings) warnings.push({ key: text, text });
    }
  }
  const visiblePromptSet = new Set(files.filter(f => f.endsWith('.prompt.md') && workspace.allows(policy, f)));
  const metaCache = new Map();
  const getMeta = p => {
    if (metaCache.has(p)) return metaCache.get(p);
    try {
      const meta = parsePromptMeta(safeRead(root, p));
      metaCache.set(p, meta);
      return meta;
    } catch {
      metaCache.set(p, null);
      return null;
    }
  };
  const collectClosure = startPrompt => {
    const visited = new Set();
    const queue = [startPrompt];
    while (queue.length) {
      const cur = queue.shift();
      if (!cur || visited.has(cur) || !visiblePromptSet.has(cur)) continue;
      visited.add(cur);
      const meta = getMeta(cur);
      if (!meta) continue;
      for (const call of Array.isArray(meta.iface?.calls) ? meta.iface.calls : []) {
        if (typeof call?.target === 'string') queue.push(call.target);
      }
      if (!meta.hasEmbeddedInterface || meta.hasFrontmatter) {
        for (const target of promptTargets(meta.prose, cur, visiblePromptSet)) queue.push(target);
      }
    }
    return visited;
  };
  const promptFilter = promptPaths ? new Set(promptPaths) : null;
  const promptExists = promptPath => {
    if (typeof promptPath !== 'string' || !promptPath.endsWith('.prompt.md')) return false;
    if (visiblePromptSet.size > 0) return visiblePromptSet.has(promptPath);
    try { safeRead(root, promptPath); return true; } catch { return false; }
  };
  const promptDeclaresOp = (promptPath, op) => {
    const meta = getMeta(promptPath);
    if (!meta || typeof op !== 'string' || !op.trim()) return false;
    if (meta.hasEmbeddedInterface && Array.isArray(meta.iface?.entries)) {
      return meta.iface.entries.some(entry => entry?.operation === op);
    }
    return new RegExp(`(?<![A-Za-z0-9_-])${escaped(op)}(?![A-Za-z0-9_-])`).test(meta.prose);
  };
  const allMapPaths = new Set(files.filter(path => !isFixturePath(path) && APP_MAP_PATH_RE.test(path) && workspace.allows(policy, path)));
  for (const testFile of files.filter(path => !isFixturePath(path) && /^(?:tests?|.*\/tests?)\/.*\.json$/.test(path) && workspace.allows(policy, path))) {
    try {
      const doc = JSON.parse(safeRead(root, testFile));
      if (Array.isArray(doc?.app_maps)) {
        for (const candidate of doc.app_maps) {
          if (typeof candidate === 'string' && !isFixturePath(candidate) && workspace.allows(policy, candidate)) allMapPaths.add(candidate);
        }
      }
    } catch { /* handled below when Story-paired */ }
  }
  const parsedAppMaps = new Map();
  const MAX_SAFE_TIMER_INT = 9007199254740991;
  for (const mapPath of [...allMapPaths].sort()) {
    let mapDoc;
    try { mapDoc = JSON.parse(safeRead(root, mapPath)); }
    catch {
      if (!promptFilter) {
        const text = `Warning: ${mapPath}: app-map.json is not valid JSON; fix syntax and set "schema_version": "prompt-runtime.app-map.v1".`;
        warnings.push({ key: `${mapPath}\0mapjson`, text });
      }
      continue;
    }
    if (!mapDoc || typeof mapDoc !== 'object' || Array.isArray(mapDoc)) continue;
    parsedAppMaps.set(mapPath, mapDoc);
    const screens = Array.isArray(mapDoc.screens) ? mapDoc.screens.filter(s => s && typeof s === 'object') : [];
    const timers = Array.isArray(mapDoc.timers) ? mapDoc.timers : [];
    if (promptFilter) {
      const referenced = new Set([
        ...screens.map(s => s.prompt_path).filter(p => typeof p === 'string'),
        ...timers.map(t => t?.handler?.prompt_path).filter(p => typeof p === 'string'),
      ]);
      if (![...referenced].some(p => promptFilter.has(p))) continue;
    }
    if (Object.hasOwn(mapDoc, 'schema_version') && !APP_MAP_SCHEMA_VERSIONS.has(mapDoc.schema_version)) {
      const text = `Warning: ${mapPath}: app-map schema_version ${JSON.stringify(mapDoc.schema_version ?? null)} is invalid; set "schema_version": "prompt-runtime.app-map.v1" (or omit it for compact app-map.json).`;
      warnings.push({ key: `${mapPath}\0mapschema`, text });
    }
    if (!screens.length && !promptFilter) {
      const text = `Warning: ${mapPath}: app-map.json must declare a non-empty "screens" array.`;
      warnings.push({ key: `${mapPath}\0mapscreens`, text });
    }
    const validScreenIds = new Set();
    const screenPromptById = new Map();
    for (const [sIdx, screen] of screens.entries()) {
      const sId = typeof screen.id === 'string' && screen.id ? screen.id : (sIdx === 0 ? 'main' : `screen-${sIdx + 1}`);
      if (sId !== '*') validScreenIds.add(sId);
      if (typeof screen.prompt_path === 'string' && screen.prompt_path.trim()) {
        screenPromptById.set(sId, screen.prompt_path);
        if (!promptExists(screen.prompt_path)) {
          const text = `Warning: ${mapPath} (screen "${sId}"): screen prompt_path "${screen.prompt_path}" does not exist in Git-visible prompts; point prompt_path to an existing prompts/*.prompt.md file and run git add.`;
          warnings.push({ key: `${mapPath}\0mapscreen\0${sIdx}`, text });
        }
      } else if (screen.source !== 'static') {
        const text = `Warning: ${mapPath} (screen "${sId}"): screen prompt_path is missing; set "prompt_path": "prompts/<screen>.prompt.md".`;
        warnings.push({ key: `${mapPath}\0mapscreenmissing\0${sIdx}`, text });
      }
    }
    const hasStateSchema = Boolean(mapDoc.state_schema && typeof mapDoc.state_schema === 'object' && !Array.isArray(mapDoc.state_schema));
    if (mapDoc.timers !== undefined) {
      if (!Array.isArray(mapDoc.timers) || mapDoc.timers.length > 16) {
        const text = `Warning: ${mapPath}: timers must be an array of at most 16 timer objects.`;
        warnings.push({ key: `${mapPath}\0timersarr`, text });
      } else {
        const seenTimerScreens = new Set();
        for (const [tIdx, timer] of mapDoc.timers.entries()) {
          const tLabel = typeof timer?.id === 'string' && timer.id ? timer.id : `timers[${tIdx}]`;
          if (!timer || typeof timer !== 'object' || Array.isArray(timer)) {
            const text = `Warning: ${mapPath} (timer "${tLabel}"): timer entry must be an object with id, screen, interval_ms, enabled_pointer, generation_pointer, handler, input, state and next.`;
            warnings.push({ key: `${mapPath}\0timerobj\0${tIdx}`, text });
            continue;
          }
          if (typeof timer.screen !== 'string' || timer.screen === '*' || !validScreenIds.has(timer.screen) || seenTimerScreens.has(timer.screen)) {
            const text = `Warning: ${mapPath} (timer "${tLabel}"): timer screen ${JSON.stringify(timer.screen ?? null)} must name a unique existing non-wildcard screen id from screens[].`;
            warnings.push({ key: `${mapPath}\0timerscreen\0${tIdx}`, text });
          } else {
            seenTimerScreens.add(timer.screen);
          }
          if (!Number.isInteger(timer.interval_ms) || timer.interval_ms < 1000 || timer.interval_ms > 3600000) {
            const text = `Warning: ${mapPath} (timer "${tLabel}"): interval_ms (${JSON.stringify(timer.interval_ms)}) must be an integer from 1000 to 3600000 (for example "interval_ms": 1000).`;
            warnings.push({ key: `${mapPath}\0timerinterval\0${tIdx}`, text });
          }
          const enInit = readPointer(mapDoc.initial_state, timer.enabled_pointer);
          const enSchema = hasStateSchema ? readSchemaPointer(mapDoc.state_schema, timer.enabled_pointer) : null;
          if (
            typeof enInit.value !== 'boolean'
            || (hasStateSchema && (
              !enSchema.exists
              || !enSchema.required
              || enSchema.schema?.type !== 'boolean'
              || Array.isArray(enSchema.schema?.oneOf)
            ))
          ) {
            const text = `Warning: ${mapPath} (timer "${tLabel}"): enabled_pointer ${JSON.stringify(timer.enabled_pointer ?? null)} must resolve to a boolean in initial_state and a required {"type": "boolean"} property (without oneOf) in state_schema.`;
            warnings.push({ key: `${mapPath}\0timerenabled\0${tIdx}`, text });
          }
          const genInit = readPointer(mapDoc.initial_state, timer.generation_pointer);
          const genSchema = hasStateSchema ? readSchemaPointer(mapDoc.state_schema, timer.generation_pointer) : null;
          const genMin = genSchema?.schema?.minimum;
          const genMax = genSchema?.schema?.maximum;
          const validGenInit = Number.isSafeInteger(genInit.value) && genInit.value >= 0 && genInit.value <= MAX_SAFE_TIMER_INT;
          const validGenMax = genMax === undefined || (Number.isSafeInteger(genMax) && genMax <= MAX_SAFE_TIMER_INT && Number.isSafeInteger(genMin) && genMin <= genMax);
          const validGenSchema = !hasStateSchema || (
            genSchema.exists
            && genSchema.required
            && genSchema.schema?.type === 'integer'
            && !Array.isArray(genSchema.schema?.oneOf)
            && Number.isSafeInteger(genMin)
            && genMin >= 0
            && genMin <= MAX_SAFE_TIMER_INT
            && validGenMax
          );
          if (!validGenInit || !validGenSchema) {
            const text = `Warning: ${mapPath} (timer "${tLabel}"): generation_pointer ${JSON.stringify(timer.generation_pointer ?? null)} must resolve to a safe integer 0..9007199254740991 in initial_state and a required {"type": "integer", "minimum": 0} property (without oneOf) in state_schema.`;
            warnings.push({ key: `${mapPath}\0timergen\0${tIdx}`, text });
          }
          if (timer.tick_operation !== undefined && (!timer.handler || typeof timer.handler !== 'object')) {
            const fallbackPrompt = screenPromptById.get(timer.screen) ?? 'prompts/<screen>.prompt.md';
            const opHint = typeof timer.tick_operation === 'string' && timer.tick_operation.trim() ? timer.tick_operation : '<tick_op>';
            const text = `Warning: ${mapPath} (timer "${tLabel}"): replace tick_operation ${JSON.stringify(timer.tick_operation)} with "handler": {"prompt_path": "${fallbackPrompt}", "operation": "${opHint}"} naming an existing prompt and declared tick operation.`;
            warnings.push({ key: `${mapPath}\0timertickkey\0${tIdx}`, text });
          } else {
            const hPrompt = timer.handler?.prompt_path;
            const hOp = timer.handler?.operation;
            if (typeof hPrompt !== 'string' || !promptExists(hPrompt)) {
              const text = `Warning: ${mapPath} (timer "${tLabel}"): handler.prompt_path ${JSON.stringify(hPrompt ?? null)} must reference an existing Git-visible prompts/*.prompt.md file.`;
              warnings.push({ key: `${mapPath}\0timerhprompt\0${tIdx}`, text });
            } else if (typeof hOp !== 'string' || !hOp.trim() || !promptDeclaresOp(hPrompt, hOp)) {
              const text = `Warning: ${mapPath} (timer "${tLabel}"): tick_operation / handler.operation ${JSON.stringify(hOp ?? null)} is not declared in ${hPrompt}; declare "${hOp || '<tick_op>'}" in ${hPrompt} or update handler.operation.`;
              warnings.push({ key: `${mapPath}\0timerhop\0${tIdx}`, text });
            }
          }
        }
      }
    }
    if (mapDoc.state_schema && typeof mapDoc.state_schema === 'object' && !Array.isArray(mapDoc.state_schema)) {
      const checkStateRefs = (node, label) => {
        if (!node || typeof node !== 'object') return;
        if (!Array.isArray(node) && Object.keys(node).length === 1 && typeof node.$ref === 'string') {
          if (node.$ref.startsWith('/state/')) {
            const statePtr = node.$ref.slice('/state'.length);
            const hit = readSchemaPointer(mapDoc.state_schema, statePtr);
            if (!hit.exists) {
              const text = `Warning: ${mapPath} (${label}): $ref ${JSON.stringify(node.$ref)} does not resolve in state_schema; declare ${statePtr} in state_schema and initial_state or fix the $ref pointer.`;
              warnings.push({ key: `${mapPath}\0stateref\0${label}\0${node.$ref}`, text });
            }
          }
          return;
        }
        for (const child of Object.values(node)) checkStateRefs(child, label);
      };
      const checkStateTargets = (stateNode, label) => {
        if (!stateNode || typeof stateNode !== 'object' || Array.isArray(stateNode)) return;
        if (Object.keys(stateNode).length === 1 && typeof stateNode.$ref === 'string') return;
        for (const key of Object.keys(stateNode)) {
          const ptr = key.startsWith('/') ? key : `/${key.replaceAll('~', '~0').replaceAll('/', '~1')}`;
          const hit = readSchemaPointer(mapDoc.state_schema, ptr);
          if (!hit.exists) {
            const text = `Warning: ${mapPath} (${label}): state target ${JSON.stringify(key)} does not resolve in state_schema; declare ${ptr} in state_schema and initial_state or update state.`;
            warnings.push({ key: `${mapPath}\0statetarget\0${label}\0${key}`, text });
          }
        }
      };
      for (const [sIdx, screen] of screens.entries()) {
        const sLabel = `screen "${typeof screen.id === 'string' && screen.id ? screen.id : `screens[${sIdx}]`}"`;
        checkStateRefs(screen.input, sLabel);
      }
      const handlers = Array.isArray(mapDoc.handlers) ? mapDoc.handlers : [];
      for (const [hIdx, handler] of handlers.entries()) {
        if (!handler || typeof handler !== 'object' || Array.isArray(handler)) continue;
        const hLabel = `handler "${typeof handler.id === 'string' && handler.id ? handler.id : `handlers[${hIdx}]`}"`;
        checkStateRefs(handler.input, hLabel);
        checkStateRefs(handler.state, hLabel);
        checkStateTargets(handler.state, hLabel);
        for (const [aIdx, afterStep] of (Array.isArray(handler.after) ? handler.after : []).entries()) {
          if (!afterStep || typeof afterStep !== 'object' || Array.isArray(afterStep)) continue;
          const aLabel = `${hLabel} after[${aIdx}]`;
          checkStateRefs(afterStep.input, aLabel);
          if (typeof afterStep.bind === 'string' && afterStep.bind.startsWith('/')) {
            const hit = readSchemaPointer(mapDoc.state_schema, afterStep.bind);
            if (!hit.exists) {
              const text = `Warning: ${mapPath} (${aLabel}): bind ${JSON.stringify(afterStep.bind)} does not resolve in state_schema; declare ${afterStep.bind} in state_schema and initial_state or update bind.`;
              warnings.push({ key: `${mapPath}\0afterbind\0${aLabel}\0${afterStep.bind}`, text });
            }
          }
        }
      }
      for (const [tIdx, timer] of (Array.isArray(mapDoc.timers) ? mapDoc.timers : []).entries()) {
        if (!timer || typeof timer !== 'object' || Array.isArray(timer)) continue;
        const tLabel = `timer "${typeof timer.id === 'string' && timer.id ? timer.id : `timers[${tIdx}]`}"`;
        checkStateRefs(timer.input, tLabel);
        checkStateRefs(timer.state, tLabel);
        checkStateTargets(timer.state, tLabel);
      }
    }
  }
  const storyFiles = files.filter(
    p =>
      p.endsWith('.md') &&
      p.split('/').slice(0, -1).includes('user_stories') &&
      !['plan.md', 'readme.md'].includes(p.split('/').at(-1).toLowerCase()),
  );
  const storyPathByStem = new Map();
  for (const sp of storyFiles) {
    const stem = sp.split('/').at(-1).slice(0, -3);
    if (!storyPathByStem.has(stem)) storyPathByStem.set(stem, sp);
  }
  const storyStems = new Set(storyPathByStem.keys());
  const checkableScenarioEntries = new Set();
  const PORT_OP_RE = /^[A-Za-z][A-Za-z0-9_-]*\.[A-Za-z][A-Za-z0-9_-]*$/;
  for (const testFile of files.filter(path => /^(?:tests?|.*\/tests?)\/.*\.json$/.test(path) && workspace.allows(policy, path))) {
    const isFixtureJson = isFixturePath(testFile);
    const baseStem = testFile.split('/').at(-1).slice(0, -5);
    const primaryStem = baseStem.split('.')[0];
    const isCasesJson = baseStem === 'cases' || baseStem.endsWith('-cases');
    const pairedStoryPath = !isFixtureJson && !isCasesJson
      ? (storyPathByStem.get(baseStem) ?? storyPathByStem.get(primaryStem) ?? null)
      : null;
    const pairedWithStory = pairedStoryPath !== null;
    let doc;
    try { doc = JSON.parse(safeRead(root, testFile)); }
    catch {
      if (pairedWithStory && !promptFilter) {
        const text = `Warning: ${testFile}: scenario test file is not valid JSON; write a JSON object with "schema_version": "prompt-runtime.program-scenario.v1".`;
        warnings.push({ key: `${testFile}\0testjson`, text });
      }
      continue;
    }
    const isNativeCaseDoc = isCasesJson || Array.isArray(doc?.cases) || /^pdd\.native-cases\./.test(String(doc?.schema_version ?? ''));
    let shortCompileHandled = false;
    if (
      !isFixtureJson &&
      !isNativeCaseDoc &&
      doc &&
      typeof doc === 'object' &&
      !Array.isArray(doc) &&
      needsScenarioCompile(doc)
    ) {
      shortCompileHandled = isShortScenarioDoc(doc);
      const targetStoryPath = typeof doc.story_path === 'string' && doc.story_path ? doc.story_path : pairedStoryPath;
      let storySource = null;
      if (typeof targetStoryPath === 'string' && workspace.allows(policy, targetStoryPath)) {
        try { storySource = safeRead(root, targetStoryPath); } catch { storySource = null; }
      }
      const compiled = compileScenario(doc, { path: testFile, storyPath: pairedStoryPath, storySource });
      if (!compiled.refusal) {
        doc = compiled.doc;
      }
    }
    const looksLikeScenario = !isFixtureJson && !isNativeCaseDoc && doc && typeof doc === 'object' && !Array.isArray(doc) && (
      pairedWithStory
      || typeof doc.story_path === 'string'
      || (Array.isArray(doc.steps) && doc.steps.some(s => s && typeof s === 'object' && (typeof s.entry_path === 'string' || typeof s.operation === 'string') && Array.isArray(s.checks)))
    );
    if (looksLikeScenario && !shortCompileHandled && doc.schema_version !== V1_SCENARIO_SCHEMA) {
      const candidateSteps = Array.isArray(doc.steps) ? doc.steps : [];
      const matchesFilter = !promptFilter || candidateSteps.some(s => typeof s?.entry_path === 'string' && promptFilter.has(s.entry_path));
      if (matchesFilter) {
        const text = `Warning: ${testFile}: scenario schema_version ${JSON.stringify(doc.schema_version ?? null)} is invalid; set "schema_version": "prompt-runtime.program-scenario.v1".`;
        warnings.push({ key: `${testFile}\0testschema`, text });
      }
    }
    if (isFixtureJson || isNativeCaseDoc || !doc || typeof doc !== 'object' || doc.schema_version !== V1_SCENARIO_SCHEMA || !Array.isArray(doc.steps)) continue;
    for (const mapCandidate of Array.isArray(doc.app_maps) ? doc.app_maps : []) {
      const mapDoc = typeof mapCandidate === 'string' ? parsedAppMaps.get(mapCandidate) : null;
      if (!mapDoc) continue;
      for (const s of Array.isArray(mapDoc.screens) ? mapDoc.screens : []) {
        if (typeof s?.prompt_path === 'string' && visiblePromptSet.has(s.prompt_path) && !getMeta(s.prompt_path)?.isNativeOnly) checkableScenarioEntries.add(s.prompt_path);
      }
      for (const h of Array.isArray(mapDoc.handlers) ? mapDoc.handlers : []) {
        const hp = h?.handler?.prompt_path;
        if (typeof hp === 'string' && visiblePromptSet.has(hp) && !getMeta(hp)?.isNativeOnly) checkableScenarioEntries.add(hp);
      }
      for (const t of Array.isArray(mapDoc.timers) ? mapDoc.timers : []) {
        const tp = t?.handler?.prompt_path;
        if (typeof tp === 'string' && visiblePromptSet.has(tp) && !getMeta(tp)?.isNativeOnly) checkableScenarioEntries.add(tp);
      }
    }
    const inRepoSteps = doc.steps.filter(step => step && typeof step.entry_path === 'string' && visiblePromptSet.has(step.entry_path));
    for (const step of inRepoSteps) {
      if (!getMeta(step.entry_path)?.isNativeOnly) checkableScenarioEntries.add(step.entry_path);
    }
    if (!inRepoSteps.length) continue;
    const stepClosures = new Map();
    const allClosurePrompts = new Set();
    for (const step of inRepoSteps) {
      if (!stepClosures.has(step.entry_path)) stepClosures.set(step.entry_path, collectClosure(step.entry_path));
      for (const p of stepClosures.get(step.entry_path)) allClosurePrompts.add(p);
    }
    if (promptFilter && ![...allClosurePrompts].some(p => promptFilter.has(p))) continue;
    const resolvedWorld = resolveInitialWorld(root, testFile, doc.initial_world);
    const schemaAllowsPointer = (schema, pointer) => {
      if (typeof pointer !== 'string' || pointer === '') return true;
      if (!pointer.startsWith('/')) return false;
      const walk = (cur, segs) => {
        if (!segs.length || !cur || typeof cur !== 'object') return true;
        for (const union of ['oneOf', 'anyOf']) {
          if (Array.isArray(cur[union])) return cur[union].some(branch => walk(branch, segs));
        }
        const kind = cur.type;
        if (Array.isArray(kind)) return kind.some(candidate => walk({ ...cur, type: candidate }, segs));
        const token = segs[0].replaceAll('~1', '/').replaceAll('~0', '~');
        const rest = segs.slice(1);
        if (kind === 'object') {
          const props = cur.properties && typeof cur.properties === 'object' ? cur.properties : {};
          if (Object.hasOwn(props, token)) return walk(props[token], rest);
          if (cur.additionalProperties === false) return false;
          return true;
        }
        if (kind === 'array') {
          if (!/^(?:0|[1-9]\d*)$/.test(token)) return false;
          const items = cur.items;
          return items && typeof items === 'object' ? walk(items, rest) : true;
        }
        if (kind === undefined || kind === null) return true;
        return false;
      };
      return walk(schema, pointer.slice(1).split('/'));
    };
    const summarizeClosure = closureSet => {
      const resources = new Map();
      const resultSchemas = new Map();
      const addResourceAccess = (key, access, resultSchema) => {
        if (typeof key !== 'string' || !key) return;
        if (!resources.has(key)) resources.set(key, new Set());
        if (typeof access === 'string' && access) resources.get(key).add(access);
        if (resultSchema && typeof resultSchema === 'object' && !resultSchemas.has(key)) resultSchemas.set(key, resultSchema);
      };
      let hasPlainPrompt = false;
      const proseChunks = [];
      for (const p of closureSet) {
        const meta = getMeta(p);
        if (!meta) continue;
        proseChunks.push(meta.prose);
        if (!meta.hasEmbeddedInterface) hasPlainPrompt = true;
        for (const res of Array.isArray(meta.iface?.resources) ? meta.iface.resources : []) {
          if (res?.kind === 'port' && typeof res.name === 'string' && Array.isArray(res.operations)) {
            for (const op of res.operations) {
              if (typeof op?.name === 'string' && op.name) {
                addResourceAccess(`${res.name}.${op.name}`, op.access ?? res.access, op.result_schema ?? op.output_schema ?? null);
              }
            }
          } else if (typeof res?.operation === 'string') {
            addResourceAccess(res.operation, res.access, res.result_schema ?? res.output_schema ?? null);
          }
        }
      }
      return { resources, resultSchemas, hasPlainPrompt, combinedProse: proseChunks.join('\n') };
    };
    const criteriaById = new Map(
      (Array.isArray(doc.criteria) ? doc.criteria : [])
        .filter(c => c && typeof c.id === 'string')
        .map(c => [c.id, typeof c.text === 'string' ? c.text : '']),
    );
    const wholeSummary = summarizeClosure(allClosurePrompts);
    if (doc.simulation && typeof doc.simulation === 'object' && !Array.isArray(doc.simulation)) {
      for (const [opKey, rawSim] of Object.entries(doc.simulation)) {
        if (!PORT_OP_RE.test(opKey)) {
          if (wholeSummary.hasPlainPrompt) {
            const text = `Warning: ${testFile}: simulation key "${opKey}" must have <port>.<operation> form`;
            warnings.push({ key: `${testFile}\0simfmt\0${opKey}`, text });
          }
          continue;
        }
        if (wholeSummary.hasPlainPrompt && !wholeSummary.resources.has(opKey) && !proseMentionsPortOp(wholeSummary.combinedProse, opKey)) {
          const text = `Warning: ${testFile}: simulation port "${opKey}" is not mentioned in reachable prompt prose; name ${opKey} explicitly so lazy interface synthesis binds the port`;
          warnings.push({ key: `${testFile}\0simprose\0${opKey}`, text });
        }
        const simBinding = rawSim?.binding && typeof rawSim.binding === 'object' ? rawSim.binding : rawSim;
        const rvp = typeof simBinding?.result_value_pointer === 'string' ? simBinding.result_value_pointer : null;
        if (rvp !== null) {
          const rSchema = wholeSummary.resultSchemas.get(opKey);
          if (rSchema && !schemaAllowsPointer(rSchema, rvp)) {
            const text = `Warning: ${testFile}: simulation "${opKey}" result_value_pointer "${rvp}" is excluded by "${opKey}" result_schema (impossible-result-value-pointer)`;
            warnings.push({ key: `${testFile}\0simrvpschema\0${opKey}`, text });
          }
          if (rvp !== '' && simBinding && Object.hasOwn(simBinding, 'result_template') && !hasPointer(simBinding.result_template, rvp)) {
            const text = `Warning: ${testFile}: simulation "${opKey}" result_template is missing result_value_pointer "${rvp}" (missing-result-placeholder)`;
            warnings.push({ key: `${testFile}\0simrvptpl\0${opKey}`, text });
          }
        }
      }
    }
    for (const [idx, step] of doc.steps.entries()) {
      const overrides = step?.simulation_overrides;
      if (!overrides || typeof overrides !== 'object' || typeof step.entry_path !== 'string' || !visiblePromptSet.has(step.entry_path)) continue;
      const stepLabel = typeof step.step_id === 'string' && step.step_id ? step.step_id : `steps[${idx}]`;
      const summary = summarizeClosure(stepClosures.get(step.entry_path) ?? collectClosure(step.entry_path));
      const checkedIds = new Set((Array.isArray(step.checks) ? step.checks : []).map(ch => ch?.criterion_id).filter(Boolean));
      const entries = Array.isArray(overrides)
        ? overrides.filter(row => row && typeof row === 'object').map((row, rowIdx) => ({
            opKey: typeof row.operation === 'string' ? row.operation : '',
            binding: row.binding && typeof row.binding === 'object' ? row.binding : row,
            cid: typeof row.criterion_id === 'string' ? row.criterion_id : '',
            fquote: typeof row.failure_quote === 'string' ? row.failure_quote : '',
            rowKey: String(rowIdx),
          }))
        : Object.entries(overrides).map(([opKey, binding]) => ({
            opKey,
            binding: binding?.binding && typeof binding.binding === 'object' ? binding.binding : binding,
            cid: typeof binding?.criterion_id === 'string' ? binding.criterion_id : '',
            fquote: typeof binding?.failure_quote === 'string' ? binding.failure_quote : '',
            rowKey: opKey,
          }));
      if (!Array.isArray(overrides)) {
        const text = `Warning: ${testFile} (${stepLabel}): simulation_overrides should be an array of {operation, criterion_id, failure_quote, reason, binding} objects`;
        warnings.push({ key: `${testFile}\0ovshape\0${stepLabel}`, text });
      }
      for (const { opKey, binding, cid, fquote, rowKey } of entries) {
        if (!PORT_OP_RE.test(opKey)) {
          const text = `Warning: ${testFile} (${stepLabel}): simulation_overrides operation "${opKey}" must have <port>.<operation> form`;
          warnings.push({ key: `${testFile}\0ovfmt\0${stepLabel}\0${rowKey}`, text });
          continue;
        }
        const declared = summary.resources.get(opKey);
        if (!declared) {
          if (!summary.hasPlainPrompt) {
            const text = `Warning: ${testFile} (${stepLabel}): simulation_overrides port "${opKey}" is not declared in reachable Runtime interface resources for ${step.entry_path}`;
            warnings.push({ key: `${testFile}\0ovres\0${stepLabel}\0${rowKey}`, text });
          } else if (!proseMentionsPortOp(summary.combinedProse, opKey)) {
            const text = `Warning: ${testFile} (${stepLabel}): simulation_overrides port "${opKey}" is not mentioned in reachable prompt prose (${step.entry_path}); name ${opKey} explicitly so lazy interface synthesis binds the port`;
            warnings.push({ key: `${testFile}\0ovprose\0${stepLabel}\0${rowKey}`, text });
          }
        } else if (binding?.action === 'port.write' && !declared.has('read') && !declared.has('write') && !declared.has('read_write')) {
          const text = `Warning: ${testFile} (${stepLabel}): port.write simulation_overrides on "${opKey}" requires read or write port access in reachable Runtime interface resources`;
          warnings.push({ key: `${testFile}\0ovacc\0${stepLabel}\0${rowKey}`, text });
        }
        if (binding?.action === 'port.write' && typeof binding.world_pointer === 'string' && resolvedWorld.resolvable && !hasPointer(resolvedWorld.world, binding.world_pointer)) {
          const text = `Warning: ${testFile} (${stepLabel}): simulation_overrides "${opKey}" world_pointer "${binding.world_pointer}" is missing from initial_world`;
          warnings.push({ key: `${testFile}\0ovwp\0${stepLabel}\0${rowKey}`, text });
        }
        const ovRvp = typeof binding?.result_value_pointer === 'string' ? binding.result_value_pointer : null;
        if (ovRvp !== null) {
          const ovSchema = summary.resultSchemas.get(opKey);
          if (ovSchema && !schemaAllowsPointer(ovSchema, ovRvp)) {
            const text = `Warning: ${testFile} (${stepLabel}): simulation_overrides "${opKey}" result_value_pointer "${ovRvp}" is excluded by "${opKey}" result_schema (impossible-result-value-pointer)`;
            warnings.push({ key: `${testFile}\0ovrvpschema\0${stepLabel}\0${rowKey}`, text });
          }
          if (ovRvp !== '' && binding && Object.hasOwn(binding, 'result_template') && !hasPointer(binding.result_template, ovRvp)) {
            const text = `Warning: ${testFile} (${stepLabel}): simulation_overrides "${opKey}" result_template is missing result_value_pointer "${ovRvp}" (missing-result-placeholder)`;
            warnings.push({ key: `${testFile}\0ovrvptpl\0${stepLabel}\0${rowKey}`, text });
          }
        }
        if (!cid || !checkedIds.has(cid)) {
          const text = `Warning: ${testFile} (${stepLabel}): simulation_overrides "${opKey}" criterion_id "${cid}" is not checked by step ${stepLabel}`;
          warnings.push({ key: `${testFile}\0ovcid\0${stepLabel}\0${rowKey}`, text });
        } else if (fquote.trim() && !criteriaById.get(cid)?.includes(fquote)) {
          const text = `Warning: ${testFile} (${stepLabel}): simulation_overrides "${opKey}" failure_quote "${fquote}" is absent from criterion ${cid}`;
          warnings.push({ key: `${testFile}\0ovfq\0${stepLabel}\0${rowKey}`, text });
        }
      }
    }
  }
  const storyReachablePrompts = new Set();
  for (const entry of checkableScenarioEntries) {
    const closure = collectClosure(entry);
    if (promptFilter && ![...closure].some(p => promptFilter.has(p))) continue;
    for (const p of closure) storyReachablePrompts.add(p);
  }
  for (const prompt of [...storyReachablePrompts].sort()) {
    if (promptFilter && !promptFilter.has(prompt)) continue;
    const meta = getMeta(prompt);
    if (!meta || meta.isNativeOnly || (meta.hasEmbeddedInterface && !meta.hasFrontmatter)) continue;
    for (const dep of collectClosure(prompt)) {
      if (dep === prompt) continue;
      if (getMeta(dep)?.isNativeOnly) {
        const text = `Warning: ${prompt}: checkable prompt links kind: native-only prompt ${dep} (invert the dependency and inject a <port>.<op> port so Story checks do not skip)`;
        warnings.push({ key: `${prompt}\0native\0${dep}`, text });
      }
    }
  }
  return [...new Map(warnings.sort((a, b) => a.key < b.key ? -1 : a.key > b.key ? 1 : 0).map(warning => [warning.text, warning.text])).values()];
}
