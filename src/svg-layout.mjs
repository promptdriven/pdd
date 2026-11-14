// Generated from prompts/cli/svg-layout.prompt.md (sha256: 2969078ae0e2067e53589bc5893ce851612af71025b9c1d590719f19b4aacc57).
import { lstatSync, readFileSync } from 'node:fs';
import { dirname, relative, resolve, sep } from 'node:path';
import { lintScreenDesign } from './screen-design-check.mjs';
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
const refDefs = text => new Map([...text.matchAll(/^\s*\[([^\]]+)\]:\s*<?([^\s>]+)>?/gm)].map(m => [normalize(m[1]), m[2]]));
function links(text, refs = refDefs(text)) {
  return [...new Set([
    ...[...text.matchAll(/!?\[[^\]]*\]\(\s*(?:<([^>]+)>|([^\s)]+))(?:\s+["'][^)]*)?\)/g)].map(m => m[1] || m[2]),
    ...[...text.matchAll(/!?\[([^\]]+)\]\[([^\]]*)\]/g)].map(m => refs.get(normalize(m[2] || m[1]))),
    ...[...text.matchAll(/!?\[([^\]]+)\](?![\[(:])/g)].map(m => refs.get(normalize(m[1]))),
  ].filter(value => value && !/^(?:[a-z][a-z\d+.-]*:|\/\/|#)/i.test(value) && /\.ui\.svg(?:#.*)?$/i.test(value)).map(value => value.split('#')[0]))];
}
const mentioned = (prose, value) => new RegExp(`(^|[^\\p{L}\\p{N}_])${escaped(normalize(value))}($|[^\\p{L}\\p{N}_])`, 'u').test(normalize(prose));
const resolveDrawing = (root, prompt, link) => {
  try { return relative(root, resolve(root, dirname(prompt), decodeURIComponent(link))).split(sep).join('/'); } catch { return link; }
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
  const linkedIn = text => {
    const set = new Set(links(text, refs).map(link => resolveDrawing(root, prompt, link)).filter(d => allowed.has(d)));
    return set.size > 0 && set.size < drawings.length ? set : null;
  };
  const isStandaloneImages = text => {
    const stripped = text
      .replace(/^\s*\[[^\]]+\]:\s*<?[^\s>]+>?\s*$/gm, '')
      .replace(/!\[[^\]]*\]\(\s*(?:<[^>]+>|[^\s)]+)(?:\s+["'][^)]*)?\)/g, '')
      .replace(/!\[[^\]]+\]\[[^\]]*\]/g, '')
      .replace(/!\[[^\]]+\](?![\[(:])/g, '')
      .trim();
    return !stripped && links(text, refs).length > 0;
  };
  const listLead = line => {
    const rest = line.replace(/^ {0,3}(?:[-*+]|\d+[.)])[ \t]+/, '');
    let tick = false, quote = null;
    for (let i = 0; i < Math.min(rest.length, 160); i++) {
      const ch = rest[i];
      if (ch === '`') { tick = !tick; continue; }
      if (tick) continue;
      if (quote) { if (ch === quote) quote = null; continue; }
      if (ch === '"' || ch === "'") { quote = ch; continue; }
      if (ch === ':' || ch === '—' || rest.slice(i, i + 4) === ' -- ') return rest.slice(0, i);
    }
    return '';
  };
  const lines = source.split('\n'), sections = [{ headings: [], blocks: [] }];
  let i = 0;
  const pushBlock = block => sections.at(-1).blocks.push(block);
  while (i < lines.length) {
    const line = lines[i];
    if (/^[ \t]*$/.test(line)) { i++; continue; }
    const fenceMatch = /^ {0,3}(`{3,}|~{3,})/.exec(line);
    if (fenceMatch) {
      const marker = fenceMatch[1], start = i++;
      while (i < lines.length && !new RegExp(`^ {0,3}${marker[0]}{${marker.length},}[ \\t]*$`).test(lines[i])) i++;
      if (i < lines.length) i++;
      pushBlock({ kind: 'fence', text: lines.slice(start, i).join('\n') });
      continue;
    }
    const headingMatch = /^ {0,3}(#{1,6})[ \t]+(.*)$/.exec(line);
    if (headingMatch) {
      const level = headingMatch[1].length, title = headingMatch[2];
      const prev = sections.at(-1).headings.filter(h => h.level < level);
      const targets = linkedIn(line) ?? matchTokens(title, tokenMap, drawings.length);
      sections.push({ headings: [...prev, { level, targets }], blocks: [{ kind: 'heading', text: line, ownTargets: targets }] });
      i++;
      continue;
    }
    const bulletMatch = /^( {0,3})(?:[-*+]|\d+[.)])[ \t]+/.exec(line);
    if (bulletMatch) {
      const baseIndent = bulletMatch[1].length, start = i++;
      while (i < lines.length) {
        const next = lines[i];
        if (/^[ \t]*$/.test(next)) {
          let peek = i + 1;
          while (peek < lines.length && /^[ \t]*$/.test(lines[peek])) peek++;
          if (peek < lines.length && !/^ {0,3}#{1,6}[ \t]+/.test(lines[peek]) && /^( *)/.exec(lines[peek])[1].length >= baseIndent + 2) {
            i = peek; continue;
          }
          break;
        }
        if (/^ {0,3}(?:`{3,}|~{3,}|#{1,6}[ \t]+)/.test(next)) break;
        const nextBullet = /^( {0,3})(?:[-*+]|\d+[.)])[ \t]+/.exec(next);
        if (nextBullet && nextBullet[1].length <= baseIndent) break;
        i++;
      }
      pushBlock({ kind: 'list', text: lines.slice(start, i).join('\n'), firstLine: line });
      continue;
    }
    const start = i++;
    while (i < lines.length && !/^[ \t]*$/.test(lines[i]) && !/^ {0,3}(?:`{3,}|~{3,}|#{1,6}[ \t]+|(?:[-*+]|\d+[.)])[ \t]+)/.test(lines[i])) i++;
    pushBlock({ kind: 'para', text: lines.slice(start, i).join('\n') });
  }
  const scoped = new Map(drawings.map(d => [d, []]));
  for (const section of sections) {
    const sectionTargets = [...section.headings].reverse().find(h => h.targets)?.targets ?? null;
    const standalone = section.blocks.map(b => b.kind === 'para' && isStandaloneImages(b.text));
    const gallery = standalone.map((isImg, idx) => isImg && (idx > 0 && standalone[idx - 1] || idx + 1 < standalone.length && standalone[idx + 1]));
    let imageScope = null;
    for (let idx = 0; idx < section.blocks.length; idx++) {
      const block = section.blocks[idx];
      if (standalone[idx]) {
        imageScope = gallery[idx] ? null : linkedIn(block.text);
        continue;
      }
      let targets = null;
      if (block.kind === 'heading') targets = block.ownTargets ?? sectionTargets;
      else if (block.kind === 'list') {
        const explicit = linkedIn(block.text) ?? matchTokens(listLead(block.firstLine), tokenMap, drawings.length);
        if (explicit) { imageScope = null; targets = explicit; }
        else targets = sectionTargets ?? imageScope;
      } else {
        targets = linkedIn(block.text) ?? sectionTargets ?? imageScope;
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
      const fence = /^ {0,3}(`{3,}|~{3,})[^\n]*\n([\s\S]*?)(?:\n {0,3}\1[~`]*[ \t]*(?=\n|$)|$)/.exec(rest);
      if (fence) { extractHtmlControls(fence[2], controls); endSentence(); pos += fence[0].length; continue; }
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
      const img = /^!\[[^\]]*\]\(\s*(?:<[^>]+>|[^\s)]+)(?:\s+(?:"[^"]*"|'[^']*'))?\s*\)/.exec(rest);
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

export function lintSvgLayouts({ root, files, promptPaths }) {
  const policy=workspace.policy({root});files=files.filter(path=>workspace.allows(policy,path));
  const warnings = [], promptRecords = [], add = (prompt, drawing, part, reason) => warnings.push({ key: `${prompt}\0${drawing}\0${part}\0${reason}`, text: `Warning: SVG layout ${prompt} -> ${drawing}: ${part}: ${reason}.` });
  for (const prompt of [...new Set(promptPaths ?? files.filter(path => path.endsWith('.prompt.md')))].sort()) {
    let source;
    try { source = markupTokens(safeRead(root, prompt)).map(token => token.startsWith('<!--') ? '\n' : token).join(''); } catch (error) { add(prompt, '(unread)', 'source', error.message); continue; }
    source = source.replace(/<details\b[^>]*>\s*<summary[^>]*>[^\n]*Runtime interface[^\n]*<\/summary>[\s\S]*?<\/details>/gi, '')
      .replace(/(^##+ Runtime interface[^\n]*\n)[\s\S]*?(?=^##+ |$(?![\s\S]))/gmi, '');
    const decodedSource = decodeHtml(source), drawings = [];
    const resolvedLinks = links(source).sort().map(link => resolveDrawing(root, prompt, link));
    for (const drawing of resolvedLinks) if (drawing && drawing !== '..' && !drawing.startsWith('../')) drawings.push(drawing);
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
    const mapPaths = new Set(files.filter(path => /(?:^|\/)app-map\.json$/.test(path)));
    for (const testFile of files.filter(path => /^(?:tests?|.*\/tests?)\/.*\.json$/.test(path))) {
      try {
        const doc = JSON.parse(safeRead(root, testFile));
        if (Array.isArray(doc?.app_maps)) for (const candidate of doc.app_maps) if (typeof candidate === 'string' && workspace.allows(policy, candidate)) mapPaths.add(candidate);
      } catch { /* non-scenario or unreadable JSON */ }
    }
    const appMaps = [], cssPaths = new Set(), inspectedPrompts = new Set(promptRecords.map(record => record.path));
    for (const mapPath of [...mapPaths].sort()) {
      try {
        const doc = JSON.parse(safeRead(root, mapPath));
        if (!doc || typeof doc !== 'object' || doc.schema_version !== 'prompt-runtime.app-map.v1' || typeof doc.name !== 'string' || !doc.name) continue;
        const topSheets = Array.isArray(doc.stylesheets) ? doc.stylesheets.filter(item => typeof item === 'string') : [];
        const screens = (Array.isArray(doc.screens) ? doc.screens : [])
          .filter(screen => screen && typeof screen === 'object' && typeof screen.id === 'string' && typeof screen.prompt_path === 'string' && typeof screen.source === 'string' && typeof screen.format === 'string')
          .map(screen => ({
            id: screen.id,
            prompt_path: screen.prompt_path,
            source: screen.source,
            format: screen.format,
            stylesheets: Array.isArray(screen.stylesheets) ? screen.stylesheets.filter(item => typeof item === 'string') : [],
          }));
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
  return [...new Map(warnings.sort((a, b) => a.key < b.key ? -1 : a.key > b.key ? 1 : 0).map(warning => [warning.text, warning.text])).values()];
}
