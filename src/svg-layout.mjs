// Generated from prompts/cli/svg-layout.prompt.md (sha256: 01d551eb64e2c94b35facda415bae17a325fa2892905790b138fceccc5114faf).
import { lstatSync, readFileSync } from 'node:fs';
import { dirname, relative, resolve, sep } from 'node:path';

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
function safeRead(root, path) {
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

// An inert XML reader: no document type, entity expansion, execution or resource loading.
function partsOf(source) {
  const active = source.replace(/<!--[\s\S]*?-->|<!\[CDATA\[[\s\S]*?\]\]>/g, '');
  if (/<!DOCTYPE|<!ENTITY|<\?(?!xml\s)|<\s*(?:script|foreignObject|iframe)\b|\son\w+\s*=/i.test(active)) throw Error('unsafe SVG content');
  const styles = [...source.matchAll(/<style\b[^>]*>([\s\S]*?)<\/style>/g)].flatMap(match => [...match[1].replace(/\/\*[\s\S]*?\*\//g, '').matchAll(/([^{}]+)\{([^{}]*)\}/g)].flatMap(rule => rule[1].split(',').map(selector => ({ selector: selector.trim(), style: rule[2] }))));
  if (styles.some(rule => !/^(?:[\w-]+|[.#][\w-]+)$/.test(rule.selector))) throw Error('unsupported SVG stylesheet selector in static lint');
  for (const match of source.matchAll(/<style\b[^>]*>([\s\S]*?)<\/style>/g)) if (/@import|url\s*\(/i.test(match[1].replace(/url\(\s*(['"]?)#[^)'"\s]+\1\s*\)/gi, ''))) throw Error('external SVG stylesheet resources are not allowed');
  const stack = [], parts = [], tokens = source.match(/<!--[\s\S]*?-->|<\?[\s\S]*?\?>|<!\[CDATA\[[\s\S]*?\]\]>|<[^>]*>|[^<]+/g) || [];
  let roots = 0;
  for (const token of tokens) {
    if (token.startsWith('<!--') || token.startsWith('<?')) continue;
    if (token.startsWith('</')) {
      const close = /^<\/([\w:-]+)\s*>$/.exec(token);
      if (!close || stack.pop()?.tag !== close[1]) throw Error('malformed XML closing tag');
    } else if (token.startsWith('<') && !token.startsWith('<![CDATA[')) {
      const match = /^<([\w:-]+)((?:\s+[\s\S]*?)?)\s*(\/?)>$/.exec(token);
      if (!match) throw Error('malformed XML element');
      const [, tag, raw, self] = match, attrs = {};
      let remainder = raw.trim();
      while (remainder) {
        const attr = /^([\w:-]+)\s*=\s*("[^"]*"|'[^']*')\s*/.exec(remainder);
        if (!attr || attr[1] in attrs) throw Error('malformed XML attributes');
        attrs[attr[1]] = decode(attr[2].slice(1, -1)); remainder = remainder.slice(attr[0].length);
      }
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
      for (const node of stack) if (node.tag === 'text' && !node.hidden) node.text += text;
    }
  }
  if (stack.length || roots !== 1 || tokens.join('') !== source) throw Error('malformed SVG');
  return parts.map(part => ({ kind: part.kind, value: part.node ? part.node.text.replace(/\s+/g, ' ').trim() : part.value })).filter(part => part.value);
}
function links(text) {
  const refs = new Map([...text.matchAll(/^\s*\[([^\]]+)\]:\s*<?([^\s>]+)>?/gm)].map(m => [normalize(m[1]), m[2]]));
  return [...new Set([
    ...[...text.matchAll(/!?\[[^\]]*\]\(\s*(?:<([^>]+)>|([^\s)]+))(?:\s+["'][^)]*)?\)/g)].map(m => m[1] || m[2]),
    ...[...text.matchAll(/!?\[([^\]]+)\]\[([^\]]*)\]/g)].map(m => refs.get(normalize(m[2] || m[1]))),
    ...[...text.matchAll(/!?\[([^\]]+)\](?![\[(:])/g)].map(m => refs.get(normalize(m[1]))),
  ].filter(value => value && !/^(?:[a-z][a-z\d+.-]*:|\/\/|#)/i.test(value) && /\.ui\.svg(?:#.*)?$/i.test(value)).map(value => value.split('#')[0]))];
}
const mentioned = (prose, value) => new RegExp(`(^|[^\\p{L}\\p{N}_])${escaped(normalize(value))}($|[^\\p{L}\\p{N}_])`, 'u').test(normalize(prose));

export function lintSvgLayouts({ root, files, promptPaths }) {
  const warnings = [], add = (prompt, drawing, part, reason) => warnings.push({ key: `${prompt}\0${drawing}\0${part}\0${reason}`, text: `Warning: SVG layout ${prompt} -> ${drawing}: ${part}: ${reason}.` });
  for (const prompt of [...new Set(promptPaths ?? files.filter(path => path.endsWith('.prompt.md')))].sort()) {
    let source;
    try { source = safeRead(root, prompt); } catch (error) { add(prompt, '(unread)', 'source', error.message); continue; }
    source = source.replace(/<!--[\s\S]*?-->/g, '').replace(/<details\b[^>]*>\s*<summary[^>]*>[^\n]*Runtime interface[^\n]*<\/summary>[\s\S]*?<\/details>/gi, '')
      .replace(/(^##+ Runtime interface[^\n]*\n)[\s\S]*?(?=^##+ |$(?![\s\S]))/gmi, '');
    for (const link of links(source).sort()) {
      let drawing;
      try { drawing = relative(root, resolve(root, dirname(prompt), decodeURIComponent(link))).split(sep).join('/'); } catch { drawing = link; }
      let parts;
      try { parts = partsOf(safeRead(root, drawing)); } catch (error) { add(prompt, drawing, 'drawing', error.message); continue; }
      const appearance = source.match(/^##+ Appearance\b[^\n]*\n([\s\S]*?)(?=^##? |$(?![\s\S]))/m)?.[1] || '';
      for (const { kind, value } of parts) {
        if (kind === 'text' && !/^[\d\s.,+%-]+$/.test(value) && !mentioned(source, value)) add(prompt, drawing, `label "${value}"`, 'drawing label absent from prompt');
        if (kind === 'id') {
          const name = escaped(value), words = escaped(value.replace(/[-_]/g, ' '));
          const declaration = new RegExp(`(?:\\b(?:region|id|part|container|bar|box)\\s*(?:=|:)?\\s*["'\x60]?${name}(?![\\w-])|(?<![\\w-])${name}["'\x60]?\\s+(?:region|box|bar|container|button|grid|heading|label)|(?<![\\w-])${words}\\s+(?:region|box|bar|container|button|grid|heading|label))`, 'i');
          if (!declaration.test(source) && !appearance.includes(`\`${value}\``)) add(prompt, drawing, `region #${value}`, 'drawing region layout unspecified in prompt');
        }
      }
      const controls = new Set();
      // A data/root id is not itself a control declaration. Keep the control's
      // whole sentence so wrapped Markdown does not lose its named ids.
      for (const sentence of source.split(/(?<=[.!?])\s+|\n\s*\n/).filter(text => /\b(?:buttons?|controls?)\b/i.test(text))) {
        for (const id of sentence.matchAll(/\b(?:id|ids|value|values)\s*(?:=|:)?\s*["'`]+([\w-]+)["'`]+/gi)) controls.add(id[1]);
        for (const id of sentence.matchAll(/`([\w]+-[\w-]+)`/g)) controls.add(id[1]);
        for (const label of sentence.matchAll(/["“]([^"”]+)["”]/g)) controls.add(label[1]);
      }
      if (/\b(?:(?:four|4)\s+)?(?:touch-sized\s+)?direction(?:al)?\s+(?:buttons|controls)\b/i.test(source)) {
        for (const direction of ['left', 'right', 'up', 'down']) if (!parts.some(part => mentioned(part.value.replace(/[-_]/g, ' '), direction))) controls.add(`move-${direction}`);
      }
      for (const control of controls) if (!parts.some(part => normalize(part.value) === normalize(control))) add(prompt, drawing, `control "${control}"`, 'prompt control absent from drawing');
    }
  }
  return [...new Map(warnings.sort((a, b) => a.key < b.key ? -1 : a.key > b.key ? 1 : 0).map(warning => [warning.text, warning.text])).values()];
}
