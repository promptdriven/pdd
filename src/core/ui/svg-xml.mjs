// Generated from prompts/cli/svg-layout.prompt.md.
// Inert XML reader and workspace-guarded file read for .ui.svg layout lint.
import { lstatSync, readFileSync } from 'node:fs';
import { relative, resolve, sep } from 'node:path';
import { runtimeWorkspaceSlice, workspace } from '../../shared/workspace-policy.mjs';

const { requireRuntimePath } = runtimeWorkspaceSlice();

export function decodeXml(text) {
  if (/&(?!(?:amp|lt|gt|quot|apos|#\d+|#x[\da-f]+);)/i.test(text)) throw Error('invalid XML entity');
  return text.replace(/&([^;\s]+);/g, (_, value) => {
    const named = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'" };
    if (value in named) return named[value];
    const number = /^#x[\da-f]+$/i.test(value) ? parseInt(value.slice(2), 16) : /^#\d+$/.test(value) ? Number(value.slice(1)) : NaN;
    if (!Number.isInteger(number) || number <= 0 || number > 0x10ffff || (number >= 0xd800 && number <= 0xdfff)) throw Error('invalid XML entity');
    return String.fromCodePoint(number);
  });
}

export function safeRead(root, path, policy = null) {
  requireRuntimePath(policy ?? workspace.policy({ root }), { path, from: 'SVG advice' });
  const full = resolve(root, path);
  const rel = relative(resolve(root), full);
  if (!rel || rel === '..' || rel.startsWith(`..${sep}`) || resolve(root, rel) !== full) throw Error('path escapes repository');
  const parts = rel.split(sep);
  for (let i = 1; i <= parts.length; i++) {
    const stat = lstatSync(resolve(root, ...parts.slice(0, i)));
    if (stat.isSymbolicLink()) throw Error('symlink paths are not allowed');
    if (i === parts.length && !stat.isFile()) throw Error('not a regular file');
  }
  return readFileSync(full, 'utf8');
}

export function markupTokens(source) {
  const tokens = source.match(/<!--[\s\S]*?(?:-->|$)|<!\[CDATA\[[\s\S]*?\]\]>|<[^>]*>|[^<]+|</g) || [];
  for (const token of tokens) {
    if (token.startsWith('<!--') && (!token.endsWith('-->') || token.slice(4, -3).includes('--') || token.slice(4, -3).endsWith('-'))) {
      throw Error('malformed or nested markup comment');
    }
  }
  return tokens;
}

// An inert XML reader: no document type, entity expansion, execution or resource loading.
export function partsOf(source) {
  const tokens = markupTokens(source);
  const active = tokens.filter(token => !token.startsWith('<!--') && !token.startsWith('<![CDATA[')).join('\n');
  const styles = [...active.matchAll(/<style\b[^>]*>([\s\S]*?)<\/style>/g)].flatMap(match =>
    [...match[1].replace(/\/\*[\s\S]*?\*\//g, '').matchAll(/([^{}]+)\{([^{}]*)\}/g)].flatMap(rule =>
      rule[1].split(',').map(selector => ({ selector: selector.trim(), style: rule[2] })),
    ),
  );
  if (styles.some(rule => !/^(?:[\w-]+|[.#][\w-]+)$/.test(rule.selector))) throw Error('unsupported SVG stylesheet selector in static lint');
  for (const match of active.matchAll(/<style\b[^>]*>([\s\S]*?)<\/style>/g)) {
    if (/@import|url\s*\(/i.test(match[1].replace(/url\(\s*(['"]?)#[^)'"\s]+\1\s*\)/gi, ''))) throw Error('external SVG stylesheet resources are not allowed');
  }
  const stack = [];
  const parts = [];
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
      const [, tag, raw, self] = match;
      const attrs = {};
      if (['script', 'foreignobject', 'iframe', 'object', 'embed'].includes(tag.split(':').at(-1).toLowerCase())) throw Error('unsafe SVG content');
      let remainder = raw.trim();
      while (remainder) {
        const attr = /^([\w:-]+)\s*=\s*("[^"]*"|'[^']*')\s*/.exec(remainder);
        if (!attr || attr[1] in attrs) throw Error('malformed XML attributes');
        attrs[attr[1]] = decodeXml(attr[2].slice(1, -1));
        remainder = remainder.slice(attr[0].length);
      }
      if (Object.keys(attrs).some(name => /^on/i.test(name))) throw Error('unsafe SVG content');
      if (!stack.length && (tag !== 'svg' || roots++)) throw Error('expected one SVG root');
      const resourceValues = Object.values(attrs).join(' ').replace(/url\(\s*(['"]?)#[^)'"\s]+\1\s*\)/gi, '');
      if (Object.entries(attrs).some(([name, value]) => /^(?:href|xlink:href|src)$/i.test(name) && !value.startsWith('#')) || /(?:@import|url\s*\()/i.test(resourceValues)) {
        throw Error('external SVG resources are not allowed');
      }
      const simpleMatch = selector => selector === tag || selector === `#${attrs.id}` || (selector.startsWith('.') && (attrs.class || '').split(/\s+/).includes(selector.slice(1)));
      const declarations = new Map(['display', 'visibility', 'opacity'].filter(name => attrs[name] !== undefined).map(name => [name, { value: attrs[name], important: false }]));
      const specificity = rule => (rule.selector.startsWith('#') ? 100 : rule.selector.startsWith('.') ? 10 : 1);
      for (const style of [...styles.filter(rule => simpleMatch(rule.selector)).sort((a, b) => specificity(a) - specificity(b)).map(rule => rule.style), attrs.style || '']) {
        for (const entry of style.split(';')) {
          const decl = /^\s*([\w-]+)\s*:\s*(.*?)\s*(!important)?\s*$/i.exec(entry);
          if (!decl) continue;
          const [, name, value, important] = decl;
          const previous = declarations.get(name.toLowerCase());
          if (!previous?.important || important) declarations.set(name.toLowerCase(), { value: value.toLowerCase().trim(), important: !!important });
        }
      }
      const css = Object.fromEntries([...declarations].map(([key, declaration]) => [key, declaration.value]));
      const hidden = stack.at(-1)?.hidden || ['title', 'desc', 'defs', 'metadata', 'style'].includes(tag) || attrs['data-context-only'] === 'true'
        || (attrs.class || '').split(/\s+/).includes('context-only') || css.display === 'none' || ['hidden', 'collapse'].includes(css.visibility)
        || (css.opacity !== undefined && Number(css.opacity) === 0);
      const node = { tag, hidden, text: '', id: attrs.id };
      if (!hidden && attrs.id) parts.push({ kind: 'id', value: attrs.id });
      if (!hidden && tag === 'text') parts.push({ kind: 'text', node });
      if (!self) stack.push(node);
    } else {
      const text = token.startsWith('<![CDATA[') ? token.slice(9, -3) : decodeXml(token);
      if (!stack.length && text.trim()) throw Error('text outside SVG root');
      if (!stack.at(-1)?.hidden) for (const node of stack) if (node.tag === 'text' && !node.hidden) node.text += text;
    }
  }
  if (stack.length || roots !== 1 || tokens.join('') !== source) throw Error('malformed SVG');
  return parts.map(part => ({ kind: part.kind, value: part.node ? part.node.text.replace(/\s+/g, ' ').trim() : part.value })).filter(part => part.value);
}
