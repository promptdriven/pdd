// Generated from prompts/cli/svg-layout.prompt.md.
// HTML and prose control-declaration extraction for .ui.svg layout lint.

export const normalize = text => text.replace(/\s+/g, ' ').trim().toLowerCase();
export const escaped = text => text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
export const mentionedNormalized = (normalizedProse, value) =>
  new RegExp(`(^|[^\\p{L}\\p{N}_])${escaped(normalize(value))}($|[^\\p{L}\\p{N}_])`, 'u').test(normalizedProse);
export const mentioned = (prose, value) => mentionedNormalized(normalize(prose), value);

export function decodeHtml(text) {
  return text.replace(/&(#x[\da-f]+|#\d+|amp|lt|gt|quot|apos|nbsp);/gi, (raw, entity) => {
    const named = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'", nbsp: ' ' };
    const lower = entity.toLowerCase();
    if (lower in named) return named[lower];
    const code = lower.startsWith('#x') ? parseInt(lower.slice(2), 16) : Number(lower.slice(1));
    return Number.isInteger(code) && code > 0 && code <= 0x10ffff && (code < 0xd800 || code > 0xdfff)
      ? String.fromCodePoint(code)
      : raw;
  });
}

const VOID_HTML = new Set(['area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'param', 'source', 'track', 'wbr']);
const BLOCK_HTML = new Set(['address', 'article', 'aside', 'blockquote', 'br', 'dd', 'details', 'dialog', 'div', 'dl', 'dt', 'fieldset', 'figcaption', 'figure', 'footer', 'form', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'header', 'hgroup', 'hr', 'li', 'main', 'nav', 'ol', 'p', 'pre', 'section', 'summary', 'table', 'tbody', 'td', 'tfoot', 'th', 'thead', 'tr', 'ul']);
const CONTROL_ATTRS = new Set(['id', 'ids', 'name', 'names', 'value', 'values']);
const NON_CONTROL_NAMES = /^(?:aria-[\w-]+|data-[\w-]+|class|role|style|type|placeholder|title|href|src|for|action|method|tabindex|disabled|readonly|required|checked|selected|hidden|multiple|autofocus)$/i;

function parseHtmlTag(token) {
  const head = /^<(\/?)([a-zA-Z][\w:-]*)(?=\s|\/?>)((?:"[^"]*"|'[^']*'|[^"'>])*)>$/.exec(token);
  if (!head) return null;
  const closing = head[1] === '/';
  const tag = head[2].toLowerCase();
  if (closing) return { closing: true, tag, selfClosing: false, attrs: {} };
  let rest = head[3];
  let selfClosing = VOID_HTML.has(tag);
  const attrs = {};
  while (rest) {
    rest = rest.replace(/^\s+/, '');
    if (!rest) break;
    if (rest === '/') { selfClosing = true; break; }
    const attr = /^([a-zA-Z_:][\w:.-]*)(?:\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s"'=<>`/]+(?:\/(?!\s*$)[^\s"'=<>`/]*)*)))?/.exec(rest);
    if (!attr) { rest = rest.slice(1); continue; }
    const name = attr[1].toLowerCase();
    const raw = attr[2] ?? attr[3] ?? attr[4];
    if (!(name in attrs)) attrs[name] = raw === undefined ? '' : decodeHtml(raw).replace(/\s+/g, ' ').trim();
    rest = rest.slice(attr[0].length);
  }
  return { closing: false, tag, selfClosing, attrs };
}

function extractHtmlControls(fragment, controls) {
  const add = value => { const trimmed = value?.replace(/\s+/g, ' ').trim(); if (trimmed) controls.add(trimmed); };
  const tagRe = /<\/?[a-zA-Z][\w:-]*(?=\s|\/?>)(?:"[^"]*"|'[^']*'|[^"'>])*>/g;
  let last = 0;
  let button = null;
  for (const match of fragment.matchAll(tagRe)) {
    if (button && button.hiddenDepth === 0) button.text += decodeHtml(fragment.slice(last, match.index));
    last = match.index + match[0].length;
    const parsed = parseHtmlTag(match[0]);
    if (!parsed) continue;
    const { closing, tag, selfClosing, attrs } = parsed;
    if (closing) {
      if (tag === 'button' && button) { add(button.text); button = null; }
      else if (button && button.hiddenStack.at(-1) === tag) {
        button.hiddenStack.pop();
        button.hiddenDepth = button.hiddenStack.length;
      }
      continue;
    }
    if (button) {
      if (tag === 'button') button = null;
      else if (tag === 'br' && button.hiddenDepth === 0) button.text += ' ';
      else if (!selfClosing && (['script', 'style', 'template'].includes(tag) || 'hidden' in attrs || /(?:^|;)\s*(?:display\s*:\s*none|visibility\s*:\s*(?:hidden|collapse))\b/i.test(attrs.style || ''))) {
        button.hiddenStack.push(tag);
        button.hiddenDepth = button.hiddenStack.length;
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
  let start = 0;
  let depth = 0;
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
      const before = sentence.slice(start, i);
      const after = sentence.slice(i + 1);
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

export function extractControls(source, parts) {
  const controls = new Set();
  const add = value => { const trimmed = value?.replace(/\s+/g, ' ').trim(); if (trimmed) controls.add(trimmed); };
  let S = '\x02';
  while (source.includes(S)) S += '\x02';
  const escS = escaped(S);
  const items = [];
  const sentences = [''];
  const put = (kind, value) => { const idx = items.length; items.push(value); return `${S}${kind}${idx}${S}`; };
  const push = text => { sentences[sentences.length - 1] += text; };
  const endSentence = () => { if (sentences.at(-1).trim()) sentences.push(''); };
  let pos = 0;
  let inHeading = false;

  while (pos < source.length) {
    const ch = source[pos];
    const lineStart = pos === 0 || source[pos - 1] === '\n';
    if (!lineStart && ch !== '`' && ch !== '!' && ch !== '<' && ch !== '"' && ch !== '“' && ch !== "'" && ch !== '|' && ch !== '\n' && ch !== '.' && ch !== '?') {
      if (/[a-zA-Z_:]/.test(ch) && (pos === 0 || !/[\p{L}\p{N}_-]/u.test(source[pos - 1]))) {
        let j = pos + 1;
        while (j < source.length && /[a-zA-Z0-9_:.-]/.test(source[j])) j++;
        let k = j;
        while (k < source.length && (source[k] === ' ' || source[k] === '\t')) k++;
        if (source[k] !== '=' && source[k] !== ':') {
          push(source.slice(pos, j));
          pos = j;
          continue;
        }
      } else {
        push(ch);
        pos++;
        continue;
      }
    }
    const rest = source.slice(pos);
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
      const ticks = /^`+/.exec(rest)[0];
      const body = rest.slice(ticks.length);
      const close = new RegExp(`(?<!\`)${ticks}(?!\`)`).exec(body);
      if (close && !/\n[ \t]*\n/.test(body.slice(0, close.index))) {
        const inner = body.slice(0, close.index);
        if (/<\/?[a-zA-Z][\w:-]*(?=\s|\/?>)/.test(inner)) {
          extractHtmlControls(inner, controls); push(` ${S}H0${S} `);
        } else if (/=/.test(inner) && /^(?:[a-zA-Z_:][\w:.-]*(?:\s*=\s*(?:"[^"]*"|'[^']*'|[^\s"'=<>`]+))?\s*)+$/.test(inner.trim())) {
          for (const attrMatch of inner.trim().matchAll(/([a-zA-Z_:][\w:.-]*)(?:\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s"'=<>`]+)))?/g)) {
            const attr = attrMatch[1].toLowerCase();
            const val = (attrMatch[2] ?? attrMatch[3] ?? attrMatch[4] ?? '').replace(/\s+/g, ' ').trim();
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
        const attr = eqAttr[1].toLowerCase();
        const val = (eqAttr[2] ?? eqAttr[3] ?? eqAttr[4] ?? eqAttr[5] ?? '').replace(/\s+/g, ' ').trim();
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
      const rawInner = quote[1].replace(/\s*\n\s*/g, ' ');
      const val = rawInner.replace(/\s+/g, ' ').trim();
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
        for (const direction of ['left', 'right', 'up', 'down']) {
          if (!parts.some(part => mentioned(part.value.replace(/[-_]/g, ' '), direction))) controls.add(`move-${direction}`);
        }
      }
    }
  }
  return controls;
}
