// Generated from prompts/cli/runtime-markdown.prompt.md (sha256: 49f404e3b5ad6e61ca380f4ec5b73a8c86b95a3acc51b1b1c9bb2984ed4f50fe).
export function markdownDefinitions(text) {
  const definitions = new Map();
  for (const match of text.matchAll(/^ {0,3}\[([^\]\n]+)\]:[ \t]*(?:<([^>\n]+)>|(\S+))/gm)) {
    const id = match[1].trim().replace(/\s+/g, ' ').toLowerCase();
    if (!definitions.has(id)) definitions.set(id, match[2] ?? match[3]);
  }
  return definitions;
}

function markdownEscaped(text, index) {
  let start = index;
  while (start > 0 && text[start - 1] === '\\') start--;
  return (index - start) % 2 === 1;
}

// Return local destinations without treating link labels or reference definitions as file paths.
export function markdownLinks(text, definitions, imagesOnly = false) {
  const paths = [];
  const inline = /(!?)\[[^\]\n]*\]\([ \t]*/g;
  for (let match; (match = inline.exec(text));) {
    if (markdownEscaped(text, match.index + match[1].length)) {
      inline.lastIndex = match.index + match[1].length + 1;
      continue;
    }
    if (imagesOnly && (!match[1] || markdownEscaped(text, match.index))) continue;
    let index = match.index + match[0].length, path = '', depth = 0;
    if (text[index] === '<') {
      const end = text.indexOf('>', index + 1);
      if (end >= 0) paths.push(text.slice(index + 1, end));
      continue;
    }
    for (; index < text.length; index++) {
      const char = text[index];
      if (char === '\\' && index + 1 < text.length) { path += text[++index]; continue; }
      if (/\s/.test(char) || (char === ')' && depth === 0)) break;
      if (char === '(') depth++;
      if (char === ')') depth--;
      path += char;
    }
    if (path) paths.push(path);
  }
  const reference = /(!?)\[([^\]\n]+)\](?:\[([^\]\n]*)\])?/g;
  for (let match; (match = reference.exec(text));) {
    if (markdownEscaped(text, match.index + match[1].length)) {
      reference.lastIndex = match.index + match[1].length + 1;
      continue;
    }
    if (imagesOnly && (!match[1] || markdownEscaped(text, match.index))) continue;
    const following = text[match.index + match[0].length];
    if (following === '(' || following === ':') continue;
    const target = definitions.get((match[3] || match[2]).trim().replace(/\s+/g, ' ').toLowerCase());
    if (target) paths.push(target);
  }
  return paths;
}

// Consume existing block containers, without treating fence content as new markup.
// A quote needs its marker on every code line; a list needs its content indent.
function markdownContainerLine(line, containers) {
  let matched = 0;
  for (const indent of containers) {
    if (indent === '>') {
      const quote = /^ {0,3}> ?/.exec(line);
      if (!quote) break;
      line = line.slice(quote[0].length);
    } else {
      const spaces = /^ */.exec(line)[0].length;
      if (line.trim() && spaces < indent) break;
      line = line.slice(Math.min(spaces, indent));
    }
    matched++;
  }
  return { line, matched };
}

// Discovery sees prose only; preserve offsets and newlines without changing captured bytes.
export function markdownSectionText(text) {
  const parts = [], inline = /`+|<!--|</g;
  const opaque = /<(?:[A-Za-z][A-Za-z0-9-]*(?:[ \t\r\n]+[A-Za-z_:][A-Za-z0-9_.:-]*(?:[ \t\r\n]*=[ \t\r\n]*(?:"[^"]*"|'[^']*'|[^\s"'=<>`]+))?)*[ \t\r\n]*\/?|\/[A-Za-z][A-Za-z0-9-]*[ \t\r\n]*|[A-Za-z][A-Za-z0-9+.-]{1,31}:[^\x00-\x20<>]*|[A-Za-z0-9.!#$%&'*+/=?^_`{|}~-]+@[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?(?:\.[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?)*)>/y;
  let containers = [], fence = null, comment = false, indented = false, copied = 0, paragraph = false;
  let scopeStart = null, scopeEnd = 0;
  const mask = (start, end) => {
    parts.push(text.slice(copied, start), text.slice(start, end).replace(/[^\r\n]/g, ' '));
    copied = end;
  };
  // Inline parsing belongs to one leaf block. A matching run in a later
  // paragraph, heading or container cannot turn intervening prose into code.
  const flush = () => {
    if (scopeStart === null) return;
    inline.lastIndex = scopeStart;
    for (let match; (match = inline.exec(text)) && match.index < scopeEnd;) {
      let tokenStart = match.index, token = match[0], slashes = 0;
      for (let index = tokenStart - 1; index >= scopeStart && text[index] === '\\'; index--) slashes++;
      if (slashes % 2) {
        if (token === '<!--' || token.length === 1) continue;
        // An escape consumes one punctuation character, not the entire run.
        tokenStart++; token = token.slice(1);
      }
      if (token === '<') {
        // Valid tags/autolinks consume their own backticks before code-opener
        // lexing. Leave their bytes available to the existing capture policy.
        opaque.lastIndex = tokenStart;
        if (opaque.test(text) && opaque.lastIndex <= scopeEnd) inline.lastIndex = opaque.lastIndex;
        continue;
      }
      let closeEnd;
      if (token === '<!--') {
        const close = text.indexOf('-->', inline.lastIndex);
        if (close < 0 || close + 3 > scopeEnd) continue;
        closeEnd = close + 3;
      } else {
        const closing = new RegExp('(?<!`)`{' + token.length + '}(?!`)', 'g');
        closing.lastIndex = inline.lastIndex;
        const close = closing.exec(text);
        if (!close || close.index + close[0].length > scopeEnd) continue;
        // Backslashes have no escape meaning inside an actual code span.
        closeEnd = close.index + close[0].length;
      }
      mask(tokenStart, closeEnd);
      inline.lastIndex = closeEnd;
    }
    scopeStart = null;
  };
  for (const row of text.matchAll(/[^\r\n]*(?:\r\n|[\r\n]|$)/g)) {
    if (!row[0]) continue;
    const original = row[0].replace(/[\r\n]+$/, '');
    const start = row.index, end = start + original.length;
    {
      // Tabs affect Markdown indentation only. This view is never captured.
      let column = 0;
      const expanded = original.replace(/[^\t]|\t/g, char => {
        const width = char === '\t' ? 4 - column % 4 : 1;
        column += width;
        return char === '\t' ? ' '.repeat(width) : char;
      });
      let { line, matched } = markdownContainerLine(expanded, containers);
      const thematic = /^ {0,3}(?:(?:\* *){3,}|(?:- *){3,}|(?:_ *){3,})$/;
      const item = /^ {0,3}([-+*]|[0-9]{1,9}[.)]) +(\S.*)$/.exec(line);
      const fenceStart = /^ {0,3}(`{3,}|~{3,})(.*)$/.exec(line);
      const validFence = fenceStart && !(fenceStart[1][0] === '`' && fenceStart[2].includes('`'));
      // Only HTML block types that can interrupt a paragraph split its inline
      // scope; ordinary angle prose and custom inline tags do not.
      const htmlStart = /^ {0,3}<(?:!--|\?|![A-Z]|!\[CDATA\[|(?:pre|script|style|textarea)(?=[\t >]|$))/i.test(line)
        || /^ {0,3}<\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?=[\t >]|\/>|$)/i.test(line);
      const startsBlock = /^ {0,3}(?:>|#{1,6}(?: |$))/.test(line) || validFence || htmlStart || thematic.test(line)
        || (item && (!paragraph || !/^[0-9]/.test(item[1]) || /^1[.)]$/.test(item[1])
          || (matched < containers.length && containers[matched] !== '>')));
      // Lazy paragraph continuation keeps its parent containers available for a
      // later indented fence. Code itself never permits lazy continuation.
      const lazy = matched < containers.length && !fence && !comment && !indented && paragraph && line.trim() && !startsBlock;
      const boundary = !line.trim() || startsBlock || /^ {0,3}(?:=+|-+) *$/.test(line)
        || (!lazy && matched < containers.length);
      if (boundary) flush();
      if (!lazy && matched < containers.length) { fence = null; comment = false; indented = false; paragraph = false; }
      if (!lazy) containers = containers.slice(0, matched);
      if (fence) {
        mask(start, end);
        const close = /^ {0,3}(`{3,}|~{3,}) *$/.exec(line);
        if (close && close[1][0] === fence[0] && close[1].length >= fence.length) fence = null;
        continue;
      }
      if (comment) {
        const close = original.indexOf('-->');
        mask(start, close < 0 ? end : start + close + 3);
        if (close < 0) continue;
        comment = false;
        scopeStart = start + close + 3; scopeEnd = end;
        flush();
        continue;
      }
      // Code starts only at a leaf boundary. Its indentation belongs to the
      // existing container; markup inside it cannot open another container.
      if ((indented && !line.trim()) || (!paragraph && /^ {4}/.test(line))) {
        indented = true; mask(start, end); continue;
      }
      indented = false;
      // Start containers only outside code; a list's continuation width belongs
      // to its item, so a sibling marker or dedent ends an unclosed example.
      for (; !lazy;) {
        const quote = /^ {0,3}> ?/.exec(line);
        if (quote) { containers.push('>'); line = line.slice(quote[0].length); paragraph = false; continue; }
        const list = /^( {0,3})([-+*]|[0-9]{1,9}[.)])( +|$)/.exec(line);
        if (!list || thematic.test(line)) break;
        const rest = line.slice(list[0].length);
        if (paragraph && (!rest.trim() || (/^[0-9]/.test(list[2]) && !/^1[.)]$/.test(list[2])))) break;
        const padding = rest.trim() && list[3].length <= 4 ? list[3].length : 1;
        const indent = list[1].length + list[2].length + padding;
        containers.push(indent); line = line.slice(indent); paragraph = false;
      }
      if (!paragraph && /^ {4}/.test(line)) {
        indented = true; mask(start, end); continue;
      }
      const opening = /^ {0,3}(`{3,}|~{3,})(.*)$/.exec(line);
      if (!lazy && opening && !(opening[1][0] === '`' && opening[2].includes('`'))) {
        fence = opening[1]; paragraph = false; mask(start, end); continue;
      }
      if (/^ {0,3}<!--/.test(line)) {
        const opening = original.indexOf('<!--'), close = original.indexOf('-->', opening + 4);
        mask(start + opening, close < 0 ? end : start + close + 3);
        comment = close < 0; paragraph = false;
        if (!comment) { scopeStart = start + close + 3; scopeEnd = end; flush(); }
        continue;
      }
      const definition = !paragraph && /^ {0,3}\[[^\]]+\]:/.test(line);
      paragraph = Boolean(line.trim()) && !thematic.test(line) && !definition && !htmlStart
        && !/^ {0,3}(?:#{1,6}(?: |$)|=+ *$)/.test(line);
    }
    if (scopeStart === null) scopeStart = start;
    scopeEnd = end;
    if (!paragraph) flush();
  }
  flush();
  return parts.join('') + text.slice(copied);
}
