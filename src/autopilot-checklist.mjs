// Generated from prompts/cli/autopilot-checklist.prompt.md (sha256: 84456317b86350f21adf5a0d30c0e6470b5cdf542f652fe7d1641108b1764150).

const MAX_ITEMS = 30, MAX_CHARS = 300, MAX_QUOTE = 200, MAX_HEADING = 120, PREFIX_WORDS = 8, MIN_QUOTE_WORDS = 3;
const WORD = /[\p{L}\p{N}]+/gu, HAS_WORD = /[\p{L}\p{N}]/u;
const LABEL = /^(?:done(?:\s+|-)when|expected|acceptance criteri(?:a|on)|test(?:s|ing)?|wanted|proposed outcomes?)(?![\p{L}\p{N}])/iu;
// Context words (the release lead's list): their lists and tables describe the issue and give no summary item.
const CONTEXT = /^(?:problem|evidence|background|context|notes|related|references|sources|what\s+happens)(?![\p{L}\p{N}])/iu;
// A colon after the label, with at most 3 more words before it ("Expected result:").
const LABEL_COLON = /^((?:[\s*_`]*[\p{L}\p{N}][\p{L}\p{N}'’-]*){0,3})[\s*_`]*:(.*)$/u;
const ATX = /^ {0,3}(#{1,6})(?=[ \t]|$)/;
const SETEXT = /^ {0,3}(=+|-+)[ \t]*$/;
const THEMATIC = /^ {0,3}([-*_])(?:[ \t]*\1){2,}[ \t]*$/;
const HTML_LINE = /^ {0,3}<\/?[A-Za-z][\w-]*(?:[\s>/]|$)/;
const QUOTED = /^ {0,3}>/;
const LIST = /^( *)(?:[-*+]|\d{1,9}[.)])(?:[ \t]+(.*))?$/;
const PR_LIST = /^( *)(?:[-*+]|\d{1,9}[.):])(?:[ \t]+(.*))?$/;
const TASK = /^\[[ xX]\][ \t]+(.*)$/;
const PIPE = /(?<!\\)\|/;
const START = /^(?:issue\s+)?checklist\s*(?::.*)?$/i;
const ID = /^[\s*_[(`]*C(\d{1,3})(?![\p{L}\p{N}])[*_\])`]*/iu;
// A range of ids after an id: C1-C3, C1–C3, C1..C3, C1 to C3.
const ID_RANGE = /^\s*(?:-|–|—|\.\.|to(?![\p{L}\p{N}]))\s*[*_[(`]*C(\d{1,3})(?![\p{L}\p{N}])[*_\])`]*/iu;
const ID_SEP = /^\s*(?:[,/&+]\s*)?(?:and(?![\p{L}\p{N}])\s*)?/iu;
const ID_LINE = /^[\s*_[(`]*C\d{1,3}(?![\p{L}\p{N}])/iu;
const EXCLUSION = /^(?:exclu\p{L}*|out\s+of\s+scope|not\s+in\s+scope)(?![\p{L}\p{N}])/iu;
const NOT_DONE = /^(?:no|not|none|nothing|never|n\/a|na|without|cannot|can[’']t|won[’']t|pending|todo|to\s+do|tbd|tbc|wip|later|deferred|defer|postponed|will|follow(?:-|\s+)?up|skipped|skip|missing|planned|blocked|waiting)(?![\p{L}\p{N}])/iu;
// An item whose own text marks it as optional may be excluded with a quote of its own text (RUNBOOK §15).
const OPTIONAL = /(?<![\p{L}\p{N}])(?:optional|optionally|if\s+possible|nice\s+to\s+have)(?![\p{L}\p{N}])/iu;
const BARE = /^(?:done|yes|ok|okay|complete|completed|covered|fixed|implemented|verified|finished|tested)[^\p{L}\p{N}]*$/iu;
const RANK = { missing: 1, unsupported: 2, excluded: 3, covered: 4 };

const str = value => typeof value === 'string' ? value : '';
const lines = text => text.split(/\r\n|\r|\n/).map(line => line.replace(/\t/g, '    '));
const indentOf = line => line.length - line.trimStart().length;
const words = text => [...text.matchAll(WORD)];
const lowerWords = text => words(text).map(match => match[0].toLowerCase());
const quoteForm = text => text.normalize('NFC').replace(/[“”]/g, '"').replace(/[‘’]/g, "'").replace(/[`*_]/g, '').replace(/\s+/g, ' ').trim();
// Every cut keeps whole code points and ends with "…".
const clip = (text, size) => { const chars = [...text]; return chars.length <= size ? text : `${chars.slice(0, size - 1).join('').trimEnd()}…`; };
// The same form decides the dedup: emphasis marks, white space and case go; every other character stays.
const wordChar = char => /[\p{L}\p{N}]/u.test(char);
const unmark = text => text.replace(/\*+|_+|~{2,}/g, (run, at) => {
  const before = text[at - 1] ?? '', after = text[at + run.length] ?? '';
  const opens = !wordChar(before) && after !== '' && !/\s/.test(after), closes = !wordChar(after) && before !== '' && !/\s/.test(before);
  return opens || closes ? '' : run;
});
const sameForm = text => unmark(text).replace(/\s+/g, ' ').trim().toLowerCase();
// A table row's cells: outer pipes go (both are optional), an escaped pipe (\|) stays in its cell.
const cells = line => line.trim().replace(/^\|/, '').replace(/(?<!\\)\|$/, '').split(/(?<!\\)\|/).map(cell => cell.trim().replace(/\\\|/g, '|'));
const delimiter = line => PIPE.test(line) && cells(line).every(cell => /^:?-+:?$/.test(cell));
// A quoted line is read as the text after its > marks.
const unquote = line => QUOTED.test(line) ? { line: line.replace(/^(?: {0,3}> ?)+/, ''), quoted: true } : { line, quoted: false };

// An ATX heading with its level and text, in linear time (no regex backtracking on long lines).
function headingOf(line) {
  const open = ATX.exec(line);
  if (!open) return null;
  let text = line.slice(open[0].length).trim(), at = text.length;
  while (at > 0 && text[at - 1] === '#') at--;
  if (at < text.length && (at === 0 || text[at - 1] === ' ' || text[at - 1] === '\t')) text = text.slice(0, at).trimEnd();
  return { level: open[1].length, text };
}

// Fenced code blocks and HTML comment blocks are not read.
function blockStart(line) {
  const fence = /^ *(`{3,}|~{3,})(.*)$/.exec(line);
  if (fence && !(fence[1][0] === '`' && fence[2].includes('`'))) return { fence: fence[1][0], size: fence[1].length };
  const text = line.trimStart();
  if (text.startsWith('<!--')) return text.indexOf('-->', 4) >= 0 ? { closed: true } : { comment: true };
  return null;
}
function blockEnd(block, line) {
  if (block.comment) return line.includes('-->');
  const close = /^ *(`{3,}|~{3,}) *$/.exec(line);
  return !!close && close[1][0] === block.fence && close[1].length >= block.size;
}
// The issue text that the reader reads: no fenced code block, no HTML comment block, no > marks.
function readable(text) {
  const out = [];
  let block = null;
  for (const raw of lines(text)) {
    const { line } = unquote(raw);
    if (block) { if (blockEnd(block, line)) block = null; continue; }
    const opened = blockStart(line);
    if (opened) { if (!opened.closed) block = opened; continue; }
    out.push(line);
  }
  return out.join('\n');
}

// The text after a label (or a context word), or null. Leading non-letters (marks, emoji) and a number such as "2." do not count.
function afterLabel(text, words = LABEL) {
  const plain = text.trim().replace(/^[^\p{L}\p{N}]+/u, '').replace(/^\d{1,3}[.)]\s*/, '').replace(/^[^\p{L}\p{N}]+/u, '');
  const label = words.exec(plain);
  return label ? plain.slice(label[0].length) : null;
}
// A label line gives its item text ('' when none), or null when the line is not a label line.
function labelLine(line) {
  const after = afterLabel(line);
  if (after === null) return null;
  const colon = LABEL_COLON.exec(after);
  if (colon) return colon[2];
  if (/^[*_`\s]*$/.test(after)) return '';
  const text = line.trim();
  return text.length <= 60 && /^(\*\*|__).*\1$/.test(text) ? '' : null;
}
// A descriptive label line: a context word, then a colon (within 3 words or at the end), only marks, or a short bold line.
function contextLine(line) {
  const after = afterLabel(line, CONTEXT);
  if (after === null) return false;
  const text = line.trim();
  return LABEL_COLON.test(after) || /^[*_`\s]*$/.test(after) || /:[*_\s]*$/.test(text) || (text.length <= 60 && /^(\*\*|__).*\1$/.test(text));
}

// A summary item for the lists or tables of one kind under one heading, outside the checklist sections.
function summaryText({ heading, kind, count, n }) {
  const [one, many, part, parts] = kind === 'table' ? ['table', 'tables', 'row', 'rows'] : ['list', 'lists', 'item', 'items'];
  const where = heading === null ? 'before its first heading' : `under "${heading}"`;
  return `The issue's other ${count > 1 ? `${count} ${many}` : one} ${where} (${n} ${n === 1 ? part : parts}): each ${part} done, or left out with a reason`;
}

export function issueChecklist(text) {
  const found = [], groups = new Map(), stack = [];
  let current = null, heading = null, label = false, blank = true, block = null, table = null;
  let title = null, headings = 0, run = null, context = false, sectionStart = 0, prose = [];
  const close = () => { if (current) found.push(current); current = null; };
  const inSection = () => heading !== null || label;
  // Under a context heading (or a parent one), or after a descriptive label line: no summary item.
  const quiet = () => context || stack.some(entry => entry.context);
  const group = kind => {
    const key = `${headings}|${kind}`;
    if (!groups.has(key)) groups.set(key, { heading: title, kind, count: 0, n: 0 });
    return groups.get(key);
  };
  const join = (separator, part) => {
    if (!part.trim()) return;
    current.text = current.text.trim() ? `${current.text}${separator}${part}` : part;
  };
  // A heading section with no item but with prose gives one item: its prose.
  const endSection = () => {
    if (heading !== null && !found.slice(sectionStart).some(entry => HAS_WORD.test(entry.text)) && prose.length) found.push({ text: prose.join(' ') });
    heading = null;
  };
  const startHeading = (level, headingText) => {
    close(); label = false; blank = false; run = null; context = false;
    headings++; title = clip(headingText.replace(/\s+/g, ' ').trim(), MAX_HEADING);
    while (stack.length && stack.at(-1).level >= level) stack.pop();
    stack.push({ level, context: afterLabel(headingText, CONTEXT) !== null });
    if (heading !== null && level <= heading) endSection();
    if (heading === null && afterLabel(headingText) !== null) { heading = level; sectionStart = found.length; prose = []; }
  };
  const all = lines(str(text)).map(unquote);
  for (let at = 0; at < all.length; at++) {
    const { line, quoted } = all[at];
    if (block) { if (blockEnd(block, line)) { block = null; blank = true; } continue; }
    const row = PIPE.test(line) ? cells(line) : null;
    if (!row) table = null;
    const opened = blockStart(line);
    if (opened) { if (opened.fence && indentOf(line) < 2) close(); if (!opened.closed) block = opened; blank = true; continue; }
    if (!line.trim()) { blank = true; continue; }
    if (HTML_LINE.test(line) || THEMATIC.test(line)) { close(); blank = true; continue; }
    const head = quoted ? null : headingOf(line);
    if (head) { startHeading(head.level, head.text); continue; }
    // A table: a header row, a delimiter row, then data rows. In a section each data row is an item.
    const next = all[at + 1]?.line ?? '';
    if (row && (table || delimiter(next))) {
      close(); blank = false; run = null;
      if (table === null && !inSection() && !quiet()) group('table').count++;
      if (table === 'rows') { if (inSection()) found.push({ text: row.filter(Boolean).join(' | ') }); else if (!quiet()) group('table').n++; }
      table = table === null ? 'header' : 'rows';
      continue;
    }
    const list = LIST.exec(line);
    if (list) {
      const indent = list[1].length, body = list[2] ?? '', task = TASK.exec(body);
      const empty = current?.label && !HAS_WORD.test(current.text);
      if (task) { close(); current = { indent, text: task[1] }; }
      else if (current && !empty && indent > current.indent) join('; ', body);
      else {
        close();
        if (inSection()) current = { indent, text: body };
        else if (!quiet() && (run === null || indent <= run)) { const g = group('list'); if (run === null) g.count++; g.n++; run = indent; }
      }
      blank = false; continue;
    }
    // A line of other text continues the current item right after it, when indented, or as the text of an empty label.
    const continues = !!current && (!blank || indentOf(line) >= current.indent + 2 || (current.label && !HAS_WORD.test(current.text)));
    if (!quoted && !continues && all[at + 1] && !all[at + 1].quoted && SETEXT.test(next)) { startHeading(next.trim()[0] === '=' ? 1 : 2, line.trim()); at++; continue; }
    const labelText = labelLine(line);
    if (labelText !== null) { close(); label = true; run = null; context = false; current = { indent: indentOf(line), text: labelText, label: true }; blank = false; continue; }
    if (contextLine(line)) { close(); label = false; run = null; context = true; blank = false; continue; }
    if (run !== null && blank && indentOf(line) < run + 2) run = null;
    if (context && blank && indentOf(line) < 2) context = false;
    if (continues) join(' ', line.trim());
    else { close(); label = false; if (heading !== null) prose.push(line.trim()); }
    blank = false;
  }
  close();
  endSection();
  const items = [], seen = new Set();
  for (const entry of found) {
    let item = entry.text.replace(/\s+/g, ' ').trim();
    if (entry.label) item = item.replace(/^[*_\s]+|[*_\s]+$/g, '');
    item = clip(item, MAX_CHARS);
    if (!HAS_WORD.test(item)) continue;
    const form = sameForm(item);
    if (seen.has(form)) continue;
    seen.add(form);
    items.push(item);
  }
  for (const g of groups.values()) if (g.n) items.push(summaryText(g));
  // Never cut silently: the 30th item says how many items the cut leaves out.
  if (items.length > MAX_ITEMS) {
    const more = items.length - MAX_ITEMS, tail = `; and ${more} more item${more === 1 ? '' : 's'} in the issue; the reviewer checks them`;
    items.length = MAX_ITEMS;
    items[MAX_ITEMS - 1] = clip(items[MAX_ITEMS - 1], MAX_CHARS - [...tail].length) + tail;
  }
  return items.map((item, i) => ({ id: `C${i + 1}`, text: item }));
}

const listOf = items => Array.isArray(items) ? items : [];
const itemLines = items => items.map((item, i) => `C${i + 1}. ${str(item?.text)}`).join('\n');

export function checklistBrief(items) {
  const list = listOf(items);
  if (!list.length) return '';
  return `Issue checklist. Autopilot took these items from the issue text, apart from your plan. Your plan cannot drop an item, and the list does not make the issue smaller:
${itemLines(list)}
In the PR body, write one "Checklist:" section with one line for each item, in this form:
Checklist:
- C1: EVIDENCE
- C2: excluded: "QUOTE"
EVIDENCE is the test (its file and name), the check (its command and result) or the file that shows that the item is done. A line that defers the item or says that it is not done ("later", "follow-up", "not done") is no evidence. QUOTE is an exact quote from the issue text, at least 3 whole words and not the item's own text, that allows leaving the item out. Autopilot checks this section: an item with no line or no evidence is red, and an exclusion whose quote is not in the issue text is red. A fresh reviewer checks that the evidence is real and that each quote allows its exclusion.`;
}

export function checklistReview(items) {
  const list = listOf(items);
  if (!list.length) return '';
  return `Issue checklist. Autopilot took these items from the issue text, apart from the builder's plan. The list does not make the issue smaller: check the change against the whole issue as before.
${itemLines(list)}
For each item, check its line in the PR body's "Checklist:" section against the diff. An item needs real evidence (a test that checks it, a check with its result, or a file that does it) or an exclusion whose exact quote from the issue text really allows leaving the item out. An item with no real evidence and no supported exclusion is a P2 must-fix that names the item, for example "P2 checklist C3: no test checks ...".`;
}

// The lines of every Checklist: section of the PR body, in body order (with their continuations), or null when there is none.
function prSection(body) {
  const out = [];
  let block = null, open = false, any = false, entry = null, table = false;
  const all = lines(body);
  for (const [at, line] of all.entries()) {
    if (!PIPE.test(line)) table = false;
    if (block) { if (blockEnd(block, line)) block = null; continue; }
    const opened = blockStart(line);
    if (opened) { open = false; if (!opened.closed) block = opened; continue; }
    if (START.test(line.trim().replace(/^#{1,6}(?:\s+|$)/, '').replace(/[*_]/g, '').trim())) { open = true; any = true; entry = null; continue; }
    if (!open || !line.trim()) continue;
    if (headingOf(line)) { open = false; continue; }
    const indent = indentOf(line), next = all[at + 1] ?? '';
    if (entry && indent >= entry.indent + 2) { entry.text += ` ${line.trim()}`; entry.raw += ` ${line.trim()}`; continue; }
    // A table row (a leading pipe, a delimiter row below, or a row of a table) reads as its cells joined by ": ".
    if (PIPE.test(line) && (table || line.trim().startsWith('|') || delimiter(next))) {
      entry = null; table = true;
      if (!delimiter(line) && !delimiter(next)) out.push({ text: cells(line).filter(Boolean).join(': '), raw: line.trim(), indent });
      continue;
    }
    if (!PR_LIST.test(line) && !ID_LINE.test(line)) { open = false; continue; }
    entry = { text: line.trim(), raw: line.trim(), indent };
    out.push(entry);
  }
  return any ? out : null;
}

const findWords = (hay, needle) => {
  for (let at = 0; at + needle.length <= hay.length; at++) if (needle.every((word, i) => hay[at + i] === word)) return at;
  return -1;
};

// The items that one section line names, and the rest of the line after the name.
function matchLine(text, forms) {
  let line = text, number = null, open = false;
  const marker = /^(?:[-*+]|(\d{1,9})[.):])(?:[ \t]+|$)/.exec(line);
  if (marker) { number = marker[1] ? Number(marker[1]) : null; line = line.slice(marker[0].length); }
  const box = /^\[([ xX])\][ \t]*/.exec(line);
  if (box) { open = box[1] === ' '; line = line.slice(box[0].length); }
  const ids = [];
  let rest = line, id;
  while ((id = ID.exec(rest))) {
    const first = Number(id[1]);
    rest = rest.slice(id[0].length);
    const range = ID_RANGE.exec(rest), last = range ? Number(range[1]) : first;
    if (range) rest = rest.slice(range[0].length);
    if (last >= first && last - first < 100) for (let n = first; n <= last; n++) ids.push(n); else ids.push(first, last);
    rest = rest.replace(ID_SEP, '');
  }
  const named = [...new Set(ids)].filter(n => n >= 1 && n <= forms.length).map(n => n - 1);
  if (named.length) return { indexes: named, rest: rest.replace(/^\s*[:.)|\-–—]?\s*/, ''), open };
  const found = words(line), lower = found.map(match => match[0].toLowerCase());
  let best = null, ties = [];
  forms.forEach((form, i) => {
    if (!form.words.length) return;
    const at = findWords(lower, form.words);
    if (at < 0) return;
    const hit = { i, size: form.text.length, end: at + form.words.length };
    if (!ties.length || hit.size > ties[0].size) ties = [hit]; else if (hit.size === ties[0].size) ties.push(hit);
  });
  // On a tie of the loose form, only the one item whose same form is in the line matches.
  if (ties.length === 1) best = ties[0];
  else if (ties.length > 1) { const exact = ties.filter(hit => sameForm(line).includes(forms[hit.i].same)); if (exact.length === 1) best = exact[0]; }
  if (!best) {
    const hits = [];
    forms.forEach((form, i) => {
      if (form.words.length <= PREFIX_WORDS) return;
      const at = findWords(lower, form.words.slice(0, PREFIX_WORDS));
      if (at >= 0) hits.push({ i, end: at + PREFIX_WORDS });
    });
    if (hits.length === 1) best = hits[0];
  }
  if (best) {
    const last = found[best.end - 1];
    return { indexes: [best.i], rest: line.slice(last.index + last[0].length).replace(/^[\s*_:.,;)\]"'”’\-–—]+/, ''), open };
  }
  if (number !== null && number >= 1 && number <= forms.length) return { indexes: [number - 1], rest: line, open };
  return null;
}

// The quote is in the readable issue text at whole words: it does not start or end inside a word.
function wholeIn(hay, needle) {
  for (let at = hay.indexOf(needle); needle && at >= 0; at = hay.indexOf(needle, at + 1)) {
    const before = hay[at - 1] ?? '', after = hay[at + needle.length] ?? '';
    if ((!wordChar(needle[0]) || !wordChar(before)) && (!wordChar(needle.at(-1)) || !wordChar(after))) return true;
  }
  return false;
}

function lineState(rest, open, issueForm, own, items) {
  const plain = rest.replace(/^[\s*_~([]+/, '');
  const exclusion = EXCLUSION.exec(plain);
  if (exclusion) {
    const after = plain.slice(exclusion[0].length), start = after.search(/["“]/);
    const end = Math.max(after.lastIndexOf('"'), after.lastIndexOf('”'));
    const quote = start >= 0 && end > start ? after.slice(start + 1, end).trim() : '';
    const form = quoteForm(quote);
    // Never a part of another item's text; a part of its own text only when the item marks itself as optional.
    const ok = words(form).length >= MIN_QUOTE_WORDS && wholeIn(issueForm, form)
      && items.every(text => text === own || !quoteForm(text).includes(form)) && (!quoteForm(own).includes(form) || OPTIONAL.test(own));
    return { state: ok ? 'excluded' : 'unsupported', quote };
  }
  if (open || !HAS_WORD.test(plain) || NOT_DONE.test(plain) || BARE.test(plain)) return { state: 'missing', quote: null };
  return { state: 'covered', quote: null };
}

function redText(row) {
  if (row.state === 'missing') return `Checklist item ${row.id} has no evidence line in the PR body's "Checklist:" section: "${row.text}". Add "${row.id}: EVIDENCE" (the test, check or file that shows that it is done) or "${row.id}: excluded: "QUOTE"" with an exact quote from the issue text.`;
  const quote = row.quote ? `"${clip(row.quote, MAX_QUOTE)}"` : '(no quote)';
  return `Checklist item ${row.id} is excluded without an exact quote of at least 3 whole words from the issue text (not from the item itself, a code block or a comment): ${quote}. Quote the issue text exactly, or give the evidence for "${row.text}".`;
}

export function checkChecklist(prBody, items, issueText) {
  const list = listOf(items);
  const rows = list.map((item, i) => ({ id: `C${i + 1}`, text: str(item?.text), state: 'missing', line: null, quote: null }));
  const counts = { total: rows.length, covered: 0, excluded: 0, missing: 0, unsupported: 0 };
  if (!rows.length) return { state: 'none', items: rows, counts, reds: [] };
  const forms = rows.map(row => { const form = lowerWords(row.text); return { words: form, text: form.join(' '), same: sameForm(row.text) }; });
  const issueForm = quoteForm(readable(str(issueText)));
  for (const entry of prSection(str(prBody)) ?? []) {
    const hit = matchLine(entry.text, forms);
    if (!hit) continue;
    for (const i of hit.indexes) {
      const row = rows[i], { state, quote } = lineState(hit.rest, hit.open, issueForm, row.text, rows.map(other => other.text));
      if (row.line === null || RANK[state] > RANK[row.state]) Object.assign(row, { state, line: entry.raw, quote });
    }
  }
  for (const row of rows) counts[row.state]++;
  const reds = rows.filter(row => row.state === 'missing' || row.state === 'unsupported').map(redText);
  return { state: reds.length ? 'red' : 'pass', items: rows, counts, reds };
}

export function checklistNote(check) {
  if (!check || typeof check !== 'object' || check.state === 'none' || !check.counts) return [];
  const { covered, total, excluded } = check.counts;
  return [`- Checklist: ${covered} of ${total} covered (${excluded} excluded)`];
}
