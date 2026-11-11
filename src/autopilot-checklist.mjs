// Generated from prompts/cli/autopilot-checklist.prompt.md (sha256: dc8be89c0b9405a8b43517c190d485f88c0a289716772c069f4c7c893544ec58).

const MAX_ITEMS = 30, MAX_CHARS = 300, MAX_QUOTE = 200, PREFIX_WORDS = 8, MIN_QUOTE_WORDS = 3;
const WORD = /[\p{L}\p{N}]+/gu, HAS_WORD = /[\p{L}\p{N}]/u;
const LABEL = /^(?:done when|expected|acceptance criteri(?:a|on)|test(?:s|ing)?|wanted|proposed outcomes?)(?![\p{L}\p{N}])/iu;
// A colon after the label, with at most 3 more words before it ("Expected result:").
const LABEL_COLON = /^((?:[\s*_`]*[\p{L}\p{N}][\p{L}\p{N}'’-]*){0,3})[\s*_`]*:(.*)$/u;
const HEADING = /^ {0,3}(#{1,6})(?:[ \t]+(.*?))?(?:[ \t]+#+)?[ \t]*$/;
const LIST = /^( *)(?:[-*+]|\d{1,9}[.)])(?:[ \t]+(.*))?$/;
const PR_LIST = /^( *)(?:[-*+]|\d{1,9}[.):])(?:[ \t]+(.*))?$/;
const TASK = /^\[[ xX]\][ \t]+(.*)$/;
const TABLE_ROW = /^\s*\|/;
const START = /^(?:issue\s+)?checklist\s*(?::.*)?$/i;
const ID = /^[\s*_[(]*C(\d{1,3})(?![\p{L}\p{N}])[*_\])]*/iu;
const ID_SEP = /^\s*(?:[,/&+]\s*)?(?:and(?![\p{L}\p{N}])\s*)?/iu;
const ID_LINE = /^[\s*_[(]*C\d{1,3}(?![\p{L}\p{N}])/iu;
const NO_EVIDENCE = /^(?:pending|todo|to do|tbd|not done|not yet|none|n\/a|missing|no evidence|not covered)[\s*_]*(?:$|[:(\-–—,;.])/iu;
const RANK = { missing: 1, unsupported: 2, excluded: 3, covered: 4 };

const str = value => typeof value === 'string' ? value : '';
const lines = text => text.split(/\r\n|\r|\n/).map(line => line.replace(/\t/g, '    '));
const indentOf = line => line.length - line.trimStart().length;
const words = text => [...text.matchAll(WORD)];
const lowerWords = text => words(text).map(match => match[0].toLowerCase());
const quoteForm = text => text.normalize('NFC').replace(/[“”]/g, '"').replace(/[‘’]/g, "'").replace(/[`*_]/g, '').replace(/\s+/g, ' ').trim();
const cut = (text, size) => [...text].slice(0, size).join('');
// A table row's cells: outer pipes go, an escaped pipe (\|) stays in its cell.
const cells = line => line.trim().replace(/^\|/, '').replace(/(?<!\\)\|$/, '').split(/(?<!\\)\|/).map(cell => cell.trim().replace(/\\\|/g, '|'));
const delimiter = row => row.length > 0 && row.every(cell => /^:?-+:?$/.test(cell));

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

// The text after a label, or null. Leading marks and a number such as "2." do not count.
function afterLabel(text) {
  const plain = text.trim().replace(/^[*_`\s]+/, '').replace(/^\d{1,3}[.)]\s*/, '').replace(/^[*_`\s]+/, '');
  const label = LABEL.exec(plain);
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

// A summary item for the lists or tables of one kind under one heading, outside the checklist sections.
function summaryText({ heading, kind, count, n }) {
  const [one, many, part, parts] = kind === 'table' ? ['table', 'tables', 'row', 'rows'] : ['list', 'lists', 'item', 'items'];
  const where = heading === null ? 'before its first heading' : `under "${heading}"`;
  return `The issue's other ${count > 1 ? `${count} ${many}` : one} ${where} (${n} ${n === 1 ? part : parts}): each ${part} done, or left out with a reason`;
}

export function issueChecklist(text) {
  const found = [], groups = new Map();
  let current = null, heading = null, label = false, blank = true, block = null, table = null;
  let title = null, headings = 0, run = null;
  const close = () => { if (current) found.push(current); current = null; };
  const inSection = () => heading !== null || label;
  const group = kind => {
    const key = `${headings}|${kind}`;
    if (!groups.has(key)) groups.set(key, { heading: title, kind, count: 0, n: 0 });
    return groups.get(key);
  };
  const join = (separator, part) => {
    if (!part.trim()) return;
    current.text = current.text.trim() ? `${current.text}${separator}${part}` : part;
  };
  const all = lines(str(text));
  for (const [at, line] of all.entries()) {
    if (block) { if (blockEnd(block, line)) { block = null; blank = true; } continue; }
    const row = TABLE_ROW.test(line) ? cells(line) : null;
    if (!row) table = null;
    const opened = blockStart(line);
    if (opened) { if (opened.fence && indentOf(line) < 2) close(); if (!opened.closed) block = opened; blank = true; continue; }
    if (!line.trim()) { blank = true; continue; }
    const head = HEADING.exec(line);
    if (head) {
      close(); label = false; blank = false; run = null;
      headings++; title = cut((head[2] ?? '').replace(/\s+/g, ' ').trim(), 120);
      const level = head[1].length;
      if (heading !== null && level <= heading) heading = null;
      if (heading === null && afterLabel(head[2] ?? '') !== null) heading = level;
      continue;
    }
    // A table: a header row, a delimiter row, then data rows. In a section each data row is an item.
    const next = all[at + 1];
    if (row && (table || (TABLE_ROW.test(next ?? '') && delimiter(cells(next))))) {
      close(); blank = false; run = null;
      if (table === null && !inSection()) group('table').count++;
      if (table === 'rows') { if (inSection()) found.push({ text: row.filter(Boolean).join(' | ') }); else group('table').n++; }
      table = table === null ? 'header' : 'rows';
      continue;
    }
    const list = LIST.exec(line);
    if (list) {
      const indent = list[1].length, body = list[2] ?? '', task = TASK.exec(body);
      const empty = current?.label && !current.text.trim();
      if (task) { close(); current = { indent, text: task[1] }; }
      else if (current && !empty && indent > current.indent) join('; ', body);
      else {
        close();
        if (inSection()) current = { indent, text: body };
        else if (run === null || indent <= run) { const g = group('list'); if (run === null) g.count++; g.n++; run = indent; }
      }
      blank = false; continue;
    }
    const labelText = labelLine(line);
    if (labelText !== null) { close(); label = true; run = null; current = { indent: indentOf(line), text: labelText, label: true }; blank = false; continue; }
    if (run !== null && blank && indentOf(line) < run + 2) run = null;
    if (current && (!blank || indentOf(line) >= current.indent + 2)) join(' ', line.trim());
    else { close(); label = false; }
    blank = false;
  }
  close();
  const items = [], seen = new Set();
  for (const entry of found) {
    let item = entry.text.replace(/\s+/g, ' ').trim();
    if (entry.label) item = item.replace(/^[*_\s]+|[*_\s]+$/g, '');
    item = cut(item, MAX_CHARS).trimEnd();
    if (!HAS_WORD.test(item)) continue;
    const form = lowerWords(item).join(' ');
    if (seen.has(form)) continue;
    seen.add(form);
    items.push(item);
  }
  for (const g of groups.values()) if (g.n) items.push(summaryText(g));
  // Never cut silently: the 30th item says how many items the cut leaves out.
  if (items.length > MAX_ITEMS) {
    const more = items.length - MAX_ITEMS, tail = `; and ${more} more item${more === 1 ? '' : 's'} in the issue; the reviewer checks them`;
    items.length = MAX_ITEMS;
    items[MAX_ITEMS - 1] = cut(items[MAX_ITEMS - 1], MAX_CHARS - [...tail].length).trimEnd() + tail;
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
EVIDENCE is the test (its file and name), the check (its command and result) or the file that shows that the item is done. QUOTE is an exact quote from the issue text, at least 3 words, that allows leaving the item out. Autopilot checks this section: an item with no line or no evidence is red, and an exclusion whose quote is not in the issue text is red. A fresh reviewer checks that the evidence is real and that each quote allows its exclusion.`;
}

export function checklistReview(items) {
  const list = listOf(items);
  if (!list.length) return '';
  return `Issue checklist. Autopilot took these items from the issue text, apart from the builder's plan. The list does not make the issue smaller: check the change against the whole issue as before.
${itemLines(list)}
For each item, check its line in the PR body's "Checklist:" section against the diff. An item needs real evidence (a test that checks it, a check with its result, or a file that does it) or an exclusion whose exact quote from the issue text really allows leaving the item out. An item with no real evidence and no supported exclusion is a P2 must-fix that names the item, for example "P2 checklist C3: no test checks ...".`;
}

// The PR body's Checklist: section: its lines (with their continuations), or null when there is none.
function prSection(body) {
  const out = [];
  let block = null, started = false, entry = null;
  for (const line of lines(body)) {
    if (!started) {
      if (block) { if (blockEnd(block, line)) block = null; continue; }
      const opened = blockStart(line);
      if (opened) { if (!opened.closed) block = opened; continue; }
      started = START.test(line.trim().replace(/^#{1,6}(?:\s+|$)/, '').replace(/[*_]/g, '').trim());
      continue;
    }
    if (!line.trim()) continue;
    if (blockStart(line) || HEADING.test(line)) break;
    const indent = indentOf(line);
    if (entry && indent >= entry.indent + 2) { entry.text += ` ${line.trim()}`; continue; }
    if (!PR_LIST.test(line) && !ID_LINE.test(line)) break;
    entry = { text: line.trim(), indent };
    out.push(entry);
  }
  return started ? out : null;
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
  while ((id = ID.exec(rest))) { ids.push(Number(id[1])); rest = rest.slice(id[0].length).replace(ID_SEP, ''); }
  const named = [...new Set(ids)].filter(n => n >= 1 && n <= forms.length).map(n => n - 1);
  if (named.length) return { indexes: named, rest: rest.replace(/^\s*[:.)\-–—]?\s*/, ''), open };
  const found = words(line), lower = found.map(match => match[0].toLowerCase());
  let best = null;
  forms.forEach((form, i) => {
    if (!form.words.length) return;
    const at = findWords(lower, form.words);
    if (at >= 0 && (!best || form.text.length > best.size)) best = { i, size: form.text.length, end: at + form.words.length };
  });
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

function lineState(rest, open, issueForm) {
  const plain = rest.replace(/^[\s*_]+/, '');
  const excluded = /^excluded(?![\p{L}\p{N}])/iu.exec(plain);
  if (excluded) {
    const after = plain.slice(excluded[0].length), start = after.search(/["“]/);
    const end = Math.max(after.lastIndexOf('"'), after.lastIndexOf('”'));
    const quote = start >= 0 && end > start ? after.slice(start + 1, end).trim() : '';
    const form = quoteForm(quote);
    return { state: words(form).length >= MIN_QUOTE_WORDS && issueForm.includes(form) ? 'excluded' : 'unsupported', quote };
  }
  if (open || !HAS_WORD.test(plain) || NO_EVIDENCE.test(plain)) return { state: 'missing', quote: null };
  return { state: 'covered', quote: null };
}

function redText(row) {
  if (row.state === 'missing') return `Checklist item ${row.id} has no evidence line in the PR body's "Checklist:" section: "${row.text}". Add "${row.id}: EVIDENCE" (the test, check or file that shows that it is done) or "${row.id}: excluded: "QUOTE"" with an exact quote from the issue text.`;
  const quote = row.quote ? `"${cut(row.quote, MAX_QUOTE)}"` : '(no quote)';
  return `Checklist item ${row.id} is excluded without an exact quote of at least 3 words from the issue text: ${quote}. Quote the issue text exactly, or give the evidence for "${row.text}".`;
}

export function checkChecklist(prBody, items, issueText) {
  const list = listOf(items);
  const rows = list.map((item, i) => ({ id: `C${i + 1}`, text: str(item?.text), state: 'missing', line: null, quote: null }));
  const counts = { total: rows.length, covered: 0, excluded: 0, missing: 0, unsupported: 0 };
  if (!rows.length) return { state: 'none', items: rows, counts, reds: [] };
  const forms = rows.map(row => { const form = lowerWords(row.text); return { words: form, text: form.join(' ') }; });
  const issueForm = quoteForm(str(issueText));
  for (const entry of prSection(str(prBody)) ?? []) {
    const hit = matchLine(entry.text, forms);
    if (!hit) continue;
    const { state, quote } = lineState(hit.rest, hit.open, issueForm);
    for (const i of hit.indexes) {
      const row = rows[i];
      if (row.line === null || RANK[state] > RANK[row.state]) Object.assign(row, { state, line: entry.text, quote });
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
