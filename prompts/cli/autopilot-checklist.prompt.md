# Autopilot issue checklist

Own `src/autopilot-checklist.mjs`. The build agent of the [Autopilot core](autopilot-core.prompt.md)
decides the scope of its PR, and nothing keeps the full list of what the issue asks for. So a PR
can pass every check and still leave items of the issue undone (#3249; in the funnel audit of Nov 9
to 11, the first PR of pdd #2892 left checklist items of the issue pending, and the work of pdd
#3012 lacked the pilot that the issue requires). This module reads a checklist from the issue text
with fixed rules, apart from the builder's plan. It writes the checklist text for the build, repair
and review briefs, and it checks the PR body's `Checklist:` section against the items.

Why fixed rules: the builder must not choose the list that checks the builder. Why the limits: the
items go into each brief and red, so at most 30 items of at most 300 characters keep them short.
The engine checks only what a program can check: each item has a line with evidence, and an
exclusion quotes the issue text. Whether the evidence is real, and whether a quote really allows the
exclusion, is the fresh reviewer's work (Serhan agreed that this may make reviews stricter).

The module is pure: no files, network, clock or processes. The core is the caller: at job start it
saves the items in the job file, apart from the builder's scope, and it shows the texts and results.
Nothing in the issue is lost silently: a list or a table outside the checklist sections gives one
summary item, and a cut at the limit says how many items it left out. An issue with no checklist
(no task item, no list and no table) gives no text, no line and no new red.

## Read the checklist from the issue

`issueChecklist(text)` returns the items `[{id, text}]` in issue order. `id` is `C1`, `C2`, … by
place, after the dedup and the limit. `text` is the item's text. No checklist: `[]`. A `text` that
is not a string counts as empty.

The reader reads the issue line by line (a tab counts as 4 spaces of indent).

- **Not read.** A fenced code block (a line that starts, after spaces, with 3 or more backticks or
  tildes, and for backticks has no other backtick, to the closing fence of the same character and
  at least the same length, or to the end) and an HTML comment block (a line that starts, after
  spaces, with `<!--`, to the line that holds `-->`) give no items, headings or label lines. Code
  blocks hold examples, logs and templates, not requests. A code block that is not indented ends
  the current item; after a code block or a comment block, the next line counts as after a blank
  line.
- **Quoted lines.** A line that starts, after at most 3 spaces, with `>` is read as the text after
  its `>` marks (each with at most one space after it), so a quoted task list (`> - [ ] x`) gives
  items. A quoted line is never a heading.
- **HTML and breaks.** A line that starts with an HTML tag (`<details>`, `</details>`,
  `<summary>…`) and a thematic break (3 or more `-`, `*` or `_`, with spaces between allowed) end
  the current item, continue no item and are no prose; the next line counts as after a blank line.
- **List lines.** A list line starts, after its indent, with `-`, `*` or `+`, or a number and `.` or
  `)`, then a space. A **task item** is a list line whose text starts with `[ ]`, `[x]` or `[X]` and
  a space; its text is the text after the box.
- **Labels.** "Done when" (also "Done-when"), "Expected", "Acceptance criteria" (also "criterion"), "Test" (also
  "Tests" and "Testing"), "Wanted" and "Proposed outcome" (also "outcomes"), in any case, as whole
  words ("Testability" is not a label). "Proposal" is not a label: a proposal lists ways to do the
  work, not what must be true. Before the label, characters that are not letters or digits (marks,
  quote marks, emoji) and a number such as `2.` are skipped. "Wanted" and "Proposed outcome" are labels because the two evidence issues use
  them: pdd #2892 ("## Wanted") and pdd #3012 ("## Proposed outcome for discussion", with the pilot
  that the work lacked).
- **Checklist sections.**
  - A **heading** is a line of `#` to `######` (after at most 3 spaces) and then a space or the
    end; its text loses a closing run of `#` that follows a space. A **setext heading** is a line
    of other text that continues no item, right above a line of only `=` (level 1) or only `-`
    (level 2) after at most 3 spaces; the underline line is not read again. A heading whose text
    starts with a label starts a section. It ends at the next heading of the same or a higher level
    (as many `#` or fewer). A deeper heading stays in the section.
  - A **label line** is a line that is not a heading or a list line, that starts with a label, and
    that either has a colon after the label with at most 3 more words before the colon
    (`Expected result:`), or has only marks after the label (`**Done when**`), or is at most 60
    characters and in bold (`**Expected behavior**`). It starts a section that ends at the next
    heading or at the next line of other text that does not continue an item. The text after its
    colon is an item; text right below it continues that item.
- **Items.**
  - Each task item, inside or outside a section, is an item.
  - Inside a section, each list line is an item, except a list line that is more indented than the
    current item: it joins the current item after `"; "`. A task item never joins: it is always its
    own item. A label line has text only when a letter or digit is left after its Markdown marks
    go. A label line with no text takes no list line (the list line starts a new item), and a line
    of other text after it, also after a blank line, is its text.
  - A line of other text continues the current item (after a space) when it comes right after the
    item's lines with no blank line between, or after a blank line when it is indented at least 2
    spaces more than the item. Any other line of other text ends the current item. A heading ends
    it. A list line outside a section that does not join ends it.
  - A table in a section is a header row, a delimiter row (cells such as `---`, `:--` or `:-:`), then
    data rows. A row is a line that holds a `|` that is not escaped; a leading and a trailing `|`
    are optional (`Where | What` then `--- | ---`). Each data row is an item: its text is its
    cells that are not empty, trimmed, joined by ` | ` (an escaped `\|` stays in its cell). The
    header and delimiter rows are not items. A table row, in a section or not, ends the current
    item and takes no continuation. A table ends at the first line that is not a row. A line with a
    `|` that is not in a table is a line of other text.
  - A section's items are its list lines, its task items, its table rows and the text of its label
    lines. A heading section that ends with none of these, but holds prose, gives **one item**: its
    lines of prose (the lines of other text that continue no item and are not label lines),
    joined by one space, at the section's place. Why: a bug report's usual form is
    `## Expected behavior` and a paragraph; nothing is lost silently (group lead, Nov 11).
- **Other lists and tables.** A list or a table outside the checklist sections gives one
  **summary item** for each heading and kind (list or table). Why: the audit rows R0 to R64 of
  pdd #2892 were under a heading that is not a label, and its first PR left one of them pending.
  The summary item makes the PR say what it did with each row (release lead decision, Nov 11).
  - A list here is a run of list lines outside the sections that are not task items (task items
    are items already). The run's first line sets its indent; a list line more indented than that
    is nested and does not count (a less indented one counts and sets the indent), and a list line
    that joins a task item does not count. A run
    ends at a heading, a table, a label line, or a line of other text after a blank line that is
    not indented at least 2 spaces more than the run. A table here is a table outside the sections.
  - N is the number of counted list lines, or of data rows, of that kind under that heading.
    HEADING is the text of the nearest heading above (white space runs as one space, cut at 120
    characters as below). The text is
    `The issue's other list under "HEADING" (N items): each item done, or left out with a reason`
    or `The issue's other table under "HEADING" (N rows): each row done, or left out with a reason`.
    When there are K lists (or tables) under one heading, `other list` becomes `other K lists`
    (`other K tables`). One item or row is `(1 item)` or `(1 row)`. With no heading above,
    `under "HEADING"` becomes `before its first heading`. When N is 0 (a table with no data row),
    there is no summary item.
  - **Descriptive parts give no summary item.** A list or table under a descriptive heading, or
    under a heading whose parent heading (a higher level heading above it) is descriptive, gives
    no summary item. A heading is descriptive when its text starts with one of these context
    words, in any case, as whole words, after the marks and number that labels skip: "Problem",
    "Evidence", "Background", "Context", "Notes", "Related", "References", "Sources" and "What
    happens" (the release lead's list, Nov 11). No other word is descriptive: "Proposal", "Test",
    "Expected", "What is needed", "What I want", "Why", "Source", "Problems" and every other
    heading keep their summary items. A **descriptive label line** (a line of other text that
    starts with a context word, and that has a colon after at most 3 more words, ends with a
    colon, has only marks after the words, or is at most 60 characters and in bold, such as
    `Evidence (funnel audit, Nov 9 to 11):`) does the same for the lists and tables after it. It
    ends the current item and a label-line section. Its part ends at the next heading, the next
    label line, or a line of other text after a blank line that is not indented 2 or more spaces.
    Why: these parts describe the problem and its history; they ask for no work. Items in
    checklist sections stay items.
- **Text.** Runs of white space become one space, and leading and trailing space go. A label line's
  item loses its leading `*` and `_` marks and its trailing ones. A text with more than 300
  characters is **cut**: it keeps its first 299 characters (whole code points), trailing space
  goes, and `…` ends it. Every cut in this module works this way. A text with no letter or digit is
  no item.
- **Order, dedup and limit.** The items come in issue order, then the summary items in the order
  of their first line. Two items are one item only when their same form (below) is the same; the
  item stays at the place of the first. Summary items are never merged. When there are more than
  30 items after the dedup, the first 29 stay, the 30th item stays with `; and N more items in the
  issue; the reviewer checks them` at the end of its text (N is the number of items after it; one
  is `1 more item`), and the rest go. Its own text is cut first, so that the whole text stays
  within 300 characters.

The **same form** of an item's text decides the dedup. Markdown emphasis marks go: a run of `*`
or `_`, or of 2 or more `~`, that opens (no letter or digit before it, and no space after it) or
closes (no letter or digit after it, and no space before it). A run between two letters or digits
(`max_items`) or between spaces (`x * y`) stays. Then runs of white space become one space,
leading and trailing space go, and the text is in lower case. Every other character stays:
operators, numbers and punctuation. So `Reject x < 0.` and `Reject x = 0.` are two items (review
round 1, Nov 11: a loose dedup made one item of them, and a PR with only the negative case
passed).

The **match form** of a text is its words (runs of letters and digits, in lower case), joined by
one space. Marks, punctuation and spacing do not change it. It only matches PR lines to items; it
never makes one item of two.

## The brief for the build and repair jobs

`checklistBrief(items)` returns `''` when there are no items. Else it returns this text, one line
per item in item order (`C1. TEXT`):

```text
Issue checklist. Autopilot took these items from the issue text, apart from your plan. Your plan cannot drop an item, and the list does not make the issue smaller:
C1. TEXT
C2. TEXT
In the PR body, write one "Checklist:" section with one line for each item, in this form:
Checklist:
- C1: EVIDENCE
- C2: excluded: "QUOTE"
EVIDENCE is the test (its file and name), the check (its command and result) or the file that shows that the item is done. A line that defers the item or says that it is not done ("later", "follow-up", "not done") is no evidence. QUOTE is an exact quote from the issue text, at least 3 whole words and not the item's own text, that allows leaving the item out. Autopilot checks this section: an item with no line or no evidence is red, and an exclusion whose quote is not in the issue text is red. A fresh reviewer checks that the evidence is real and that each quote allows its exclusion.
```

## Check the PR body

`checkChecklist(prBody, items, issueText)` returns `{state, items, counts, reds}`.

- `state`: `none` (no items), `pass` (each item is covered or excluded) or `red`.
- `items`: one row per item, in item order: `{id, text, state, line, quote}`. `id` is `C` and the
  item's place (the same ids as `issueChecklist`), `text` the item's text. `state` is `covered`,
  `excluded`, `missing` or `unsupported`. `line` is the PR line that decided the state (trimmed,
  with its continuation lines after a space), or `null` when no line names the item. `quote` is
  the exclusion's quote (an exclusion with no quote has `''`), else `null`.
- `counts`: `{total, covered, excluded, missing, unsupported}`.
- `reds`: one text for each `missing` or `unsupported` item, in item order.

`issueText` is the issue's title and body; the caller decides whether trusted comments are added.
A `prBody` or `issueText` that is not a string counts as empty; `items` that is not an array counts
as no items.

**The section.** A section starts at each line, outside fenced code blocks and HTML comment
blocks, that is `Checklist` or `Issue checklist` (any case), alone or with a colon and any text
after it, when its leading `#` marks, its `*` and `_` marks and its outer spaces are left out
(`Checklist:`, `## Checklist`, `**Checklist:**`). Every section counts, in body order, so a
template's own `## Checklist` before the job's section does not hide it. The lines after it belong to the section: blank
lines, list lines (also a number and `:`), lines that start with an item id, table rows, and lines
indented at least 2 spaces more than the section line before them, which continue that line. A
**table row** (a line with a `|` that is not escaped) is read as its cells that are not empty,
joined by `: ` (`| C3 | excluded | "QUOTE" |` reads as `C3: excluded: "QUOTE"`); a delimiter row
and the header row above it are not read. The item's `line` is the row as written. The section ends
at a heading, a fence, a comment block or any other line. So the `Runtime:` and `Evidence:` lines,
and a numbered list after them, are not part of it. A PR body with no section has every item
`missing`.

**How a line is matched.** Before the match, the list marker (and its number) and a box (`[ ]`,
`[x]`) go. The first rule that gives an item decides:

1. **Ids.** The line starts with one or more ids: `C` and the item number, in any case, alone or in
   `[]`, `()`, backtick, `*` or `_` marks, separated by spaces, `,`, `/`, `&`, `+` or "and". A
   range (`C1-C3`, also with `–`, `—`, `..` or "to") names each id from the first to the last; a
   range whose last id is lower names only its two ids. Each id of an item matches that item. An
   id later in the line ("see C1") does not count. The **rest** is the text after the ids and one
   separator (`:`, `.`, `)`, `-`, `–` or `—`).
2. **Item text.** The line repeats an item's text: the line's match form holds the item's whole
   match form as whole words. When several items match, the longest match form wins. On a tie,
   the one item whose same form is part of the line's same form wins; when that is not exactly
   one item, the line gives no match this way. When none matches this way, an item with more than
   8 words matches when the line holds its first 8 words and no other item matches that way. The rest is the text after the last
   matched word, without the spaces, marks, quote marks, dashes and `:`, `.`, `,`, `;`, `)` or `]`
   that lead it.
3. **Number.** The line is numbered and item `C`N exists for its number N. The rest is the line's
   text.

A line that matches no item is not used.

**The state of a line.** After the rest loses its leading spaces and its leading `*`, `_`, `~`,
`(` and `[` marks (review round 1, Nov 11: deferral lines counted as covered, and other exclusion
forms escaped the quote rule):

- The rest starts with a word that starts with "exclu" (excluded, exclusion, exclude), or with
  "out of scope" or "not in scope" (any case, whole words): an **exclusion**. Its quote is the
  text between the first `"` or `“` and the last `"` or `”` after those words, trimmed, so a quote
  may hold quotes. It is `excluded` when the quote has at least 3 words, its quote form is part of
  the quote form of the issue's readable text at whole words (a quote that starts or ends with a
  letter or digit does not start or end inside a word), and it is not part of the quote form of
  any item's text (release lead, Nov 11). One exception keeps the RUNBOOK §15 example right: when
  the item's own text marks it as optional ("optional", "optionally", "if possible" or "nice to
  have", whole words, any case), a quote from its own text supports its exclusion. So
  `Optionally add a picture` can exclude the item `Optionally add a picture`, and a plain quote of
  an item's text cannot exclude it or another item. Else it is `unsupported`. The **readable text** is `issueText` without the
  fenced code blocks and HTML comment blocks that the reader does not read.
- Else the line gives no evidence (`missing`) when its box is `[ ]`, when the rest has no letter or
  digit, when the rest starts with a negation or a deferral (any case, as a whole word or words:
  "no", "not", "none", "nothing", "never", "n/a", "na", "without", "cannot", "can't", "won't",
  "pending", "todo", "to do", "tbd", "tbc", "wip", "later", "deferred", "defer", "postponed",
  "will", "follow-up", "follow up", "followup", "skipped", "skip", "missing", "planned",
  "blocked" or "waiting"), or when the rest is only a status word with no evidence after it
  ("done", "yes", "ok", "okay", "complete", "completed", "covered", "fixed", "implemented",
  "verified", "finished" or "tested", then only marks and punctuation).
- Else the item is `covered`.

The **quote form** of a text: the text in Unicode NFC form, `“` and `”` become `"`, `‘` and `’`
become `'`, the marks `` ` ``, `*` and `_` go, runs of white space become one space, and leading
and trailing space go. Case stays: the quote must be exact.

When several lines match one item, the best state wins, in this order: `covered`, `excluded`,
`unsupported`, `missing`. The first line with that state is the item's `line`. An item that no
line matches is `missing` with `line` `null`.

**The red texts** (`ID`, `TEXT` and `QUOTE` are the item's id, text and quote; a quote of more than
200 characters is cut at 200; an empty quote shows as `(no quote)` with no quote marks):

- `missing`: `Checklist item ID has no evidence line in the PR body's "Checklist:" section: "TEXT". Add "ID: EVIDENCE" (the test, check or file that shows that it is done) or "ID: excluded: "QUOTE"" with an exact quote from the issue text.`
  In this text, QUOTE is the word QUOTE.
- `unsupported`: `Checklist item ID is excluded without an exact quote of at least 3 whole words from the issue text (not from the item itself, a code block or a comment): "QUOTE". Quote the issue text exactly, or give the evidence for "TEXT".`

## The merge note

`checklistNote(check)` returns the merge note lines: `[]` when `check` is missing or its `state`
is `none`; else one line, `- Checklist: N of M covered (K excluded)`, with N `covered`, M `total`
and K `excluded` from its counts.

## The reviewer text

`checklistReview(items)` returns `''` when there are no items. Else it returns this text, one line
per item in item order (`C1. TEXT`):

```text
Issue checklist. Autopilot took these items from the issue text, apart from the builder's plan. The list does not make the issue smaller: check the change against the whole issue as before.
C1. TEXT
C2. TEXT
For each item, check its line in the PR body's "Checklist:" section against the diff. An item needs real evidence (a test that checks it, a check with its result, or a file that does it) or an exclusion whose exact quote from the issue text really allows leaving the item out. An item with no real evidence and no supported exclusion is a P2 must-fix that names the item, for example "P2 checklist C3: no test checks ...".
```

## Public contract

Exports: `issueChecklist(text)`, `checklistBrief(items)`,
`checkChecklist(prBody, items, issueText)`, `checklistNote(check)` and `checklistReview(items)`,
as above. Each returns a new value, never throws for the input kinds above, and changes no input.

## Dependencies

None. The link to the core above is navigation only.
