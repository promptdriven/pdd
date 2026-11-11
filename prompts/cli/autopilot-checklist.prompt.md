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
An issue with no checklist gives no text, no line and no new red.

## Read the checklist from the issue

`issueChecklist(text)` returns the items `[{id, text}]` in issue order. `id` is `C1`, `C2`, … by
place, after the dedup and the limit. `text` is the item's text. No checklist: `[]`. A `text` that
is not a string counts as empty.

The reader reads the issue line by line (a tab counts as 4 spaces of indent).

- **Not read.** A fenced code block (a line that starts, after spaces, with 3 or more backticks or
  tildes, and for backticks has no other backtick, to the closing fence of the same character and
  at least the same length, or to the end) and an HTML comment block (a line that starts, after
  spaces, with `<!--`, to the line that holds `-->`) give no items, headings or label lines. Code blocks hold examples, logs and templates, not
  requests. A code block that is not indented ends the current item; after a code block or a
  comment block, the next line counts as after a blank line.
- **List lines.** A list line starts, after its indent, with `-`, `*` or `+`, or a number and `.` or
  `)`, then a space. A **task item** is a list line whose text starts with `[ ]`, `[x]` or `[X]` and
  a space; its text is the text after the box.
- **Labels.** "Done when", "Expected", "Acceptance criteria" (also "criterion") and "Test" (also
  "Tests" and "Testing"), in any case, as whole words ("Testability" is not a label). Before the
  label, `*`, `_` and backtick marks and a number such as `2.` are skipped.
- **Checklist sections.**
  - A heading (`#` to `######` and a space) whose text starts with a label starts a section. It ends
    at the next heading of the same or a higher level (as many `#` or fewer). A deeper heading stays
    in the section.
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
    own item. A label line with no text yet takes no list line: the list line starts a new item.
  - A line of other text continues the current item (after a space) when it comes right after the
    item's lines with no blank line between, or after a blank line when it is indented at least 2
    spaces more than the item. Any other line of other text ends the current item. A heading ends
    it. A list line outside a section that does not join ends it.
  - A paragraph under a heading is not an item: a section's items are its list lines, and the text of
    a label line.
- **Text.** Runs of white space become one space, and leading and trailing space go. A label line's
  item loses its leading `*` and `_` marks and its trailing ones. A text with more than 300
  characters keeps its first 300 characters (whole code points), then trailing space goes. A text
  with no letter or digit is no item.
- **Dedup and limit.** Two items with the same match form are one item, at the place of the first.
  After the dedup, the first 30 items count, and the rest go.

The **match form** of a text is its words (runs of letters and digits, in lower case), joined by
one space. Marks, punctuation and spacing do not change it.

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
EVIDENCE is the test (its file and name), the check (its command and result) or the file that shows that the item is done. QUOTE is an exact quote from the issue text, at least 3 words, that allows leaving the item out. Autopilot checks this section: an item with no line or no evidence is red, and an exclusion whose quote is not in the issue text is red. A fresh reviewer checks that the evidence is real and that each quote allows its exclusion.
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

A `prBody` or `issueText` that is not a string counts as empty; `items` that is not an array counts
as no items.

**The section.** The section starts at the first line, outside fenced code blocks and HTML comment
blocks, that is `Checklist` or `Issue checklist` (any case), alone or with a colon and any text
after it, when its leading `#` marks, its `*` and `_` marks and its outer spaces are left out
(`Checklist:`, `## Checklist`, `**Checklist:**`). The lines after it belong to the section: blank
lines, list lines (also a number and `:`), lines that start with an item id, and lines indented at
least 2 spaces more than the section line before them, which continue that line. The section ends
at a heading, a fence, a comment block or any other line. So the `Runtime:` and `Evidence:` lines,
and a numbered list after them, are not part of it. A PR body with no section has every item
`missing`.

**How a line is matched.** Before the match, the list marker (and its number) and a box (`[ ]`,
`[x]`) go. The first rule that gives an item decides:

1. **Ids.** The line starts with one or more ids: `C` and the item number, in any case, alone or in
   `[]`, `()`, `*` or `_` marks, separated by spaces, `,`, `/`, `&`, `+` or "and". Each id of an
   item matches that item. An id later in the line ("see C1") does not count. The **rest** is the
   text after the ids and one separator (`:`, `.`, `)`, `-`, `–` or `—`).
2. **Item text.** The line repeats an item's text: the line's match form holds the item's whole
   match form as whole words. When several items match, the longest match form wins (on a tie, the
   first item). When none matches this way, an item with more than 8 words matches when the line
   holds its first 8 words and no other item matches that way. The rest is the text after the last
   matched word, without the spaces, marks, quote marks, dashes and `:`, `.`, `,`, `;`, `)` or `]`
   that lead it.
3. **Number.** The line is numbered and item `C`N exists for its number N. The rest is the line's
   text.

A line that matches no item is not used.

**The state of a line.** After the rest loses its leading `*` and `_` marks:

- The rest starts with the word "excluded" (any case): an **exclusion**. Its quote is the text
  between the first `"` or `“` and the last `"` or `”` after that word, trimmed, so a quote may
  hold quotes. It is `excluded` when the quote has at least 3 words and its quote form is part of
  the quote form of `issueText`; else `unsupported`.
- Else the line gives no evidence (`missing`) when its box is `[ ]`, when the rest has no letter or
  digit, or when the rest starts with "pending", "todo", "to do", "tbd", "not done", "not yet",
  "none", "n/a", "missing", "no evidence" or "not covered" (any case), followed, after spaces and
  marks, by the end or by `:`, `(`, `-`, `–`, `—`, `,`, `;` or `.`.
- Else the item is `covered`.

The **quote form** of a text: the text in Unicode NFC form, `“` and `”` become `"`, `‘` and `’`
become `'`, the marks `` ` ``, `*` and `_` go, runs of white space become one space, and leading
and trailing space go. Case stays: the quote must be exact.

When several lines match one item, the best state wins, in this order: `covered`, `excluded`,
`unsupported`, `missing`. The first line with that state is the item's `line`. An item that no
line matches is `missing` with `line` `null`.

**The red texts** (`ID`, `TEXT` and `QUOTE` are the item's id, text and quote; a quote of more than
200 characters keeps its first 200; an empty quote shows as `(no quote)` with no quote marks):

- `missing`: `Checklist item ID has no evidence line in the PR body's "Checklist:" section: "TEXT". Add "ID: EVIDENCE" (the test, check or file that shows that it is done) or "ID: excluded: "QUOTE"" with an exact quote from the issue text.`
  In this text, QUOTE is the word QUOTE.
- `unsupported`: `Checklist item ID is excluded without an exact quote of at least 3 words from the issue text: "QUOTE". Quote the issue text exactly, or give the evidence for "TEXT".`

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
