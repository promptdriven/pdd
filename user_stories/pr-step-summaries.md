# Read step summary evidence on GitHub

As a PR reviewer, I want to read each step summary, or its important outcome, limitation and reference lines when the notes exceed the body budget, so that I can see late evidence on GitHub.

## Acceptance criteria

1. A step summary of 444 characters with a limitation and an issue link near its end appears whole in one closed "Full step summaries" section below the Steps list. The Steps list keeps its short line for that step, and that line does not have the late issue link.
2. The section has every step of this PR in the order of the Steps list, with the line breaks of each summary. It has no step from an earlier PR of the run.
3. Text in a summary stays plain text in the section and in the Steps list: a label such as "Review:" or "Not checked:" is not lifted to the top of the PR, HTML and `<details>` tags do nothing, an @ mention does not notify anyone, and "Fixes #N" closes nothing. A private Try link and a local path never appear, and a report link and an issue link stay readable. Lines that only pdd may write ("Old-code proof:", "Tests vs base:") are dropped as before.
4. When the summaries do not all fit in the PR size limit, ordinary notes are shortened first and shorter summaries stay whole. Complete sanitized lines containing outcomes, limitations, failures or HTTP(S) references stay visible even after a long omitted middle; gaps are marked with "…" and these notes remain unchecked agent text. No local run-folder pointer is offered as the recovery route. One line above the section names each shortened step and how many characters were left out, and the kept part and the count add up to the whole summary. The whole description, with its ownership marker, stays within 60,000 characters, and the Steps list, the top evidence and the Verify section are not cut to make room. When pdd updates the PR 1 description later and the evidence grows, the section stays, is shortened again first, and its notice stays true.
5. If protected evidence alone cannot fit with the required body, publication refuses with advice to shorten the notes while retaining that evidence; no incomplete description is published. An update keeps its previous description.
6. A PR title is `spec(AREA): STATEMENT (#N · part 1: spec)` for PR 1 and `fix(AREA): STATEMENT (#N · part 2: fix)` for the code PR (see [readable PRs](readable-pr-body.md)), and it keeps the whole statement when it fits in GitHub's 256-character limit. A title that does not fit is cut in sight: its statement ends with " …" before the suffix, it has at most 256 characters, and it does not split a character.

## Rules to check

Wrong: a shortened summary whose protected evidence a reviewer cannot read on GitHub; a cut with no count; a protected late outcome, limitation or reference omitted for ordinary notes; a run-folder path offered as the only recovery route; a notice that no longer matches the section after a PR 1 update; a section folded into one "not shown here" line; a label in a summary that becomes top evidence; an active mention, closing keyword, HTML block or second ownership or product marker from summary text, in the section or in the Steps list; a Try link or local path in the description; a description over the limit; room taken from the Steps list, the top evidence or verify.md for the section; a silently cut title, or a cut title that is not needed.

## Native checks

The checks are in [test/workflow-pr-publication.test.mjs](../test/workflow-pr-publication.test.mjs) (cases named `2874`, `PRSUM`, `PRTITLE`, `PR1-REFRESH-SUMMARIES` and `PR1-REFRESH-CODE-TAGS`). They publish through the real workflow command with local Git and a fake `gh` command. No interpreter run and no GitHub rendering is claimed.
