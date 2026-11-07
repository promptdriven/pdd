# Read a pdd PR at a glance

As a reviewer of a pdd pull request, I want a short readable top with the user story, a summary and checks that pdd itself recorded, so that I can decide on the PR without reading machine lines.

## Acceptance criteria

1. Every PR that a pdd workflow opens starts with one status line (`✅ Ready to merge`, `⏳ Waiting for …` or `⛔ Blocked: <reason>`), then the user story from the Story's "As a …, I want …, so that …" line, a summary, a cases table, what changed with its +/− counts and files, and a Checks table (PR 1) or a Proof table (code PR). When no Story has that line, the PR has no User story section and its Details say why.
2. PR 1's summary has Problem, This PR and Verdict; a code PR's has Problem, Cause, Fix and Result; a one-PR small change has Problem, Change and Result. The agent gives these as labeled lines in its `done` summaries; its words never fill a check or proof row, and a claim such as "CI is green" stays only in the summary.
3. The tables and the status line come only from pdd's records: saved `pdd test` and `pdd lint` results (one report link), replay evidence with new-code and old-code (or planted-mistake) counts, the formal result (Proved only for a proved record), the old-code proof, review.md, CI and the checker verdict for the current head. A row with no result yet shows `⏳ pending`, and pdd refreshes it when it updates the PR.
4. PR 1 has one Approval line: in Autopilot `auto` mode "Automatic approval: Autopilot `auto` mode, started by <login> on <date>. No person was asked."; in a manual run the person's words on one line. Its Next line links PR 2 once PR 2 is open, says that PR 2 starts by itself in Autopilot, and says "The code PR starts when you ask for it." in a manual run. A code PR's Merge line says that it merges automatically when every check is green only in Autopilot `auto` mode, else that it waits for a person, and it closes the issue.
5. Everything else (pdd result lines, IDs, batches, request IDs, agent notes, approval records, step summaries, verify.md) is in one closed "Details for tools and audits" section, whole. The readable part has no internal words and no repeated link, and agent words in it cannot add HTML, a mention, a closing keyword or an ownership marker.

## Rules to check

Wrong: a proof or check row, or a ready status, that only an agent's words support; "Proved" for a formal check that has no proved record; a lost machine line; "The code comes in PR 2 only when the person asks for it" in an Autopilot run; a description over 60,000 characters; a second ownership marker.

## Native checks

The checks are in [test/workflow-pr-body.test.mjs](../test/workflow-pr-body.test.mjs) (fixtures modeled on two real sandbox PRs) and in [test/workflow-pr-publication.test.mjs](../test/workflow-pr-publication.test.mjs) (cases named `READABLE`, `PRTITLE`). They render through the public builders and publish through the real workflow command with local Git and a fake `gh` command. No interpreter run and no GitHub rendering is claimed.
