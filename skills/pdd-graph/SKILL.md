---
name: pdd-graph
description: Use when asked to read or open the saved PDD issue dependency graph, explain why an issue waits, or show what has no recorded blocker.
metadata:
  pdd-skills: 0.1.29
---

Use the supported CLI and its saved model. Do not redraw or infer the graph with a model.

- "Show dependency graph": run `pdd graph --open` in the chat repository.
- "Why is issue 42 waiting?": run `pdd graph --issue 42` and explain its saved reasons with issue/evidence links.
- "What is next?" or "What can run?" in dependency context: run `pdd graph`; separate dependency eligibility from the current owner's scheduling, room and approval checks.

An explicitly named repository uses graph-only `--repo OWNER/REPO`. Without a checkout or a named repository, ask for that repository. Do not choose a folder or start setup/login/clone.

On a headless VM, relay the exact laptop command returned by PDD. Do not claim the VM opener opens a laptop. Cached, stale, unchecked and offline facts stay labeled. `Stale review` means that something the review depends on changed: an input it used, an issue it names as a prerequisite, a link that a person changed to or from its issue, a person's answer to its question, or a trusted impact that names it as affected; an input that cannot be read also makes it stale. A new or unrelated issue, or a link that PDD writes for another issue's review, never causes it. A missing review is not a completed empty review.

A graph request is read-only. Never invoke dependency prepare/complete, AI analysis, GitHub mutation or a new workflow to answer it. If analysis is needed, explain the separate intake action and leave the read result honest.
