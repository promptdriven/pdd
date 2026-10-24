---
name: pdd
description: Use PDD's Prompting guide to draft or revise module prompts, Stories and independent expected cases, review changes, and follow local issue workflows or development recipes in the person's existing coding-agent conversation. Use when the person asks for PDD or prompt-first work.
---

# PDD Alpha

## Load the guide before authoring

Read the **entire canonical [Prompting guide](../../docs/prompting-guide.md) in this actual conversation before drafting any Story or prompt**, including when joining an existing conversation. A link or format checker does not supply its contents. If the guide is absent, inaccessible or truncated, obtain the complete file before authoring; do not invent replacement rules. Briefly explain the relevant method for the task, then apply it. Do not require a fixed Story format or confuse a test answer with a specification.

The local native session launcher must supply the full guide and bundled workflow content automatically before any Story. It uses the person's installed agent and existing permissions, not a private Host. If working in a manually opened conversation, explicitly load the same complete context.

The local `--skill` output includes the guide first and all bundled skill references. Resolve file paths from their actual package locations. If output is clipped, read the full files in sections. The guide is the single authority for prompt-writing rules; these instructions describe how to use it.

## Follow the person's useful task

Read [prompt-session guidance](references/prompt-session.md). Inspect the selected folder and its project instructions. Identify the useful change and preserve the person's scope. For local drafting, do not turn HOME into a project checkout or require an issue, enrollment, special account or private Host session. The explicit issue runner requires a real issue in the current GitHub repository. Ask only for decisions that affect the requested behavior.

Draft the relevant module contract, observable Story and independent expected cases using the guide. Reuse existing project paths. Keep unreviewed work labeled draft. For existing-code adoption, read callers and tests as evidence, preserve implementation during draft-only work and identify unresolved compatibility. An interface declaration is not evidence that a program ran.

## Review, then implement when requested

Read [review guidance](references/review.md). Show the draft contract and cases; preserve the person's actual revision and acceptance. On feedback, explain what changed and any unresolved point. When implementation is requested, follow the owning prompts and run the project's genuine tests using available tools. Do not write an implementation merely to imitate an execution result during prompt-only work.

Choose a manual [feature](../../.pdd/workflows/feature/WORKFLOW.md), [bug](../../.pdd/workflows/bug/WORKFLOW.md) or [small-change](../../.pdd/workflows/small-change/WORKFLOW.md) recipe when useful. Read its linked steps. Use the actual package entrypoint, for example `node /actual/package/bin/pdd.mjs workflow run NAME ISSUE [--agent codex|claude]`, only for requested issue workflow execution: it assigns an issue worktree, launches fresh background native stages under a foreground PDD controller and can create real GitHub PRs. Project definitions are validated and snapshotted for the run; later edits do not silently change it. Use only its actual saved run identity and supported resume decisions and active attachment from [workflow guidance](../../docs/workflows.md). The companion named-recipe shortcut and manual recipe remain single-conversation work. Local PR preparation is distinct from actual publication. A requested workflow run includes its real PR stages; report only verified returned PR identity and preserve human decisions and merge waits.

## Report evidence honestly

Keep drafted, reviewed, implemented, tested and published separate. Expected cases come from the contract, not from the program's observed answer. Report exact checks actually run, failures and unverified gaps. A source reading is not a test, and a project test is not formal verification.

This alpha has no PDD Runtime lint/CHECK/Try/replay, private managed service or private Host fallback. Do not recommend unavailable PDD commands, invent an SDK or install a private service to complete a recipe. Use the person's own agent and project tools under their actual authority and budget; do not assume agent work is free. Missing execution does not prevent prompt drafts or authorize claiming they passed.

For a complete synthetic example, read [ticket status](../../examples/ticket-status/README.md). For supported local CLI commands, read [CLI guidance](../../docs/cli.md).
