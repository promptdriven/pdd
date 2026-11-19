# Runbook: Bug Workflow, PR Fields, Checklists, and Handoffs

> Deep reference for [RUNBOOK.md](../RUNBOOK.md).

## 14. Bug workflow

1. Find the owning prompt and reproduce the issue against the CURRENT prompt with `pdd test` (save as `"before"` evidence: `pdd workflow evidence-associate RUN --workspace . --stage before --commit SHA --test PATH`, then `pdd workflow evidence RUN --summary /tmp/before.json`).
2. Put the verdict line first at the Story gate:
   - Prompt bug: `"Verdict: the bug is in the PROMPT (its check fails on the issue's case)."` → show `before ✗ → after ✓`.
   - Code-only bug: `"Verdict: the prompt is right; the bug is only in the CODE."` → unchanged prompt passes fresh `pdd test` on old & new snapshots; native regression fails on old code for the bug's reason and passes on new code (`before ✓ → after ✓`).
   - No prompt yet: say in reproduce: `"No prompt exists yet for this behavior, so the bug can only be in the code."` Verdict: `"Verdict: no prompt covers this yet; the bug can only be in the code."` Write `"before: no prompt"` in PR 1.
3. Keep PR 1 small (one prompt when possible; issue criteria only; never turn repo tests red on PR 1).

## 15. PR text

In a `pdd workflow` run, `pdd` writes the PR title, status line, and proof tables from its own saved records (`pdd test`, `pdd lint`, replay evidence §17, old-code proof, `review.md`, CI, checker verdict); `pdd workflow status N` refreshes open PRs.

### Small-change issue checklist & formal policy

Save `<run-folder>/small-change-checklist.json` (`schema_version: "pdd.small-change-checklist.v1"`, `run_id`, `source: {"kind": "git-content-v1", "sha256": "..."}`, `items: [{id, request, source, quote, state: "pending"|"done"|"excluded", evidence|exclusion}]`) preserving every requested item from the issue and trusted comments. Update `source.sha256` with `sourceFingerprint(root)` after source edits.

The structured `formal` block in `replay-evidence.json` (§17 and `docs/replay-evidence.md`) is the only formal exemption field. For documentation-only work, record `result: "not_applicable"`, a specific `scope` and `reason`, and `control_outcome: "not_run"` with normal `schema_version`, `run_id`, and current source fingerprint. A one-PR small-change requires a recorded formal result, even without a Story or Rules to check. Missing formal evidence waits before formal step completion and blocks readiness after completion; malformed, stale, failed or not_run evidence cannot say ready. Other workflows keep their step-completion policy for a missing formal block unless a known Story has `## Rules to check`.

### Agent PR fields

Pass labeled lines in your `done` summary (later lines replace earlier ones):
- `Title:` what must be true (PR 1) / what is true after merge (PR 2)
- `Problem:` wrong or missing behavior in one sentence
- `Cause:`, `Fix:`, `Result:` (PR 2, one sentence each)
- `Case:` one line per issue case (`input, today, expected` / `input, before, after, expected`)

## 22. Bounded handoffs and measurement

- Author a single coupled slice (`1–2` prompts) in one session (`0` authoring subagents). Parallelize only `3+` independent modules after locking shared contracts (`app-map.json` / interfaces).
- Give each subagent its full brief once and wait once; keep code verification, formal check, and review on fresh independent subagents.

### Autopilot core jobs

Autopilot core jobs read `autopilot-job-rules.md` from `$PDD_SKILLS/pdd-prompting/autopilot-job-rules.md`, run `$PDD_CLI` (never bare `pdd`), keep one PR per job, and obey the operator's mode (`observe` vs `auto`) and merge-check rules.
