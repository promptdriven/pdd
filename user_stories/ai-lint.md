# Advisory AI prompt and Story lint

As a developer authoring PDD prompts and Stories, I want `pdd lint --ai` to run targeted read-only checklists with quote verification and a fresh second-eyes verifier, so that real contract, interface, traceability, abuse, and structural flaws are caught without noisy false alarms or merge blocks.

## Acceptance criteria

1. Running `pdd lint --ai` selects applicable checklists (`contract`, `interfaces`, `trace`, `abuse`, `design`), collects every linked neighbor, paired Story, scenario, test, and drawing without an arbitrary neighbor cap, and gives the read-only reviewer access to inspect repository files.
2. Every reported finding carries a quote verified against disk (with both sides verified for cross-file interface mismatches); unverified findings are never shown, and the output records and prints `N findings dropped (unverified quote)` whenever candidates are dropped.
3. When two or more verified candidates remain (or one or more when configured), a fresh read-only second-eyes verifier filters weak or stylistic warnings, output is capped at 7 highest-impact findings, and `--json` reports exact funnel counts (`raw_candidates`, `quote_verified`, `quote_dropped`, `verifier_kept`, `verifier_dropped`, `cap7_dropped`).
4. AI warnings are strictly advisory and exit `0` when no offline structural errors exist; offline structural errors still exit `1`.
5. Completed runs are cached by exact input hash and reused on identical inputs until any target, linked file, checklist, provider, model, or mode changes; if the AI provider fails, times out, or returns unreadable output, the command never prints a green `0 advisory findings` summary and instead emits a visible `AI lint incomplete/unavailable` warning without caching the failed run.
6. Host agents can drive the exact same pack, verification, and apply pipeline without spawning nested CLIs while keeping user-facing help limited to `pdd lint` and `pdd lint --ai` and keeping existing `--codex` and `--local` forms working.
