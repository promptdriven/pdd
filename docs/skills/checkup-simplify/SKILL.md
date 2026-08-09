# Checkup simplify (multi-provider workflow)

Use this skill when the user asks for conservative cleanup of **already changed** source files,
similar to Claude Code `/simplify`, but the active agent may be Cursor, Codex, Gemini, or OpenCode.

## When to use

- User mentions `pdd checkup simplify`, `/simplify`, or wants a **verified, conservative** cleanup
  of a bounded file set from a git diff.
- User wants parity with PDD's simplify selection rules without running the full CLI.

## When not to use

- Greenfield feature work or large refactors across the repo.
- Replacing `pdd checkup` PR review loops or contract/coverage gates.

## Workflow

1. **Establish scope** — Only files the user (or PDD) listed. Ask if the allowlist is unclear.
2. **Read the diff** — Understand what already changed; simplify *that*, do not redesign.
3. **Three passes** — Quality (dead code, clarity), efficiency (control flow), consistency (style).
4. **Edit minimally** — Prefer the candidate touching the fewest files that still improves the code.
5. **Preserve behavior** — Do not change semantics without tests; skip uncertain edits.
6. **Summarize** — List files touched and what you intentionally skipped.

## PDD parity rules (if emulating `pdd checkup simplify`)

- Reject / refuse out-of-scope file edits.
- With multiple attempts, only claim success when configured verification would pass.
- For `--staged` workflows, never overwrite unstaged content on the same paths.
- Load `[tool.pdd.checkup.simplify]` from the **repository root**, not the current subdirectory.

## Provider notes

- **Claude Code** — Production path uses `/simplify` via `pdd checkup simplify --apply`.
- **Codex / Gemini / OpenCode** — Use the matching `pdd/prompts/checkup_simplify_invoke_*_LLM.prompt`
  asset as the invocation template until PDD wires them in code.

## Reference prompts in repo

- `pdd/prompts/checkup_simplify_workflow_LLM.prompt`
- `docs/checkup_simplify_providers.md`
