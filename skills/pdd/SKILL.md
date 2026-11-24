---
name: pdd
description: Prompt-driven development workflow. Use when planning a product, fixing a bug, adding a feature, or making a small non-product change in a repository that uses PDD.
metadata:
  pdd-skills: 0.1.51
---

# PDD

In PDD, **Prompts** (`prompts/*.prompt.md`) are the source of truth for owned modules, **Stories** (`user_stories/*.md`) state observable user behavior, and deterministic harness tools (`pdd lint`, `pdd test`, direct `pdd <PROMPT.md|STORY>`, `pdd prove`) own the facts while you own the method.

## Step 0 — Orient first and pick mode

1. Run `pdd status --json` to inspect prompts, Stories, ownership, and the Feature Map (`pdd.json` `verify.paths`). If `pdd` is not installed yet, inspect `prompts/`, `user_stories/`, `pdd.json`, and `CLAUDE.md`/`AGENTS.md` directly. Suggest `pdd init` once *after* delivering the first prompt-backed win when `has_pdd_block` is `false`.
2. Pick mode in strict fail-safe order (`product` → `bug` → `feature` → `small-change`):
   - **`product`** — Multi-part roadmap, shared contracts, or `product/plan.md`. Load [references/product.md](references/product.md).
   - **`bug`** — Defect, stack trace, or broken existing product behavior/code.
   - **`feature`** — New or changed behavior, OR touching any product code (`src/`, `app/`, `lib/`, `packages/`), owned or unowned.
   - **`small-change`** *(strictly last)* — Allowed **only** when every touched path is non-product (docs, guides, specs, CI, config, lockfiles, test maintenance) **and** `0` prompt-owned or product-code files are touched (verify with `pdd status --changed` or `pdd owner`), including docs-only issues describing a defect.
3. **Hybrid rule:** Bug + Feature → reproduce and fix the defect first (`bug`), then clarify only the new behavior (`feature`).

## Step 1 — Explore and clarify consequential forks

- Read the relevant code, prompts, tests, and ownership *before* asking questions. Settle convention-decided details silently as stated defaults.
- Skip clarifying questions when there are no consequential forks (public API/schema, UX flow, security/data loss, or major rework).
- When real forks exist, batch them concisely with **bold recommended defaults** (*"Reply `ok` for defaults, or override by number"*). Keep interactive design checks brief (reserve deeper planning trees for `product`).
- **Interactive vs. headless:** Use structured question UI (`ask_question`, `AskUserQuestion`, `request_user_input`) only when available and interactive. In headless or Autopilot runs, follow Autopilot's job rules for real human blockers; for non-blocking defaults, choose the safest option and record it.

## Step 2 — Author Story, Prompt, and scenarios before code

- **Root fix + missing guard:** Always fix both the defect and the test or guard that missed it.
- **Pure code bugs:** Check ownership first and state `Defect:` and `Not caught because:`. If the owning prompt is already right (a pure code bug), skip Step 3's pre-code pause and go straight to Red→Green TDD (failing regression test on unpatched code → fix → pass).
- **Features and prompt bugs:** Load [references/prompting.md](references/prompting.md) and [references/stories.md](references/stories.md) on demand (plus [references/ports-and-cli.md](references/ports-and-cli.md) for external ports/CLIs and [references/ui-and-screens.md](references/ui-and-screens.md) for UI screens).
- Keep **100% Truth**: an owned file's `.prompt.md` covers 100% of that file with a top-of-file `// Prompt: <path>` header (first 4 KiB, followed by a blank line). Hybrid brownfield PRs may pair clean PDD modules with surgical unowned legacy wiring verified natively.
- Run offline `pdd lint` first, then `pdd test` (inspect receipts with `pdd test --read --details`). Expected values come from the Story and the person — never weaken a criterion or test to force a pass.

## Step 3 — Pre-code check, prompt approval, and 1 PR

- Before writing implementation code, pause with a 1-screen plain-English Story/cases check unless the person said *"all the way"* (pure code bugs and `small-change` skip this pause; *"all the way"* skips only the pause, not prompt approval). For UI work, recommend `pdd <PROMPT.md|STORY>` so the person can try the live screen first.
- Record the person's approval for changed prompts via `pdd approve PROMPT` (see [references/prompting.md §5](references/prompting.md#5-expected-values-approvals-and-merges)).
- Deliver **1 PR** when authorized to open a PR (never 2 stacked PRs; the only exception is a multi-part product run using `Through: prompt-pr` / `pdd product start RUN --through prompt-pr`, which explicitly stages a prompt PR first). Never merge unless explicitly requested by the person.

## Step 4 — Build, prove the real user path, and verify

Load [references/verification.md](references/verification.md) before finalizing implementation and review (and [references/formal.md](references/formal.md) only for invariant-heavy work):

- **Prove the real user path:** Exercise the real user-facing surface (CLI subprocess, local server/browser, or real integration boundary — never mocked-only stubs) and keep `pdd.json` `verify.paths` current when adding or changing a surface.
- **Native tests:** Cover every Story criterion 1-to-1 in the repo's native runner (with unchanged-state checks on negative rules). Require Red→Green TDD on bug fixes.
- **Exit check:** Run offline `pdd lint --diff`, native tests, safe live local smoke checks (ask before touching personal credentials), and **`pdd prove`** (`Proved` / `Failed` / `Not proved`). Always disclose `Not proved:` honestly.

## Independent verification (scaled to risk)

- **Trivial interactive pure-code fix** (human reviewing a tiny diff with causal `pdd prove --base ... --expect ...` Red→Green): verify in the same session.
- **Normal or high-risk changes** (behavior/prompt edits, multi-file changes, security/state logic, or any unattended run): use a **writable Fresh Verifier** (runs real checks + Deliberate-Break Probe) and a **Blind Read-Only Reviewer** (strictly read-only; receives only clean file paths and Verifier/harness outputs — zero Builder chat history). Inside Autopilot, builders skip self-spawning a verifier because Autopilot runs its own Blind Read-Only Reviewer next.
- On hosts without subagents, run `pdd lint --diff` + `pdd prove` and disclose same-session verification honestly. Escalate to the human if repair loops do not converge.

## References (load strictly on demand)

| Need | File |
|---|---|
| Prompting rules, 100% Truth, `// Prompt:` headers, `native-only` specs, approvals | [references/prompting.md](references/prompting.md) |
| Stories, compact scenario JSON, targets, operators, schemas & budgets | [references/stories.md](references/stories.md) |
| Multi-part product maps, plans, contracts & `--through prompt-pr` | [references/product.md](references/product.md) |
| External fakes, DB/HTTP/CLI, 3-Port Rule, telemetry & `pdd mcp` | [references/ports-and-cli.md](references/ports-and-cli.md) |
| Single-file plain-prose UI, optional `app-map.json`, `.ui.svg` & direct `pdd` | [references/ui-and-screens.md](references/ui-and-screens.md) |
| Native tests, Feature Map (`verify.paths`), `pdd prove` & Deliberate-Break Probe | [references/verification.md](references/verification.md) |
| Code-bound formal verification (3-tier stack, Z3 isolation & mutation control) | [references/formal.md](references/formal.md) |
