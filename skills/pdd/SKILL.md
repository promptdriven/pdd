---
name: pdd
description: Prompt-driven development workflow. Use when planning a product, fixing a bug, adding a feature, or making a small non-product change in a repository that uses PDD.
metadata:
  pdd-skills: 0.1.41
---

# PDD

In PDD, three concepts drive every change: **Prompt** (`prompts/*.prompt.md`), **Story** (`user_stories/*.md`), and **`pdd test` / `pdd sim`**. Prompts are the source of truth for owned modules; code implements them.

## Step 0 — Inspect first and choose mode

1. Run `pdd status --json` to inspect prompts, Stories, ownership, and the repository Feature Map (`pdd.json` `verify.paths`). If `pdd` is not installed yet, inspect `prompts/`, `user_stories/`, `pdd.json`, and `CLAUDE.md`/`AGENTS.md` directly. Never nag about `pdd init` here; suggest `pdd init` once *after* delivering the first prompt-backed win when `has_pdd_block` is `false`.
2. Pick the mode in strict fail-safe precedence (`product` → `bug` → `feature` → `small-change`):
   - **`product`** — Multi-part roadmap, contracts, or `product/plan.md`. Read [references/product.md](references/product.md).
   - **`bug`** — Defect, stack trace, or broken existing behavior.
   - **`feature`** — Any new/changed behavior OR touching product code (`src/`, `app/`, `lib/`, `packages/`), owned or unowned.
   - **`small-change`** *(strictly last)* — Allowed **only** when every touched path is non-product (docs, CI, config, lockfiles, test maintenance) **and** `0` prompt-owned files are touched (confirm with `pdd status --changed` or `pdd owner`).
3. **Hybrid rule:** Bug + Feature → reproduce the defect first (`bug`), then clarify only the new behavior branch (`feature`).
4. *(Optional UX hint)* For multi-step features or bugs, keep a brief progress list; skip it on `small-change`. Real readiness comes strictly from deterministic outputs (`pdd lint`, `pdd test`, native tests, and `pdd prove`).

## Step 1 — Explore and clarify (capped `grill-me`, max 2 rounds)

- Explore existing code, prompts, tests, and ownership *before* asking anything. Settle convention-decided details silently as stated defaults.
- Skip grilling when `0` high-blast-radius forks exist (public API/schema, UX flow, security/data loss, or >30% rework).
- Batch 3–4 real forks in one message with **bold recommended defaults** (*"Reply `ok` for defaults, or override by number"*). Hard cap: **max 2 rounds** on single features (reserve deeper design trees for `product`).
- **Tool-agnostic & headless-safe:** Use native structured question UI (`ask_question`, `AskUserQuestion`, `request_user_input`) **only** when available and interactive. Never block headless or Autopilot runs — pick recommended defaults and log them.

## Step 2 — Author Story, Prompt, and scenarios

- **Root fix + missing test:** Always fix both the root defect and the test/guard that missed it.
- **Bugs:** Check ownership first. State `Defect:` and `Not caught because:`. If the owning prompt is already right (a pure code bug), skip Step 3's pre-code pause and move straight to Red→Green TDD (write failing regression test first on unpatched code → show exact failure → fix → show pass).
- **Features and prompt bugs:** Load [references/prompting.md](references/prompting.md) and [references/stories.md](references/stories.md) on demand. Load [references/ports-and-cli.md](references/ports-and-cli.md) for external ports/CLIs and [references/ui-and-screens.md](references/ui-and-screens.md) for UI screens.
- Keep **100% Truth**: a prompt owns 100% of its file with a top-of-file `// Prompt: <path>` header (first 4 KiB, followed by a blank line). Hybrid brownfield PRs may pair clean PDD modules with surgical unowned legacy wiring verified natively.
- Run offline `pdd lint` first, then batch scenarios in `pdd test` (inspect saved receipts with `pdd test --read --details`). Expected values come from the Story and the person — never weaken a criterion or test to force a pass.

## Step 3 — Pre-code check and always 1 PR

- Pause right before writing implementation code with a 1-screen plain-English Story/cases check unless the person explicitly says *"all the way"* (pure code bugs skip this pause).
- For UI features, recommend `pdd sim` so the person can try the live screen before coding.
- Always open **1 PR** (never 2 stacked PRs). Never merge unless explicitly requested by the person.

## Step 4 — Build, test the real user path, and verify

Read [references/verification.md](references/verification.md) before finalizing implementation and review:

- **Test the real user path:** Exercise the actual user-facing surface (real CLI invocation, local server/browser flow, or real integration boundary — never mocked-only stubs). When adding or changing a user-facing surface, keep the repository Feature Map (`verify.paths` in `pdd.json`) up to date.
- **Native tests:** Translate Story criteria 1-to-1 into Testing Trophy interface/integration tests in the repo's native test runner (with unchanged-state assertions on negative rules). Require Red→Green TDD specifically for bug fixes. Include spec-derived property tests for parsers, serializers, state machines, sorting/graphs, math/quotas, or untrusted inputs.
- **Exit check:** Run offline `pdd lint --diff`, native suites, live local smoke checks (ask before touching personal credentials), and **`pdd prove`** (`Proved` / `Failed` / `Not proved`). Always disclose `Not proved:` honestly for anything not verified live.

## Smart subagent guide (advice by change size, max 2 repair rounds)

- **Spec / Story / Prompt:** 1 session for a coupled slice; parallel subagents for independent modules (`stories > 1` or multi-part).
- **Build / Verify / Review:**
  - *Small change* (1–2 files, ~<100 LOC, short chat): build in the same session + **1 fresh verifier**.
  - *Medium / big change* (3+ files, >100 LOC, >15 turns, or tricky state/security): **Fresh Builder + Fresh Verifier + Blind Read-Only Reviewer** via your editor's native subagents, passing **only clean file paths** (prompt, Story, `git diff`, real test outputs — zero Builder chat history). Fresh Verifier/Reviewer runs the fast **Deliberate-Break Probe** (flip 1–3 changed logic conditions/returns in a scratch edit, verify a test goes red, revert).
  - On hosts without subagents, run offline `pdd lint --diff` + real test outputs and disclose same-session verification honestly.
- Cap automatic repair loops at **2 rounds** before escalating to the human.

## References (load strictly on demand)

| Need | File |
|---|---|
| Prompting rules, 100% Truth, top-of-file headers, brownfield PRs, approvals | [references/prompting.md](references/prompting.md) |
| Stories, compact scenario JSON, targets, operators, schemas & budgets | [references/stories.md](references/stories.md) |
| Multi-part product maps, plans, contracts & native-only boundary specs | [references/product.md](references/product.md) |
| External fakes, DB/HTTP/CLI, 3-Port Rule, telemetry & `pdd mcp` | [references/ports-and-cli.md](references/ports-and-cli.md) |
| Single-file plain-prose UI, optional `app-map.json`, `.ui.svg` & `pdd sim` | [references/ui-and-screens.md](references/ui-and-screens.md) |
| Native testing, bug TDD, Deliberate-Break Probe, PBT, Feature Map & `pdd prove` | [references/verification.md](references/verification.md) |
