# Workflows in depth

PDD provides one router skill, [`/pdd`](../skills/pdd/SKILL.md) (`$pdd` in Codex, `/pdd` in Claude Code), backed by focused references in `skills/pdd/references/` and headless background execution via `pdd autopilot`.

## The four modes inside `/pdd`

| Mode | Use it for |
|---|---|
| `feature` | New behavior: author or update the owning prompt, Story, tests, and implementation. |
| `bug` | Broken behavior: reproduce with a failing-first test, fix the owning prompt and code, and prove base-vs-head contrast. |
| `small-change` | Changes outside PDD (docs, guides, packages, config, CI, lockfiles, or test-only maintenance — never prompts, Stories, or product code). Product or prompt-owned code uses `bug` or `feature`. |
| `product` | Map a multi-part product, shared contracts, and staged runs (`pdd product status`, `pdd product next`, `pdd product start`). |

## Interactive workflow in your coding agent (`/pdd`)

Open Codex, Claude Code, Gemini CLI, or Antigravity in your repository and invoke `/pdd` (or `$pdd`):

```text
/pdd Add CSV export to the orders command.
/pdd Fix off-by-one pagination on empty results.
/pdd Update the README installation steps.
```

1. **Orient offline:** the agent runs `pdd status --json` (and `pdd owner PATH...` for planned files) to inspect prompts, Stories, tests, ownership headers, and the `pdd.json` `verify.paths` Feature Map.
2. **Load only the needed references on demand:**
   - [`skills/pdd/references/prompting.md`](../skills/pdd/references/prompting.md): module ownership, contracts, and prompt authoring.
   - [`skills/pdd/references/stories.md`](../skills/pdd/references/stories.md): Stories (`user_stories/*.md`) and scenario JSON (`tests/*.json`).
   - [`skills/pdd/references/ports-and-cli.md`](../skills/pdd/references/ports-and-cli.md): ports, interfaces, CLI programs, HTTP routes, and persistence.
   - [`skills/pdd/references/ui-and-screens.md`](../skills/pdd/references/ui-and-screens.md): screens, `.ui.svg` drawings, app maps, and Simulator verification.
   - [`skills/pdd/references/product.md`](../skills/pdd/references/product.md): multi-part roadmaps and shared contracts.
   - [`skills/pdd/references/verification.md`](../skills/pdd/references/verification.md): real-path verification, `pdd prove`, and independent review.
3. **Author prompt space first (`feature` and `bug`):**
   - For a `bug`, reproduce the defect first with the smallest failing test.
   - For a multi-behavior `feature`, draft `user_stories/PLAN.md` with one Story and test file per behavior.
   - Edit the owning `prompts/*.prompt.md`, `user_stories/*.md`, and `tests/*.json` before changing product code. Expected values come from the person and Stories, never from reading code output.
4. **Check and simulate:**
   - Run offline `pdd lint` (0 AI, 0 network) to catch structural, SVG, scenario, and diff problems immediately.
   - Run `pdd test --files STORY && pdd test STORY` on the PDD interpreter, or `pdd simulate STORY` (short: `pdd sim`) to try the program interactively before writing code.
5. **Approve prompts:**
   - Review prompt changes and approve with `pdd approve PROMPT` in a terminal, or reply in chat so your agent records your exact words with `pdd approve PROMPT --said - <<'PDD_SAID'`. Strict mode (`"strict_approvals": true` in root `pdd.json`) requires a person terminal.
6. **Build, prove, and review:**
   - Implement code from the approved prompts and keep `// Prompt: ...` headers or `pdd-bindings.json` current (`pdd update --check`).
   - Run `pdd prove --base origin/main` to verify offline lint, diff checks, the repository test suite, and merge-base trusted `verify.paths` recipes. For bug fixes, prove base-vs-head contrast with `pdd prove --base origin/main --test "CMD" --expect "DEFECT_TEXT"`.
   - Have a fresh subagent that did not write the code review the diff and exercise a real changed path.
   - Open a PR when asked; merge only on an explicit human request under [Prompting guide §5](../skills/pdd/references/prompting.md#5-expected-values-approvals-and-merges).

## Two ways to run PDD

| | Interactive (`/pdd` in your coding agent) | Autonomous (`pdd autopilot`) |
|---|---|---|
| Start | Invoke `/pdd` (Claude Code) or `$pdd` (Codex) in your repo | `pdd autopilot add N` and `pdd autopilot start --label pdd:autopilot` |
| Isolation | Works directly in your checkout or chosen branch | Isolated worktree, branch, and headless worker job per issue |
| Inspection | `pdd status`, `pdd lint`, `pdd update`, `pdd prove` | `pdd autopilot status`, `pdd autopilot logs [ISSUE] [-f]`, `pdd graph` |
| Approvals | Person approves prompts in chat or terminal (`pdd approve`) | Operator's `pdd autopilot start` delegates ordinary prompt approvals in `auto`/`observe` mode; `strict_approvals` still requires a person |
| PRs and merges | Agent opens PRs and merges only on explicit human request | Autopilot opens one PR per issue; in `auto` mode merges after CI, fresh review, and full test suite pass (in `observe` mode posts "would merge") |

## Headless Autopilot workflow (`pdd autopilot`)

Autopilot runs headless agent workers (`codex`, `claude`, `gemini`, or `agy`) on a 10-minute user timer (`systemd` on Linux, `LaunchAgent` on macOS). Empty ticks make zero AI calls.

1. **Preflight:** `pdd autopilot doctor` checks tools, sign-ins, permissions, GitHub `pdd.json` parity, and interpreter access read-only.
2. **Queue and execute:** Each tick claims ready opt-in issues (`pdd:autopilot` or vetted ready cards under `--intake active`), allocates an isolated worktree, and runs a headless worker following [`src/autopilot/job-rules.md`](../src/autopilot/job-rules.md).
3. **Inspect live progress:** Run `pdd autopilot status` for an overview, `pdd autopilot logs` to list active workers, or `pdd autopilot logs ISSUE -f` to follow one worker live without disturbing it.
4. **Full-suite queue:** Parallel jobs serialize heavy test suites through the shared machine queue (`pdd autopilot suite --command "npm test"`), sizing check slots to CPU and memory limits.
5. **Merge lane and verification:** Before merging in `auto` mode, Autopilot verifies green CI, a passing full test suite on the current head, verified `Runtime:` and `Evidence:` records, and a fresh independent reviewer PASS.

## Product plans (`pdd product`)

For multi-part products with shared contracts, use `/pdd` in `product` mode to plan `user_stories/PRODUCT-PLAN.md` and `contracts/`, then track and prepare runs with:

- `pdd product status [--json] [--through prompt-pr|code]`
- `pdd product next [--through prompt-pr|code]`
- `pdd product start RUN [--no-run] [--agent codex|claude|gemini|agy|ENTRY] [--through prompt-pr|code] [--base BRANCH]` (creates or reuses the scoped run issue and prints a `/pdd` handoff prompt)
- `pdd product contracts` (alias: `pdd contracts`)
- `pdd graph [--open] [--issue N]`

See [Build a whole product](build-a-whole-product.md) and [the CLI reference](cli.md).

## Where skills live

`pdd setup` installs the single `/pdd` skill globally into user skill folders without touching repository files:

| Agent | Global skills folder |
|---|---|
| Codex & Gemini CLI | `~/.agents/skills/` (also syncs existing marked `~/.codex/skills/` and `$CODEX_HOME/skills/`) |
| Claude Code | `~/.claude/skills/` or `$CLAUDE_CONFIG_DIR/skills/` (skips copying `/pdd` when the Claude Code plugin is installed, while cleaning marked retired skills) |
| Antigravity | `~/.gemini/config/skills/` (when Antigravity is detected or holds marked skills) |

Each copy managed by `pdd` carries `.pdd-skill.json`. `pdd setup`, `pdd upgrade`, and once-per-version automatic sync update older or changed marked copies and remove marked retired split skills (`pdd-autopilot`, `pdd-check`, `pdd-merge`, `pdd-setup`, `pdd-prompting`, `pdd-small-change`, `pdd-bug`, `pdd-feature`, `pdd-product`, `pdd-graph`) while preserving unmarked copies and symlinks untouched.
