# PDD checkup commands — cheatsheet

Quick reference for every `pdd checkup …` subcommand: what it checks, when to run it,
and how the formalization benchmark uses it.

**Canonical experiment map:** [EXPERIMENT_DESIGN.md](EXPERIMENT_DESIGN.md)  
**Literal per-task commands:** [COMMANDS.md](COMMANDS.md)  
**One-command shell wrappers:** [scripts/cmd/README.md](scripts/cmd/README.md)

## Contents

**Phase 1 (M1) — one section per command**

- [`pdd checkup lint`](#pdd-checkup-lint) — vague terms, missing vocabulary, weak observable verbs
- [`pdd checkup contract check`](#pdd-checkup-contract-check) — `R*` rule structure, modals, waivers
- [`pdd checkup coverage`](#pdd-checkup-coverage) — rule → story → test matrix and status meanings

Each Phase 1 section includes: purpose · behavior · when to run · CLI examples · benchmark
wrapper scripts · exit codes.

**Phase 3 (M3)**

- [`pdd checkup gate`](#pdd-checkup-gate) — evidence policy (stale code, missing verify)
- [`pdd checkup drift`](#pdd-checkup-drift) — dry-run vs live regen stability
- [`pdd checkup simplify`](#pdd-checkup-simplify-optional) — optional post-gen cleanup (not in harness)

**Reference tables**

- [Command comparison](#command-comparison-at-a-glance) — reads / writes / LLM / benchmark wiring
- [Common flags](#common-flags) — `--json`, `--strict`, `--stories` vs `--stories-dir`, etc.
- [Wrapper env vars](#environment-variables-benchmark-wrappers) — `TASK`, `PROMPT_ARM`, `M1_DIR`, …
- [Typical live runtimes](#typical-live-runtimes)

---

## Where checkup fits in the workflow

The benchmark mirrors production PDD in three phases. Checkup commands appear in
**Phase 1** (before generation spend) and **Phase 3** (after code exists).

```
┌─────────────────────────────────────────────────────────────┐
│ 1. PROMPT QUALITY (before spend on generate)                │
│    lint → contract check → coverage                         │
└───────────────────────────┬─────────────────────────────────┘
                            ▼
┌─────────────────────────────────────────────────────────────┐
│ 2. GENERATE + RECORD                                        │
│    pdd generate / test / sync --evidence  (not checkup)     │
└───────────────────────────┬─────────────────────────────────┘
                            ▼
┌─────────────────────────────────────────────────────────────┐
│ 3. SHIP + STABILITY (after code exists)                     │
│    checkup gate → checkup drift (+ optional simplify)       │
└─────────────────────────────────────────────────────────────┘
```

| Phase | Benchmark | Checkup commands |
|-------|-----------|------------------|
| **1 — Prompt quality** | **M1** | `lint`, `contract check`, `coverage` |
| **2 — Generate + record** | **M2** | *(none — use `pdd generate` / `pdd test`)* |
| **3 — Ship + stability** | **M3** | `gate`, `drift`, `simplify` (optional) |

There is also a **legacy agentic** `pdd checkup <github-issue-url>` mode (full
project health check from an issue). The formalization benchmark does **not** use that
path; it uses the deterministic local subcommands below.

---

## Phase 1 — Prompt quality (M1)

Run these **before** `pdd generate`. They are read-only (except when you manually
apply suggestions). All three are deterministic and fast — suitable for CI.

**Typical order:** lint → contract check → coverage.  
**M1 automation:** `checkup_formalize.py` loops these until pass or iteration budget.

Each command below follows the same layout: **Purpose** · **What it does** · **When to use**
· **Usage** · **Benchmark wrapper** · **Exit codes**.

### `pdd checkup lint`

**Purpose:** Catch ambiguous natural language in prompts and user stories.

**What it does:**

- Scans `<contract_rules>`, `<requirements>`, `<acceptance_tests>`, and story
  acceptance criteria for **vague terms** (e.g. `valid`, `safe`, `graceful`) that
  are not defined in a `<vocabulary>` / `<glossary>` block.
- Flags rules that use vague terms but lack an **observable outcome verb**
  (`returns`, `raises`, `rejects`, `writes`, …).
- Optionally scans a `--stories` directory alongside the prompt.
- With `--llm`, adds an advisory cloud review of ambiguous prose (costs tokens;
  not required for the benchmark harness).

**When to use:** First pass on any new or edited prompt. A0 prompts usually fail
here; formalized A1 prompts should pass after vocabulary and observable rules are added.

**Usage:**

```bash
# Single prompt (benchmark A0)
pdd checkup lint benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  --stories benchmarks/formalization/corpus/tier_gold/email_validator/stories \
  --json

# Formalized A1 (M1 output)
pdd checkup lint benchmarks/formalization/experiments/latest/email_validator/A1.prompt \
  --stories benchmarks/formalization/corpus/tier_gold/email_validator/stories \
  --json
```

**Benchmark wrapper:**

```bash
TASK=email_validator PROMPT_ARM=A0 bash benchmarks/formalization/scripts/cmd/pdd_checkup_lint.sh
TASK=email_validator PROMPT_ARM=A1 M1_DIR=benchmarks/formalization/experiments/latest \
  bash benchmarks/formalization/scripts/cmd/pdd_checkup_lint.sh
```

**Exit codes:** `0` pass · `1` warnings · `2` errors (or warnings with `--strict`)

---

### `pdd checkup contract check`

**Purpose:** Validate **structure** of contract sections — not whether stories/tests
cover every rule (that is `coverage`).

**What it does:**

- Parses `<contract_rules>`, `<vocabulary>`, `<capabilities>`, `<coverage>`,
  `<waivers>`, and `<non_responsibilities>`.
- Enforces rule shape: explicit IDs (`R1`, `R-001`), **modal verbs** (`MUST`, `MUST NOT`,
  `SHALL`, …), no duplicate IDs, valid waiver references.
- Cross-checks story files (via `--stories`) for rule references that match the prompt.
- Fully deterministic — no LLM.

**Alias:** `pdd checkup contracts check` (same behavior).

**When to use:** After lint is clean enough to add structured rules. Turns prose
requirements into checkable `R*` contract lines.

**Usage:**

```bash
pdd checkup contract check benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  --stories benchmarks/formalization/corpus/tier_gold/email_validator/stories \
  --json
```

**Benchmark wrapper:**

```bash
TASK=email_validator PROMPT_ARM=A0 bash benchmarks/formalization/scripts/cmd/pdd_checkup_contract.sh
TASK=email_validator PROMPT_ARM=A1 M1_DIR=benchmarks/formalization/experiments/latest \
  bash benchmarks/formalization/scripts/cmd/pdd_checkup_contract.sh
```

**Exit codes:** `0` pass · `1` warnings only · `2` errors (or warnings with `--strict`)

---

### `pdd checkup coverage`

**Purpose:** Build a **rule → story → test** coverage matrix.

**What it does:**

- Reads `<contract_rules>` IDs from the prompt.
- Maps each rule to user stories (via `## Covers R*` in `story__*.md` files) and to
  tests (via test file references or naming conventions under `--tests-dir`).
- Reports per-rule status:

  | Status | Meaning |
  |--------|---------|
  | **checked** | Rule has both story and test coverage |
  | **story-only** | Story covers rule, no matching test |
  | **test-only** | Test references rule, no story |
  | **unchecked** | No story or test |
  | **waived** | Explicit waiver in prompt |
  | **failed** | Referenced story/test unreadable or invalid |

- Default scan dirs: `user_stories/` and `tests/` relative to cwd; override with
  `--stories-dir` and `--tests-dir`.

**When to use:** After contract rules exist and stories are written (#820 template).
Ensures every `R*` rule is traceable before generation.

**Usage:**

```bash
STORIES=benchmarks/formalization/corpus/tier_gold/email_validator/stories

pdd checkup coverage benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  --stories-dir "$STORIES" --json
```

**Benchmark wrapper:**

```bash
export STORIES_DIR=benchmarks/formalization/corpus/tier_gold/email_validator/stories
TASK=email_validator PROMPT_ARM=A0 bash benchmarks/formalization/scripts/cmd/pdd_checkup_coverage.sh
TASK=email_validator PROMPT_ARM=A1 M1_DIR=benchmarks/formalization/experiments/latest \
  bash benchmarks/formalization/scripts/cmd/pdd_checkup_coverage.sh
```

**Exit codes:** `0` all rules checked or waived · `1` gaps or read errors · `2` fatal (missing prompt)

**Note:** Flag is `--stories-dir` here; `lint` and `contract check` use `--stories`
for the same directory — the wrappers set the correct flag per command.

---

### Phase 1 — A0 vs A1 in the benchmark

| Arm | Prompt path | Expected checkup result |
|-----|-------------|-------------------------|
| **A0** | `corpus/tasks/<task>/A0.prompt` | Many lint/contract/coverage findings (control) |
| **A1** | `experiments/<m1_run>/<task>/A1.prompt` | Target: all three pass after formalization |

Tier **A** tasks (`hello_fn`, `pi_digits`) have no stories — omit `--stories` flags.  
Tier **B** gold tasks (`email_validator`, `token_bucket`, `refund_handler`) require
stories for full coverage scoring.

**M1 batch entry:**

```bash
python benchmarks/formalization/pipelines/checkup_formalize.py \
  --task email_validator --output-dir benchmarks/formalization/experiments/latest/email_validator
```

---

## Phase 3 — Ship and stability (M3)

These commands assume **M2 artifacts exist** (`pdd generate` output on disk) and
(optionally) evidence manifests from `--evidence` runs.

Same layout as Phase 1: **Purpose** · **What it does** · **When to use** · **Usage**
· **Benchmark wrapper** · **Exit codes**.

### `pdd checkup gate`

**Purpose:** CI **policy gate** on the evidence store — block merges when prompts,
generated code, or verification are out of sync.

**What it does:**

- Reads `.pdd/evidence/devunits/*.latest.json` (or a specific devunit target).
- Applies YAML policy (default built-in; override with `--policy`):

  | Policy key | Typical requirement |
  |------------|---------------------|
  | `stories_pass` | Story checks passed |
  | `verify_pass` | Sync/verify evidence present |
  | `unit_tests_pass` | Generated tests passed |
  | `generated_outputs_fresh` | Code hash matches prompt generation |
  | `no_unchecked_critical_rules` | Contract coverage complete |

- Can re-run contract coverage checks when `--stories-dir` / `--tests-dir` are passed.

**When to use:** Pre-merge or pre-release, after `pdd generate` + `pdd test` +
`pdd sync --evidence`. Not yet wired into `run_eval.sh`; manual product path.

**Usage:**

```bash
pdd checkup gate --json
pdd checkup gate --policy .pdd/policy.yml --stories-dir user_stories/ --tests-dir tests/
```

**Benchmark wrapper:** No `scripts/cmd/` wrapper yet — run from repo root after M2
evidence exists (`.pdd/evidence/devunits/` or task-specific manifests). Probed in epic
#833 scorecard; M3 harness focuses on **drift** today. See [WORKFLOW.md](WORKFLOW.md).

**Exit codes:** `0` pass · non-zero with failure list (includes suggested fix commands)

---

### `pdd checkup drift`

**Purpose:** Measure **regeneration stability** — if you run `pdd generate` again
from the same prompt, does behavior stay aligned?

**What it does:**

1. Loads baseline code from `--code-file` and prompt path from `--from-evidence`
   (evidence manifest JSON).
2. Unless `--dry-run`, regenerates code into **isolated temp directories**
   (`--runs N`, default 1) using the same prompt.
3. Compares each candidate to baseline:
   - **Public API** (function/class signatures via AST)
   - **Implementation structure** (hash / structural diff)
   - **Behavior** (re-runs tests, stories, verify when configured)
4. Enforces a cost cap (`--max-cost`, default $20 for live runs).

**Modes:**

| Mode | Flag | Cost | Use case |
|------|------|------|----------|
| **Dry-run** | `--dry-run` | Free | CI smoke — structural checks only, no regen |
| **Live** | *(default)* | LLM | Paid drift benchmark — real regen + compare |

**When to use:** After M2 completes for tier B tasks. M3 compares A0 vs A1 drift
(hypothesis: formalized prompts produce more stable regens).

**Usage:**

```bash
# Dry-run smoke (no API spend)
pdd checkup drift email_validator \
  --from-evidence benchmarks/formalization/experiments/m3_latest/email_validator/evidence_A0.json \
  --code-file benchmarks/formalization/experiments/m2_latest/email_validator/A0/generated/src/email_validator.py \
  --dry-run --json

# Live regen compare
pdd checkup drift email_validator \
  --from-evidence benchmarks/formalization/experiments/m3_latest/email_validator/evidence_A1.json \
  --code-file benchmarks/formalization/experiments/m2_latest/email_validator/A1/generated/src/email_validator.py \
  --json
```

**Benchmark wrapper** (auto-creates minimal evidence JSON if missing):

```bash
export M2_DIR=benchmarks/formalization/experiments/m2_latest
export M3_DIR=benchmarks/formalization/experiments/m3_latest
TASK=email_validator ARM=A0 MODE=dry-run bash benchmarks/formalization/scripts/cmd/pdd_drift.sh
TASK=email_validator ARM=A1 MODE=live   bash benchmarks/formalization/scripts/cmd/pdd_drift.sh
```

**M3 pipeline entry:**

```bash
python benchmarks/formalization/pipelines/run_m3_pipeline.py --replay-fixtures \
  --m1-dir benchmarks/formalization/experiments/ci_smoke --tasks email_validator
```

**Exit codes:** `0` stable · non-zero when API, implementation, or behavior drift detected

---

### `pdd checkup simplify` *(optional)*

**Purpose:** Post-generation **code cleanup** using an external simplify agent
(Claude Code `/simplify`, Codex, Gemini, OpenCode).

**What it does:**

- Without `--apply`: lists files in scope (respects `--since`, `--staged`, `--max-files`).
- With `--apply`: runs the simplify agent on selected files.
- With `--verify`: runs format/lint/typecheck/tests after edits.
- With `--evidence`: writes report under `.pdd/evidence/checkups/`.

**When to use:** Product workflow after generate — **not** in the M1/M2/M3 harness.
Useful when generated code works but is verbose or inconsistent.

**Usage:**

```bash
pdd checkup simplify src/my_module.py              # list targets
pdd checkup simplify src/ --apply --verify         # edit + verify
pdd checkup simplify --engine claude --apply --evidence
```

**Benchmark wrapper:** Not in the formalization harness (no `scripts/cmd/pdd_simplify.sh`).
Product-only path after `pdd generate`.

**Exit codes:** `0` success · non-zero on agent/verify failure (varies by `--apply` / `--verify`)

---

## Command comparison at a glance

| Command | Phase | Reads | Writes | LLM? | Benchmark |
|---------|-------|-------|--------|------|-----------|
| `checkup lint` | 1 | Prompt, stories | Nothing | Optional (`--llm`) | **M1** — score + formalize loop |
| `checkup contract check` | 1 | Prompt, stories | Nothing | No | **M1** |
| `checkup coverage` | 1 | Prompt, stories, tests | Nothing | No | **M1** |
| `checkup gate` | 3 | Evidence manifests, policy | Nothing | No | Manual / future CI |
| `checkup drift` | 3 | Evidence, baseline code | Temp regen dirs | Yes (live mode) | **M3** |
| `checkup simplify` | 3 | Source tree | Code (with `--apply`) | Yes | Not in harness |

---

## Common flags

| Flag | Commands | Effect |
|------|----------|--------|
| `--json` | All subcommands above | Machine-readable stdout for pipelines |
| `--strict` | lint, contract check | Treat warnings as errors (exit 2) |
| `--stories` | lint, contract check | User-story directory |
| `--stories-dir` | coverage, gate | User-story directory |
| `--tests-dir` | coverage, gate | Test directory override |
| `--dry-run` | drift | Skip regen; compare structure only |
| `--from-evidence` | drift | Evidence manifest path |
| `--code-file` | drift | Baseline generated `.py` path |
| `--apply` | simplify | Actually run the simplify agent |

---

## Environment variables (benchmark wrappers)

Set these before running `scripts/cmd/*.sh`:

```bash
export TASK=email_validator          # corpus task name
export PROMPT_ARM=A0                 # A0 (corpus) or A1 (M1 output) for Phase 1
export ARM=A0                        # A0 or A1 for M2/M3
export M1_DIR=benchmarks/formalization/experiments/latest
export M2_DIR=benchmarks/formalization/experiments/m2_latest
export M3_DIR=benchmarks/formalization/experiments/m3_latest
export STORIES_DIR=benchmarks/formalization/corpus/tier_gold/email_validator/stories
export MODE=dry-run                  # drift only: dry-run | live
export COMMANDS_LOG=path/to/commands.jsonl   # optional audit log
```

Resolve paths without running PDD:

```bash
python benchmarks/formalization/scripts/cmd/_resolve_paths.py m2 \
  --task email_validator --arm A0 \
  --m1-dir benchmarks/formalization/experiments/latest
```

---

## Typical live runtimes

| Command | Est. time |
|---------|-----------|
| `checkup lint` / `contract check` / `coverage` | Sub-second (deterministic) |
| `checkup drift --dry-run` | ~1–5 s |
| `checkup drift` (live) | 1–15 min (regen + tests) |
| `checkup gate` | Sub-second to few seconds |
| `checkup simplify --apply` | 2–10 min per batch |

---

## Related docs

| Doc | Role |
|-----|------|
| [EXPERIMENT_DESIGN.md](EXPERIMENT_DESIGN.md) | Phase → milestone → command map |
| [COMMANDS.md](COMMANDS.md) | Copy-paste literals for every corpus task |
| [EVALUATION.md](EVALUATION.md) | Step-by-step runbook |
| [WORKFLOW.md](WORKFLOW.md) | Product PRs mapped to checkup features |
| [scripts/cmd/README.md](scripts/cmd/README.md) | One-command shell wrappers |
| [pipelines/checkup_formalize.py](pipelines/checkup_formalize.py) | M1 checkup-driven A0→A1 loop |
