# Design: Agentic Localization Degradation Under Repository Bloat

**Issue:** [#1209](https://github.com/promptdriven/pdd/issues/1209) — Research: measure agentic localization degradation under repository bloat
**Status:** Draft (pilot design) — **§10 decisions LOCKED** (Codex CLI · hand-authored repos · Linux container + OverlayFS + FUSE byte-extent reads · N=5 · 30-min timeout)
**Branch:** `research/issue-1209-repo-bloat-benchmark`
**Last updated:** 2026-06-03

---

## 1. Purpose and research question

**Research question.** Does irrelevant repository bloat increase localization cost and reduce hidden-test success for agentic code patching?

Operationalized:

> Given the same target task, same model, same verifier, and the same starting code, what happens to an agentic code-patching workflow as the surrounding repository grows with plausible-but-irrelevant files?

The benchmark holds the *task* constant and varies *only* the volume of irrelevant co-resident files, then measures whether the agent reads more, searches more, spends more tokens, edits the wrong files, or fails hidden tests as the repo grows.

This document is the design deliverable for the pilot. It specifies, in order:

1. [Benchmark architecture](#3-benchmark-architecture)
2. [Scenario format](#4-scenario-format)
3. [Distractor generation strategy](#5-distractor-generation-strategy)
4. [Instrumentation plan](#6-instrumentation-plan)
5. [Reporting format](#7-reporting-format)

### Pilot scope

- **3 frozen bug-fix scenarios** (the minimum for the issue's acceptance criteria).
- **Deterministic distractor manifests** at **1x / 5x / 20x / 50x** repo sizes, committed *before* any model run.
- **One arm only** for the first pass: `agentic_code_patch`. The optional `pdd_prompt_space` comparison arm is specified but deferred (see [§8](#8-arms)).
- **Primary outcomes:** hidden-pass-rate and token usage, plus localization-cost metrics (files read / tool calls before first edit).

### Falsification stance (pre-registered)

This is a **pilot**: its job is to estimate effect sizes and variance and to give a **descriptive/directional** read, not to declare statistical significance from `N = 5` (review #5; see [§6.5](#65-replication-trials), [§7.2](#72-trend--slope-fits)). We therefore pre-commit to **practical thresholds** rather than p-values. The "effective context window" claim is, directionally:

- **supported** if, as repo size grows, the agentic arm shows a monotone increase in localization cost (input tokens, files read, irrelevant-read ratio) crossing the pre-registered practical thresholds in [§7.5](#75-conclusion-required-pre-committed-interpretation) **and/or** a `hidden_pass_rate` drop beyond its threshold;
- **weakened** if cost and `hidden_pass_rate` are effectively flat across `S` (within the same thresholds);
- **inconclusive** if replicate dispersion is large relative to the trend.

These thresholds and interpretations are fixed *before* running models, per the issue's non-goals ("Do not tune prompts or tasks after seeing model outputs"). A formally powered, significance-tested confirmatory study is scoped as follow-up, sized from this pilot's measured variance.

---

## 2. Design principles

These constraints come directly from issue #1209's "Hold constant", "Distractor design", and "Non-goals" sections, and govern every later decision.

- **Determinism before runs.** Every scenario, distractor manifest, and verifier is content-addressed (sha256) and committed before a single model invocation. A run references manifests by hash; a changed manifest is a new experiment, never a silent edit.
- **Hidden-test isolation.** Hidden verifiers live outside the repo tree handed to the agent and are never placed in model context, never copied as distractors, and never used as grounding. Visible tests and hidden verifiers are physically separate trees.
- **Only one thing varies.** Across sizes `S ∈ {1x, 5x, 20x, 50x}` for a given scenario, the base commit, task brief, target files, allowed edit scope, model, timeout, visible tests, and hidden verifier are byte-identical. The *only* difference is the set of injected distractor files.
- **Realistic distractors.** Distractors must be plausible enough that agentic search may legitimately inspect them (same package/layer, shared vocabulary). No random filler, no synthetic noise, no files that change target behavior by merely existing, no import collisions, no leaked answers.
- **No benchmark tell.** Nothing the agent can observe inside the sandbox may reveal which files are distractors vs. target. The manifest is never mounted into the sandbox; distractors carry **no marker** — no `_distractors/` directory, no naming prefix, no tier label, no comment. They are interleaved into realistic locations and named like real code. A file may be distinguishable as irrelevant **only by genuine reasoning** (reachability, imports, test references) — never by a benchmark artifact. Distractor-vs-target classification for metrics is done **post-hoc** by the harness against the out-of-tree manifest, not by anything in the repo. *(See [§3.3](#33-determinism-and-isolation-guarantees), [§5.3](#53-sourcing-and-placing-distractor-files), [§6.2](#62-how-we-capture-it-defense-in-depth).)*
- **Hidden success is the verdict.** A visible-test pass with a hidden-verifier failure counts as a failure. Token economy is secondary to whether the agent actually fixed the bug under the hidden contract.
- **Reproducible by a third party.** The harness, raw traces, manifests, and analysis must let an external evaluator re-derive every table from raw logs.

---

## 3. Benchmark architecture

### 3.1 Component overview

```
                         ┌────────────────────────┐
                         │  scenario fixtures      │   frozen, content-addressed
                         │  (base repo + tasks)    │
                         └───────────┬────────────┘
                                     │
              ┌──────────────────────┼───────────────────────┐
              ▼                      ▼                        ▼
   ┌────────────────┐     ┌────────────────────┐    ┌──────────────────┐
   │ distractor pool │ ──▶ │ manifest builder   │ ─▶ │ size manifests   │
   │ (donor files)   │     │ (deterministic)    │    │ 1x/5x/20x/50x    │
   └────────────────┘     └────────────────────┘    └────────┬─────────┘
                                                              │
                                                              ▼
                                                    ┌──────────────────┐
                                                    │ variant builder  │  materialize a
                                                    │ (base + manifest)│  per-(scenario,size)
                                                    └────────┬─────────┘  working repo
                                                             ▼
   ┌──────────────────────────────────────────────────────────────────────┐
   │                          run harness                                   │
   │  ┌──────────────┐   ┌───────────────────┐   ┌──────────────────────┐  │
   │  │ sandbox      │ → │ agent arm runner  │ → │ instrumentation tap   │ │
   │  │ (isolated FS │   │ (agentic_code_    │   │ (fs reads, tool calls,│  │
   │  │  + git)      │   │  patch)           │   │  tokens, edits)       │  │
   │  └──────────────┘   └───────────────────┘   └──────────┬───────────┘  │
   └──────────────────────────────────────────────────────────┼───────────┘
                                                               ▼
                                              ┌────────────────────────────┐
                                              │ hidden verifier (isolated) │
                                              └──────────────┬─────────────┘
                                                             ▼
                                              ┌────────────────────────────┐
                                              │ run record (JSONL) +        │
                                              │ raw trace artifacts         │
                                              └──────────────┬─────────────┘
                                                             ▼
                                              ┌────────────────────────────┐
                                              │ analysis + report generator │
                                              └────────────────────────────┘
```

### 3.2 Stages

1. **Scenario fixtures.** A frozen base repository per scenario, pinned to a base commit, with a target task brief, target implementation file(s), visible tests, and an out-of-tree hidden verifier. ([§4](#4-scenario-format))
2. **Distractor pool + manifest builder.** A pool of donor files and a deterministic algorithm that selects/renames them into a per-(scenario, size) manifest, committed before runs. ([§5](#5-distractor-generation-strategy))
3. **Variant builder.** Given `(base repo, manifest)`, materializes a working repo by copying distractor files to their destination paths. Pure function of inputs → byte-identical output; verified by re-hashing the resulting tree.
4. **Run harness.** For each `(scenario, size, trial)`:
   - creates an isolated sandbox (fresh temp dir + `git init` at base commit),
   - launches the agent arm with the fixed task brief and the materialized repo,
   - records the instrumentation trace,
   - runs the hidden verifier against the post-edit repo,
   - writes a run record.
5. **Analysis + report generator.** Aggregates run records into per-size tables, slope fits, and a conclusion. ([§7](#7-reporting-format))

### 3.3 Determinism and isolation guarantees

- **No network for materialization.** Variant building is offline and reproducible.
- **One sandbox per run.** No state leaks between sizes or trials. Each run starts from the base commit in a fresh container with a clean Codex environment ([§8.1.1](#811-run-environment-freeze-review-3)); the agent's edits are confined to the sandbox.
- **Hidden verifier never enters the sandbox** the agent sees. It is mounted/executed from a sibling location the agent's working tree does not include.
- **Manifest never enters the sandbox.** The distractor manifest, `scenario.json`, `target_files`, and the donor pool are harness infrastructure under `research/repo-bloat-benchmark/`. The variant builder copies **only** the base repo + the materialized distractor *files* (at interleaved realistic paths) into the OverlayFS `merged` mount. The agent therefore cannot read the answer key — the FS tap confirms it can only `open()` paths that were actually mounted.
- **No on-disk distractor marker.** Distractors are placed inside real package/layer directories with realistic names; there is no `_distractors/` root or label anywhere the agent can see. The mapping of which paths are distractors lives solely in the out-of-tree manifest and is applied only during post-hoc analysis ([§6.2](#62-how-we-capture-it-defense-in-depth)).
- **Frozen-before-runs invariant** is enforced: the harness refuses to run a `(scenario, size)` whose manifest hash is not present in a committed lockfile.

### 3.4 Proposed directory layout (this branch)

```
research/repo-bloat-benchmark/
  design.md                      ← this document
  README.md                      ← branch orientation / index
  scenarios/
    <scenario_id>/
      base/                      frozen base repo (target task, visible tests)
      task.md                    issue-style task brief given to the agent
      scenario.json              scenario descriptor (see §4)
      hidden/                    hidden verifier — NOT mounted into the agent sandbox
  distractors/                   ← HARNESS-ONLY; never mounted into the agent sandbox
    pool/                        donor modules (hand-authored, deterministically sourced)
    manifests/
      <scenario_id>.<size>.json  per-size distractor manifest = the secret label key (see §5)
    manifests.lock               sha256 lockfile of all committed manifests
  harness/                       runner, variant builder, instrumentation tap, verifier driver
  reports/
    <run_id>/                    raw traces, run records (JSONL), generated tables/plots
```

The `distractors/` and `scenarios/<id>/{scenario.json,hidden}` paths above are **harness infrastructure** and are deliberately *outside* what the agent sees. At run time the variant builder produces a sandbox repo that contains only `base/` plus the materialized distractor files placed at **interleaved, realistic destinations inside the real source tree** (e.g. a `same-package` distractor lands next to the target in `src/pkg/`). The materialized repo has no `_distractors/` directory and nothing labeling a file as a distractor — that knowledge stays in the manifest.

> Note on placement: experiment infra (harness code, fixtures, manifests, raw traces) lives under a top-level `research/` tree on this branch to keep it isolated from the shipped `pdd` package. Polished write-ups intended for the product narrative can later be promoted to `docs/whitepaper_with_benchmarks/`, consistent with existing repo convention.

---

## 4. Scenario format

A **scenario** is a frozen, hidden-testable maintenance task. The pilot uses 3 bug-fix scenarios. Each scenario directory contains a base repo, a task brief, a machine-readable descriptor, and an isolated hidden verifier.

### 4.1 Selection criteria for the 3 pilot scenarios

Each scenario must:

- be a **bug fix** with a single, unambiguous correct behavior change,
- have a **localized ground-truth edit** (a known small set of target files) so "wrong-file edit" is well defined,
- ship **visible tests** that are necessary-but-not-sufficient (they constrain the change without revealing the hidden contract),
- ship a **hidden verifier** that exercises behavior the visible tests do not fully pin down,
- be **deterministic** to verify (no flakiness, no wall-clock/network dependence),
- support a base repo small enough that 50x bloat is materially larger but still runnable within the timeout.

To reduce single-codebase bias, the 3 scenarios should not all be trivial variants of one another; aim for distinct subsystems/vocabularies even if all in one language for the pilot.

### 4.2 `scenario.json` descriptor

```json
{
  "scenario_id": "off-by-one-pagination",
  "schema_version": 1,
  "language": "python",
  "base_commit": "0000000000000000000000000000000000000000",
  "base_repo_path": "scenarios/off-by-one-pagination/base",
  "base_repo_loc": 1234,
  "base_repo_sha256": "…tree hash of base/…",
  "task_brief_path": "scenarios/off-by-one-pagination/task.md",
  "bug_class": "off_by_one",
  "target_files": [
    "src/pkg/pagination.py"
  ],
  "allowed_edit_globs": [
    "src/pkg/**"
  ],
  "forbidden_paths": [
    "hidden/**"
  ],
  "visible_tests": {
    "command": "pytest -q tests/visible",
    "expected_exit_code": 0
  },
  "hidden_verifier": {
    "location": "scenarios/off-by-one-pagination/hidden",
    "command": "pytest -q hidden/",
    "mounted_into_agent_sandbox": false,
    "pass_exit_code": 0,
    "sha256": "…hidden tree hash…"
  },
  "constants_held": [
    "base_commit", "task_brief", "target_files", "allowed_edit_globs",
    "model", "timeout", "visible_tests", "hidden_verifier"
  ]
}
```

Field notes:

- `target_files` + `allowed_edit_globs` define the ground truth for non-distractor edits in `wrong_file_edit_rate`. They live only in `scenario.json` (out-of-tree) and are **not** given to the agent.
- Reading a distractor is **not** forbidden — it is exactly the irrelevant read we measure (`irrelevant_file_read_ratio`), classified post-hoc against the manifest ([§6.2](#62-how-we-capture-it-defense-in-depth)), not via any in-repo path. Editing a distractor is always a wrong-file edit, captured by `wrong_file_edit_rate`, even when its interleaved `destination_path` would otherwise match a broad `allowed_edit_globs` pattern.
- `forbidden_paths` is reserved for the hidden tree only — a defense-in-depth assertion; since the hidden tree is never mounted, any `forbidden_file_reads`/`forbidden_file_edits` count > 0 indicates an isolation bug, not agent behavior.
- `base_repo_sha256` and `hidden_verifier.sha256` are tree hashes that the harness checks before each run (freeze enforcement).
- `mounted_into_agent_sandbox: false` is asserted by the harness; a run aborts if the hidden tree is ever visible to the agent.

### 4.3 `task.md` (the brief the agent receives)

An issue-style request: symptom, reproduction, and acceptance phrased as behavior — **without** naming the fix, the target line, or the hidden assertions. The same `task.md` is used verbatim across all sizes. It must not reference distractor files or the hidden verifier.

### 4.4 Visible vs hidden split

- **Visible tests** travel inside the base repo and may be read/run by the agent. They guard against obviously-wrong edits but deliberately under-determine the contract.
- **Hidden verifier** lives in `hidden/`, never mounted into the agent's sandbox, and is the sole arbiter of success. The methodology note ([§7.4](#74-methodology-note)) records exactly what the hidden verifier checks that the visible tests do not.

---

## 5. Distractor generation strategy

Distractors inflate the repo with **plausible-but-irrelevant** files so that agentic search may legitimately, but unprofitably, inspect them. The strategy is deterministic, tiered, and recorded in a manifest committed before runs.

### 5.1 Sizing model

`S` multiplies *added distractor LOC* relative to the base repo:

| Size | Target added distractor LOC | Total repo LOC (≈) |
|------|------------------------------|--------------------|
| 1x   | 0 (control)                  | `base_loc`         |
| 5x   | `4 × base_loc`               | `5 × base_loc`     |
| 20x  | `19 × base_loc`              | `20 × base_loc`    |
| 50x  | `49 × base_loc`              | `50 × base_loc`    |

`1x` is the no-distractor control. Sizes are LOC-budget targets; the builder fills the budget greedily from the ordered candidate list (below) until within a tolerance (e.g. ±2% of target), recording the realized LOC. If a size is infeasible for a scenario (e.g. pool too small for 50x), that is documented per the acceptance criteria rather than silently skipped.

### 5.2 Distractor tiers

Tiers control how "near" a distractor is to the target, so we can later see whether near distractors do more damage than far ones.

| Tier | Description | Intended effect |
|------|-------------|-----------------|
| `same-package`   | files placed in the target's package/module dir, sharing imports and vocabulary | strongest lure for localization search |
| `same-layer`     | files in the same architectural layer (e.g. other services/handlers) | plausible but one hop away |
| `cross-cutting`  | utilities/helpers referenced by vocabulary overlap | weak lure, volume filler |

The manifest records each file's tier so the report can break `irrelevant_file_read_ratio` down by tier.

### 5.3 Sourcing and placing distractor files

Because the base repos are **hand-authored** (decision [§10](#10-locked-decisions).3), there is no upstream project to harvest distractors from, so the donor pool is **hand-authored too** — a curated `distractors/pool/` of plausible modules written in the same domain vocabulary, imports, and architectural layer as each scenario. To fill large LOC budgets (up to 50x) without resorting to "obviously synthetic filler," the pool is expanded by a **deterministic rename/templating transform** that applies content-stable identifier rewrites (module/class/function renames) so each materialized distractor has unique importable names and does not collide with the target.

**Placement (critical for validity).** Materialized distractors are written to **interleaved, realistic destinations inside the real source tree** — a `same-package` distractor lands in the *same directory* as the target (`src/pkg/<realistic_name>.py`), a `same-layer` distractor in a sibling layer dir (`src/services/...`), etc. There is **no `_distractors/` root, no tier folder, no naming convention** that an agent could filter on; on disk a distractor is indistinguishable from genuine code. The only record of which materialized paths are distractors is the out-of-tree manifest ([§5.5](#55-manifest-format)), used solely for post-hoc classification. This is what prevents the agent from reading a label and jumping straight to the real file.

This has a known honesty cost: templated siblings of an authored donor are less organically varied than real-project files, and a sufficiently sharp agent might pattern-match them as boilerplate. We mitigate with a **varied donor set + per-file identifier/domain variation** and accept the residual as a recorded methodology caveat ([§7.4](#74-methodology-note)); the [§10](#10-locked-decisions) plausibility review is the gate that keeps near-tier distractors from becoming trivially ignorable. If the pilot shows agents skip distractors regardless of size (flat `irrelevant_file_read_ratio`), that is itself reported — it would indicate the distractors, not the agent, are the limiting factor.

**Hard constraints enforced by the builder (run aborts on violation):**

- no distractor introduces a runtime import collision with `target_files`' modules,
- no distractor changes target behavior by existing (no monkeypatching, no conftest/plugin side effects, no shadowing of target import paths),
- no hidden-verifier file or its content is ever included,
- no distractor contains the hidden contract's answer (checked against a denylist of hidden-assertion tokens),
- distractors compile/import cleanly so they are not trivially ignorable as broken.

### 5.4 Determinism

Selection is seeded and order-stable: given the pool, the scenario, the size budget, and a fixed `selection_seed`, the manifest is reproducible. The builder is a pure function `(base, manifest) → tree`; the harness re-hashes the materialized tree and compares to `manifest.materialized_tree_sha256`.

### 5.5 Manifest format

Extends the issue's suggested schema with hashes and enforcement metadata:

```json
{
  "scenario_id": "off-by-one-pagination",
  "size": "20x",
  "schema_version": 1,
  "selection_seed": 1209,
  "base_repo_loc": 1234,
  "distractor_loc": 23446,
  "realized_total_loc": 24680,
  "size_loc_target": 23446,
  "size_loc_tolerance_pct": 2.0,
  "materialized_tree_sha256": "…hash of base+distractors…",
  "files": [
    {
      "source_path": "distractors/pool/billing/invoice_renderer.py",
      "destination_path": "src/pkg/ledger_formatter.py",
      "loc": 200,
      "sha256": "…content hash after rename transform…",
      "tier": "same-package",
      "rename_rule": "deterministic-id-rewrite@v1"
    }
  ]
}
```

The `destination_path` values are **interleaved into the real source tree** (note: `src/pkg/...`, the target's own directory — no `_distractors/` marker), so the on-disk repo gives the agent no tell. Every path listed under `files[]` is, by definition, a distractor — this manifest *is* the secret label key the post-hoc classifier ([§6.2](#62-how-we-capture-it-defense-in-depth)) uses to tag reads/edits as distractor vs. target. The harness must also assert no `destination_path` collides with a real base-repo file or a `target_files` path.

A `manifests.lock` aggregates the sha256 of every committed manifest; the harness checks a run's manifest against this lock before executing (freeze enforcement).

---

## 6. Instrumentation plan

Instrumentation answers: *how hard did the agent have to work to localize, and did it succeed under the hidden contract?* The pilot prioritizes **file reads**, **tool calls**, **token usage**, and **hidden pass/fail**.

### 6.1 What we capture

For every run, segmented at the **first edit** boundary (the issue's key cut point):

**Localization cost (before first edit):**

- `files_read_before_first_edit` (distinct file paths opened before the first edit; FS tap)
- `search_or_tool_calls_before_first_edit` (transcript tap)
- `bytes_read_before_first_edit` (FS tap — a read-**volume** proxy, *not* a token count; see note below)
- `input_tokens_before_first_edit` (transcript tap — the actual model token cost of localization; sum of provider-reported input tokens for requests issued before the first edit)

**Cumulative cost (whole run):**

- `input_tokens_per_run` (cumulative provider-reported input tokens)
- `max_request_input_tokens` (largest single request, provider-reported)
- `wall_clock_seconds`

> **Read volume ≠ tokens (review #1).** `bytes_read_*` comes from the FUSE filesystem tap and measures bytes the *process* read off disk. That is **not** the number of tokens the model saw: it includes repeated reads, tool/`rg`/metadata/runtime scans, cache effects, and bytes that are never surfaced to the model at all. We therefore keep two distinct families: **read-volume** metrics (`bytes_read_*`, `files_read_*`) come only from the FS tap and are reported as volume — never converted to tokens; **token** metrics (`input_tokens_*`) come *only* from the provider's `usage` accounting via the transcript tap. The two are reported side by side, never conflated.

**Targeting quality:**

- `irrelevant_file_read_ratio` = distractor reads / total file reads (distractor set resolved post-hoc from the manifest, not from any in-repo marker)
- `wrong_file_edit_rate` = edits outside `target_files` ∪ allowed scope, with manifest distractor `destination_path`s classified as wrong-file before applying `allowed_edit_globs`
- `forbidden_file_reads`, `forbidden_file_edits` = reads/edits of the hidden tree only; expected to be 0 (non-zero ⇒ isolation bug)

**Outcome:**

- `hidden_pass` (bool) — sole success criterion
- `visible_pass` (bool) — recorded but never overrides hidden
- `failure_class` (see [§6.4](#64-failure-classification))

### 6.2 How we capture it (defense in depth)

The agent arm may report some of this; we do **not** trust self-report alone. Three independent taps, reconciled in analysis:

1. **Filesystem tap (ground truth for reads + edits) — LOCKED: Linux container + OverlayFS + FUSE passthrough.** The agent runs inside a **Linux container** (Docker/Podman/Colima) so the kernel features below work regardless of the macOS dev host. Two stacked layers:
   - **OverlayFS for write isolation / edit ground truth.** `lowerdir` = the frozen materialized repo (base + distractors, read-only), `upperdir` = empty scratch, `merged` = what the agent sees and edits. Every file the agent writes lands in `upperdir`, so post-run the `upperdir` **is** the edit set (no diff heuristics) and the base stays provably pristine. This feeds `wrong_file_edit_rate` and `forbidden_file_edits`.
   - **FUSE passthrough for read ground truth.** A passthrough FUSE daemon mounts the repo and logs every `open`/`read` with `{path, offset, length, pid, ts}`, forwarding to the backing files. **Byte-extent granularity is locked** (over coarser fanotify open-events) so we capture read *volume* and exact path extents, not just which files were opened. This underpins `files_read_*`, `bytes_read_*`, `irrelevant_file_read_ratio`, and `forbidden_file_reads`, regardless of what the agent claims. **Filesystem bytes are deliberately not turned into a token metric** — see the read-volume-≠-tokens note in [§6.1](#61-what-we-capture); model token counts come exclusively from the transcript tap below.

   The container needs `/dev/fuse` + `CAP_SYS_ADMIN`. FUSE adds per-read latency, which inflates `wall_clock_seconds` (a secondary metric) but **not** the read/token *counts* that are the primary signal — flagged in the methodology note ([§7.4](#74-methodology-note)). This kernel/FS-boundary tap is chosen over an in-process shim precisely because Codex may shell out to tools (`ripgrep`, `grep`, subprocesses) whose reads a wrapper shim would miss.
2. **Tool-call / transcript tap.** The agent runner emits a structured event log of tool invocations (search, read, edit, shell) and per-request token accounting from the provider response `usage` (input tokens, output tokens, with request timestamps). **All `input_tokens_*` metrics come exclusively from this provider accounting**, split at the first-edit boundary by request timestamp — never derived from filesystem bytes. The tool-call counts yield `search_or_tool_calls_before_first_edit`. (If Codex's emitted transcript does not expose per-request `usage`, that is a blocker resolved in [§8.1](#81-agentic_code_patch-pilot-required) before runs — token metrics must have a real source.) The `pdd context-audit` token accounting (#789, pending) and `pdd.server.token_counter` utilities are reused only for the deferred prompt-space arm.
3. **Git diff tap (ground truth for edits).** Post-run `git diff` against the base commit classifies every changed path as target / in-scope / wrong-file / forbidden, giving `wrong_file_edit_rate` and `forbidden_file_edits` independent of the transcript.

The **first-edit boundary** is determined by the first write event that lands in the OverlayFS `upperdir` (tap 1), and is used to split tap-2 events into before/after. The git-diff tap (3) is retained as a redundant cross-check on the OverlayFS `upperdir`, not the primary edit source.

**Post-hoc classification (where the secret label key is applied).** The agent's sandbox carries no distractor/target labels ([§2](#2-design-principles), [§3.3](#33-determinism-and-isolation-guarantees)). Classification happens **after** the run, in the analysis step, never during it:

1. Load the run's manifest (out-of-tree) → the authoritative set of distractor `destination_path`s — plus the scenario's `target_files` and `allowed_edit_globs`. The classifier resolves `allowed_edit_globs` against the base repo's file set, not the materialized distractor-augmented tree, so broad globs cannot silently whitelist newly placed distractors.
2. For each read in the FS-tap log, tag it `target` / `base-non-target` / `distractor` by matching its path against those sets → `irrelevant_file_read_ratio` (and the per-tier breakdown).
3. For each path in the `upperdir` edit set, classify in this precedence order: hidden/forbidden path ⇒ `forbidden`; manifest `destination_path` ⇒ `wrong-file`; exact `target_files` match ⇒ `in-scope`; base-repo path matching `allowed_edit_globs` ⇒ `in-scope`; everything else ⇒ `wrong-file`. This makes interleaved same-package distractor edits wrong-file edits even when they sit under paths like `src/pkg/**`.

Because the manifest is consulted only here — by the scorer, on logs, after the agent has finished — knowing the answer key cannot influence the agent. If a future arm were ever found to expose any label to the agent, that run is void.

### 6.3 Run record schema

One JSONL line per run, plus pointers to raw trace artifacts:

```json
{
  "run_id": "off-by-one-pagination.20x.trial0.2026-06-03T00:00:00Z",
  "schema_version": 1,
  "scenario_id": "off-by-one-pagination",
  "size": "20x",
  "arm": "agentic_code_patch",
  "trial_index": 0,
  "codex_seed": null,
  "codex_cli_version": "<pinned>",
  "model": "<frozen Codex model id>",
  "reasoning_effort": "<frozen>",
  "env_fingerprint_sha256": "…hash of the frozen run-environment manifest (§8.1)…",
  "calibration_passed": true,
  "timeout_seconds": 1800,
  "manifest_sha256": "…",
  "base_repo_sha256": "…",

  "files_read_before_first_edit": 0,
  "search_or_tool_calls_before_first_edit": 0,
  "bytes_read_before_first_edit": 0,
  "input_tokens_before_first_edit": 0,
  "input_tokens_per_run": 0,
  "max_request_input_tokens": 0,
  "wall_clock_seconds": 0.0,

  "irrelevant_file_read_ratio": 0.0,
  "wrong_file_edit_rate": 0.0,
  "forbidden_file_reads": 0,
  "forbidden_file_edits": 0,

  "visible_pass": false,
  "hidden_pass": false,
  "failure_class": null,

  "repo_loc": 24680,
  "additional_distractor_loc": 23446,
  "number_of_distractor_files": 117,

  "raw_trace_paths": {
    "fs_reads": "reports/<run_id>/fs_reads.log",
    "tool_calls": "reports/<run_id>/tool_calls.jsonl",
    "git_diff": "reports/<run_id>/post_run.diff"
  }
}
```

### 6.4 Failure classification

Every non-pass run is labeled with exactly one primary `failure_class` (issue requires classifying failures, especially wrong-file reads/edits, overflow, timeout, hidden-contract misses):

- `wrong_file_edit` — edited outside allowed scope / target.
- `localization_miss` — never read the target file before exhausting attempts.
- `context_overflow` — hit a context/window limit (single-request or cumulative).
- `timeout` — exceeded the frozen timeout.
- `hidden_contract_miss` — visible tests pass but hidden verifier fails.
- `forbidden_access` — read/edited the hidden tree or distractor-prohibited path.
- `other` — with a free-text note; should be rare.

### 6.5 Replication (trials)

Each `(scenario, size)` is run over **`N = 5` replicates** (`trial_index` 0–4) — 3 scenarios × 4 sizes × 5 = **60 runs** for the pilot arm. All replicates of a cell share the identical materialized repo; only the agent's run-to-run nondeterminism varies.

**Seed vs. replicate (review #2).** Calling these "seeds" would imply a pinned, reproducible RNG. Codex CLI does **not** currently expose a documented, supported seed that makes a run bit-reproducible, so we do **not** claim reproducibility of individual trials. They are **replicates** that sample Codex's natural run-to-run variance (sampling temperature, tool-ordering, etc.), recorded as `trial_index`. The run schema keeps an optional `codex_seed` field: *if* a supported seed mechanism is confirmed ([§8.1](#81-agentic_code_patch-pilot-required)), we pin it, populate `codex_seed`, and only then describe trials as reproducible seeds. Until then, variance language throughout is about **dispersion across replicates**, not seed-controlled reproducibility.

**Sample-size honesty (review #5).** `N = 5` is a **pilot** sample chosen to surface effect sizes and variance, not to power a significance test. It is almost certainly underpowered for formal inference on a binary outcome like `hidden_pass`. The pilot is therefore **descriptive/directional** (see [§1](#falsification-stance-pre-registered), [§7.2](#72-trend--slope-fits), [§7.5](#75-conclusion-required-pre-committed-interpretation)); a power/effect-size calculation that sets `N` for a confirmatory follow-up is an explicit deliverable of the pilot, not a claim made from it.

### 6.6 Instrumentation calibration gate (review #4)

The locked FUSE/OverlayFS/transcript stack can fail silently — a missed read event, a write that bypasses `upperdir`, a misattributed first-edit boundary — and a silently-broken trace would poison every downstream metric without ever erroring. So **before any model run** (and re-run whenever the container image, FUSE/overlay config, or harness changes), the harness executes a **synthetic calibration scenario** in the *same* container, with no model involved:

1. A fixture script performs a **known set of reads** of known files through several access paths — `cat`, `sed -n`, `rg`, and a Python `open().read()` — including one distractor path and one target path, with known byte extents.
2. It performs **one known edit** (a fixed line change) to a known file.
3. The harness then **asserts the instrumentation agrees with ground truth**:
   - the FUSE log contains exactly the expected read paths and byte extents (and the distractor/target classification resolves correctly against a calibration manifest),
   - the OverlayFS `upperdir` contains exactly the one expected changed file,
   - the transcript/event tap recorded the synthetic tool calls,
   - the **first-edit boundary** lands at the known edit, correctly splitting before/after.

The run record carries `calibration_passed: true`; **a failed or skipped calibration aborts the cell** (no model tokens are spent against an uninstrumented sandbox). This converts "we believe the traces are valid" into a checked precondition, and is added to the freeze checklist ([§9](#9-pilot-execution-checklist-maps-to-acceptance-criteria)).

---

## 7. Reporting format

The report turns run records into per-size tables, trend fits, and an explicit verdict on the effective-context claim.

### 7.1 Per-size summary table (per scenario and pooled)

| Metric (point estimate ± interval over 5 replicates) | 1x | 5x | 20x | 50x |
|-----------------------------------|----|----|-----|-----|
| `hidden_pass_rate`                |    |    |     |     |
| `files_read_before_first_edit`    |    |    |     |     |
| `search_or_tool_calls_before_first_edit` | | |  |     |
| `input_tokens_per_run`            |    |    |     |     |
| `input_tokens_per_hidden_success` |    |    |     |     |
| `irrelevant_file_read_ratio`      |    |    |     |     |
| `wrong_file_edit_rate`            |    |    |     |     |
| `wall_clock_seconds`              |    |    |     |     |
| `max_request_input_tokens`        |    |    |     |     |

`input_tokens_per_hidden_success` = total input tokens spent in a cell ÷ number of hidden passes in that cell (undefined/flagged when a cell has zero hidden passes — itself a notable result).

**Interval method (review #5).** With 5 replicates per cell, intervals are **descriptive**, not inferential. For rate metrics (`hidden_pass_rate`, `wrong_file_edit_rate`) report **Wilson score intervals** (appropriate for small binomial counts) and the raw `k/5`; for count/continuous metrics report the median and min–max (or bootstrap interval), not a normal-theory CI that 5 points cannot justify. Intervals communicate dispersion; they are not significance tests.

### 7.2 Trend / slope fits

Report slopes against *additional repo LOC* (the issue's suggested form) **as descriptive effect-size estimates**, with `R²` and a bootstrap interval — explicitly *not* as significance claims:

```
input_tokens          ≈ α + β · additional_repo_loc
files_read            ≈ α + β · additional_repo_loc
irrelevant_read_ratio  by S         (table + line)
hidden_pass_rate       by S         (table + line)
```

The directional read is: a positive `β` for cost metrics whose magnitude crosses the pre-registered practical threshold ([§7.5](#75-conclusion-required-pre-committed-interpretation)), and/or a `hidden_pass_rate` decline past its threshold, is the **supporting** signal; slopes within the threshold band are the **weakening** signal; trends swamped by replicate dispersion are **inconclusive**. We report effect sizes and let the thresholds — not a p-value on N=5 — drive the verdict.

### 7.3 Plots

- `hidden_pass_rate` vs `S` (primary — the headline).
- `input_tokens_per_run` vs `additional_repo_loc` (with slope fit).
- `files_read_before_first_edit` vs `S`.
- `irrelevant_file_read_ratio` vs `S`, stacked by distractor tier.
- Failure-class breakdown per `S` (stacked bar).

### 7.4 Methodology note

A short prose section recording, per the acceptance criteria:

- what was held constant vs varied,
- how hidden-test isolation was enforced (and the harness assertion that proves the hidden tree never entered the agent sandbox),
- how distractor-label isolation was enforced — that the manifest never entered the sandbox, that materialized distractors carried no on-disk marker, and that distractor/target classification was applied post-hoc against the out-of-tree manifest,
- exactly what each hidden verifier checks beyond the visible tests,
- manifest hashes used (proving freeze-before-runs),
- the frozen Codex run-environment fingerprint ([§8.1.1](#811-run-environment-freeze-review-3)) and the calibration-gate result ([§6.6](#66-instrumentation-calibration-gate-review-4)),
- replicate count, whether trials were seed-pinned or sampled, and how dispersion was reported,
- the pre-registered practical thresholds ([§7.5](#75-conclusion-required-pre-committed-interpretation)) and confirmation they were fixed before runs,
- any infeasible `(scenario, size)` cells and why.

### 7.5 Conclusion (required, pre-committed interpretation)

**Pre-registered practical thresholds (review #5).** Fixed before any run; the verdict is read against these, not against a significance test on `N = 5`. (Magnitudes below are the design's *initial* registered values; if a variance pilot or domain rationale changes them, that change is itself committed before runs.)

| Direction | Registered practical threshold (1x → 50x) |
|-----------|-------------------------------------------|
| Localization-cost rise | ≥ **2×** in `input_tokens_per_run` **or** in `files_read_before_first_edit`, monotone non-decreasing across `S` |
| Targeting degradation | `irrelevant_file_read_ratio` rises by ≥ **0.20** absolute |
| Hidden-success drop | `hidden_pass_rate` falls by ≥ **20 percentage points** |
| "Flat" (weakening evidence) | all of the above stay within half their threshold across every step |

The report must then state, in plain language, whether the result:

- **supports** the effective-context-window claim — at least one cost/targeting threshold crossed **and/or** the hidden-success drop met, with the trend monotone in `S`;
- **weakens** it — metrics stay within the "flat" band across `S`;
- **is inconclusive** — replicate dispersion is large relative to the effect, or signals are mixed (some thresholds crossed, others not) such that no directional call is warranted at `N = 5`.

It must call out the most informative single finding — explicitly noting the case the issue flags: token usage may rise only modestly while hidden success collapses because the agent reads the wrong files or never inspects the right one. Because the pilot is descriptive, the conclusion is framed as directional evidence that motivates (and sizes) a powered confirmatory study, not as a significance verdict.

### 7.6 Follow-up issues

The report closes by filing follow-up issues for any product gaps surfaced (e.g. missing context manifests, weak token accounting, insufficient read-trace instrumentation), per the issue's suggested deliverables.

---

## 8. Arms

### 8.1 `agentic_code_patch` (pilot, required)

**LOCKED: Codex CLI (GPT), run inside the Linux container ([§6.2](#62-how-we-capture-it-defense-in-depth)).** Codex receives `task.md` and the materialized repo via the OverlayFS `merged` mount, may search/read before editing, and edits implementation code. All [§6](#6-instrumentation-plan) instrumentation applies.

#### 8.1.1 Run-environment freeze (review #3)

Filesystem isolation alone is not enough: the *agent* environment is a second source of uncontrolled variance and hidden inputs (e.g. a stray web search or a cached session could let the agent "localize" without reading the repo). Every run must execute against a **frozen, isolated, fingerprinted** Codex environment. The harness asserts each item below before the run and records the combination as `env_fingerprint_sha256` in the run record; a mismatch aborts the run.

| Control | Requirement |
|---------|-------------|
| **Codex CLI version** | Pinned to one exact build (recorded as `codex_cli_version`); no auto-update. |
| **Model + reasoning effort** | Exact model id and reasoning-effort setting frozen and identical across all cells. |
| **User config** | `--ignore-user-config` (or equivalent) so no machine-local `config.toml` leaks settings. |
| **`CODEX_HOME`** | A fresh, empty, per-run `CODEX_HOME`; never the developer's. |
| **Session persistence** | Ephemeral — no resumed/rollover sessions, no history carried between runs (`--ephemeral` / fresh state per run). |
| **Web search / network** | Explicitly set and logged. Default: **network egress disabled** in the container except the model API endpoint; web-search tool off unless a variant deliberately studies it. |
| **MCP servers / plugins / hooks** | None enabled unless part of the arm definition; the set is enumerated and frozen. |
| **Shell environment** | Sanitized allowlist of env vars; secrets limited to the model API key; no inherited dev shell. |
| **Caches** | Prompt/response/tool caches cleared or disabled so a warm cache cannot shortcut localization. |

Anything genuinely variable that cannot be eliminated (e.g. provider-side nondeterminism) is documented in the methodology note ([§7.4](#74-methodology-note)) rather than left implicit.

**Still to confirm before runs** (does not block scenario authoring): the exact pinned Codex CLI version + model id + reasoning effort; whether Codex exposes a supported seed ([§6.5](#65-replication-trials)); and whether its transcript exposes per-request `usage` for the token metrics ([§6.2](#62-how-we-capture-it-defense-in-depth)).

### 8.2 `pdd_prompt_space` (deferred comparison)

A PDD-style prompt/test/spec context rendered from a fixed manifest. The key property to validate: for a fixed task, the **resolved prompt is byte-identical across repo-size variants** unless the manifest intentionally changes — i.e. prompt-space context does not dilute with repo bloat. This arm is a sanity check, not the core question, and is out of scope for the first pass. When added, `pdd context-audit` (#789) provides its token attribution.

---

## 9. Pilot execution checklist (maps to acceptance criteria)

- [ ] 3 frozen bug-fix scenarios defined (`scenario.json` + `task.md` + base repo + hidden verifier).
- [ ] Per-scenario size variants at 1x/5x/20x/50x, or a documented infeasibility reason.
- [ ] Deterministic distractor manifests committed (+ `manifests.lock`) before any model run; distractors interleaved with no on-disk marker.
- [ ] Hidden verifiers physically separate from visible tests; harness asserts they never enter the agent sandbox.
- [ ] Distractor manifest never mounted into the sandbox; distractor/target classification applied post-hoc.
- [ ] Codex run-environment frozen + fingerprinted (CLI version, model+effort, clean `CODEX_HOME`, no user config, ephemeral session, web/MCP/hook/network/cache settings explicit) — [§8.1.1](#811-run-environment-freeze-review-3).
- [ ] Instrumentation calibration gate passes in-container before model runs — [§6.6](#66-instrumentation-calibration-gate-review-4).
- [ ] Read-volume (`bytes_read_*`, FS tap) and token (`input_tokens_*`, provider `usage`) metrics kept separate; tokens never derived from bytes.
- [ ] Pre-registered practical thresholds fixed before runs; pilot framed as descriptive/directional.
- [ ] Agentic arm records file reads, tool calls, edits, token usage, wall time, hidden pass/fail.
- [ ] Report includes per-size tables + descriptive slope/effect-size fits + a conclusion on bloat → localization cost / hidden success.
- [ ] Failures classified (esp. wrong-file, overflow, timeout, hidden-contract miss).
- [ ] Report states explicitly: supports / weakens / inconclusive for the effective-context-window claim.

## 10. Locked decisions

Frozen before any model run (pre-registration). A change to any of these is a new experiment, not an edit to this one.

| # | Decision | Locked choice | Where it lands |
|---|----------|---------------|----------------|
| 1 | Pilot arm agent/CLI + model | **Codex CLI (GPT)**, frozen environment held constant across all sizes/trials | [§8.1](#81-agentic_code_patch-pilot-required), [§8.1.1](#811-run-environment-freeze-review-3) |
| 2 | Filesystem tap | **Linux container + OverlayFS (edits) + FUSE passthrough, byte-extent reads** | [§6.2](#62-how-we-capture-it-defense-in-depth) |
| 3 | Base repo source | **Hand-authored minimal repos** (controlled, deterministic, easy hidden-test isolation) | [§4](#4-scenario-format), [§5.3](#53-sourcing-and-placing-distractor-files) |
| 4 | Replicates per `(scenario, size)` | **`N = 5`** (trials; seed-pinned only if Codex supports it) → 60 runs for the pilot arm | [§6.5](#65-replication-trials) |
| 5 | Per-run timeout | **1800 s (30 min)** — generous enough that 50x is not penalized on wall-clock alone | run config / [§6.3](#63-run-record-schema) |

### Still to confirm (Codex specifics — do not block scenario authoring)

1. **Exact Codex model id + reasoning-effort** setting to pin in the run config (must be stated in the report).
2. **Codex read/search execution path** — confirm whether Codex shells out (e.g. `ripgrep`) vs reads in-process. Either way the kernel-level FUSE tap captures it; this only affects how we *reconcile* the transcript tap against the FS tap.

### Consequence of choice #3 (hand-authored repos) — realism guardrail

Hand-authored repos trade organic realism for control, so the issue's non-goal — "no synthetic filler an agent would trivially ignore" — becomes an explicit authoring obligation, enforced by the distractor constraints in [§5.3](#53-sourcing-and-placing-distractor-files): distractors must share the target's vocabulary, imports, and architectural layer, and must compile/import cleanly. A pre-run **plausibility review** (a human spot-check that near-tier distractors are not obviously irrelevant) is added to the freeze checklist.

---

## 11. Non-goals (carried from the issue)

- Not proving "all of PDD beats all agentic coding"; this measures one effect.
- No tuning of prompts/tasks after seeing model outputs.
- Final target code and hidden tests are never used as grounding or distractors.
- A visible-test pass with hidden failure is never counted as success.
- No synthetic filler an agent would trivially ignore.

---

## References

- Issue [#1209](https://github.com/promptdriven/pdd/issues/1209) — research question, metrics, acceptance criteria, non-goals (source of truth for this design).
- Issue [#789](https://github.com/promptdriven/pdd/issues/789) — context budget audit (still **open**; the `pdd context-audit` command and its `docs/context_audit.md` are proposed in PR #1387 and **not yet merged to `main`**). Its token attribution is reused only by the deferred prompt-space arm, and only once that work lands; this pilot does not depend on it.
- `docs/pdd_vs_agentic_cli_definitive_proof_plan.md` — broader pre-registration/falsification methodology this pilot follows.
- `docs/whitepaper_with_benchmarks/` — existing benchmark report layout precedent.
