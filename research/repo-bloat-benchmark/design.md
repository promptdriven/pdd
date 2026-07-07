# Design: Agentic Localization Degradation Under Repository Bloat

**Issue:** [#1209](https://github.com/promptdriven/pdd/issues/1209) — Research: measure agentic localization degradation under repository bloat
**Status:** Draft **v2** (pilot design) — §10 decisions re-locked after review feedback (Codex CLI **unforked**, instrumented at the API boundary · **PDD as primary target repo** · subset-and-regrow + definition-driven generator modes for 50x+ · context snapshots as the primary instrument · N=5 · 30-min timeout)
**Branch:** `epic/1209-repo-bloat-v2`
**Last updated:** 2026-07-06

> **Revision note (2026-06-04).** §10 decision #3 was revised *before any model run* from "hand-authored minimal repos" to **real open-source snapshots, dependency-sliced to a minimal core with one seeded bug, regrown with the repo's own out-of-core files** (see [§5](#5-distractor-definition-and-sourcing-strategy), [§10](#10-locked-decisions)). Rationale: hand-authoring believable repos *and* a 50x distractor pool is costly and carries an "honesty cost" — synthetic siblings an agent may pattern-match as filler. Using a real repo's own files as distractors removes that cost and is intrinsically realistic. Because no runs have occurred, this is a legitimate pre-registration revision, not post-hoc tuning. Two metric families were added in the same revision: **distractor context-window penetration** ([§6.1](#61-what-we-capture)) and a **token-dose vs. fixability** axis ([§7.2](#72-trend--slope-fits)).

> **Revision note (2026-07-06, v2).** A second pre-run revision incorporating review feedback. Because no model runs have occurred, these remain legitimate pre-registration revisions, not post-hoc tuning. The changes:
>
> 1. **SWE-bench is explicitly excluded from the core experiment** ([§1.2](#12-why-swe-bench-is-excluded-from-the-core-experiment)). It was never a scenario source in v1; v2 states the exclusion and its rationale so the paper cannot drift back toward it.
> 2. **Context snapshots become the primary instrument** ([§6.2](#62-how-we-capture-it-defense-in-depth)): an API-boundary **recording proxy** captures the byte-exact composed context of every model request. The FUSE/OverlayFS filesystem tap is demoted from *required* to an *optional cross-check tier* — the design no longer relies on file-level read tracing as its main evidence, and the pilot becomes runnable without a Linux container.
> 3. **Within-run token-bloat trajectory is a new pre-registered hypothesis (H2)** ([§1.1](#11-hypotheses)): does irrelevant-context share accumulate gradually across agent iterations (tool-result accretion), or arrive as a step? Measured from the per-request snapshot series, with early/middle/late phase comparison ([§6.1](#61-what-we-capture)).
> 4. **PDD is the primary target repository** ([§4.1.0](#410-primary-upstream-repo-pdd-itself)); **Codex CLI is not forked** — it is instrumented *around*, at the API boundary, preserving external validity ([§8.1](#81-agentic_code_patch-pilot-required)).
> 5. **"Distractor file" gets a formal, checkable definition** ([§5.0](#50-what-is-a-distractor-file-formal-definition)), and the generator gains `mutate` and `template` modes derived from that definition so the dose can scale past the pool's natural size — enabling an aggressive ladder (`1x/2x/5x/10x/20x/50x`) plus a **breakdown probe** beyond 50x ([§5.1](#51-sizing-model-token-budgeted)).
> 6. **Task performance vs. distractor scale** is reported per ladder step so the degradation curve's knee is located, not just its endpoints ([§7](#7-reporting-format)).

---

## 1. Purpose and research question

**Research question.** Does irrelevant repository bloat increase localization cost and reduce hidden-test success for agentic code patching?

Operationalized:

> Given the same target task, same model, same verifier, and the same starting code, what happens to an agentic code-patching workflow as the surrounding repository grows with plausible-but-irrelevant files?

The benchmark holds the *task* constant and varies *only* the volume of irrelevant co-resident files, then measures whether the agent reads more, searches more, spends more tokens, edits the wrong files, or fails hidden tests as the repo grows. Critically, it also measures **how much of that irrelevant bulk actually crosses into the model's context window** (vs. is merely visited on disk and dropped), so the "effective context window" claim is tested against the *in-context distractor dose* in tokens — not just against on-disk repo size.

**Where the repos come from.** Rather than hand-author repos and a synthetic distractor pool, each scenario is built from a **real open-source repository** — primarily **PDD itself** ([§4.1.0](#410-primary-upstream-repo-pdd-itself)) — pinned to a commit, then *dependency-sliced* to a minimal runnable **core** into which we **seed one controlled bug**. The repo's own files that lie *outside* that core are the distractor pool; bloat is produced by deterministically **regrowing** those real files back to a token budget, extended past the pool's natural size by definition-derived `mutate`/`template` generation when a ladder step demands it ([§5](#5-distractor-definition-and-sourcing-strategy)). This makes distractors intrinsically realistic (they are the project's actual code) while keeping the manipulation fully controlled. Because public upstream code may be memorized, the design does **not** assert by default that the oracle fix is absent from training data; each seed must pass a seed-novelty audit or be reported under an explicit upstream-recall caveat.

### 1.1 Hypotheses

Three pre-registered hypotheses, each falsifiable from the pilot's own data:

- **H1 (cross-size degradation).** As the provisioned distractor dose grows along the size ladder, the agentic arm's localization cost rises (input tokens, tool calls, files consulted before the first edit) and/or `hidden_pass_rate` falls, beyond the practical thresholds in [§7.5](#75-conclusion-required-pre-committed-interpretation). The sharper form regresses success against the **realized in-context distractor dose**, not on-disk size.
- **H2 (within-run gradual bloat).** *Within a single run*, the irrelevant share of the context window is not delivered in one step: it **accumulates across agent iterations** as tool results (file reads, search output) accrete into the conversation. Concretely: `distractor_context_share` measured per request rises from the run's **early** phase to its **late** phase, and cumulative input tokens grow super-linearly in iteration index at large `S` while staying near-linear at `1x`. The alternative (a step profile — one large read dominates, after which composition is flat) is distinguishable in the same per-request series ([§6.1](#61-what-we-capture), "iteration trajectory" family). H2 matters because it decides *where* a mitigation belongs: gradual accretion points at context-management policy (compaction, result truncation, selective retention); a step profile points at retrieval policy (what to read at all).
- **H3 (breakdown location).** There exists a ladder step `S*` at which task performance stops degrading gracefully and **breaks down** — `hidden_pass_rate` at `S*` falls below half its `1x` value, or `context_overflow`/`timeout` failures become the modal failure class. The pilot's job is to locate `S*` (or establish it lies beyond 50x), which is why the ladder is dense (`1x/2x/5x/10x/20x/50x`) rather than endpoint-only, and why a breakdown probe past 50x is specified ([§5.1](#51-sizing-model-token-budgeted)).

### 1.2 Why SWE-bench is excluded from the core experiment

SWE-bench (and its Lite/Verified variants) is the field's default substrate for agentic code-patching evaluation, so its exclusion needs to be explicit and argued, not implicit:

1. **The independent variable is not controllable there.** SWE-bench instances come with their repos as-is; repo size varies *across* instances together with task difficulty, project vocabulary, test style, and era. Our design needs the same task at multiple repo sizes — a within-task manipulation SWE-bench cannot provide without rebuilding the instance, at which point none of its ecosystem value (leaderboards, comparability) survives anyway.
2. **Contamination is pervasive and unmeasurable at the instance level.** SWE-bench repos, issues, and gold patches are heavily represented in training corpora; models demonstrably solve some instances from memory. For a *causal* claim about localization cost this is fatal: a memorized fix short-circuits exactly the search behavior we are measuring. Our seeded-bug + novelty-audit procedure exists precisely to control this.
3. **Its success criterion is coarser than ours.** SWE-bench scores patch acceptance against fixed tests; it has no notion of localization cost, context composition, or read behavior. Everything this experiment adds (context snapshots, penetration metrics, iteration trajectories) would have to be bolted on anyway — the instances contribute nothing but the task, which is the cheapest part to replace.
4. **Task heterogeneity buries the signal.** With ~2k heterogeneous tasks, size effects are swamped by between-task variance; with a small curated subset, SWE-bench's statistical appeal disappears and only its contamination remains.

What survives: the **hidden-test idea** (success judged by tests the agent never sees) is adopted from SWE-bench's design ([§4.4](#44-visible-vs-hidden-split)), and SWE-bench remains a citation anchor in related work (see `research-context/literature-review.md`). It contributes **no scenarios, no repos, no tasks, and no evaluation harness** to the core experiment.

This document is the design deliverable for the pilot. It specifies, in order:

1. [Benchmark architecture](#3-benchmark-architecture)
2. [Scenario format](#4-scenario-format)
3. [Distractor sourcing strategy](#5-distractor-definition-and-sourcing-strategy)
4. [Instrumentation plan](#6-instrumentation-plan)
5. [Reporting format](#7-reporting-format)

### Pilot scope

- **3 frozen bug-fix scenarios**, each a **seeded bug in a dependency-sliced real-OSS core** (primary repo: PDD, [§4.1.0](#410-primary-upstream-repo-pdd-itself)) — the minimum for the issue's acceptance criteria.
- **Deterministic distractor manifests** on the ladder **1x / 2x / 5x / 10x / 20x / 50x** — produced by regrowing the repo's own out-of-core files to a token budget (extended by `mutate`/`template` modes where the pool runs out) — committed *before* any model run; plus a post-pilot **breakdown probe** beyond 50x if 50x has not yet located `S*` ([§1.1](#11-hypotheses) H3).
- **One arm only** for the first pass: `agentic_code_patch`. The optional `pdd_prompt_space` comparison arm is specified but deferred (see [§8](#8-arms)).
- **Primary outcomes:** hidden-pass-rate and token usage, plus localization-cost metrics (files read / tool calls before first edit), **distractor context-window penetration** (how many distractor tokens actually entered the model context, vs. were visited on disk and dropped), and the **iteration trajectory** of context composition within each run (H2).

### Falsification stance (pre-registered)

This is a **pilot**: its job is to estimate effect sizes and variance and to give a **descriptive/directional** read, not to declare statistical significance from `N = 5` (review #5; see [§6.5](#65-replication-trials), [§7.2](#72-trend--slope-fits)). We therefore pre-commit to **practical thresholds** rather than p-values. The "effective context window" claim is, directionally:

- **supported** if, as repo size grows, the agentic arm shows a monotone increase in localization cost (input tokens, files read, irrelevant-read ratio) crossing the pre-registered practical thresholds in [§7.5](#75-conclusion-required-pre-committed-interpretation) **and/or** a `hidden_pass_rate` drop beyond its threshold — and, more sharply, if `hidden_pass_rate` declines as a function of the **in-context distractor token dose** ([§7.2](#72-trend--slope-fits));
- **weakened** if cost and `hidden_pass_rate` are effectively flat across `S` (within the same thresholds), *especially* if distractor tokens enter the context but fix success does not move;
- **inconclusive** if replicate dispersion is large relative to the trend.

These thresholds and interpretations are fixed *before* running models, per the issue's non-goals ("Do not tune prompts or tasks after seeing model outputs"). A formally powered, significance-tested confirmatory study is scoped as follow-up, sized from this pilot's measured variance.

---

## 2. Design principles

These constraints come directly from issue #1209's "Hold constant", "Distractor design", and "Non-goals" sections, and govern every later decision.

- **Determinism before runs.** Every scenario, distractor manifest, and verifier is content-addressed (sha256) and committed before a single model invocation. A run references manifests by hash; a changed manifest is a new experiment, never a silent edit.
- **Hidden-test isolation.** Hidden verifiers live outside the repo tree handed to the agent and are never placed in model context, never copied as distractors, and never used as grounding. Visible tests and hidden verifiers are physically separate trees.
- **Only one thing varies.** Across sizes `S ∈ {1x, 2x, 5x, 10x, 20x, 50x}` for a given scenario, the **core** (the dependency-sliced slice the seeded bug lives in), task brief, target files, allowed edit scope, model, timeout, visible tests, and hidden verifier are byte-identical. The *only* difference is the set of regrown out-of-core distractor files.
- **Realistic distractors, by construction.** Distractors are the **repo's own files that lie outside the target's dependency closure** — real, same-project code with the project's actual vocabulary, imports, and layout. A file is a distractor *iff* it is outside that closure, decided **statically before any run** (never by what the agent did). No random filler, no synthetic noise, no templated siblings, no files that change target behavior by merely existing, no import collisions, no leaked answers. (This replaces the prior hand-authored/templated pool and its "honesty cost" — see [§5.3](#53-sourcing-and-placing-distractor-files).)
- **Contamination is measured, not wished away.** The base repo may appear in model training data, and for a public OSS snapshot the oracle patch might be equivalent to restoring upstream code the model has seen. Before runs, each seed must pass a **seed-novelty audit** showing the oracle patch is not a byte-for-byte restoration of the upstream file and is not a trivial semantic restoration of the pre-seed behavior. Seeds that cannot clear that audit remain eligible only as a pre-registered caveat/stratum for upstream-code recall, not as evidence that the fix was novel. Residual layout-familiarity and upstream-recall risks are recorded in the methodology note ([§7.4](#74-methodology-note), [§11](#11-non-goals-carried-from-the-issue)).
- **No benchmark tell.** Nothing the agent can observe inside the sandbox may reveal which files are distractors vs. target. The manifest is never mounted into the sandbox; distractors carry **no marker** — no `_distractors/` directory, no naming prefix, no tier label, no comment. They are interleaved into realistic locations and named like real code. A file may be distinguishable as irrelevant **only by genuine reasoning** (reachability, imports, test references) — never by a benchmark artifact. Distractor-vs-target classification for metrics is done **post-hoc** by the harness against the out-of-tree manifest, not by anything in the repo. *(See [§3.3](#33-determinism-and-isolation-guarantees), [§5.3](#53-sourcing-and-placing-distractor-files), [§6.2](#62-how-we-capture-it-defense-in-depth).)*
- **Hidden success is the verdict.** A visible-test pass with a hidden-verifier failure counts as a failure. Token economy is secondary to whether the agent actually fixed the bug under the hidden contract.
- **Reproducible by a third party.** The harness, raw traces, manifests, and analysis must let an external evaluator re-derive every table from raw logs.

---

## 3. Benchmark architecture

### 3.1 Component overview

```
                    ┌──────────────────────────────┐
                    │  pinned OSS snapshot          │  vendored, content-addressed
                    │  repo subsetter → core +     │  core = dep-closure + seeded bug
                    │  out-of-core distractor pool │  (HARNESS-ONLY; not mounted whole)
                    └───────────────┬──────────────┘
                                     │
              ┌──────────────────────┼───────────────────────┐
              ▼                      ▼                        ▼
   ┌────────────────┐     ┌────────────────────┐    ┌──────────────────┐
   │ distractor pool │ ──▶ │ manifest builder   │ ─▶ │ size manifests   │
   │ (snapshot ∖ core)│    │ (regrow to token   │    │ ladder 1x…50x    │
   │  real OSS files │     │  budget, seeded)   │    │ (token-budgeted) │
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

1. **Scenario fixtures (from a real OSS snapshot).** A pinned upstream repository snapshot, *dependency-sliced* to a minimal runnable **core** (the smallest slice in which the visible tests run), into which one controlled bug is **seeded**. The core is the 1x base repo; it carries the target task brief, target implementation file(s), visible tests, and an out-of-tree hidden verifier authored for the seeded bug. ([§4](#4-scenario-format))
2. **Distractor pool + manifest builder.** The pool is exactly the snapshot's files **outside the core** (real, same-project code). A deterministic, seeded algorithm selects pool files — in dependency-closed groups so each imports cleanly — into a per-(scenario, size) manifest sized to a **token budget**, committed before runs. ([§5](#5-distractor-definition-and-sourcing-strategy))
3. **Variant builder.** Given `(core, manifest)`, materializes a working repo by copying the selected real out-of-core files to their **original upstream paths**. Pure function of inputs → byte-identical output; verified by re-hashing the resulting tree.
4. **Run harness.** For each `(scenario, size, trial)`:
   - creates an isolated sandbox (fresh temp dir + `git init`, committing the materialized core+distractors as the pre-run baseline),
   - launches the agent arm with the fixed task brief and the materialized repo,
   - records the instrumentation trace,
   - runs the hidden verifier against the post-edit repo,
   - writes a run record.
5. **Analysis + report generator.** Aggregates run records into per-size tables, slope fits, and a conclusion. ([§7](#7-reporting-format))

### 3.3 Determinism and isolation guarantees

- **No network for materialization.** Variant building is offline and reproducible.
- **One sandbox per run.** No state leaks between sizes or trials. Each run starts from the pre-run baseline (materialized core+distractors) in a fresh container with a clean Codex environment ([§8.1.1](#811-run-environment-freeze-review-3)); the agent's edits are confined to the sandbox.
- **Hidden verifier never enters the sandbox** the agent sees. It is mounted/executed from a sibling location the agent's working tree does not include.
- **Manifest and full snapshot never enter the sandbox.** The distractor manifest, `scenario.json`, `target_files`, the core-membership list, and the **full OSS snapshot** are harness infrastructure under `research/repo-bloat-benchmark/`. The variant builder copies **only** the core + the selected out-of-core distractor *files* (at their original upstream paths) into the OverlayFS `merged` mount. The agent never sees the whole upstream repo at once, nor the answer key — the FS tap confirms it can only `open()` paths that were actually mounted.
- **No on-disk distractor marker.** Distractors are the project's own files at their **original upstream paths**, so on disk they are indistinguishable from core code by construction — there is no `_distractors/` root, no rename, no label anywhere the agent can see. The mapping of which paths are distractors (i.e. which are outside the core's dependency closure) lives solely in the out-of-tree manifest and is applied only during post-hoc analysis ([§6.2](#62-how-we-capture-it-defense-in-depth)).
- **Frozen-before-runs invariant** is enforced: the harness refuses to run a `(scenario, size)` whose manifest hash is not present in a committed lockfile.

### 3.4 Proposed directory layout (this branch)

```
research/repo-bloat-benchmark/
  design.md                      ← this document
  README.md                      ← branch orientation / index
  snapshots/                     ← HARNESS-ONLY; never mounted whole into the agent sandbox
    <repo>@<commit>/             vendored, pinned upstream repo (LICENSE + provenance recorded)
  scenarios/
    <scenario_id>/
      core/                      dependency-sliced minimal core + seeded bug = the 1x base repo
      core_files.txt             core membership (the dep-closure paths; everything else = pool)
      seed.patch                 the one controlled bug seeded into the core (provenance/audit)
      task.md                    issue-style task brief given to the agent
      scenario.json              scenario descriptor (see §4)
      hidden/                    hidden verifier — NOT mounted into the agent sandbox
  distractors/                   ← HARNESS-ONLY; never mounted into the agent sandbox
    manifests/
      <scenario_id>.<size>.json  per-size distractor manifest = the secret label key (see §5)
    manifests.lock               sha256 lockfile of all committed manifests
  harness/                       experiment code (implemented in this epic)
    context_snapshots/           API-boundary recording proxy, snapshot schema, session-log
                                 parser, per-iteration analyzer (§6.2 tap 1)
    distractors/                 DEFINITION.md + generator (regrow/mutate/template) +
                                 token-budgeted manifest builder (§5)
    runner/                      variant builder, run orchestration, metrics, report generator
  paper/
    paper.md                     research-paper draft (kept in sync with this design)
  reports/
    <run_id>/                    raw traces, run records (JSONL), generated tables/plots
```

The `snapshots/`, `distractors/`, and `scenarios/<id>/{scenario.json,core_files.txt,seed.patch,hidden}` paths above are **harness infrastructure**, deliberately *outside* what the agent sees. There is **no separate distractor-pool directory** — the pool is defined as `snapshot ∖ core`, and the variant builder pulls selected pool files straight from the vendored snapshot at their **original upstream paths**. At run time the sandbox repo therefore contains only `core/` plus the selected real out-of-core files sitting where upstream put them; nothing labels a file as a distractor, and the agent never sees the full snapshot. That label knowledge stays in the manifest.

> Note on placement: experiment infra (harness code, fixtures, manifests, raw traces) lives under a top-level `research/` tree on this branch to keep it isolated from the shipped `pdd` package. Polished write-ups intended for the product narrative can later be promoted to `docs/whitepaper_with_benchmarks/`, consistent with existing repo convention.

---

## 4. Scenario format

A **scenario** is a frozen, hidden-testable maintenance task built from a real OSS repo. The pilot uses 3 bug-fix scenarios. Each scenario directory contains a dependency-sliced **core** (the 1x base repo, with one seeded bug), a task brief, a machine-readable descriptor, and an isolated hidden verifier.

### 4.1.0 Primary upstream repo: PDD itself

The review feedback proposed two candidate substrates: fork Codex (the agent) or use PDD (the repo). These answer different needs — forking Codex is an *instrumentation* question (rejected in [§8.1](#81-agentic_code_patch-pilot-required): we instrument at the API boundary instead), while PDD-as-target is a *scenario-substrate* question, adopted here.

**Decision.** The pilot's scenarios are dependency-sliced cores of the **PDD repository itself** (`github.com/promptdriven/pdd`, pinned commit recorded per scenario). At least 2 of the 3 pilot scenarios come from distinct PDD subsystems (e.g. CLI command dispatch vs. LLM invocation vs. template preprocessing); the third may come from a second, unaffiliated OSS repo as an external-validity check if time allows.

Why PDD satisfies the §4.1 criteria better than an arbitrary OSS repo:

- **We control the ground truth.** The core/distractor boundary, the seeded bug, and the hidden verifier are auditable by the people who wrote the code. The main threat to the [§4.1.2](#412-variantoracle-equivalence-gate-pre-run) oracle gate — a "distractor" that is secretly load-bearing (dynamic import, plugin discovery, config side effect) — is far easier to catch in a codebase we maintain.
- **Right size.** `pdd/` is a mid-size production package (hundreds of modules across CLI, server, LLM-invocation, and template subsystems) — large enough that `regrow` reaches high ladder steps before generator modes must take over, small enough that dependency-sliced cores stay runnable inside the timeout.
- **License/provenance is trivial** — vendoring a pinned snapshot of our own repo raises no redistribution questions.
- **Offline-runnable tests** for the sliceable subsystems (pure-Python units under pytest), satisfying the determinism requirement.
- **Dogfooding payoff.** If bloat sensitivity is real, observing it on PDD's own codebase makes the product follow-ups (context audits, context manifests, prompt-owned module boundaries) directly actionable rather than analogical.

The known cost is **contamination**: PDD is public on GitHub and plausibly present in training data — but that is true of any real OSS repo, and the [§4.1.1](#411-subsetting--seeding-procedure-deterministic-pre-run) seed-novelty audit plus seeded (never historical) bugs are the existing controls. One PDD-specific caveat goes in the methodology note: the agent under test may have seen PDD's layout, and a familiarity effect would *reduce* measured localization cost at all sizes — biasing **against** H1, i.e. in the conservative direction.

### 4.1 Upstream-repo selection criteria

Each scenario starts from a pinned upstream repository chosen so that:

- it has a **permissive, redistribution-compatible license** (e.g. MIT/BSD/Apache-2.0) — recorded with provenance so the vendored snapshot can live in this branch;
- it is **buildable and test-runnable fully offline** (no network/service deps at test time), so runs are deterministic and the [§8.1.1](#811-run-environment-freeze-review-3) network lockdown holds;
- it is **large enough** that regrowing its own out-of-core files reaches the 50x token budget, yet a minimal core stays small enough to run inside the timeout;
- it is **not so canonical** that its structure is trivially memorized (prefer mid-popularity / recent projects); contamination of *layout* is a recorded caveat, and contamination of the *fix* is handled by the seed-novelty audit below.

To reduce single-codebase bias, the 3 scenarios should draw on **distinct repos / subsystems / vocabularies** (one language is fine for the pilot).

### 4.1.1 Subsetting + seeding procedure (deterministic, pre-run)

For each chosen repo, the harness derives the scenario as a pure, recorded transform:

1. **Pick a target site** — a file/function whose behavior is under-covered by the upstream visible tests (so a hidden verifier can pin down what they miss).
2. **Seed one controlled bug** at that site (`seed.patch`) — a single, unambiguous behavior defect.
3. **Compute the minimal core** — the dependency closure required for the relevant visible tests to run: start from `{target, its tests}`, add imports/fixtures until the visible suite executes, stop. `core_files.txt` records membership. This core is the 1x base repo.
4. **Author the hidden verifier** for the seeded bug, exercising behavior the visible tests do not fully pin down; it lives out-of-tree (`hidden/`).
5. **Define the distractor pool** as `snapshot ∖ core`. Every file outside the core is, by construction, a real same-project distractor ([§5](#5-distractor-definition-and-sourcing-strategy)).
6. **Run the seed-novelty audit** before accepting the scenario:
   - byte-compare the oracle-fixed target file(s) against the pinned upstream file(s); a byte-for-byte restoration fails the novelty claim;
   - review the oracle patch for semantic restoration of upstream behavior (for example, simply undoing the seeded hunk with no new logic); if it restores upstream semantics, record the scenario as an upstream-recall stratum or replace the seed;
   - commit `seed_novelty.md` with the audit result, reviewer, oracle patch hash, upstream target hash, and final classification (`novel`, `upstream_recall_caveat`, or `rejected`).

A scenario must verify **deterministically** (no flakiness, wall-clock, or network dependence) and have a **localized ground-truth edit** (the seeded target file(s)) so "wrong-file edit" is well defined.

### 4.1.2 Variant/oracle equivalence gate (pre-run)

Subsetting from visible tests and then regrowing files at original paths can accidentally change behavior across sizes via hidden-verifier dependencies, dynamic imports, package discovery, plugins/config, optional dependencies, or import shadowing. Therefore every materialized variant must pass an **oracle equivalence gate** before any model run.

For each `(scenario, size)` variant (every ladder step `1x`…`50x`) under one fixed dependency environment, the harness records:

- baseline visible-test result and baseline hidden-verifier result on the seeded bug;
- oracle-fixed visible-test result and oracle-fixed hidden-verifier result;
- dependency/runtime fingerprint used for both visible and hidden verification;
- import/module resolution diff against the `1x` variant for target and verifier entrypoints.

The required invariant is: baseline outcomes match the registered scenario expectation for every size, and the oracle fix passes visible + hidden verification for every size. Any hidden-verifier support files, runtime dependencies, fixtures, config, plugin metadata, or optional dependencies needed to make that invariant true are part of the invariant core or harness support, never the size-varying distractor pool. A variant that changes package discovery/import shadowing or verifier behavior is invalid until the core/pool boundary is repaired and all manifests are regenerated before runs.

### 4.2 `scenario.json` descriptor

```json
{
  "scenario_id": "off-by-one-pagination",
  "schema_version": 1,
  "language": "python",
  "upstream": {
    "repo": "github.com/example-org/example-proj",
    "commit": "0000000000000000000000000000000000000000",
    "license": "MIT",
    "snapshot_path": "snapshots/example-proj@0000000",
    "snapshot_sha256": "…tree hash of vendored snapshot…"
  },
  "core_path": "scenarios/off-by-one-pagination/core",
  "core_files_path": "scenarios/off-by-one-pagination/core_files.txt",
  "core_loc": 1234,
  "core_sha256": "…tree hash of core/ (with seed applied)…",
  "seed": {
    "patch_path": "scenarios/off-by-one-pagination/seed.patch",
    "target_site": "src/pkg/pagination.py:slice_page",
    "bug_class": "off_by_one"
  },
  "task_brief_path": "scenarios/off-by-one-pagination/task.md",
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
    "core_sha256", "seed", "task_brief", "target_files", "allowed_edit_globs",
    "model", "timeout", "visible_tests", "hidden_verifier"
  ]
}
```

Field notes:

- `upstream` records provenance + license so the vendored snapshot is auditable and redistribution is clean; `snapshot_sha256` pins exactly which upstream bytes the pool was drawn from.
- `core_files_path` is the dependency-closure membership list; any mounted file **not** in it is a distractor by definition (the secret label key the post-hoc classifier applies, [§6.2](#62-how-we-capture-it-defense-in-depth)).
- `target_files` + `allowed_edit_globs` define the ground truth for non-distractor edits in `wrong_file_edit_rate`. They live only in `scenario.json` (out-of-tree) and are **not** given to the agent.
- Reading a distractor is **not** forbidden — it is exactly the irrelevant read we measure (`irrelevant_file_read_ratio`), classified post-hoc against the core membership + manifest ([§6.2](#62-how-we-capture-it-defense-in-depth)), not via any in-repo path. Editing a distractor (any out-of-core file) is always a wrong-file edit, captured by `wrong_file_edit_rate`, even when its real upstream path would otherwise match a broad `allowed_edit_globs` pattern.
- `forbidden_paths` is reserved for the hidden tree only — a defense-in-depth assertion; since the hidden tree is never mounted, any `forbidden_file_reads`/`forbidden_file_edits` count > 0 indicates an isolation bug, not agent behavior.
- `core_sha256` and `hidden_verifier.sha256` are tree hashes that the harness checks before each run (freeze enforcement).
- `mounted_into_agent_sandbox: false` is asserted by the harness; a run aborts if the hidden tree is ever visible to the agent.

### 4.3 `task.md` (the brief the agent receives)

An issue-style request: symptom, reproduction, and acceptance phrased as behavior — **without** naming the fix, the target line, or the hidden assertions. The same `task.md` is used verbatim across all sizes. It must not reference distractor files or the hidden verifier.

### 4.4 Visible vs hidden split

- **Visible tests** are the upstream project's own tests for the sliced area; they travel inside the core and may be read/run by the agent. They guard against obviously-wrong edits but deliberately under-determine the seeded-bug contract.
- **Hidden verifier** lives in `hidden/`, never mounted into the agent's sandbox, and is the sole arbiter of success. The methodology note ([§7.4](#74-methodology-note)) records exactly what the hidden verifier checks that the visible tests do not.

---

## 5. Distractor definition and sourcing strategy

The default distractor source is unchanged from v1: the upstream repo's **own files that lie outside the core's dependency closure** — real, plausible-but-irrelevant code that agentic search may legitimately, but unprofitably, inspect, **regrown** around the minimal core. v2 adds what the feedback asked for: a **formal, checkable definition** of *distractor file*, and **generator modes derived from that definition** so the dose can scale past the pool's natural size (50x and beyond). Selection remains deterministic, tiered, and recorded in a manifest committed before runs.

### 5.0 What is a "distractor file"? (formal definition)

A file `D` is a **distractor** for a scenario `(core, task, visible_tests, hidden_verifier)` iff **all** of the following hold:

1. **Structural irrelevance.** `D ∉ closure(core)`: no core file imports, includes, or loads `D` (statically decidable **before** any run), and `D` is not among `target_files`.
2. **Behavior neutrality.** Materializing or removing `D` changes no visible-test outcome and no hidden-verifier outcome — enforced by the [§4.1.2](#412-variantoracle-equivalence-gate-pre-run) oracle equivalence gate, plus static exclusion of files with ambient side effects (`conftest.py`, pytest plugins, `sitecustomize`, import-path shadowing).
3. **Plausibility.** `D` is written in the project's language and idiom, imports cleanly within its own admission group, and would not read as filler to a reviewer who knows the project. Operationalized: same language as the core; parses; identifier-vocabulary overlap with the core at or above a recorded floor. Verbatim project files satisfy this by construction.
4. **No leakage.** `D` contains no hidden-verifier content, no oracle-patch content, and no string on the hidden-assertion denylist.
5. **No tell.** `D` carries no marker of distractor status — in path, name, comment, or content (§2 "No benchmark tell").

Conditions 1, 2, 4, 5 are machine-checked by the generator for **every** admitted file; condition 3 is machine-checked where possible (language, parse, vocabulary floor). The definition is deliberately source-agnostic: any file that meets it is admissible, which is what lets the three generator modes below share one contract — and one test suite.

### 5.0.1 Generator modes (one definition, three sources)

Real pools are finite: `snapshot ∖ core` can run out below the 50x budget, and the H3 breakdown probe needs more still. v2 defines three deterministic modes, all validated against §5.0, ordered by realism:

| Mode | Source | Realism | Role |
|------|--------|---------|------|
| `regrow` | verbatim out-of-core project files at their original upstream paths | organic (highest) | default; fills every budget it can |
| `mutate` | derived variants of pool files: seeded identifier/docstring renames from a recorded vocabulary map, semantics-preserving reordering — placed at plausible sibling paths that do not collide with any real path | high | extends the pool once `regrow` is exhausted |
| `template` | synthetic modules from parameterized skeletons (service/handler/util shapes) filled with vocabulary harvested from the core (identifier n-grams, domain nouns), seeded RNG | bounded | last resort for extreme ladder steps / the breakdown probe |

Mode policy is fixed and recorded, never chosen per run: `regrow` until exhausted, then `mutate`, then `template`. The manifest records each file's `mode` alongside its `tier`, and the report breaks read and penetration metrics down **by mode** — if agents ignore `template` files but read `regrow` files, that heterogeneity is measured rather than hidden. This handles the v1 "honesty cost" objection to synthetic files honestly: realism becomes a *measured axis* (per-mode read/penetration rates) instead of a reason to cap the experiment at the pool's natural size.

### 5.1 Sizing model (token-budgeted)

`S` multiplies *added distractor tokens* relative to the core. Tokens are the primary dose unit (LOC recorded alongside):

| Size | Target added distractor tokens | Total repo tokens (≈) |
|------|--------------------------------|-----------------------|
| 1x   | 0 (control)                    | `core_tokens`         |
| 2x   | `1 × core_tokens`              | `2 × core_tokens`     |
| 5x   | `4 × core_tokens`              | `5 × core_tokens`     |
| 10x  | `9 × core_tokens`              | `10 × core_tokens`    |
| 20x  | `19 × core_tokens`             | `20 × core_tokens`    |
| 50x  | `49 × core_tokens`             | `50 × core_tokens`    |

The v2 ladder is denser than the issue's suggested `1x/5x/20x/50x` because H3 asks *where* performance breaks down, and a knee between 5x and 50x is invisible with endpoint-heavy spacing. The four original steps are a subset of the ladder, so the issue's acceptance criteria remain satisfied verbatim.

**Two distinct "token" notions — do not conflate.** The budget above is **on-disk token size** of distractor files under a fixed, recorded tokenizer — the dose we *provision*. It is *not* the same as the **in-context distractor tokens** that actually reach the model window, which are measured per-run from the transcript ([§6.1](#61-what-we-capture)) and are the real test of the effective-context claim ([§7.2](#72-trend--slope-fits)). The pilot reports outcomes against **both**: provisioned dose (`S`) and realized in-context dose.

`1x` is the no-distractor control (core only). Sizes are token-budget targets; the builder fills the budget greedily from the ordered candidate list ([§5.3](#53-sourcing-and-placing-distractor-files)) until within a tolerance (e.g. ±2% of target), recording realized tokens and LOC. If a size is infeasible under `regrow` alone, the builder falls through to `mutate` then `template` per the §5.0.1 mode policy; a size is documented as infeasible only if the full mode cascade cannot fill it (per the acceptance criteria, never silently skipped).

**Breakdown probe (H3).** If 50x has not located `S*` — `hidden_pass_rate` at 50x still above half its 1x value, and `context_overflow`/`timeout` not the modal failure class — the ladder is extended post-pilot by doubling (100x, 200x, …) with the same manifest machinery, `mutate`/`template` supplying the dose beyond the real pool. Probe steps are pre-registered the same way (manifests committed before runs); they are an *extension* of the experiment, not a redesign.

### 5.2 Distractor tiers

Tiers control how "near" a distractor is to the target, so we can later see whether near distractors do more damage than far ones. With real OSS files, tier falls out of the repo's **actual layout** relative to the target site (assigned deterministically by the subsetter, not hand-placed):

| Tier | Description (assigned from real upstream location) | Intended effect |
|------|-----------------------------------------------------|-----------------|
| `same-package`   | out-of-core files living in the target's own package/module dir, sharing its imports and vocabulary | strongest lure for localization search |
| `same-layer`     | out-of-core files in the same architectural layer (e.g. sibling services/handlers) | plausible but one hop away |
| `cross-cutting`  | utilities/helpers/other subsystems linked only by vocabulary overlap | weak lure, volume filler |

The manifest records each file's tier so the report can break `irrelevant_file_read_ratio` (and in-context penetration) down by tier.

### 5.3 Sourcing and placing distractor files

The pool is **exactly `snapshot ∖ core`** — every file in the pinned upstream repo that the dependency-slicer left out of the core. These are real, organically-written project files, so there is **no synthetic filler, no templating, no rename transform, and no "honesty cost"** to mitigate: a distractor is genuine same-project code, in the project's own vocabulary, at its own path. This is the central payoff of the subset-and-regrow switch ([§10](#10-locked-decisions).3).

**Selection (deterministic, dependency-closed).** To hit a size budget the builder walks an ordered candidate list (seeded; ordered by tier then a stable hash of the upstream path) and admits files in **dependency-closed groups** within the pool: if a chosen file imports other pool files, those are admitted with it, so every materialized distractor still imports cleanly and is not trivially ignorable as broken. The core's dependency closure guarantees the core never imports a pool file, so admitting or omitting pool files cannot change the target's behavior.

**Placement.** Distractors are written at their **original upstream paths** — a `same-package` distractor sits in the target's own directory because that is literally where upstream keeps it. There is no `_distractors/` root, no tier folder, no naming convention to filter on; on disk a distractor is indistinguishable from core code. The only record of which mounted paths are distractors is "not listed in `core_files.txt`," captured by the out-of-tree manifest ([§5.5](#55-manifest-format)) for post-hoc classification only.

If the pilot shows agents skip distractors regardless of size (flat `irrelevant_file_read_ratio` *and* flat in-context penetration), that is itself reported — it would indicate the agent's search is robust to bloat, not that the distractors are weak (they are real project files).

**Hard constraints enforced by the builder (run aborts on violation):**

- every admitted distractor is genuinely outside the core (not in `core_files.txt`),
- no distractor is imported by the core (guaranteed by the dependency closure; re-asserted),
- no distractor changes target behavior by existing (no `conftest`/plugin/`sitecustomize` side effects, no shadowing of a core import path) — upstream test-config files outside the core are excluded from the pool,
- no hidden-verifier file or its content is ever included,
- no distractor contains the seeded contract's answer (checked against a denylist of hidden-assertion tokens — cheap insurance alongside the seed-novelty audit),
- admitted distractors import cleanly (dependency-closed grouping) so none is trivially ignorable as broken,
- every admitted file — any mode — passes the §5.0 definition checks; `mutate`/`template` files additionally pass the plausibility floor (parse + vocabulary overlap) and are recorded with their `mode` and generation seed.

### 5.4 Determinism

Selection is seeded and order-stable: given the pinned snapshot, the core, the size (token) budget, and a fixed `selection_seed`, the manifest is reproducible. The builder is a pure function `(core, manifest) → tree`; the harness re-hashes the materialized tree and compares to `manifest.materialized_tree_sha256`.

### 5.5 Manifest format

Extends the issue's suggested schema with hashes and enforcement metadata:

```json
{
  "scenario_id": "off-by-one-pagination",
  "size": "20x",
  "schema_version": 2,
  "selection_seed": 1209,
  "upstream_snapshot_sha256": "…hash of the vendored snapshot the pool is drawn from…",
  "tokenizer": "<pinned tokenizer id used for the dose budget>",
  "core_tokens": 5120,
  "core_loc": 1234,
  "distractor_tokens_on_disk": 97280,
  "distractor_loc": 23446,
  "realized_total_tokens": 102400,
  "realized_total_loc": 24680,
  "size_token_target": 97280,
  "size_token_tolerance_pct": 2.0,
  "materialized_tree_sha256": "…hash of core+distractors…",
  "files": [
    {
      "upstream_path": "src/pkg/ledger_formatter.py",
      "tokens": 820,
      "loc": 200,
      "sha256": "…content hash of the verbatim upstream bytes…",
      "tier": "same-package",
      "import_group": "g3"
    }
  ]
}
```

The `upstream_path` values are the files' **real upstream locations** (note: `src/pkg/...`, the target's own directory — no `_distractors/` marker, no rename), so the on-disk repo gives the agent no tell, and `sha256` is over the **verbatim upstream bytes** (provenance-checkable against `upstream_snapshot_sha256`). `import_group` records the dependency-closed admission group ([§5.3](#53-sourcing-and-placing-distractor-files)). Every path listed under `files[]` is, by definition, a distractor (outside `core_files.txt`) — this manifest *is* the secret label key the post-hoc classifier ([§6.2](#62-how-we-capture-it-defense-in-depth)) uses to tag reads/edits as distractor vs. core. The harness must also assert no `upstream_path` collides with a core file or a `target_files` path (impossible by construction, but re-checked).

A `manifests.lock` aggregates the sha256 of every committed manifest; the harness checks a run's manifest against this lock before executing (freeze enforcement).

---

## 6. Instrumentation plan

Instrumentation answers: *how hard did the agent have to work to localize, what actually occupied its context window while it worked, and did it succeed under the hidden contract?* The pilot prioritizes **context snapshots** (the composed model requests themselves), **token usage**, **tool calls**, and **hidden pass/fail**. File-level read tracing is a supporting, optional tier in v2: evidence about the context window comes from the window itself, not only from disk activity.

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
- `wrong_file_edit_rate` = edits outside `target_files` ∪ allowed scope, with manifest distractor `upstream_path`s (any out-of-core file) classified as wrong-file before applying `allowed_edit_globs`
- `forbidden_file_reads`, `forbidden_file_edits` = reads/edits of the hidden tree only; expected to be 0 (non-zero ⇒ isolation bug)

**Context-window penetration (how much distractor bulk actually entered the model window):**

This family answers the question the FS tap *cannot*: of all the distractor material, what fraction the agent **pulled into its context window** versus merely **visited on disk and dropped**. It is the direct mechanism behind the "effective context window" claim.

- `distractor_context_tokens_total` — repeat-counted input tokens attributable to **distractor-file content surfaced into model requests** (tool/read results that became part of a subsequent prompt), summed over the run; also split `_before_first_edit`. If the same snippet appears in three requests, it counts three times because it occupied three request windows.
- `distractor_context_share` = `distractor_context_tokens_total / input_tokens_per_run` — the fraction of the model's *consumed* context that was irrelevant bulk (repeat-counted window occupancy by distractors).
- `distractor_unique_tokens_entered_context` — de-duplicated distractor tokens whose file spans entered context at least once, capped per file/span so repeated resurfacing cannot inflate coverage.
- `distractor_pool_coverage` = `distractor_unique_tokens_entered_context / distractor_tokens_on_disk` — the fraction of the *provisioned* distractor pool ([§5.1](#51-sizing-model-token-budgeted)) that crossed into the window at least once. This is a unique-coverage metric and is bounded to `[0, 1]`.
- `distractor_files_entered_context` — distinct distractor files whose content reached a model request.
- `distractor_files_visited_not_contextualized` — distractor files **opened/searched on disk (FS tap) but whose content never entered a model request** — the "visited but not added to context" set. (= FS-distractor-read set ∖ context-entered set; a non-trivial value here means the agent's search tooling shielded the window from bulk it physically touched.)

> **Three layers, deliberately kept separate.** On-disk *dose* (`distractor_tokens_on_disk`, §5) ⊇ *visited* (FS tap, `irrelevant_file_read_ratio`) ⊇ *in-context* (transcript attribution, this family). Each inclusion can leak — an agent can provision-but-not-read, read-but-not-surface, or surface-into-context. The pilot reports all three so a flat outcome can be attributed to the right layer.

**Iteration trajectory (H2 — the within-run token-bloat profile):**

Computed from the per-request snapshot series (tap 1 in §6.2), indexed by request ordinal `i = 1..n`:

- `input_tokens[i]` and `context_growth[i] = input_tokens[i] − input_tokens[i−1]` — the per-iteration context series
- `distractor_context_share[i]` — per-request irrelevant occupancy (the §6.1 penetration attribution applied per request)
- `phase_stats` — the series split into **early / middle / late** thirds by request ordinal, with per-phase medians of both series; H2 compares late vs. early
- `growth_shape` — classification of the cumulative-context curve per run: `gradual` (no single request contributes > 30 % of final context; positive early→late trend), `step` (one request's growth dominates), `plateau` (context stops growing — compaction/truncation visible), `sawtooth` (drops from compaction mid-run)
- `largest_single_jump_share` = `max_i(context_growth[i]) / input_tokens[n]`
- `iterations_total`, `iterations_before_first_edit`

This family exists because a per-run total cannot distinguish *how* the window filled: sixty small accretions and one giant read produce the same `input_tokens_per_run` but demand different mitigations (context-management policy vs. retrieval policy). H2 is decided from this series, per [§7.5](#75-conclusion-required-pre-committed-interpretation).

**Outcome:**

- `hidden_pass` (bool) — sole success criterion
- `visible_pass` (bool) — recorded but never overrides hidden
- `failure_class` (see [§6.4](#64-failure-classification))

### 6.2 How we capture it (defense in depth)

The agent arm may report some of this; we do **not** trust self-report alone. Three independent taps, reconciled in analysis. **v2 change:** the context-snapshot tap is primary and required; the filesystem tap is an optional cross-check tier — the pilot is valid without it, and therefore runnable outside a Linux container.

1. **Context-snapshot tap (PRIMARY — ground truth for what the model saw): API-boundary recording proxy.** All of the agent's model traffic is routed through a local recording relay (base-URL override, e.g. `OPENAI_BASE_URL=http://127.0.0.1:<port>/v1`), which archives, per request: the **byte-exact request payload** — the full composed context: system/instructions, task, conversation history, tool results — the response, provider `usage` (input/output tokens), timestamps, and a request ordinal. This is a *context snapshot*: not an inference about what the model saw from disk activity, but the composed window itself.
   - **All `input_tokens_*` metrics, `max_request_input_tokens`, the penetration family, and the iteration-trajectory family come from this tap.** Attribution matches each request's surfaced content against the materialized tree + manifest (normalized-span matching), tags spans `core` / `distractor` / `hidden`(never), tokenizes distractor spans with the pinned tokenizer, and reconciles repeat-counted attribution against provider `usage` so attributed input can never exceed measured input for a request. De-duplicated span coverage per distractor file yields `distractor_unique_tokens_entered_context` and `distractor_pool_coverage`.
   - The stock CLI's own **session/rollout logs** (from the per-run `CODEX_HOME`) are parsed as a redundant cross-check: tool-call sequence and any self-reported token counts must be consistent with the proxy record; disagreement flags the run.
   - Works with the **unforked** agent binary; the same instrument serves any CLI that honors a base-URL override, which is what makes the cross-agent extension cheap.
   - *Pre-run blocker:* the pinned Codex build must honor the base-URL override for all provider traffic. Documented fallback: Codex's session transcript, iff it exposes per-request `usage` **and** tool-result content; failing both, a transport-only fork is the disclosed last resort ([§10](#10-locked-decisions), still-to-confirm #3).

2. **Filesystem tap (OPTIONAL cross-check tier — ground truth for on-disk reads + edits): Linux container + OverlayFS + FUSE passthrough.** The agent runs inside a **Linux container** (Docker/Podman/Colima) so the kernel features below work regardless of the macOS dev host. Two stacked layers:
   - **OverlayFS for write isolation / edit ground truth.** `lowerdir` = the frozen materialized repo (core + distractors, read-only), `upperdir` = empty scratch, `merged` = what the agent sees and edits. Every file the agent writes lands in `upperdir`, so post-run the `upperdir` **is** the edit set (no diff heuristics) and the core stays provably pristine. This feeds `wrong_file_edit_rate` and `forbidden_file_edits`.
   - **FUSE passthrough for read ground truth.** A passthrough FUSE daemon mounts the repo and logs every `open`/`read` with `{path, offset, length, pid, ts}`, forwarding to the backing files. **Byte-extent granularity is locked** (over coarser fanotify open-events) so we capture read *volume* and exact path extents, not just which files were opened. This underpins `files_read_*`, `bytes_read_*`, `irrelevant_file_read_ratio`, and `forbidden_file_reads`, regardless of what the agent claims. **Filesystem bytes are deliberately not turned into a token metric** — see the read-volume-≠-tokens note in [§6.1](#61-what-we-capture); model token counts come exclusively from the transcript tap below.

   The container needs `/dev/fuse` + `CAP_SYS_ADMIN`. FUSE adds per-read latency, which inflates `wall_clock_seconds` (a secondary metric) but **not** the read/token *counts* that are the primary signal — flagged in the methodology note ([§7.4](#74-methodology-note)). This kernel/FS-boundary tap is chosen over an in-process shim precisely because Codex may shell out to tools (`ripgrep`, `grep`, subprocesses) whose reads a wrapper shim would miss.
   When this tier is enabled, the "visited-but-not-contextualized" set is the FS-tap distractor-read set minus the set of distractor paths whose content appears in any request (tap 1). When it is disabled, `files_read_*`, `bytes_read_*`, `irrelevant_file_read_ratio`, `forbidden_file_reads`, and `distractor_files_visited_not_contextualized` are reported as **unavailable** — never imputed from the snapshot tap. Tool-call counts (`search_or_tool_calls_before_first_edit`) come from the snapshot tap's tool-call records and remain available either way. The merged `pdd context` audit core (PR #1387, closing #789; the `pdd.server.token_counter` utilities) is reused only for the deferred prompt-space arm.
3. **Git diff tap (ground truth for edits).** Post-run `git diff` against the pre-run baseline classifies every changed path as target / in-scope / wrong-file / forbidden, giving `wrong_file_edit_rate` and `forbidden_file_edits` independent of the transcript.

The **first-edit boundary** is determined from the snapshot series (tap 1): the first request in which the agent issues an edit/patch tool call (equivalently, the first request whose successor carries an edit-tool result). When the optional FS tier is enabled, the first OverlayFS `upperdir` write must agree with that request's timestamp — disagreement is a calibration failure, not a judgment call. The git-diff tap (3) is the primary edit ground truth when the FS tier is absent, and a redundant cross-check on `upperdir` when it is present.

**Post-hoc classification (where the secret label key is applied).** The agent's sandbox carries no distractor/target labels ([§2](#2-design-principles), [§3.3](#33-determinism-and-isolation-guarantees)). Classification happens **after** the run, in the analysis step, never during it:

1. Load the run's manifest + `core_files.txt` (out-of-tree) → the authoritative set of distractor `upstream_path`s (everything mounted but not in the core) — plus the scenario's `target_files` and `allowed_edit_globs`. The classifier resolves `allowed_edit_globs` against the **core's** file set, not the materialized distractor-augmented tree, so broad globs cannot silently whitelist regrown distractors.
2. For each read in the FS-tap log, tag it `target` / `core-non-target` / `distractor` by matching its path against those sets → `irrelevant_file_read_ratio` (and the per-tier breakdown).
3. For each path in the `upperdir` edit set, classify in this precedence order: hidden/forbidden path ⇒ `forbidden`; manifest `upstream_path` (out-of-core) ⇒ `wrong-file`; exact `target_files` match ⇒ `in-scope`; core path matching `allowed_edit_globs` ⇒ `in-scope`; everything else ⇒ `wrong-file`. This makes same-package distractor edits wrong-file edits even when they sit under paths like `src/pkg/**`.

Because the manifest is consulted only here — by the scorer, on logs, after the agent has finished — knowing the answer key cannot influence the agent. If a future arm were ever found to expose any label to the agent, that run is void.

### 6.3 Run record schema

One JSONL line per run, plus pointers to raw trace artifacts:

```json
{
  "run_id": "off-by-one-pagination.20x.trial0.2026-06-03T00:00:00Z",
  "schema_version": 2,
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
  "oracle_equivalence_passed": true,
  "timeout_seconds": 1800,
  "manifest_sha256": "…",
  "core_sha256": "…",
  "upstream_snapshot_sha256": "…",

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

  "distractor_tokens_on_disk": 97280,
  "distractor_context_tokens_total": 0,
  "distractor_context_tokens_total_before_first_edit": 0,
  "distractor_context_share": 0.0,
  "distractor_unique_tokens_entered_context": 0,
  "distractor_pool_coverage": 0.0,
  "distractor_files_entered_context": 0,
  "distractor_files_visited_not_contextualized": null,

  "iterations_total": 0,
  "iterations_before_first_edit": 0,
  "growth_shape": "gradual",
  "largest_single_jump_share": 0.0,
  "distractor_context_share_early": 0.0,
  "distractor_context_share_late": 0.0,

  "fs_tap_enabled": false,

  "visible_pass": false,
  "hidden_pass": false,
  "failure_class": null,

  "repo_loc": 24680,
  "repo_tokens": 102400,
  "additional_distractor_loc": 23446,
  "number_of_distractor_files": 117,

  "raw_trace_paths": {
    "context_snapshots": "reports/<run_id>/context_snapshots.jsonl",
    "context_payloads": "reports/<run_id>/payloads/",
    "session_log": "reports/<run_id>/codex_session.jsonl",
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

Each `(scenario, size)` is run over **`N = 5` replicates** (`trial_index` 0–4) — 3 scenarios × 6 ladder sizes × 5 = **90 runs** for the pilot arm. All replicates of a cell share the identical materialized repo; only the agent's run-to-run nondeterminism varies.

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

In v2 the calibration fixture also validates the **context-snapshot tap**: a scripted client replays a known request sequence through the recording proxy, and the harness asserts payload fidelity (byte-exact round-trip), `usage` capture, ordinal indexing, and that the first-edit boundary is detected at the scripted edit call. The FS-tap assertions above apply only when that optional tier is enabled.

The run record carries `calibration_passed: true`; **a failed or skipped calibration aborts the cell** (no model tokens are spent against an uninstrumented sandbox). This converts "we believe the traces are valid" into a checked precondition, and is added to the freeze checklist ([§9](#9-pilot-execution-checklist-maps-to-acceptance-criteria)).

---

## 7. Reporting format

The report turns run records into per-size tables, trend fits, and an explicit verdict on the effective-context claim.

### 7.1 Per-size summary table (per scenario and pooled)

| Metric (point estimate ± interval over 5 replicates) | 1x | 2x | 5x | 10x | 20x | 50x |
|-----------------------------------|----|----|----|-----|-----|-----|
| `hidden_pass_rate`                |    |    |     |     |
| `files_read_before_first_edit`    |    |    |     |     |
| `search_or_tool_calls_before_first_edit` | | |  |     |
| `input_tokens_per_run`            |    |    |     |     |
| `input_tokens_per_hidden_success` |    |    |     |     |
| `irrelevant_file_read_ratio`      |    |    |     |     |
| `distractor_context_tokens_total` |    |    |     |     |
| `distractor_context_share`        |    |    |     |     |
| `distractor_pool_coverage`        |    |    |     |     |
| `wrong_file_edit_rate`            |    |    |     |     |
| `wall_clock_seconds`              |    |    |     |     |
| `max_request_input_tokens`        |    |    |     |     |
| `iterations_total`                |    |    |     |     |
| `distractor_context_share` late − early (H2) |    |    |     |     |
| `growth_shape` modal class (H2)   |    |    |     |     |

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

**Iteration-trajectory fits (H2).** Pooled per cell from the per-request series:

```
distractor_context_share[i] ≈ α + β · i     (per run; report the median per-run β per cell —
                                             β > 0 at high S ⇒ accumulation is gradual)
growth_shape distribution by S               (gradual / step / plateau / sawtooth share per cell)
cumulative input_tokens vs. i, per S         (near-linear at 1x vs. super-linear at high S)
```

**Token-dose fits (the sharpened effective-context test).** Beyond the on-disk-size axis above, regress outcomes against the **realized in-context distractor dose** — the tokens that actually occupied the window — since that is the mechanism the claim names:

```
hidden_pass_rate      ≈ α + β · distractor_context_tokens_total     (headline; expect β < 0 if claim holds)
files_read_before_edit ≈ α + β · distractor_context_tokens_total
distractor_pool_coverage  by S    (does more on-disk bloat actually reach the window at least once, or does search shield it?)
```

The directional read is: a positive `β` for cost metrics whose magnitude crosses the pre-registered practical threshold ([§7.5](#75-conclusion-required-pre-committed-interpretation)), and/or a `hidden_pass_rate` decline past its threshold (against either `S` *or* in-context dose), is the **supporting** signal; slopes within the threshold band are the **weakening** signal; trends swamped by replicate dispersion are **inconclusive**. The penetration axis also disambiguates a flat result: if `hidden_pass_rate` is flat *because* `distractor_pool_coverage` stays near zero (the agent never let the bulk into its window), that is a different finding from bloat entering the window without hurting success. We report effect sizes and let the thresholds — not a p-value on N=5 — drive the verdict.

### 7.3 Plots

- `hidden_pass_rate` vs `S` (primary — the headline).
- `hidden_pass_rate` vs `distractor_context_tokens_total` (token-dose headline — the sharpened effective-context view).
- `input_tokens_per_run` vs `additional_repo_loc` (with slope fit).
- `files_read_before_first_edit` vs `S`.
- `irrelevant_file_read_ratio` vs `S`, stacked by distractor tier.
- `distractor_pool_coverage` and `distractor_context_share` vs `S`, stacked by distractor tier (how much provisioned bulk actually reaches the window, and from which tiers).
- Failure-class breakdown per `S` (stacked bar).
- `distractor_context_share[i]` vs. iteration ordinal `i`, one line per size (the H2 headline).
- Cumulative `input_tokens` vs. iteration ordinal, per size (gradual vs. step visible directly).
- `hidden_pass_rate` vs. ladder step with the located knee `S*` marked (H3), including breakdown-probe steps if run.

### 7.4 Methodology note

A short prose section recording, per the acceptance criteria:

- what was held constant vs varied,
- **upstream provenance** per scenario — repo, pinned commit, license, `snapshot_sha256` — and the `seed.patch` that introduced the bug, plus `seed_novelty.md` classifying whether the oracle fix is novel or an upstream-recall caveat,
- **how the core was derived** — the dependency-closure procedure ([§4.1.1](#411-subsetting--seeding-procedure-deterministic-pre-run)) and the resulting `core_files.txt`, which defines distractor membership,
- the **contamination caveat** — the base repo may appear in training data; the seed-novelty audit reports whether the oracle fix could be upstream-code recall, and residual layout-familiarity is a reason a flat localization curve is interpreted cautiously,
- how hidden-test isolation was enforced (and the harness assertion that proves the hidden tree never entered the agent sandbox),
- how distractor-label isolation was enforced — that the manifest and full snapshot never entered the sandbox, that distractors were real files at their real upstream paths with no on-disk marker, and that distractor/core classification was applied post-hoc against `core_files.txt` + the manifest,
- the **two token notions** kept separate (provisioned on-disk dose vs. realized in-context dose) and how in-context penetration was attributed to distractor paths and reconciled against provider `usage` ([§6.2](#62-how-we-capture-it-defense-in-depth)),
- exactly what each hidden verifier checks beyond the visible tests,
- manifest + snapshot hashes used (proving freeze-before-runs),
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
| Context-window penetration | `distractor_context_share` rises by ≥ **0.20** absolute *and* `distractor_pool_coverage` is non-trivial (≥ **0.10**) at 50x — i.e. the bulk genuinely reaches the window rather than being shielded by search |
| Hidden-success drop | `hidden_pass_rate` falls by ≥ **20 percentage points** across `S`, **or** a negative `hidden_pass_rate`-vs-`distractor_context_tokens_total` slope whose 1x→50x fitted drop is ≥ 20 pp |
| Within-run accumulation (H2) | median late-phase per-request `distractor_context_share` exceeds the early phase by ≥ **0.15** absolute at ≥ 20x, **and** `growth_shape = gradual` is the modal class at ≥ 20x. Step/plateau modal ⇒ H2 rejected in favor of the step profile (a finding, not a null) |
| Breakdown located (H3) | some ladder step `S*` has `hidden_pass_rate(S*) ≤ 0.5 × hidden_pass_rate(1x)`, or `context_overflow` + `timeout` jointly modal at `S*`; if no step qualifies through 50x, report "S* > 50x" and trigger the §5.1 breakdown probe |
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

**LOCKED: stock Codex CLI (GPT), unforked, with all model traffic routed through the recording proxy ([§6.2](#62-how-we-capture-it-defense-in-depth)).** Codex receives `task.md` and the materialized repo (via the OverlayFS `merged` mount when the optional FS tier is enabled; a plain isolated working copy otherwise), may search/read before editing, and edits implementation code. All [§6](#6-instrumentation-plan) instrumentation applies.

**Why not fork Codex?** The review feedback offered a fork as one instrumentation route. Rejected, for three reasons. (1) *External validity:* a fork is a different agent — any patch near context assembly or tool plumbing risks perturbing the behavior under measurement, and the claim of record must be about the stock CLI users actually run. (2) *Maintenance:* a fork must chase upstream releases for the confirmatory study and diverges silently. (3) *Sufficiency:* everything an in-process hook would reveal about the context window is already serialized, in full, at the API boundary, where the recording proxy captures it. The proxy is also agent-agnostic — the pre-registered cross-agent extension (e.g. Claude Code) reuses the same instrument unchanged. A transport-only fork (base-URL plumbing, never context assembly) remains the disclosed last resort if the pinned build cannot route through the proxy ([§10](#10-locked-decisions), still-to-confirm #3).

Codex is treated as the pilot's local agentic-search arm, but its exact read/search execution path remains a pre-run calibration item rather than a locked design fact. Current OpenAI docs establish that Codex can read/edit local files, run model-generated shell commands under sandboxing, use web search modes, connect MCP tools, and expose `apply_patch` hook matching; they do not establish a supported "no precomputed index" guarantee or the exact `grep`/`ripgrep`/`find`/`cat` command path. The companion background section ([`agentic_cli_search.md`](./agentic_cli_search.md), issue [#1430](https://github.com/promptdriven/pdd/issues/1430)) documents this distinction, places Codex provisionally in a cross-agent taxonomy, and explains why this single-agent lock is one point in a retrieval-mechanism space worth a pre-registered cross-agent extension (e.g., Claude Code as a second agentic-search agent; Aider/Cursor as index/embedding comparators).

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
| **Model traffic routing** | All provider traffic egresses **only** via the recording proxy (base-URL override); the proxy is the sole permitted network path to the model API, making the snapshot record complete by construction. |

Anything genuinely variable that cannot be eliminated (e.g. provider-side nondeterminism) is documented in the methodology note ([§7.4](#74-methodology-note)) rather than left implicit.

**Still to confirm before runs** (does not block scenario authoring): the exact pinned Codex CLI version + model id + reasoning effort; whether Codex exposes a supported seed ([§6.5](#65-replication-trials)); and that the pinned build honors a base-URL override so the recording proxy captures **all** requests ([§6.2](#62-how-we-capture-it-defense-in-depth)) — with the CLI's own session transcript as the documented fallback source.

> **Status (v2.1, 2026-07-07)**: confirmed against `codex-cli 0.142.4` by the zero-billing routing probe (`harness/runner/codex_probe.py`, record in `harness/runner/CODEX_PIN.md`): the build routes **all** provider traffic through the configured base URL (Responses wire only — `wire_api = "chat"` is rejected), no sampling seed is exposed (→ §6.5 fallback: N=5 unseeded trials), and tool execution is local. The fallback chain was not needed. The **numeric values** of model id / reasoning effort / context window remain a human pre-registration choice (see `CODEX_PIN.md`).

### 8.2 `pdd_prompt_space` (deferred comparison)

A PDD-style prompt/test/spec context rendered from a fixed manifest. The key property to validate: for a fixed task, the **resolved prompt is byte-identical across repo-size variants** unless the manifest intentionally changes — i.e. prompt-space context does not dilute with repo bloat. This arm is a sanity check, not the core question, and is out of scope for the first pass. When added, the merged `pdd context` audit (PR #1387, closing #789) provides its token attribution.

---

## 9. Pilot execution checklist (maps to acceptance criteria)

- [ ] Scenario substrate frozen per [§4.1.0](#410-primary-upstream-repo-pdd-itself): the pilot's scenarios are dependency-sliced cores of **PDD itself** @ a pinned commit (≥2 of 3 from distinct PDD subsystems, offline-runnable); the third **may** come from a second, unaffiliated OSS repo as an external-validity check if time allows — only then do third-party license/provenance/LICENSE recording obligations apply. *(v2.1 wording fix, 2026-07-07: an earlier draft of this line said "3 upstream OSS repos", contradicting §4.1.0 — §4.1.0 is the locked decision.)*
- [ ] 3 frozen bug-fix scenarios defined (`scenario.json` + `task.md` + dependency-sliced `core/` + `core_files.txt` + `seed.patch` + hidden verifier + `seed_novelty.md`); oracle fix classified as novel or upstream-recall caveat before runs.
- [ ] Per-scenario size variants at 1x/2x/5x/10x/20x/50x by **token budget**, or a documented infeasibility reason.
- [ ] Oracle equivalence gate passes for every materialized `(scenario, size)`: registered baseline outcomes match and the oracle fix passes visible + hidden verification under one fixed dependency environment.
- [ ] Deterministic distractor manifests committed (+ `manifests.lock`) before any model run; distractors = real out-of-core files at upstream paths, admitted in dependency-closed groups, no on-disk marker.
- [ ] Hidden verifiers physically separate from visible tests; harness asserts they never enter the agent sandbox.
- [ ] Distractor manifest + full snapshot never mounted into the sandbox; distractor/core classification applied post-hoc against `core_files.txt`.
- [ ] Context-window penetration captured (`distractor_context_tokens_total`, `distractor_context_share`, `distractor_unique_tokens_entered_context`, `distractor_pool_coverage`, visited-but-not-contextualized) and reconciled against provider `usage`.
- [ ] Context snapshots captured for **every** model request via the recording proxy; per-request payloads archived; provider `usage` recorded per request.
- [ ] Iteration-trajectory family computed (per-request share series, early/middle/late phase stats, growth-shape classification) — H2.
- [ ] FS tap explicitly recorded as enabled/disabled per run (`fs_tap_enabled`); when disabled, read-volume metrics reported as unavailable, never imputed.
- [ ] SWE-bench absent from scenarios, repos, tasks, and harness (related-work citation only) — §1.2.
- [ ] Codex run-environment frozen + fingerprinted (CLI version, model+effort, clean `CODEX_HOME`, no user config, ephemeral session, web/MCP/hook/network/cache settings explicit) — [§8.1.1](#811-run-environment-freeze-review-3).
- [ ] Instrumentation calibration gate passes before model runs — proxy-fidelity assertions always; FS assertions when that tier is enabled — [§6.6](#66-instrumentation-calibration-gate-review-4).
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
| 1 | Pilot arm agent/CLI + model | **Stock Codex CLI (GPT), unforked**, frozen environment held constant across all sizes/trials; all model traffic via the recording proxy *(v2: "no fork" made explicit)* | [§8.1](#81-agentic_code_patch-pilot-required), [§8.1.1](#811-run-environment-freeze-review-3) |
| 2 | Primary instrumentation | **API-boundary context-snapshot recording proxy** (byte-exact request payloads + provider `usage`); the v1 FUSE/OverlayFS filesystem tap **demoted to an optional cross-check tier** *(v2 revision 2026-07-06, pre-run)* | [§6.2](#62-how-we-capture-it-defense-in-depth) |
| 3 | Base repo + distractor source | **Real OSS snapshot — primary: PDD @ pinned commit — dependency-sliced to a minimal core with one seeded bug; distractors = out-of-core files regrown to a token budget, extended by definition-derived `mutate`/`template` modes** *(2026-06-04: subset-and-regrow; v2: PDD primary + generator modes)* | [§4.1.0](#410-primary-upstream-repo-pdd-itself), [§5](#5-distractor-definition-and-sourcing-strategy) |
| 4 | Replicates per `(scenario, size)` | **`N = 5`** (trials; seed-pinned only if Codex supports it) → 90 runs for the pilot arm | [§6.5](#65-replication-trials) |
| 5 | Per-run timeout | **1800 s (30 min)** — generous enough that 50x is not penalized on wall-clock alone | run config / [§6.3](#63-run-record-schema) |
| 6 | Size ladder | **1x / 2x / 5x / 10x / 20x / 50x** by token budget, plus a pre-registered doubling **breakdown probe** beyond 50x if H3's `S*` is not located *(v2)* | [§5.1](#51-sizing-model-token-budgeted) |
| 7 | SWE-bench | **Excluded from the core experiment** — no scenarios, repos, tasks, or harness; related-work citation only *(v2)* | [§1.2](#12-why-swe-bench-is-excluded-from-the-core-experiment) |

### Still to confirm (Codex specifics — do not block scenario authoring)

1. **Exact Codex model id + reasoning-effort** setting to pin in the run config (must be stated in the report).
2. **Codex read/search execution path** — confirm whether the pinned Codex build shells out (e.g. `ripgrep`), performs direct local file reads, or uses any server-side/MCP retrieval path. Shell-spawned and direct local reads are kernel-visible to the FUSE tap; server-side or index-backed retrieval would require an additional tool-boundary tap. This affects both how we reconcile the transcript tap against the FS tap and whether the Codex arm can be described as purely local agentic search. (Why this matters across agents is analyzed in [`agentic_cli_search.md` §6](./agentic_cli_search.md#6-implications-for-the-benchmarks-instrumentation-and-validity).)
3. **Base-URL override / proxy routing** — confirm the pinned Codex build routes **all** provider traffic through a configurable base URL so the recording proxy captures every request. Documented fallback: Codex's session transcript, iff it exposes per-request `usage` **and** tool-result content. Failing both, a transport-only fork (base-URL plumbing, never context assembly or tool logic) is the disclosed last resort. Without any of the three, token-level context-penetration metrics, the iteration-trajectory family, and token-dose thresholds are blocked and must be demoted/removed before runs.

> **Status (v2.1, 2026-07-07)** — resolved against the pinned build `codex-cli 0.142.4` by the zero-billing probe (`harness/runner/codex_probe.py`; full record + replication commands in [`harness/runner/CODEX_PIN.md`](./harness/runner/CODEX_PIN.md)):
> 1. *Pin mechanics confirmed* (`--strict-config`-validated frozen config; fingerprint schema v2). The numeric **values** of model id / reasoning effort / `model_context_window` remain a pre-registration choice to be stated in the report.
> 2. *Local execution path confirmed*: the offered toolset has no server-side retrieval tool; a scripted `exec_command` round-trip executed **locally** (marker-file echo). Kernel-visible; the Codex arm can be described as purely local agentic search.
> 3. *Routing confirmed*: all provider traffic transits the proxy (byte-exact, per-request `usage` parsed from Responses SSE). Token-level penetration metrics, the H2 trajectory family, and token-dose thresholds are **supported**; the fallback chain was not needed. The report generator additionally refuses to compute token metrics for any run lacking this evidence (schema-4 `token_metrics_supported` / `development_only` gating).

### Consequence of choice #3 (real-OSS subset-and-regrow) — contamination guardrail

Real repos give organic realism for free — distractors are the project's own files — which **removes** the hand-authored "synthetic filler" risk entirely: the issue's non-goal ("no synthetic filler an agent would trivially ignore") is satisfied by construction, not by a plausibility review. The trade is **training-data contamination**: a public repo may be partly memorized, and an oracle patch can accidentally be a restoration of memorized upstream code. We guard it by (a) requiring a **seed-novelty audit** that rejects byte-for-byte upstream restorations and classifies semantic restorations as upstream-recall caveats; (b) preferring mid-popularity / recent repos; and (c) recording residual layout-familiarity and upstream-recall risk as methodology caveats and stratification criteria ([§7.4](#74-methodology-note), [§11](#11-non-goals-carried-from-the-issue)). The pre-run freeze check is now a **license + offline-runnability + seed-novelty audit + oracle equivalence gate** rather than a synthetic-plausibility spot-check.

---

## 11. Non-goals (carried from the issue)

- Not proving "all of PDD beats all agentic coding"; this measures one effect.
- No tuning of prompts/tasks after seeing model outputs.
- Final target code and hidden tests are never used as grounding or distractors.
- A visible-test pass with hidden failure is never counted as success.
- No synthetic filler an agent would trivially ignore (now satisfied by construction — distractors are the repo's own files, [§5.3](#53-sourcing-and-placing-distractor-files)).
- Not claiming the upstream repo is unseen by the model, or that every seeded fix is automatically novel. The seed-novelty audit records whether the oracle patch could be upstream-code recall; layout-familiarity is a recorded caveat, not eliminated ([§7.4](#74-methodology-note)).
- Not a study of whole-repo comprehension: the agent sees the dependency-sliced core + regrown distractors, never the entire upstream snapshot at once.

---

## References

- [`agentic_cli_search.md`](./agentic_cli_search.md) — **background section** (issue [#1430](https://github.com/promptdriven/pdd/issues/1430)): how agentic coding CLIs acquire code context, a mechanism-level taxonomy (agentic grep/read vs. embedding/repo-map retrieval), per-agent profiles (Codex CLI, Claude Code, Aider, Cursor, SWE-agent), and why the retrieval family predicts bloat sensitivity. Motivates a pre-registered cross-agent extension and sharpens the instrumentation/validity notes referenced from §6.2, §8.1, and §10.
- Issue [#1209](https://github.com/promptdriven/pdd/issues/1209) — research question, metrics, acceptance criteria, non-goals (source of truth for this design).
- Issue [#789](https://github.com/promptdriven/pdd/issues/789) — context budget audit (**closed**; the `pdd context` command and its [`docs/context.md`](../../docs/context.md) shipped in PR #1387, merged to `main` 2026-06-11). Its token attribution is reused only by the deferred prompt-space arm; this pilot does not depend on it.
- `docs/pdd_vs_agentic_cli_definitive_proof_plan.md` — broader pre-registration/falsification methodology this pilot follows.
- `docs/whitepaper_with_benchmarks/` — existing benchmark report layout precedent.
