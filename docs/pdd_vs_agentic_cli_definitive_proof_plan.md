# Definitive Proof Plan: PDD vs Agentic CLI-Only Workflows

## Goal
Produce externally credible evidence that Prompt-Driven Development (PDD) delivers measurable advantages beyond standalone agentic CLIs (for example, Claude Code or Codex used in direct patch mode).

This plan is grounded in claims from:
- `docs/prompting_guide.md`
- `docs/prompt-driven-development-doctrine.md`

## Standard of Proof
The claim is considered proven only if all conditions below are met:
1. Results are statistically significant on pre-registered primary metrics.
2. Effects replicate across multiple repos, teams, and model families.
3. The full harness, raw logs, and analysis are reproducible by an external evaluator.
4. PDD wins on maintenance/reliability outcomes, not just one-off speed.

## Claims to Validate and How to Falsify

| Claim from docs | Hypothesis | Falsification condition |
|---|---|---|
| Prompt is source of truth; patching drifts (`prompting_guide.md`, "Why PDD Prompts") | PDD has fewer spec drift incidents per accepted change | No significant drift reduction |
| Test accumulation creates ratchet effect (`prompting_guide.md`, "Tests as Generation Context"; doctrine "Compound Interest of Molds") | PDD has lower bug recurrence after fixes | Recurrence rate is equal or worse |
| Batch workflow is more reproducible (`prompting_guide.md`, "Regenerate, Verify, Test, Update"; doctrine "Batch-First Workflow") | PDD has higher replay stability across reruns/model upgrades | No replay stability advantage |
| Agentic sessions degrade with context overhead (`prompt-driven-development-doctrine.md`, "Context Window Advantage") | Agentic-only performance degrades more in long-session stress tests than PDD | No differential degradation |
| PDD scales better for complex changes (`prompting_guide.md`, "Why PDD Scales to Large Codebases") | PDD outperforms on multi-step maintenance sequences | No advantage on complex tasks |

## Experimental Design

### Arms
1. `Agentic-Only`: Developers use agentic CLI directly on code (chat + patch workflow).
2. `PDD`: Developers use prompt-first workflow (`generate -> verify -> test -> fix -> update`) with prompts/tests as durable artifacts.
3. `PDD + Agentic Assist` (optional): Same as PDD, but agentic CLI allowed for prompt authoring/debug support, not source-of-truth code patching.

Arm 3 isolates whether PDD complements agentic CLIs rather than replacing them.

Arm execution protocol (must be frozen before benchmarking):
1. Task start state: each task starts from a clean branch at a fixed commit.
2. Attempt cap parity: same max attempts per task across all arms.
3. Tool parity: all arms may run identical local verification commands (test/lint/build).
4. `Agentic-Only` definition: source-of-truth behavior changes are implemented directly in code via agentic workflow; no prompt-first regeneration loop.
5. `PDD` definition: behavior changes must originate in prompt/spec artifacts, then regenerated and validated.
6. Context preload parity: both arms receive the same task brief and acceptance criteria file before each task.

### Repos and Task Sets
Use at least 3 repositories:
1. Python service codebase.
2. TypeScript/Node codebase.
3. Mixed-language or monorepo-style codebase.

Each repo gets the same benchmark structure:
1. Greenfield module creation tasks.
2. Maintenance sequence tasks (features, bug fixes, refactors, compliance updates).
3. Long-horizon regression tasks (10+ sequential changes on same subsystem).
4. Long-session stress tasks (history-heavy agentic sessions vs fresh PDD batch runs).
5. Handoff tasks (new developer continues work from existing artifacts).

Complexity stratification (required):
1. `Low`: localized edits, <= 2 files touched, no cross-module contract change.
2. `Medium`: 3-6 files touched, at least one interface or data-shape update.
3. `High`: >= 7 files touched or multi-module orchestration with non-functional constraints.

Sampling rule:
1. Maintain balanced coverage across `Low`/`Medium`/`High` buckets for each arm.
2. Report all primary outcomes per complexity bucket, not only aggregate totals.

Crossover assignment protocol:
1. Use blocked randomization with counterbalancing (for example, Latin-square style ordering) to reduce order effects.
2. Match task pairs by pilot-estimated difficulty before assigning to arms.
3. Use at least one washout task between arm switches in solo/crossover runs.
4. Define "comparable subsystem" up front by baseline test count, file count, and historical churn range.

Minimum scale target:
- 120+ benchmark tasks total.
- 10+ developers.
- Randomized crossover assignment (each developer uses both methodologies).

### Controls for Fairness
1. Same underlying model family per comparison block.
2. Same hidden acceptance tests and time budgets.
3. Same task specs and starting commits.
4. Randomized task order to reduce learning/order bias.
5. Pre-registered scoring and analysis before running benchmarks.
6. Blinded grading for subjective checks (for example, spec adherence review).
7. Independent adjudication: at least one evaluator who did not author either solution judges borderline outcomes.
8. Prompt parity control: both arms receive the same task specification text and acceptance criteria.
9. Constraint parity control: both arms are validated against identical security/compliance/performance acceptance checks.
10. Cost normalization control: report both raw provider cost and normalized cost from a fixed pricing snapshot date.
11. Retry-policy parity: identical retry, timeout, and abandonment rules across arms.
12. Rater reliability control: use at least 2 blinded raters for subjective labels and require Cohen's kappa >= 0.70; otherwise adjudicate and flag.

### Instrumentation
Collect machine-readable logs for every attempt:
1. `task_id`, `repo`, `developer_id`, `arm`, `model`, `timestamp`.
2. Human active minutes.
3. API tokens/cost.
4. Attempt count and pass/fail reason.
5. Final test status (unit, integration, hidden acceptance).
6. Diff stats and files touched.
7. Artifact sync evidence:
   - prompt changed when behavior changed
   - tests added for bug fixes
   - examples/docs updated when interfaces changed

For context-overhead claims, run three conditions:
1. `Agentic-Long`: one continuous history-heavy session across many tasks.
2. `Agentic-Fresh`: reset agentic session each task (history minimized).
3. `PDD-Fresh`: standard clean batch invocation each task.
4. Measure degradation as early-session vs late-session within `Agentic-Long`.
5. Measure baseline method gap using `Agentic-Fresh` vs `PDD-Fresh`.

### Primary Metrics
1. `Regression-free success rate`:
   accepted tasks that pass all existing + new tests / attempted tasks.
2. `Engineering minutes per accepted task`.
3. `API cost per accepted task`.
4. `Bug recurrence rate`:
   previously fixed bug class reappears within later tasks.
5. `Spec drift rate`:
   behavior changed without corresponding source-of-truth artifact update.
6. `Replay stability`:
   repeated reruns from same prompt/spec pass equivalence tests.
7. `Constraint preservation rate`:
   accepted tasks that pass all security/compliance/performance acceptance checks.

Metric operationalization rules (must be frozen pre-study):
1. `Spec drift` is counted only when acceptance behavior changes and no corresponding source-of-truth artifact change exists in the same task window.
2. `Bug recurrence` is counted only for bug classes explicitly tagged in prior fixed tasks.
3. `Replay stability` uses a fixed rerun count per task (minimum 5 reruns).
4. `Constraint preservation` requires predeclared checks (for example: authz rules, PII handling, latency/SLO tests) tied to each task.
5. `Spec drift` labels use a fixed rubric (`intent mismatch`, `silent behavior change`, `artifact desync`) with examples in the runbook.
6. `Bug class` taxonomy must be predeclared and bound to failing test IDs.
7. Complexity-bucket advantage is quantified as effect size by bucket; "strongest in Medium/High" means `effect_medium >= effect_low` and `effect_high >= effect_low`.
8. All subjective annotations must include rater ID and rationale text.

### Secondary Metrics
1. Time-to-first-correct solution.
2. Number of restart/abandon events.
3. Cross-developer reproducibility (new developer can continue successfully).
4. PR review friction (review cycles, change-request count).

## Statistical Plan
1. Pre-register hypotheses and thresholds.
2. Run power analysis before Phase 3 and set minimum sample size to achieve at least 0.8 power for primary outcomes.
3. Use mixed-effects models (developer and repo as random effects).
4. Use non-parametric tests where distributions are skewed.
5. Report effect sizes and 95% confidence intervals, not only p-values.
6. Correct for multiple comparisons on secondary metrics.
7. Publish null/negative findings as-is.
8. For Phase 0 and solo studies, report bootstrap confidence intervals to quantify uncertainty even when sample sizes are small.

## "Definitive" Pass Criteria
Core criteria (all required):
1. `Regression-free success rate` improves by >= 15% relative with CI excluding 0.
2. `Bug recurrence rate` is reduced by >= 30% relative with CI excluding 0.
3. `Engineering minutes per accepted task` is reduced by >= 20% on maintenance sequences.
4. `Replay stability` is >= 90% in PDD and >= 15 percentage points higher than agentic-only.
5. Results replicate in at least 2 model families and all 3 repos.

Supporting criteria (at least 2 of 3 required):
1. Long-session degradation (late-session vs early-session) is <= 10% relative in PDD and >= 25% relative in `Agentic-Long`.
2. `Constraint preservation rate` is >= 95% in PDD and >= 10 percentage points higher than agentic-only.
3. PDD shows non-negative advantage on `Regression-free success rate` in each complexity bucket (`Low`, `Medium`, `High`), with `effect_medium >= effect_low` and `effect_high >= effect_low`.

If core criteria fail, the definitive claim fails.
If core criteria pass but supporting criteria fail, claim is partial and must be narrowed (for example, "PDD improves reliability/time but not all constraints").

## Execution Phases
1. Phase 0 - Quick proofs + protocol freeze:
   run lightweight experiments, then finalize tasks, hidden tests, scoring schema, preregistration.
2. Phase 1 - Harness build:
   unified runner for both arms, log schema, replay scripts.
3. Phase 2 - Pilot:
   small dry run to validate tasks/instrumentation.
4. Phase 3 - Main study:
   run full randomized crossover benchmark.
5. Phase 4 - Replication:
   repeat on second model family and independent repo subset.
6. Phase 5 - Publication:
   release raw data, scripts, and final report.

### Phase 0 Quick Proofs (Low-Cost Experiments)
Run these before the full benchmark to validate core assumptions with minimal setup.

1. Prompt-only change propagation:
   apply one requirement change across 3 modules via prompt regeneration (PDD) vs direct patching (agentic-only).
   Success signal: fewer missed updates and lower human minutes in PDD.
2. Cold-start handoff:
   a new developer continues from artifacts only (no prior chat/thread context).
   Success signal: faster time-to-accepted-task and fewer clarification cycles in PDD.
3. Model-swap stability:
   rerun the same task set on model family A and B using identical artifacts.
   Success signal: smaller functional variance in PDD outcomes across models.
4. Rollback integrity:
   rollback one version and re-implement a change from that state.
   Success signal: fewer rollback-related defects and faster recovery with prompt-version rollback.
5. Contract ripple:
   modify one shared interface and evaluate downstream breakage on dependent modules.
   Success signal: fewer hidden breakages and faster convergence in PDD.
6. Policy injection:
   add one new security/compliance/performance policy, then run 10 follow-up tasks.
   Success signal: higher policy pass rate in PDD without manual re-briefing each task.
7. Chat-history dependence:
   run agentic tasks with full thread history and with truncated history; compare with fresh PDD batch runs.
   Success signal: larger performance drop in agentic-only under truncated history.
8. Review friction:
   track review cycles and change-request count per accepted task.
   Success signal: fewer review loops when intent is centralized in prompts/tests.

Phase 0 exit criteria:
1. At least 6 of 8 quick proofs show directional advantage for PDD.
2. No quick proof shows severe PDD regression (for example, >20% worse on success rate).
3. At least 5 of 8 quick proofs show standardized effect size >= 0.20 with bootstrap 80% CI excluding zero.
4. Instrumentation quality is sufficient to run Phase 3 without schema changes.

## Deliverables
1. Benchmark harness and runbook.
2. Raw attempt logs (redacted secrets).
3. Analysis scripts and generated plots.
4. Reproducibility package (single command replay).
5. Final report with:
   - primary/secondary outcomes
   - threats to validity
   - where PDD wins, where it does not

## Starting Point in This Repo
Existing benchmark assets can be reused and upgraded:
1. `docs/whitepaper_with_benchmarks/data_and_functions/benchmark_analysis.py`
2. `docs/whitepaper_with_benchmarks/data_and_functions/creation_compare.py`
3. `docs/whitepaper_with_benchmarks/data_and_functions/*.csv`

Main upgrades needed:
1. Move from single-case comparisons to randomized crossover.
2. Add drift, recurrence, and replay-stability metrics.
3. Add long-session stress protocol for context-overhead claims.
4. Add preregistration and external reproducibility package.

## Decision Rule
If the multi-developer study passes the criteria above, we can make a strong claim:
"PDD provides additive, measurable value beyond agentic CLIs used alone, especially for long-horizon maintenance, reliability, and reproducibility."

If it does not pass, keep PDD claims scoped to the dimensions where evidence is positive.

## Solo Fundamental Experiments (Single-Operator Protocol)
Use this protocol when one developer wants strong self-contained evidence before running the full multi-developer benchmark.

### Setup Rules
1. Same model family for both arms in each experiment.
2. Same task specs, starting commits, and acceptance tests.
3. Pre-log time budget per task and do not adjust mid-run.
4. Record all attempts in the same schema used by the main plan.
5. Counterbalance task order and include washout tasks when switching methods.
6. Report both raw and normalized costs using the same pricing snapshot date.

### Solo Experiment Set (Run All 6)
1. Maintenance sequence crossover:
   run 12 sequential changes on subsystem A with PDD and 12 on comparable subsystem B with agentic-only, then swap methods on a second round.
   Primary outputs: accepted-task rate, active minutes per accepted task, API cost per accepted task.
2. Bug recurrence ratchet test:
   fix 8 bug classes, then run 20 follow-up tasks that could re-trigger those classes.
   Primary output: recurrence count by bug class.
3. Replay stability test:
   take 10 completed tasks and rerun each from clean state 5 times per arm.
   Primary output: functional pass consistency across reruns.
4. Long-session degradation test:
   run 15 tasks in one continuous agentic thread (`Agentic-Long`), run equivalent tasks with agentic reset each task (`Agentic-Fresh`), and run equivalent tasks as fresh PDD batch runs.
   Primary outputs: early-vs-late degradation in `Agentic-Long` and baseline gap between `Agentic-Fresh` and `PDD-Fresh`.
5. Spec drift audit:
   audit 20 accepted tasks per arm for behavior changes without source-of-truth artifact updates.
   Primary output: drift incidents per accepted task.
6. Constraint preservation test:
   run 12 tasks with explicit security/compliance/performance checks.
   Primary output: constraint check pass rate.

### Solo Pass Thresholds
For a strong solo claim, target all thresholds below:
1. Maintenance sequence: >= 15% relative improvement in accepted-task rate, or >= 20% reduction in active minutes per accepted task, at equal or better quality.
2. Bug recurrence: >= 50% fewer recurrences in PDD.
3. Replay stability: >= 90% in PDD and >= 15 percentage points above agentic-only.
4. Long-session degradation: PDD degradation <= 10% relative; agentic-only degradation >= 25% relative.
5. Spec drift: PDD drift rate <= 30% of agentic-only drift rate.
6. Constraint preservation: >= 95% in PDD and >= 10 percentage points above agentic-only.
7. Uncertainty reporting: provide bootstrap confidence intervals for all six experiment outcomes.

### Solo Decision Rule
1. Solo protocol is exploratory and cannot by itself satisfy the definitive multi-developer standard.
2. If PDD wins at least 5 of 6 experiments (including experiments 1 through 4), conclude "PDD is better for this operator and codebase context."
3. If PDD wins fewer than 5 of 6, treat results as mixed and narrow claims to winning dimensions only.
4. Use solo outcomes to calibrate task design before Phase 3 multi-developer execution.
