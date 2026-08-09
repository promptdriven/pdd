# Does Irrelevant Code Break Coding Agents? A Controlled Benchmark for Repository Bloat and the Effective Context Window

**Status:** draft v2 (pre-registration stage — no model runs yet; all "Results" content is expected-results / analysis-plan)
**Tracks:** [promptdriven/pdd#1209](https://github.com/promptdriven/pdd/issues/1209) · design source of truth: [`../design.md`](../design.md)

---

## Abstract

Coding agents are routinely deployed in repositories orders of magnitude larger
than the code relevant to any one task. Whether that *irrelevant* bulk degrades
them — and through what mechanism — is asserted often but measured rarely, and
almost never causally. We present a controlled benchmark that holds a
maintenance task fixed (same seeded bug, same brief, same model, same hidden
verifier) while varying **only** the volume of plausible-but-irrelevant
co-resident code, on a dense size ladder from 1x to 50x of the task core's
token size, with a pre-registered probe beyond 50x. Distractor files satisfy a
formal, machine-checked five-condition definition (structural irrelevance,
behavior neutrality, plausibility, no leakage, no tell), sourced by a
deterministic cascade: verbatim out-of-core files of a real project (primarily
the PDD codebase itself), seeded semantics-preserving derivations, and
vocabulary-harvested synthetic modules. Our primary instrument is a **context
snapshot**: an API-boundary recording proxy captures the byte-exact composed
context of every model request the (unforked) agent CLI makes, giving us not
just token totals but the *composition* of the window over time. This lets us
test three pre-registered hypotheses: **H1**, localization cost rises and
hidden-test success falls with distractor dose; **H2**, within a run,
irrelevant context *accumulates gradually* across agent iterations rather than
arriving in one step; and **H3**, there is a locatable ladder step at which
performance stops degrading gracefully and breaks down. We commit to practical
effect-size thresholds — not p-values — before any run. The benchmark is
runnable end-to-end today with a scripted mock arm (zero model tokens),
and every metric is re-derivable from archived raw artifacts.

---

## 1. Introduction

A "128K-token" context window is an allocation, not a promise of uniform
competence: long-context evaluations consistently find that models use the
middle and tail of their windows less reliably than the head, and that
semantically plausible-but-irrelevant material is more damaging than random
filler. If those findings transfer from documents to *code repositories*, they
have a sharp practical consequence: **a large, messy repository silently taxes
every agentic coding tool run inside it**, even when the task itself is
unchanged.

The claim matters in both directions. Tools built around curated,
source-of-truth context (prompt/test/spec manifests, as in PDD) justify their
curation cost by an "effective context window" argument: keeping irrelevant
bulk *out* of the window preserves model sharpness. Agentic CLIs (Codex CLI,
Claude Code, and kin) implicitly claim the opposite: that grep-and-read
localization finds the needle regardless of the haystack. Today, neither side
has causal evidence at the repository scale. Observational results (task
benchmarks over repos of many sizes) confound repository size with task
difficulty, project age, vocabulary, and test style; anecdotes confound it
with everything else.

**Approach.** We isolate the variable. Each scenario is built from a real
project pinned at a commit — primarily the PDD codebase itself — dependency-
sliced to a minimal runnable **core** into which we seed one controlled bug
with a hidden verifier. Bloat is then *manufactured around* the unchanged
core: distractor files satisfying a formal definition are added to
deterministic, content-addressed manifests on a token-budget ladder
`1x/2x/5x/10x/20x/50x`. Everything else — brief, model, timeout, visible
tests, hidden verifier, edit scope — is byte-identical across sizes.

**Instrument.** Prior drafts of this work (and most agent telemetry) lean on
*file-level* evidence: which files the agent opened, how many bytes it read.
That evidence cannot answer the question the claim actually poses, because an
agent can open a file and discard it, or surface one function of it, or
resurface the same content into twenty consecutive requests. Our primary
instrument is therefore the **context snapshot**: a recording proxy at the
model-API boundary archives the byte-exact request payload — the composed
window itself — for every request the agent makes, along with provider token
accounting. The agent binary is stock; no fork is needed (§5.2 argues why a
fork would be the wrong instrument even if free).

**Contributions.**

1. A **controlled repo-bloat benchmark**: same task, same verifier, only the
   irrelevant co-resident code varies, on a dense ladder with a documented
   probe protocol past 50x (§4).
2. A **formal, machine-checked definition of "distractor file"** and a
   three-mode deterministic generator (`regrow`/`mutate`/`template`) that
   scales the dose past the natural size of any real pool without weakening
   the definition (§3.2, §4.3).
3. **Context-snapshot instrumentation** of unmodified agent CLIs, with
   usage-reconciled attribution of window content to core vs. distractor
   origin, and a per-iteration **trajectory analysis** distinguishing gradual
   accumulation from step, plateau, and sawtooth profiles (§5).
4. A **pre-registered analysis plan**: three falsifiable hypotheses (H1–H3),
   practical effect-size thresholds fixed before any run, and an explicit
   outcome matrix including the results that would *weaken* the effective-
   context-window claim (§7, §8).
5. A **runnable open harness** in which the full measurement chain —
   generation, freeze, materialization, instrumented run, verification,
   reporting — validates end-to-end with zero model tokens via a scripted
   mock arm.

---

## 2. Related work

We order the field by distance from our design; the refrain throughout is
that no existing work holds the bug constant while scaling *irrelevant* code
and measuring both window composition and hidden-test success.

**Static long-context decay.** NIAH-style probes, LongBench, and NoLiMa
establish that nominal context length overstates usable length, and that
degradation sharpens when the "needle" lacks lexical overlap with the
distractor mass. These motivate *why* bloat should hurt, but they are
document tasks with no repository, no tool loop, and no localization cost.

**Dynamic agentic context growth.** LOCA-bench keeps task semantics fixed
while scaling a noise variable inside an agent loop, and *Lost in the Noise*
shows hard negatives (semantically near distractors) hurt far more than
random ones — directly motivating our tier design (same-package distractors
as the strongest lure). Neither uses source-code distractors, filesystem-real
repositories, or hidden verification.

**Observational repo-size effects in code.** FeatBench and RepoMod-Bench
report success collapsing as repositories grow (RepoMod-Bench: 91.3%→15.3%
across scale buckets) — but observationally, with task and repo varying
together. We use their magnitudes to calibrate thresholds; our design is the
controlled follow-on that could attribute such collapses causally.

**Localization and retrieval.** RepoBench, CrossCodeEval, CodeSearchNet
frame cross-file context retrieval; LocAgent and repository-memory work
measure localization *accuracy*. Our complement is localization *cost* —
tokens, tool calls, and window occupancy spent before the first edit — under
a controlled dose of irrelevant candidates.

**Context overhead in agent workflows.** The AGENTS.md evaluation finds that
*more* repository-provided context can raise cost ~20% and reduce success —
the closest existing evidence for our claim, though its variable is
instruction files, not code volume. SlopCodeBench studies iterative erosion
(agents degrading their own workspace), an adjacent but distinct mechanism
from injected-bloat localization cost.

**SWE-bench, and why it is not our substrate.** SWE-bench defined
patch-under-hidden-tests evaluation at repository scale, and we adopt exactly
one element of it: the hidden-test idea — success judged by tests the agent
never sees. As an experimental substrate for *this* question, however, it is
excluded from the core experiment, deliberately and entirely (no scenarios,
no repos, no tasks, no harness), for four reasons developed in the design
(§1.2 there): (i) its repositories arrive at fixed sizes, so the independent
variable cannot be manipulated within-task; (ii) instance-level training-data
contamination is pervasive and unmeasurable, and a memorized fix
short-circuits precisely the search behavior under measurement; (iii) its
success criterion carries no notion of localization cost or window
composition, so everything this study measures would have to be bolted on
anyway; and (iv) its statistical appeal rests on task volume that a
controlled size-ladder design cannot and should not use. SWE-bench therefore
appears in this paper only as related work.

---

## 3. Problem statement and definitions

### 3.1 Research question and hypotheses

> Given the same target task, model, verifier, and starting code, what
> happens to an agentic code-patching workflow as the surrounding repository
> grows with plausible-but-irrelevant files?

Pre-registered hypotheses (verbatim from the design, which is the source of
truth):

- **H1 (cross-size degradation).** As provisioned distractor dose grows
  along the ladder, localization cost rises (input tokens, tool calls before
  first edit) and/or hidden-test success falls beyond the §7 thresholds. The
  sharp form regresses success on the *realized in-context* distractor dose,
  not on-disk size.
- **H2 (within-run gradual bloat).** Within a single run, irrelevant window
  share is not delivered at once: it accumulates across agent iterations as
  tool results accrete. Operationally: per-request distractor share rises
  from the run's early to late phase, and the modal growth-shape
  classification at high dose is `gradual` rather than `step`/`plateau`/
  `sawtooth`. H2 decides *where* mitigation belongs: gradual accretion
  indicts context-management policy (compaction, truncation, selective
  retention); a step profile indicts retrieval policy (what to read at all).
- **H3 (breakdown location).** There exists a ladder step `S*` where
  degradation stops being graceful: hidden pass rate at `S*` falls to half
  its 1x value, or context-overflow/timeout become the modal failure class.
  The ladder is dense (`1x/2x/5x/10x/20x/50x`) precisely to locate `S*`; if
  50x does not, a pre-registered doubling probe (100x, 200x, …) extends the
  ladder with the same machinery.

### 3.2 What is a distractor file?

A file `D` is a **distractor** for scenario `(core, task, visible tests,
hidden verifier)` iff all five conditions hold (each machine-checked by the
generator; DEFINITION.md in the harness maps each to its implementation):

1. **Structural irrelevance** — `D` is outside the core's dependency
   closure and is not a target file; no core file imports or loads it.
2. **Behavior neutrality** — materializing or removing `D` changes no
   visible-test or hidden-verifier outcome; files with ambient side effects
   (`conftest.py`, import hooks, path shadowing) are categorically excluded,
   and every materialized variant must pass an oracle-equivalence gate.
3. **Plausibility** — project language and idiom; parses; identifier
   vocabulary overlapping the core above a recorded floor. Verbatim project
   files satisfy this by construction.
4. **No leakage** — no hidden-verifier or oracle-patch content, screened
   against a per-scenario denylist.
5. **No tell** — nothing observable marks `D` as benchmark filler: no
   special directory, prefix, tier label, or comment. A file may be
   dismissed as irrelevant only by genuine reasoning (reachability, imports,
   test references).

**Effective context window** (the claim under test): the portion of a
model's nominal window that can be occupied while task-relevant competence is
preserved. The benchmark operationalizes it as the relationship between
*realized in-context distractor tokens* (measured, §5) and hidden-test
success.

### 3.3 Two token doses, never conflated

The **provisioned dose** is the on-disk token size of materialized
distractors under a pinned tokenizer — what the experimenter controls. The
**realized dose** is the distractor content that actually entered model
requests — what the agent's behavior admits. All penetration metrics report
the second; ladder placement is defined by the first; the analysis relates
outcomes to both, because a flat outcome has two very different explanations
(the agent shielded its window vs. the bulk entered and did not matter), and
only this separation distinguishes them.

---

## 4. Benchmark design

### 4.1 Scenarios: subset-and-regrow on a real project

Each scenario derives from a pinned snapshot of a real repository by a
recorded, deterministic transform: pick an under-tested target site; seed one
unambiguous behavioral bug (`seed.patch`); compute the minimal dependency
closure in which the relevant visible tests run (the **core**, which is the
1x variant); author a hidden verifier for exactly what the visible tests
under-determine; and audit the oracle fix for novelty (a fix that merely
restores upstream bytes or semantics is reclassified or rejected, since it
could be recalled from training data rather than derived).

**Primary substrate: the PDD repository itself.** The review feedback
proposed forking Codex or targeting PDD; these answer different questions —
the fork is an instrumentation choice (rejected, §5.2), PDD-as-target is a
substrate choice (adopted). PDD is a mid-size production Python codebase we
control end-to-end, which makes the single greatest validity threat in this
family of designs — a "distractor" that is secretly load-bearing — auditable
by the code's own maintainers. Its subsystems (CLI dispatch, LLM invocation,
template preprocessing) yield vocabularily distinct cores; licensing and
offline test-running are trivially satisfied; and any measured bloat
sensitivity translates directly into product action. The contamination
caveat (PDD is public) is shared by any real OSS substrate and is controlled
by seeded bugs plus the novelty audit; the residual layout-familiarity
effect biases *against* H1 — the conservative direction.

### 4.2 The size ladder

`S ∈ {1x, 2x, 5x, 10x, 20x, 50x}` multiplies *added distractor tokens*
relative to core tokens (1x = zero-distractor control). The four sizes
suggested in the originating issue are a subset; the ladder is denser
because H3 asks *where* the knee is, which endpoint-heavy spacing cannot
answer. Manifests for every step are content-addressed, committed before any
model run, and enforced by a lockfile the runner checks — a changed manifest
is a new experiment, never an edit.

### 4.3 Filling the ladder: one definition, three sources

Real pools are finite; a 50x budget (and any probe beyond it) can exceed the
project's own out-of-core supply. The generator therefore fills each budget
by a fixed cascade, every file passing the same five-condition checker:

| Mode | Source | Realism | Role |
|---|---|---|---|
| `regrow` | verbatim out-of-core project files at original paths, admitted in dependency-closed import groups | organic | default |
| `mutate` | seeded identifier/docstring derivations of pool files at non-colliding sibling paths | high | after pool exhaustion |
| `template` | synthetic modules from skeletons filled with core-harvested vocabulary; size-tunable | bounded | terminal filler; guarantees convergence |

Each manifest records per-file `mode` and `tier` (same-package, same-layer,
cross-cutting, assigned from real layout distance to the target), so
realism becomes a **measured axis**: the report breaks read and penetration
rates down by mode and tier rather than assuming synthetic and organic
distractors behave alike.

### 4.4 Held constant

Across all sizes of a scenario: the core (bit-identical), task brief, target
files, allowed edit scope, model and reasoning settings, timeout (30 min),
visible tests, hidden verifier, and the agent's frozen run environment
(pinned CLI build, clean per-run state, no caches, no web search, network
egress restricted to the model API via the recording proxy). The *only*
difference between variants is the distractor file set.

---

## 5. Instrumentation: context snapshots first

### 5.1 The recording proxy (primary tap)

All of the agent's model traffic is routed through a local recording relay
(base-URL override; no agent modification). Per request it archives the
byte-exact request payload — the composed context: system content, task,
conversation, tool results — the response, provider `usage`, timestamps, and
a request ordinal. Provider `usage` is the *only* authoritative token count
anywhere in the study.

**Attribution.** Analysis matches surfaced request content against the
materialized tree using a normalized-line index keyed by the out-of-tree
manifest (the agent's sandbox carries no labels; classification is strictly
post-hoc). Attributed distractor tokens are reconciled against provider
usage so attribution can never exceed measurement; ambiguous lines (present
in both core and distractor files) count against the distractor total.
Attribution is an honest lower bound: paraphrased content does not match.

**Iteration trajectory (H2).** From the ordinal-indexed series we compute
per-request input tokens and growth, per-request distractor share,
early/middle/late phase medians, the largest single-request contribution,
and a growth-shape classification — `gradual`, `step`, `plateau`,
`sawtooth` — with thresholds fixed in advance (a single request contributing
>30% of final context ⇒ step; <5% of final context added in the last third ⇒
plateau; any >2% shrink ⇒ sawtooth; precedence sawtooth→step→plateau→
gradual). A per-run total cannot distinguish sixty small accretions from one
giant read; this series can, and the two demand different mitigations.

**Cross-checks.** The CLI's own session log is parsed tolerantly and
reconciled against the proxy record (token drift, or more usage events than
proxied requests — i.e. traffic that bypassed the proxy — flag the run). A
git-diff tap against the pre-run baseline grounds edit classification. The
v1 filesystem tap (OverlayFS + FUSE byte-extent reads) is retained as an
*optional* tier for read-volume metrics; the pilot's primary claims do not
depend on it, and runs without it are valid with those metrics reported as
unavailable rather than imputed.

**Calibration gate.** Before any model run, a scripted client replays a
known request sequence through the proxy and the harness asserts payload
fidelity, usage capture, ordinal indexing, and first-edit boundary
detection; the mock-arm end-to-end suite extends the same principle to the
whole pipeline. (This discipline has already paid for itself: it caught an
attribution bug — JSON-escaped newlines silently defeating line matching —
that would have zeroed the penetration metrics of every real run.)

### 5.2 Why not fork the agent?

An instrumented fork of Codex was considered and rejected. (i) *External
validity*: a fork is a different agent — patches near context assembly or
tool plumbing risk perturbing the behavior under measurement, and the claim
of record must hold for the stock CLI users run. (ii) *Maintenance*: a fork
chases upstream releases and diverges silently. (iii) *Sufficiency*: every
byte an in-process hook would see of the composed context is already
serialized at the API boundary. The proxy is also agent-agnostic, making the
pre-registered cross-agent extension (e.g. Claude Code) a configuration
change rather than a second engineering effort. A transport-only fork
(base-URL plumbing, never context logic) remains a disclosed last resort if
a pinned build cannot route through the proxy.

---

## 6. Metrics

Grouped by the question they answer; all re-derivable from archived raw
artifacts by a third party.

**Outcome.** `hidden_pass` (sole success criterion; a visible-test pass with
hidden failure is a failure), `visible_pass`, `failure_class` ∈
{wrong_file_edit, localization_miss, context_overflow, timeout,
hidden_contract_miss, forbidden_access, other}.

**Localization cost.** `input_tokens_before_first_edit`,
`search_or_tool_calls_before_first_edit`, `iterations_before_first_edit`;
cumulative `input_tokens_per_run`, `max_request_input_tokens`,
`wall_clock_seconds`. The first-edit boundary is the first request carrying
an edit-tool call, cross-checked against write timestamps where the FS tier
runs.

**Window penetration.** Repeat-counted `distractor_context_tokens_total`
(and its before-first-edit split), `distractor_context_share` of consumed
input, de-duplicated `distractor_unique_tokens_entered_context`,
`distractor_pool_coverage` (unique in-window distractor tokens over
provisioned dose, bounded [0,1]), `distractor_files_entered_context` — each
also broken down by tier and by generator mode.

**Iteration trajectory (H2).** `growth_shape`, `largest_single_jump_share`,
per-phase medians of per-request distractor share, and the late−early share
delta.

**Targeting.** Edit classification by fixed precedence (forbidden ⇒
distractor ⇒ target ⇒ allowed-glob-within-core ⇒ wrong), `wrong_file_edit_rate`;
`irrelevant_file_read_ratio` when the optional FS tier runs.

---

## 7. Experimental protocol and analysis plan

**Arms.** Pilot: `agentic_code_patch` — stock Codex CLI, pinned build, frozen
environment, routed through the proxy. Deferred comparison:
`pdd_prompt_space`, whose defining property (the rendered prompt is
byte-identical across repo sizes) makes it a control for the bloat mechanism
rather than a competitor arm. Pre-registered extension: additional CLIs
through the identical instrument.

**Replication.** N = 5 replicates per (scenario, size) cell — 3 scenarios ×
6 sizes × 5 = 90 runs. Codex exposes no supported determinism seed, so
replicates sample natural run-to-run variance; N = 5 is a pilot size chosen
to estimate effect sizes and dispersion, not to power significance tests. A
powered confirmatory design, sized from the pilot's measured variance, is an
explicit deliverable.

**Statistics.** Descriptive only: medians and min–max per cell; Wilson
intervals for small-sample rates; least-squares slopes as effect-size
estimates with Spearman ρ alongside (monotone, threshold-like degradation is
expected and linear fits alone would miss it).

**Pre-registered thresholds (fixed before any run).**

| Signal | Threshold |
|---|---|
| Localization-cost rise | ≥2× median `input_tokens_per_run` (or files-read where FS tier runs), monotone across S |
| Penetration rise | `distractor_context_share` +0.20 absolute and pool coverage ≥0.10 at 50x |
| Hidden-success drop | ≥20 percentage points across S, or equivalent fitted drop vs. realized dose |
| H2 accumulation | late−early per-request share ≥ +0.15 at ≥20x, with `gradual` the modal shape |
| H3 breakdown | first S* with hidden rate ≤ 0.5 × rate(1x), or overflow+timeout modal; else "S* > 50x" triggers the probe |
| Flat (weakening) | all of the above within half-threshold at every step |

---

## 8. Expected results and interpretation matrix

We commit to publishing whichever cell obtains:

| Observation | Reading |
|---|---|
| Cost and/or hidden-success thresholds crossed, monotone in S; success declines in realized dose | **Supports** the effective-context-window claim; curation of context is defensible engineering, and H2's shape says whether context management or retrieval policy is the lever |
| Metrics flat; pool coverage ≈ 0 | Agent search **shields** the window: bloat exists but never enters context. The claim narrows from "bloat breaks agents" to "bloat is search-affordable" — a substantive negative result |
| Distractor tokens enter the window (share and coverage rise) but success is flat | The strongest anti-claim result: irrelevant in-context bulk is tolerated. Effective-context arguments must retreat to cost (tokens/latency/price), not competence |
| Success collapses while token cost rises only modestly | The issue's flagged case: failure by *mis-selection* (wrong files read, right file missed), visible in wrong-file edits and localization misses rather than window occupancy |
| Large dispersion across replicates relative to trends | **Inconclusive** at pilot N; the variance estimate itself sizes the confirmatory study |

H2 has its own matrix: modal `gradual` at high S implicates accretion
(mitigation: compaction/retention policy); modal `step` implicates single
large reads (mitigation: retrieval granularity); `plateau`/`sawtooth`
indicate the CLI's own context management already intervening — itself a
measurement of vendor mitigation in the wild.

---

## 9. Limitations and threats to validity

- **Construct: attribution is a lower bound.** Line matching misses
  paraphrase and summary; penetration metrics understate true occupancy.
  Reconciliation guarantees they never overstate it, which is the direction
  that protects the claim being tested.
- **External: one agent, one language, three scenarios.** The pilot locks
  Codex CLI and Python; conclusions are about this configuration.
  The instrument is agent-agnostic by design, and the cross-agent extension
  is pre-registered rather than improvised.
- **Contamination.** PDD and any real substrate may be in training data.
  Seeded (non-historical) bugs, the seed-novelty audit, and reporting
  layout-familiarity as a caveat address the fix; familiarity with layout
  biases against H1, making observed degradation more, not less, credible.
- **Generated distractors.** `mutate`/`template` files may be less
  compelling lures than organic code. This is measured (per-mode read and
  penetration rates), not assumed away; if agents ignore generated files,
  high-ladder doses are reinterpreted accordingly.
- **Proxy visibility.** The record is complete only if all traffic routes
  through the proxy; egress lockdown plus session-log reconciliation
  (flagging bypassed requests) enforce and verify this. Streamed responses
  are buffered, inflating wall-clock (a secondary metric) but not token or
  composition measurements.
- **Pilot power.** N = 5 per cell supports directional, threshold-based
  reads only; the design says so before the data exists, and the
  confirmatory N is a deliverable of the pilot, not a post-hoc rescue.
- **What this does not test.** Whole-repo comprehension tasks, multi-file
  feature work, non-Python ecosystems, and IDE-embedded (index/embedding)
  retrieval agents — the last being the most interesting extension, since
  their mechanism predicts different bloat sensitivity.

---

## 10. Conclusion

This benchmark converts a widely asserted, rarely tested claim — "irrelevant
repository bloat degrades coding agents" — into a falsifiable measurement
with a controlled dose, a formal distractor contract, window-level
instrumentation of unmodified agents, and pre-committed interpretation
rules. Whatever the outcome, the result is decision-grade: it either
quantifies the tax that context curation avoids, locates the scale at which
agents break, or demonstrates that modern agentic search shields the window
well enough that the effective-context argument must be recast in cost terms.
The harness, manifests, and analysis are fully deterministic and open; the
pilot's remaining pre-run blockers (Codex build pinning and base-URL
confirmation, PDD scenario authoring) are enumerated in the design document.

---

## References

Formatted per the research-context literature review
([`../research-context/literature-review.md`](../research-context/literature-review.md)),
which carries full citation details for:

1. Jimenez, Yang et al., *SWE-bench: Can Language Models Resolve Real-World
   GitHub Issues?* (arXiv:2310.06770) — hidden-test evaluation; excluded as
   substrate (§2).
2. Modarressi et al., *NoLiMa: Long-Context Evaluation Beyond Literal
   Matching* (arXiv:2502.05167).
3. Bai et al., *LongBench* (arXiv:2308.14508).
4. *LOCA-bench* (arXiv:2602.07962) — fixed task semantics under scaled noise
   in agent loops.
5. *Lost in the Noise* (arXiv:2601.07226) — hard-negative distractors and
   attention fixation.
6. Xia et al., *Agentless* (arXiv:2407.01489) — localization→repair
   decomposition; ground-truth audit precedent for our seed-novelty audit.
7. *FeatBench* (arXiv:2509.22237); *RepoMod-Bench* (arXiv:2602.22518) —
   observational scale effects used for threshold calibration.
8. Liu et al., *RepoBench* (arXiv:2306.03091); Ding et al., *CrossCodeEval*
   (arXiv:2310.11248); Husain et al., *CodeSearchNet* (arXiv:1909.09436).
9. *LocAgent / Loc-Bench* (arXiv:2503.09089); *Improving Code Localization
   with Repository Memory* (arXiv:2510.01003).
10. *Evaluating AGENTS.md* (arXiv:2602.11988) — repository context overhead.
11. *SlopCodeBench* (arXiv:2603.24755) — iterative workspace erosion.
