# Potential Ways to Integrate with Existing Studies

**Epic:** [#1429](https://github.com/promptdriven/pdd/issues/1429) (item 2)
**Reads with:** [`literature-review.md`](literature-review.md) · [`../design.md`](../design.md)

This document turns the literature review into an **action plan**: for each
verified study, *how* the Repo-Bloat Localization Benchmark should connect to it —
cite it, adapt its method, reuse its artifact, or position against it — and what
remains our own work. Integration types:

- **Cite-motivate** — use as theoretical/empirical grounding in §1 / Related Work.
- **Adapt-method** — borrow a methodology or protocol.
- **Reuse-artifact** — use a released dataset, harness, or code component.
- **Position-against** — explicit Related-Work contrast that defends novelty.
- **Calibrate** — use the study's reported magnitudes to sanity-check our
  pre-registered thresholds (design §7.5).

All arXiv IDs were verified (see [`README.md`](README.md)).

---

## 1. Integration matrix

| Study | Integration type | Concrete action | What it does *not* give us |
|-------|------------------|-----------------|-----------------------------|
| **NoLiMa** (2502.05167) | Cite-motivate · Calibrate | Use its length-degradation curves as the theoretical baseline and to justify why a ≥2× cost rise / ≥20 pp pass-rate drop is a *meaningful* threshold magnitude. | No repo-LOC variable, no coding agent, no `files_read`. |
| **LongBench** (2308.14508) / **NIAH** | Cite-motivate | Background on long-context evaluation norms; NIAH framing for "needle among distractors." | Document tasks only. |
| **LOCA-bench** (2602.07962) | Position-against (Critical) · Adapt-method · Reuse-artifact (eval) | Adopt the "keep task semantics fixed, scale the noise variable" principle and cite as the closest related work; frame ours as the *code-repository + FS-instrumented + localization-cost* analogue. Their open-source harness (`hkust-nlp/LOCA-bench`) is a reference for context-management baselines. | No source-code distractors, no FS reads, no cost-before-first-edit. |
| **Lost in the Noise** (2601.07226) | Cite-motivate · Adapt-method | Cite the hard-negative-vs-random finding to motivate our same-package tier being most harmful; reuse the attention-fixation result as the mechanistic hypothesis our per-tier `irrelevant_file_read_ratio` tests in code; mirror their inverse-scaling probe (compare reasoning-effort settings under bloat). | Documents not source files; no LOC scaling; no FS tap. |
| **SWE-bench** (2310.06770) | Adapt-method · Position-against | Adopt hidden-test isolation philosophy (design §4.4) and use agent papers as a weak prior for baseline `files_read` at 1×. | Uncontrolled repo size; cannot import scenarios directly. |
| **Agentless** (2407.01489) | Adapt-method | Reuse its localization→repair→validation decomposition as a reference pipeline and, crucially, its manual ground-truth audit → **Lite-S** as precedent for our **seed-novelty audit** (oracle/distractor must not restore upstream code). | No bloat variable; no cost instrumentation. |
| **FeatBench** (2509.22237) | Calibrate · Position-against | Cite its 29.94% top resolved rate and scope-creep/regression failure mode as observational evidence; frame ours as the controlled causal follow-on. | Observational; confounds size with task; no localization cost. |
| **RepoMod-Bench** (2602.22518) | Calibrate · Position-against · Adapt-method | Use 91.3%→15.3% scaling collapse to calibrate threshold magnitudes; borrow its **implementation-agnostic, hidden test suite** idea to harden our hidden verifiers; position ours as controlled (bug held constant). | Observational LOC effect; translation not bug-fix; no cost metrics. |
| **RepoBench** (2306.03091) / **CrossCodeEval** (2310.11248) | Cite-motivate | Ground cross-file localization as a core sub-problem; cite as prior art that motivates measuring it. | Completion quality, not localization cost; fixed repo size. |
| **LocAgent / Loc-Bench** (2503.09089) | Cite-motivate · Reuse-artifact (optional) | Establish localization as an active target; Loc-Bench's instances could seed candidate bug *classes*; contrast Accuracy@k (theirs) vs. cost-before-first-edit (ours). | Accuracy not cost; no repo-size variable. |
| **Improving Code Localization w/ Repository Memory** (2510.01003) | Cite-motivate · Position-against | Cite as state-of-the-art localization-accuracy work; note our cost-efficiency dimension is complementary; their memory tool is a future scaffold variable. | No size variable; no cost metric. |
| **CodeSearchNet / CoSQA / CodeXGLUE** (1909.09436 / 2105.13239 / 2102.04664) | Cite-motivate | Frame `irrelevant_file_read_ratio` as the agentic analogue of retrieval precision@k. | Retrieval decoupled from patching; no distractor-density control. |
| **Evaluating AGENTS.md** (2602.11988) | Cite-motivate (High) | Cite as the closest existing evidence that *more repository context harms coding agents* (+20% cost, lower success); ours is the controlled file-count follow-on. | Instruction files, not file-count growth; no LOC variable. |
| **SlopCodeBench** (2603.24755) | Position-against | Cite as a related-but-distinct degradation mechanism (self-extension erosion vs. injected-file localization cost). | Different IV (iteration vs. LOC volume). |

---

## 2. Reusable engineering & methodology components

Beyond the papers, several **artifacts** can be integrated directly (detailed
in [`../agentic_cli_search.md`](../agentic_cli_search.md) and design §6):

- **OverlayFS + libfuse passthrough** (Linux kernel) — the FS tap's byte-extent
  read logging is engineering reuse of `passthrough_fh.c`; only the manifest-lookup
  classifier that tags reads as distractor/in-scope is novel.
- **ripgrep** — the de-facto content-search backbone for Family-A agents
  (Claude Code's `Grep`, shell agents); its `.gitignore`-awareness is why
  distractors must be regrown into the *tracked* tree.
- **Wilson score & bootstrap CIs** (`scipy.stats.proportion_confint(method='wilson')`)
  — standard small-n reporting, already endorsed by the design.
- **OSF / BIG-bench / HELM pre-registration norms** — methodological precedent for
  our pre-registered *practical-threshold* (not p-value) verdict.
- **PDD internal precedent** — the `pdd_prompt_space` comparison arm (design §8.2)
  reuses PDD's `token_counter` (#789 / PR #1387) once it lands, operationalizing
  the "PDD vs. agentic" framing via prompt-space byte-invariance across repo sizes.

---

## 3. Related-Work paragraph scaffold (for the eventual write-up)

A defensible Related-Work section orders the field by *distance* from our design:

1. **Static long-context decay** (NoLiMa, LongBench, NIAH) — *why* bloat should hurt.
2. **Dynamic agentic context growth** (LOCA-bench; Lost in the Noise) — *same
   one-variable principle, different domain* → cite-and-differentiate.
3. **Observational repo-size effects in code** (FeatBench, RepoMod-Bench) — *the
   correlation our controlled design explains causally.*
4. **Localization & retrieval** (LocAgent, Repository-Memory, RepoBench,
   CrossCodeEval, CodeSearchNet) — *accuracy/quality, not cost.*
5. **Context overhead & iterative erosion** (AGENTS.md, SlopCodeBench) — *adjacent
   mechanisms.*

Each cluster ends with the same refrain — none holds the bug constant while
scaling *irrelevant* code and measuring localization cost at the filesystem
boundary — which is the white space [`literature-review.md`](literature-review.md) §8 claims.

---

## 4. Priority order for integration work

| Priority | Action |
|----------|--------|
| **Critical** | Write the LOCA-bench cite-and-differentiate paragraph; confirm Codex CLI exposes per-request `usage` (the only blocker to runs, design §8.1). |
| **High** | Calibrate §7.5 thresholds against RepoMod-Bench (91→15) and NoLiMa curves; adopt Agentless-style seed-novelty audit; cite AGENTS.md as direct support. |
| **Medium** | Mirror the *Lost in the Noise* inverse-scaling probe across reasoning-effort settings; evaluate reusing Loc-Bench bug classes. |
| **Deferred** | `pdd_prompt_space` arm after #789 / PR #1387 lands. |
