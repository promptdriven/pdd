# Repo-Bloat Localization Benchmark (issue #1209)

Experiment workspace for measuring whether **irrelevant repository bloat**
increases localization cost and reduces hidden-test success for **agentic code
patching**.

> Research question: given the same task, model, verifier, and starting code,
> what happens to an agentic code-patching workflow as the surrounding
> repository grows with plausible-but-irrelevant files?

This is the home branch for the experiment. Polished write-ups may later be
promoted to `docs/whitepaper_with_benchmarks/`; active infra lives here.

**v2 (2026-07-06):** the design was revised — before any model run — to
incorporate review feedback: SWE-bench explicitly excluded from the core
experiment; **context snapshots** (API-boundary recording proxy) promoted to
primary instrumentation; a pre-registered **within-run token-bloat** hypothesis
(H2) and **breakdown-location** hypothesis (H3); **PDD as the primary target
repo**; a formal distractor definition with `regrow`/`mutate`/`template`
generator modes; and a denser size ladder (`1x/2x/5x/10x/20x/50x` plus a
breakdown probe). See `epic-1209-v2.md` for the decision table.

## Start here

- **[design.md](design.md)** — the design document: hypotheses, benchmark
  architecture, scenario format, distractor definition + sourcing, instrumentation
  plan, and reporting format. Read this first.
- **[epic-1209-v2.md](epic-1209-v2.md)** — the v2 epic plan: what the review
  feedback asked for, the decisions made, and the sub-PR map.
- **[paper/paper.md](paper/paper.md)** — the research-paper draft (added in this
  epic; kept in sync with `design.md`).
- **[presentation.md](presentation.md)** — a GitHub-rendered, Marp-exportable slide
  deck of the design talk (the question → subset-and-regrow → the pipeline → the
  three instrumentation taps → pre-registered verdict). A 15-slide tour of `design.md`.
- **[agentic_cli_search.md](agentic_cli_search.md)** — background section (issue
  [#1430](https://github.com/promptdriven/pdd/issues/1430)): how agentic coding CLIs
  acquire code context, a mechanism-level taxonomy (agentic grep/read vs.
  embedding/repo-map retrieval), per-agent profiles (Codex CLI, Claude Code, Aider,
  Cursor, SWE-agent), and why the retrieval family predicts an agent's sensitivity to
  repo bloat — motivating a pre-registered cross-agent extension. Cited.
- **[pdd_direct_generation_routing.md](pdd_direct_generation_routing.md)** —
  design note for issue [#1584](https://github.com/promptdriven/pdd/issues/1584):
  how to compare model, temperature, reasoning, and multi-shot configs for the
  native `llm_invoke` path before shipping a static v1 policy.
- **[agentic_cli_routing.md](agentic_cli_routing.md)** — design note for issue
  [#1585](https://github.com/promptdriven/pdd/issues/1585): how to compare
  agentic CLI harness, model, thinking, and repeat-run configs once cross-CLI
  usage/cost instrumentation is available.

## Layout

```
research/repo-bloat-benchmark/
  design.md            ← design document (v2)
  README.md            ← this file
  epic-1209-v2.md      ← v2 epic plan (feedback → decisions → sub-PR map)
  paper/               ← research-paper draft (this epic)
  harness/             ← experiment code (this epic)
    context_snapshots/   API-boundary recording proxy + per-iteration analyzer
    distractors/         distractor definition, generator (regrow/mutate/template), manifests
    runner/              variant builder, run orchestration, metrics, report generator
  snapshots/           ← pinned, vendored upstream repos (harness-only) (planned)
  scenarios/           ← dependency-sliced cores + seed.patch + task briefs + hidden verifiers
  distractors/         ← per-size token-budgeted manifests + manifests.lock (generated)
  reports/             ← raw traces, run records, generated tables/plots (generated)
```

## Pilot scope

- 3 frozen bug-fix scenarios — each a **bug seeded into a dependency-sliced
  real-OSS core**; primary upstream repo: **PDD itself** (design §4.1.0).
- Deterministic distractor manifests on the ladder **1x / 2x / 5x / 10x / 20x / 50x**
  by **token budget** (regrow → mutate → template mode cascade), committed before
  runs; pre-registered **breakdown probe** beyond 50x if the knee is not located (H3).
- One arm first: `agentic_code_patch`. (`pdd_prompt_space` comparison deferred.)
- Primary outcomes: hidden-pass-rate and token usage, plus localization cost
  (files read / tool calls before first edit), **distractor context-window
  penetration** (how much bloat actually reaches the model window), and the
  **iteration trajectory** of context composition within each run (H2).
- **SWE-bench is excluded** from the core experiment (design §1.2) — related-work
  citation only.

## Locked decisions (frozen before runs — see design §10)

| Decision | Choice |
|----------|--------|
| Pilot agent + model | **Stock Codex CLI (GPT), unforked** — instrumented at the API boundary |
| Primary instrumentation | **Context-snapshot recording proxy** (byte-exact request payloads + provider `usage`); FUSE/OverlayFS filesystem tap demoted to an optional cross-check tier *(v2, pre-run)* |
| Base repo + distractor source | **Real OSS snapshot — primary: PDD @ pinned commit — sliced to a minimal core + one seeded bug; distractors = out-of-core files regrown to a token budget, extended by `mutate`/`template` modes** |
| Size ladder | **1x/2x/5x/10x/20x/50x** + doubling breakdown probe past 50x *(v2)* |
| Replicates per `(scenario, size)` | **5** (`trial_index`; seed-pinned only if Codex exposes a supported seed → 90 runs) |
| Per-run timeout | **30 min** |
| SWE-bench | **Excluded from the core experiment** *(v2)* |

Still to confirm (does not block scenario authoring): exact Codex model id +
reasoning effort; whether Codex exposes a supported seed; and that the pinned
build honors a base-URL override so the recording proxy captures all requests —
fallback: its session transcript (needs per-request `usage` + tool-result
content), last resort: a disclosed transport-only fork. Without any of the
three, token-level penetration and iteration-trajectory metrics must be demoted
before runs.

## Ground rules (see design §2)

- Determinism + content hashing before any model run.
- Distractors satisfy the formal definition in design §5.0 (structurally
  irrelevant, behavior-neutral, plausible, leak-free, tell-free); the default
  source is the upstream repo's own out-of-core files, extended by `mutate`/
  `template` modes only when a ladder step exceeds the real pool. Each seed
  needs a novelty audit because an oracle patch can otherwise be an
  upstream-code restoration.
- Hidden verifiers are physically isolated and never enter the agent's context.
- Only distractor volume varies across sizes; everything else is held constant.
- Every materialized size variant must pass the oracle equivalence gate: registered
  baseline outcomes match and the oracle fix passes visible + hidden verification.
- Hidden success is the sole verdict; a visible pass with a hidden failure is a failure.

## Status

- [x] Design document drafted.
- [x] §10 pilot decisions locked.
- [x] v2 revision incorporating review feedback (SWE-bench exclusion, context
      snapshots primary, H2/H3, PDD target, distractor definition + modes, ladder).
- [ ] Harness + instrumentation implemented (`harness/` — this epic: proxy +
      analyzer, distractor generator, runner + report).
- [ ] Paper draft (`paper/paper.md` — this epic).
- [ ] PDD pinned snapshot vendored; scenarios defined (sliced cores + seeded bugs
      + hidden verifiers + seed-novelty audits).
- [ ] Token-budgeted distractor manifests committed.
- [ ] Oracle equivalence gate passed for every `(scenario, size)` variant.
- [ ] Pilot runs + report.

Tracking issue: [#1209](https://github.com/promptdriven/pdd/issues/1209)
