# Repo-Bloat Localization Benchmark (issue #1209)

Experiment workspace for measuring whether **irrelevant repository bloat**
increases localization cost and reduces hidden-test success for **agentic code
patching**.

> Research question: given the same task, model, verifier, and starting code,
> what happens to an agentic code-patching workflow as the surrounding
> repository grows with plausible-but-irrelevant files?

This is the home branch for the experiment. Polished write-ups may later be
promoted to `docs/whitepaper_with_benchmarks/`; active infra lives here.

## Start here

- **[design.md](design.md)** — the design document: benchmark architecture,
  scenario format, distractor sourcing strategy (subset-and-regrow), instrumentation
  plan, and reporting format. Read this first.
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

## Planned layout

```
research/repo-bloat-benchmark/
  design.md          ← design document (current deliverable)
  README.md          ← this file
  snapshots/         ← pinned, vendored upstream OSS repos (harness-only) (planned)
  scenarios/         ← dependency-sliced cores + seed.patch + task briefs + hidden verifiers (planned)
  distractors/       ← per-size token-budgeted manifests + manifests.lock (planned)
  harness/           ← subsetter, runner, variant builder, instrumentation tap, verifier driver (planned)
  reports/           ← raw traces, run records, generated tables/plots (planned)
```

## Pilot scope

- 3 frozen bug-fix scenarios — each a **bug seeded into a dependency-sliced real-OSS core**.
- Deterministic distractor manifests at **1x / 5x / 20x / 50x** by **token budget**,
  produced by regrowing the repo's own out-of-core files, committed before runs.
- One arm first: `agentic_code_patch`. (`pdd_prompt_space` comparison deferred.)
- Primary outcomes: hidden-pass-rate and token usage, plus localization cost
  (files read / tool calls before first edit) and **distractor context-window
  penetration** (how much bloat actually reaches the model window).

## Locked decisions (frozen before runs — see design §10)

| Decision | Choice |
|----------|--------|
| Pilot agent + model | **Codex CLI (GPT)** |
| Base repo + distractor source | **Real OSS snapshot, dependency-sliced to a minimal core + one seeded bug; distractors = the repo's own out-of-core files regrown to a token budget** *(revised 2026-06-04 from hand-authored repos, before any run)* |
| Filesystem tap | **Linux container + OverlayFS (edits) + FUSE passthrough, byte-extent reads** |
| Replicates per `(scenario, size)` | **5** (`trial_index`; seed-pinned only if Codex exposes a supported seed → 60 runs) |
| Per-run timeout | **30 min** |

Still to confirm (does not block scenario authoring): exact Codex model id +
reasoning effort, whether Codex exposes a supported seed, whether its
transcript exposes per-request `usage` **and tool-result content** (for token-level
context-penetration attribution), and the pinned Codex read/search execution path
(shell-spawned, direct local reads, or any server-side/MCP retrieval). Tool-result
content, or a harness wrapper that captures surfaced read/search content, is a
blocker for token-level context-penetration metrics; without it, token-dose
thresholds must be demoted before runs.

## Ground rules (see design §2)

- Determinism + content hashing before any model run.
- Distractors are the upstream repo's own files outside the target's dependency
  closure; each seed needs a novelty audit because an oracle patch can otherwise
  be an upstream-code restoration.
- Hidden verifiers are physically isolated and never enter the agent's context.
- Only distractor volume varies across sizes; everything else is held constant.
- Every materialized size variant must pass the oracle equivalence gate: registered
  baseline outcomes match and the oracle fix passes visible + hidden verification.
- Hidden success is the sole verdict; a visible pass with a hidden failure is a failure.

## Status

- [x] Design document drafted.
- [x] §10 pilot decisions locked.
- [ ] Upstream OSS repos chosen + vendored as pinned snapshots (license/provenance recorded).
- [ ] Scenarios defined (sliced cores + seeded bugs + hidden verifiers + seed-novelty audits).
- [ ] Token-budgeted distractor manifests committed.
- [ ] Oracle equivalence gate passed for every `(scenario, size)` variant.
- [ ] Harness + instrumentation implemented.
- [ ] Pilot runs + report.

Tracking issue: [#1209](https://github.com/promptdriven/pdd/issues/1209)
