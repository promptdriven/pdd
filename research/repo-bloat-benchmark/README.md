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
context-penetration attribution), and whether Codex shells out for reads/search.

## Ground rules (see design §2)

- Determinism + content hashing before any model run.
- Distractors are the upstream repo's own files outside the target's dependency
  closure; contamination of the *fix* is precluded by seeding a novel bug.
- Hidden verifiers are physically isolated and never enter the agent's context.
- Only distractor volume varies across sizes; everything else is held constant.
- Hidden success is the sole verdict; a visible pass with a hidden failure is a failure.

## Status

- [x] Design document drafted.
- [x] §10 pilot decisions locked.
- [ ] Upstream OSS repos chosen + vendored as pinned snapshots (license/provenance recorded).
- [ ] Scenarios defined (sliced cores + seeded bugs + hidden verifiers).
- [ ] Token-budgeted distractor manifests committed.
- [ ] Harness + instrumentation implemented.
- [ ] Pilot runs + report.

Tracking issue: [#1209](https://github.com/promptdriven/pdd/issues/1209)
