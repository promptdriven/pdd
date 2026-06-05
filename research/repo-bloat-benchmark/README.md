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
  scenario format, distractor generation strategy, instrumentation plan, and
  reporting format. Read this first.
- **[agentic_cli_search.md](agentic_cli_search.md)** — background section (issue
  [#1430](https://github.com/promptdriven/pdd/issues/1430)): how agentic coding CLIs
  acquire code context, a mechanism-level taxonomy (agentic grep/read vs.
  embedding/repo-map retrieval), per-agent profiles (Codex CLI, Claude Code, Aider,
  Cursor, SWE-agent), and why the retrieval family predicts an agent's sensitivity to
  repo bloat — motivating a pre-registered cross-agent extension. Cited.

## Planned layout

```
research/repo-bloat-benchmark/
  design.md          ← design document (current deliverable)
  README.md          ← this file
  scenarios/         ← frozen base repos, task briefs, hidden verifiers (planned)
  distractors/       ← donor pool + per-size manifests + manifests.lock (planned)
  harness/           ← runner, variant builder, instrumentation tap, verifier driver (planned)
  reports/           ← raw traces, run records, generated tables/plots (planned)
```

## Pilot scope

- 3 frozen bug-fix scenarios.
- Deterministic distractor manifests at **1x / 5x / 20x / 50x**, committed before runs.
- One arm first: `agentic_code_patch`. (`pdd_prompt_space` comparison deferred.)
- Primary outcomes: hidden-pass-rate and token usage, plus localization cost
  (files read / tool calls before first edit).

## Locked decisions (frozen before runs — see design §10)

| Decision | Choice |
|----------|--------|
| Pilot agent + model | **Codex CLI (GPT)** |
| Base repo source | **Hand-authored minimal repos** |
| Filesystem tap | **Linux container + OverlayFS (edits) + FUSE passthrough, byte-extent reads** |
| Replicates per `(scenario, size)` | **5** (`trial_index`; seed-pinned only if Codex exposes a supported seed → 60 runs) |
| Per-run timeout | **30 min** |

Still to confirm (does not block scenario authoring): exact Codex model id +
reasoning effort, whether Codex exposes a supported seed, whether its
transcript exposes per-request `usage` for token metrics, and whether Codex
shells out for reads/search.

## Ground rules (see design §2)

- Determinism + content hashing before any model run.
- Hidden verifiers are physically isolated and never enter the agent's context.
- Only distractor volume varies across sizes; everything else is held constant.
- Hidden success is the sole verdict; a visible pass with a hidden failure is a failure.

## Status

- [x] Design document drafted.
- [x] §10 pilot decisions locked.
- [ ] Scenarios defined.
- [ ] Distractor pool + manifests committed.
- [ ] Harness + instrumentation implemented.
- [ ] Pilot runs + report.

Tracking issue: [#1209](https://github.com/promptdriven/pdd/issues/1209)
