# Qwen3.8 27B oQ8e: Pi versus Prime Agent coding pilot

In this small coding-only pilot, Prime Agent did **not** improve correctness over
vanilla Pi. Pi passed 6/8 runs versus Prime's 5/8 and received a higher mean
external score (0.825 versus 0.735). Pi won one paired task/trial comparison,
seven tied, and Prime won none. Prime used 20.7% more total wall time and 13.1%
more completed-response output tokens.

The practical result on this machine is to prefer Pi for this model and setup.
That is a directional harness choice, not a general claim that Prime cannot
help on other models, tasks, budgets, or configurations.

## Aggregate result

| Metric | Pi 0.73.1 | Prime Agent 0.7.3 | Prime vs Pi |
| --- | ---: | ---: | ---: |
| External passes | 6/8 | 5/8 | Prime -1 |
| Mean external score | 0.825 | 0.735 | Prime -0.090 |
| Paired wins / losses / ties | 1 / 0 / 7 | 0 / 1 / 7 | Pi +1 win |
| Timeouts | 2 | 3 | Prime +1 |
| Total wall time | 5,894.9 s | 7,112.3 s | +20.7% |
| Median wall time | 711.2 s | 1,060.5 s | +49.1% |
| Endpoint requests | 80 | 78 | -2.5% |
| Completed-response input tokens | 924,171 | 795,656 | -13.9% |
| Completed-response output tokens | 24,905 | 28,166 | +13.1% |
| Median output tokens | 2,868 | 2,102 | -26.7% |

Prime was slower on all five pairs where both harnesses passed. On the other
separating pair, Pi passed `taskflow` while Prime hit the cap without a file
change. Both `webcore` pairs hit the same 1,200-second cap, made no file changes,
and received the untouched fixture's 0.30 partial score.

| Task | Pi passes | Prime passes | Pi mean wall | Prime mean wall |
| --- | ---: | ---: | ---: | ---: |
| `make-ci-green` | 2/2 | 2/2 | 195.6 s | 300.2 s |
| `add-feature` | 2/2 | 2/2 | 673.2 s | 860.2 s |
| `taskflow` | 2/2 | 1/2 | 878.2 s | 1,195.4 s |
| `webcore` | 0/2 | 0/2 | 1,200.4 s | 1,200.4 s |

## Environment and model

- MacBook Pro, Apple M4 Max, 16 CPU cores, 128 GB unified memory
- macOS 26.5.2; oMLX 0.6.1
- Model: locally converted `Qwen3.8-27B-MLX-oQ8e-mtp`
- Source: `fcmeyer/Qwen3.8-27B-MLX-bf16-mtp`, pinned revision
  `fe34c8d6784c6d9b463756dd020492123137b732`
- Non-strict enhanced 8-bit affine, group size 64, BF16 compute, native MTP
- 98,304-token context; 32,768 max output; medium thinking; temperature 0.6;
  top-p 0.95; top-k 20; three MTP draft tokens
- TurboQuant KV, DFlash, SpecPrefill, VLM MTP, guided grammar, and remote code
  disabled

The exact converted-model hashes and conversion limitations are documented in
the adjacent [`omlx-qwen38-quantization`](../omlx-qwen38-quantization/README.md)
study.

## Protocol

Four coding fixtures were pinned from OpenBench commit
`9e26c96a7df012ca9173e9725211c4cc58e11948`. Each task was run twice per
harness with balanced order:

- `make-ci-green`: multi-module repair from a failing suite
- `add-feature`: recursive config includes with hidden feature tests
- `taskflow`: multi-module orchestration and scheduling defects
- `webcore`: connected repository-scale routing feature

Every cell received a fresh workspace, home, session, and Prime IPython state.
Both harnesses used the same local oMLX OpenAI-compatible endpoint and the same
20-minute wall-clock cap. A per-cell loopback proxy injected the real API key,
metered all parent and child requests, and exposed only a dummy key to the
harness. External hidden checkers were the sole judge; agent self-reports were
never scored.

Prime's stock persistent IPython/RLM behavior was enabled because the question
was whether native Prime improves on native Pi. This is a whole-harness
comparison, not an isolated system-prompt or tool-loop comparison.

Agents ran under macOS Seatbelt with host-home and hidden-grader content reads
denied, external network denied, and writes scoped to per-run directories.
Beyond standard system runtime roots and each cell's run directories, only the
exact Pi, Prime, and Prime-kernel installation roots were readable. Prime's
necessary loopback kernel sockets were allowed. This is best-effort local
isolation, not a hardened security boundary.

## Integrity checks

The published run used a hardened proxy boundary:

1. timeout cancellation closes every active upstream response;
2. all proxy handlers must drain within 30 seconds;
3. every request must have exactly one response or error terminal event;
4. oMLX must report zero active and waiting requests twice before crossing a
   cell boundary.

All 16 rows have unique IDs, the expected four task hashes, and exact
request/terminal-event parity. The minimum gap from one cell's terminal event
to the next cell's first request was 2.342 seconds. Five proxy errors are
expected cancellations of the five timed-out cells. The runner denied 12
representative hidden-file probes before execution; an independent adversarial
audit denied all 101 files under the selected tasks' checker, checker-data, and
solution paths and found no workspace symlink escape. No Prime daemon, IPython
kernel, benchmark process, or benchmark socket remained after the run. The
model returned to its pre-run unloaded state.

Two earlier candidate matrices are excluded. The first exposed a 10.2-second
residual request crossing a cell boundary. The second fixed that problem but
used an overly broad tool-install read root that technically made hidden graders
readable; transcript review found no access, but the matrix was still rejected.
The runner in this directory contains both fixes and this matrix was executed
from scratch afterward.

The first attempt at the final cell completed its model budget, but the
post-timeout Prime shutdown command itself timed out before grading, so no result
row was committed. Its proxy log had exact 7/7 request-terminal parity, its raw
directory was archived, all associated processes were terminated, and oMLX was
verified idle and unloaded. The published final cell is a fresh full-budget
retry. The runner now records graceful versus forced shutdown and fails if any
cell-associated process survives or respawns.

## Limitations

- Four fixtures and two trials are far too small for a general harness ranking.
- The single recovered final-cell retry was triggered by post-inference cleanup,
  not by its score, but it is still an additional execution of that cell.
- Runs were balanced but not fully randomized, and one long local session can
  still contain thermal, cache, or power drift.
- Token totals include completed responses. The partial final stream in each of
  the five timed-out cells had no final usage trailer and is omitted.
- Native tool schemas differ. The comparison equalizes the endpoint, capability
  boundary, sandbox, task, and budget—not internal implementation details.
- `webcore` did not separate the harnesses: neither produced a patch.

A stronger follow-up should use more held-out repositories, randomized order,
at least five trials per task, and explicit thermal/power telemetry.

## Reproduce

Install and pin Pi, Prime Agent, and the OpenBench fixture checkout, then run:

```bash
python research/omlx-qwen38-pi-prime/benchmark.py \
  --tasks-root /path/to/openbench/tasks \
  --pi /path/to/pi \
  --prime /path/to/prime-agent \
  --tool-root /path/to/isolated/node-installs \
  --run-base /private/tmp/pi-prime-clean \
  --trials 2 \
  --timeout-seconds 1200

python research/omlx-qwen38-pi-prime/analyze.py \
  /private/tmp/pi-prime-clean/results.jsonl
```

The runner changes local oMLX model load/settings state and restores it in a
`finally` block. Review the code before running it. Raw transcripts are not
published because they can contain machine-specific paths and generated code;
the sanitized cell-level record is in
[`results/2026-08-19-clean.json`](results/2026-08-19-clean.json).

`--tool-root` must contain the exact readable subdirectories `pi/`, `prime/`,
and `prime-kernel/`; place each executable/runtime under its corresponding
subdirectory. Keep `--tasks-root` and `--run-base` disjoint from those roots and
from each other. The runner checks these hidden-grader boundaries before loading
the model.
