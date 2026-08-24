# Qwen3.8 27B oQ8e: Pi versus official DeepSeek Harness

Date: 2026-08-23 (America/Los_Angeles)

In this 16-run, coding-only benchmark, Pi led the official DeepSeek Harness
(DSH) on the measured sample. Pi passed 6/8 externally checked runs versus
DSH's 4/8, with mean external scores of 0.825 and 0.680 respectively. Pi won
two paired task/trial comparisons, six tied, and DSH won none. Both separating
pairs were `taskflow`: Pi passed both; DSH timed out with partial scores of
0.28 and 0.56.

DSH also used 14.0% more total wall time (7,356.5 versus 6,455.5 seconds). It
produced 14.8% more completed-response output tokens and had 10.7% lower
aggregate generation throughput. These are whole-harness outcomes on one local
model/runtime, not evidence that Pi is universally better. Four fixtures, two
trials, and only two non-tied pairs are too small for a general ranking or a
statistically persuasive winner claim.

This is a separate follow-up to the checked-in
[`Pi versus Prime`](../omlx-qwen38-pi-prime/README.md) study. It does not replace
or modify that study.

### What this benchmark can and can't tell you

Of the four tasks, two were at ceiling for both harnesses (`make-ci-green` and
`add-feature`, 2/2 each) and one was at floor for both (`webcore`, 0/2 each,
neither harness changing a file). Exactly one, `taskflow`, separated them. The
entire pass-rate and mean-score margin therefore comes from a single fixture,
and only two of eight paired cells were non-tied. That supports a lead on the
measured sample and the cost/latency observations, not a general harness
ranking; no confidence interval or significance claim is warranted. The floor
task also argues against fixture curation in Pi's favor. See
[Limitations](#limitations) for the full list.

## Aggregate result

| Metric | Pi 0.73.1 | DSH 0.1.1-rc.2 | DSH vs Pi |
| --- | ---: | ---: | ---: |
| External passes | 6/8 (75%) | 4/8 (50%) | -2 passes |
| Mean external score | 0.825 | 0.680 | -0.145 |
| Paired wins / losses / ties | 2 / 0 / 6 | 0 / 2 / 6 | Pi +2 wins |
| Timeouts | 3 | 4 | +1 |
| Total wall time | 6,455.5 s | 7,356.5 s | +14.0% |
| Median wall time | 906.5 s | 1,055.2 s | +16.4% |
| Endpoint requests | 86 | 80 | -7.0% |
| Completed responses | 83 | 76 | -8.4% |
| Completed-response input tokens | 1,009,881 | 1,130,071 | +11.9% |
| Completed-response output tokens | 26,587 | 30,520 | +14.8% |
| Median output tokens per run | 3,012 | 2,981.5 | -1.0% |
| Aggregate prompt tokens/s | 387.47 | 382.55 | -1.3% |
| Aggregate generation tokens/s | 12.74 | 11.38 | -10.7% |
| Mean time to first token | 31.40 s | 38.87 s | +23.8% |

The token totals cover responses that delivered a final usage trailer. Seven
timed-out request streams (three Pi, four DSH) were cancelled and therefore
have no final usage record; their partial final-stream tokens are omitted. A
timeout does not automatically mean incorrect code: Pi's second `taskflow`
cell reached the cap but its resulting workspace passed the hidden checker.

| Task | Pi passes | DSH passes | Pi mean score | DSH mean score | Pi mean wall | DSH mean wall |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `make-ci-green` | 2/2 | 2/2 | 1.00 | 1.00 | 221.7 s | 385.1 s |
| `add-feature` | 2/2 | 2/2 | 1.00 | 1.00 | 608.0 s | 892.6 s |
| `taskflow` | 2/2 | 0/2 | 1.00 | 0.42 | 1,197.4 s | 1,200.4 s |
| `webcore` | 0/2 | 0/2 | 0.30 | 0.30 | 1,200.7 s | 1,200.2 s |

On the four pairs where both harnesses passed, Pi was faster by 144.3 to
291.8 seconds. Both harnesses made no file changes in either `webcore` trial,
so its unchanged fixture score of 0.30 did not separate them.

## Cell-level evidence

`Pass` is the external hidden checker's result. `Cap` means the harness process
reached the common 1,200-second limit. Output tokens exclude a capped cell's
unterminated final stream.

| Trial | Task | Harness | Score | Pass | Cap | Wall (s) | Requests | Output tokens | Changed files |
| ---: | --- | --- | ---: | :---: | :---: | ---: | ---: | ---: | ---: |
| 1 | `make-ci-green` | Pi | 1.00 | yes | no | 229.7 | 6 | 1,253 | 6 |
| 1 | `make-ci-green` | DSH | 1.00 | yes | no | 374.0 | 7 | 2,499 | 6 |
| 1 | `add-feature` | DSH | 1.00 | yes | no | 874.9 | 11 | 7,875 | 1 |
| 1 | `add-feature` | Pi | 1.00 | yes | no | 597.6 | 12 | 5,483 | 2 |
| 1 | `taskflow` | Pi | 1.00 | yes | no | 1,194.6 | 17 | 5,693 | 7 |
| 1 | `taskflow` | DSH | 0.28 | no | yes | 1,200.5 | 12 | 3,586 | 0 |
| 1 | `webcore` | DSH | 0.30 | no | yes | 1,200.2 | 10 | 1,619 | 0 |
| 1 | `webcore` | Pi | 0.30 | no | yes | 1,200.5 | 6 | 1,120 | 0 |
| 2 | `make-ci-green` | DSH | 1.00 | yes | no | 396.2 | 9 | 3,012 | 6 |
| 2 | `make-ci-green` | Pi | 1.00 | yes | no | 213.7 | 6 | 1,518 | 6 |
| 2 | `add-feature` | Pi | 1.00 | yes | no | 618.5 | 14 | 5,804 | 2 |
| 2 | `add-feature` | DSH | 1.00 | yes | no | 910.3 | 10 | 7,253 | 2 |
| 2 | `taskflow` | DSH | 0.56 | no | yes | 1,200.3 | 12 | 2,951 | 3 |
| 2 | `taskflow` | Pi | 1.00 | yes | yes | 1,200.1 | 17 | 4,506 | 7 |
| 2 | `webcore` | Pi | 0.30 | no | yes | 1,200.8 | 8 | 1,210 | 0 |
| 2 | `webcore` | DSH | 0.30 | no | yes | 1,200.1 | 9 | 1,725 | 0 |

The field-whitelisted source for this table and all aggregate calculations is
[`results/2026-08-23-clean.json`](results/2026-08-23-clean.json). It contains
cell metadata, scores, diff hashes/status, request identity, timing, and usage,
but no full prompts, model responses, checker output, credentials, or
machine-specific absolute paths.

## Official DeepSeek Harness source and compatibility

Primary sources were accessed 2026-08-23. The benchmark pins the official
`deepseek-ai/deepseek-harness` release
[`dsh-v0.1.1-rc.2`](https://github.com/deepseek-ai/deepseek-harness/releases/tag/dsh-v0.1.1-rc.2),
commit
[`b150a551b8d465e31e418e1b2eaf5e79bbb7d28e`](https://github.com/deepseek-ai/deepseek-harness/commit/b150a551b8d465e31e418e1b2eaf5e79bbb7d28e),
npm package `@deepseek-ai/dsh@0.1.1-rc.2`, and
[MIT license](https://github.com/deepseek-ai/deepseek-harness/blob/b150a551b8d465e31e418e1b2eaf5e79bbb7d28e/LICENSE).
This is an RC/developer-preview release, so its behavior and configuration may
change quickly.

The official one-shot invocation is:

```text
dsh --profile headless --patch <benchmark.cordis.patch.yml> "<exact task>"
```

Before inference, the runner resolves that same composition without booting it:

```text
dsh --profile headless --patch <benchmark.cordis.patch.yml> --dump-config
```

The shipped
[headless bundle](https://github.com/deepseek-ai/deepseek-harness/blob/dsh-v0.1.1-rc.2/packages/bundle/headless/README.md)
creates a fresh persisted agent, submits the positional task as an ordinary
user message, waits for quiescence, and exits without starting a server. The
custom local route uses the official
[`@deepseek-ai/dsh-llm-pi-ai` adapter](https://github.com/deepseek-ai/deepseek-harness/blob/dsh-v0.1.1-rc.2/packages/llm/llm-pi-ai/README.md),
backed in this release by `@earendil-works/pi-ai` 0.82.1. That dependency is a
transport/model adapter inside DSH; it is not the Pi coding-agent harness arm.

DSH's shipped default model is `deepseek-v4-flash` through its native DeepSeek
adapter. The native adapter defaults reasoning effort to high and its own
request cap to 256,000. A hand-declared generic route instead has fallback
capacities of 262,144 context and 32,768 output, no reasoning capability unless
declared, provider-default sampling when fields are omitted, and a normal
agent-level retry policy of five retries. Those defaults were not silently
accepted: the benchmark declared the exact oMLX model/capacities, medium
reasoning, and zero agent-level retries to match a single Pi attempt.

An unknown OpenAI-compatible endpoint is not safely auto-detectable. DSH's
official adapter documentation says it otherwise assumes OpenAI-style
`developer` role, `max_completion_tokens`, and bare `reasoning_effort`. oMLX
requires explicit compatibility values here:

```yaml
api: openai-completions
baseURL: http://127.0.0.1:<per-cell-proxy>/v1
reasoning: medium
retryPolicy: {mode: normal, maxRetries: 0}
compat:
  supportsDeveloperRole: false
  supportsReasoningEffort: false
  supportsUsageInStreaming: true
  maxTokensField: max_tokens
  thinkingFormat: qwen-chat-template
models:
  - id: Qwen3.8-27B-MLX-oQ8e-mtp
    contextWindow: 98304
    maxTokens: 32000
    reasoningEfforts: {medium: medium}
```

The real key never entered this configuration. DSH saw a dummy environment
credential; the loopback proxy replaced it only on the upstream request.

### Tool defaults and benchmark overrides

The official
[base bundle](https://github.com/deepseek-ai/deepseek-harness/blob/dsh-v0.1.1-rc.2/packages/bundle/base/cordis.patch.yml)
ships a broad native tool/control surface: bash or PowerShell, background jobs,
filesystem and search tools, skills, todo/goal tools, string replacement, web
search, subagents/forks, workflows, and Ralph iteration, plus compaction and
result-pruning infrastructure. Headless defaults to `workspace-write` plus
approval prompts.

For comparability and unattended execution, DSH used native presentation mode
and native remaining tools, but the overlay disabled:

- repository instruction/context-file loading and skills, matching Pi's flags;
- web search, because the outer sandbox allowed only the local proxy;
- LLM session-title generation, which would add unscored model traffic;
- subagent, fork, workflow, and Ralph model fan-out, enforcing the no-concurrent
  oMLX rule.

The fan-out restriction is not a handicap specific to DSH. With one model loaded
on a single oMLX server, concurrent subagent requests would serialize on that
endpoint anyway, so fan-out buys no wall-clock parallelism here. Allowing it
would also break the metering invariant that no two requests overlap inside a
cell, which the analyzer enforces.

DSH retained 19 model-facing tool schemas per request; Pi retained its four
stock built-ins. DSH ran `danger-full-access` only inside the stricter outer
Seatbelt policy, removing headless approval prompts without broadening actual
filesystem or network access. This is a whole-harness comparison, not a
tool-schema-matched ablation.

## Shared model and runtime

The identity correction is material: the local model is
`Qwen3.8-27B-MLX-oQ8e-mtp`; no local oQ8c model exists. The benchmark used oQ8e
only.

- MacBook Pro, Apple M4 Max, 16 CPU cores, 128 GB unified memory
- macOS 26.5.2 build 25F84; Node.js 25.6.1
- oMLX app/server 0.6.1
- exact endpoint `http://127.0.0.1:8000/v1`
- exact model `Qwen3.8-27B-MLX-oQ8e-mtp`
- persisted 98,304-token context; 32,768 model output limit
- temperature 0.6, top-p 0.95, top-k 20, repetition penalty 1.0
- thinking enabled at medium; thinking-budget mode disabled
- native MTP enabled at draft depth 4
- DFlash, SpecPrefill, TurboQuant KV, VLM MTP, guided grammar, ANE prefill,
  and remote code disabled

The model and server settings were read and verified, not rewritten. Both
harnesses sent `max_tokens: 32000`, omitted request-level temperature, top-p,
and `reasoning_effort` so the same persisted runtime controls applied, and sent
the same Qwen chat-template kwargs (`enable_thinking: true`,
`preserve_thinking: true`). The proxy verified every measured inference used
`POST /v1/chat/completions` and the exact oQ8e model.

## Tasks, prompt, and schedule

The four tasks came from
[`minghinmatthewlam/openbench`](https://github.com/minghinmatthewlam/openbench/tree/9e26c96a7df012ca9173e9725211c4cc58e11948)
at exact commit `9e26c96a7df012ca9173e9725211c4cc58e11948`:

| Task | SHA-256 of task tree | Purpose |
| --- | --- | --- |
| `make-ci-green` | `4a32fed72b90141fe985416c4b7d44d4f7b34c453fde69773e326b3994f9ce21` | Multi-module repair from a failing suite |
| `add-feature` | `d38f578795043c0f10f139647374d3d2563fbea21161ae978ce3c3297f9dbfba` | Recursive config-include feature |
| `taskflow` | `6ed568c66534b0f7839438bfd34c0696a2b6f4a07d2f9469c1541c7e0be074bb` | Orchestration/scheduling logic repair |
| `webcore` | `a5119ebfed497c749d2d0c93ea41b85dc1fbcd35d22fb0377a836ffa411f4dde` | Connected routing/mounting feature |

Each cell received the exact fixture `instruction.md` plus the same fixed
suffix:

> Work only in the current workspace. Implement the requested coding change,
> run the relevant tests, and finish when the implementation is correct.

There were two trials per task and harness. Trial one alternated which harness
went first by task; trial two reversed every task's order. Runs were serial,
not concurrent.

## Isolation, checker, and telemetry controls

Every cell had a fresh copied workspace, initialized git baseline, HOME, temp
directory, Pi/DSH configuration, and session. A macOS Seatbelt profile denied
external network, permitted only the per-cell loopback proxy, limited writes to
the cell workspace/HOME/temp, and exposed only the exact isolated Pi and DSH
installation roots plus system runtime paths. The runner denied 12
representative hidden-checker path probes before any inference.

The hidden `checker.sh` ran outside the harness after every normal exit or
timeout, with a separate 180-second checker limit. The measured scores came
from the pinned OpenBench task tree. After adversarial review, all 16 saved
workspaces were regraded without inference: the runner first required the
complete task tree to match the hard-coded SHA-256 above, then invoked each
checker with the benchmark orchestrator's exact `sys.executable`, a minimal
allowlisted environment (no orchestrator credentials), and a separate Seatbelt
profile that denied network, limited reads to the pinned task/workspace plus
system runtimes, and limited writes to the workspace/checker temp directory.
Every score, pass flag, and checker exit matched the original result. This
separate per-run evidence is in the sanitized JSON; the published runner now
applies the hardened boundary to every new checker execution as well. Harness
self-reports and visible test claims were never scored. Golden solutions passed
all four checkers; untouched fixtures produced scores 0.312, 0.400, 0.280, and
0.300, confirming the checker path and partial-score behavior before traffic.

The metering proxy logged no message bodies. It recorded request IDs, method,
path, model, selected request fields, tool count, event timing, response bytes,
and usage/duration metadata. The analyzer required:

1. exactly one terminal response/error event per request;
2. no overlapping requests inside a cell;
3. exact endpoint and model identity;
4. the complete 4-task × 2-trial × 2-harness matrix with unique IDs;
5. exact task-tree hashes;
6. two consecutive oMLX samples with zero active and waiting requests at
   controlled boundaries.

All checks passed. Seven proxy errors are expected cancellation terminals for
the seven timed-out final streams. No Pi, DSH, or benchmark child remained
after the matrix.

## Preflights and smoke tests (excluded from results)

Two orchestration preflights failed before any benchmark trial and are
operational notes, not measurements:

1. oMLX's hard memory watermark blocked the first attempt.
2. After the previously resident `Qwen3.6-35B-A3B-bf16` model was unloaded
   (oMLX logged 65.39 GB freed), the balanced prefill guard blocked the second.

Global oMLX Memory Guard was therefore changed from balanced to aggressive for
benchmark traffic. After all traffic, the runner restored it to balanced in a
`finally` path. An independent authenticated check at 2026-08-23 15:40:16
-0700 confirmed balanced plus two consecutive oMLX 0.6.1 samples with zero
active and zero waiting requests. This evidence is included in the sanitized
JSON. No other persistent setting was changed.

Before the full protocol, the runner successfully completed a matched,
excluded `make-ci-green` smoke pair:

| Harness | External pass | Wall | Requests | Output tokens |
| --- | :---: | ---: | ---: | ---: |
| DSH | yes | 404.3 s | 8 | 1,905 |
| Pi | yes | 252.0 s | 6 | 1,283 |

The smoke gate confirmed successful process/checker exits, zero proxy errors,
and identical observed request settings before allowing the full matrix.

## Interpreting harness versus model/runtime effects

The same loaded model, endpoint, hardware, server process, persisted sampling,
reasoning mode, MTP depth, task bytes, prompt suffix, checker, isolation, and
wall-clock cap were shared. That removes obvious model/runtime substitutions.

What remains deliberately different is the harness: system-prompt assembly,
tool schemas, context/history management, retry/compaction policies, editing
strategy, termination decisions, and request count/shape. DSH's larger prompt
and 19-tool surface likely contribute to its higher input-token total and
latency, but this benchmark does not isolate a single causal mechanism.
Reported token throughput is also workload-weighted: prompt length, cache reuse,
and generation length differ because the harnesses chose different trajectories
on the same model. It should not be read as a pure oMLX kernel benchmark.

## Disclosure

The author has no affiliation with earendil-works (Pi) or deepseek-ai (DSH).
Neither harness is a dependency of pdd, and pdd itself is not an arm of this
benchmark. Pi is the harness the author uses day to day, which is why it is the
reference arm here and in the Pi-versus-Prime study; readers should treat that
as a bias to check rather than a disclosed-and-therefore-settled detail. The
reverse experiment, the same protocol run by someone whose daily driver is DSH,
is invited. The pinned locks and repro commands below exist to make that cheap.

## Limitations

- Four fixtures and two trials are too small for a general harness ranking.
  With only two non-tied pairs, even both favoring Pi is weak inferential
  evidence; no confidence interval or significance claim is warranted.
- Runs were balanced but not randomized. One long local session can contain
  thermal, cache, memory-pressure, or power drift.
- All trials used one model, one quantization, one machine, one reasoning level,
  and one timeout.
- Seven final partial streams have no token-usage trailer, so usage totals
  undercount work in capped cells.
- `webcore` was too difficult for either harness at this budget and provided no
  separation.
- DSH is an RC/developer-preview release and its generic transport is a newer,
  forked pi-ai package than Pi 0.73.1's transport. This is unavoidable for the
  pinned official release and is part of the DSH harness as shipped.
- DSH retained more native tool schemas than Pi. The capability boundary was
  equalized for network/filesystem/model concurrency, not schema count.
- Seatbelt is a best-effort local benchmark boundary, not a hardened
  multi-tenant security sandbox.

A stronger follow-up would use more held-out repositories, randomized order,
at least five trials per task, multiple budgets, and explicit thermal/power
telemetry. Tool-schema and system-prompt ablations would help explain the
whole-harness result.

## Reproduce exactly

Use an isolated tool root; do not install either harness globally. The exact
dependency graphs used for the published run are checked in under
[`tool-lock/pi`](tool-lock/pi) and [`tool-lock/dsh`](tool-lock/dsh). Their
`package-lock.json` SHA-256 values are respectively
`c2c6cbeb831c9748f7071e32d81240ed017adc2a81aac7153ea5638821ca6275`
and `d09b9445494e44c7f6239524acc4a82e751b67006f2b10ca3977eba94abd739a`;
both match the actual benchmark installations byte-for-byte. The commands
below intentionally use `/private/tmp`, those locks, and exact source commits:

```bash
bench_root=/private/tmp/pdd-pi-dsh-bench-repro
mkdir -p "$bench_root/tools/pi" "$bench_root/tools/dsh"

cp research/omlx-qwen38-pi-deepseek-harness-2026-08-23/tool-lock/pi/package*.json \
  "$bench_root/tools/pi/"
cp research/omlx-qwen38-pi-deepseek-harness-2026-08-23/tool-lock/dsh/package*.json \
  "$bench_root/tools/dsh/"
npm ci --prefix "$bench_root/tools/pi" --no-audit --no-fund
npm ci --prefix "$bench_root/tools/dsh" --no-audit --no-fund

git clone https://github.com/deepseek-ai/deepseek-harness.git \
  "$bench_root/tools/deepseek-harness"
git -C "$bench_root/tools/deepseek-harness" checkout \
  b150a551b8d465e31e418e1b2eaf5e79bbb7d28e

git clone https://github.com/minghinmatthewlam/openbench.git \
  "$bench_root/openbench"
git -C "$bench_root/openbench" checkout \
  9e26c96a7df012ca9173e9725211c4cc58e11948
```

Before inference, load `Qwen3.8-27B-MLX-oQ8e-mtp` in oMLX 0.6.1 with the exact
persisted settings above, ensure no active/waiting requests, and confirm the
global Memory Guard target/rollback. The runner validates the hidden-checker
boundary and DSH composed configuration, performs the matched smoke pair, gates
on request parity, runs the balanced matrix, and restores Memory Guard in its
outer `finally` block:

```bash
eval "$(conda shell.zsh hook)"
conda activate pdd

python research/omlx-qwen38-pi-deepseek-harness-2026-08-23/benchmark.py \
  --tasks-root "$bench_root/openbench/tasks" \
  --pi "$bench_root/tools/pi/node_modules/.bin/pi" \
  --dsh "$bench_root/tools/dsh/node_modules/.bin/dsh" \
  --tool-root "$bench_root/tools" \
  --run-base "$bench_root/run" \
  --trials 2 \
  --timeout-seconds 1200 \
  --smoke-timeout-seconds 600

python research/omlx-qwen38-pi-deepseek-harness-2026-08-23/revalidate_checkers.py \
  "$bench_root/run/benchmark/results.jsonl" \
  --tasks-root "$bench_root/openbench/tasks" \
  --raw-root "$bench_root/run/benchmark/raw" \
  --evidence-output "$bench_root/checker-revalidation.json"

python research/omlx-qwen38-pi-deepseek-harness-2026-08-23/analyze.py \
  "$bench_root/run/benchmark/results.jsonl" \
  --manifest "$bench_root/run/manifest.json" \
  --checker-revalidation "$bench_root/checker-revalidation.json" \
  --clean-output "$bench_root/clean.json"

pytest -q tests/test_omlx_pi_deepseek_harness_benchmark.py
```

`--tool-root` must contain the exact readable subdirectories `pi/` and `dsh/`;
the runner rejects overlap among tool, run, and hidden-task roots. Raw
transcripts and proxy JSONL stay in the temporary run root and must not be
published without a separate content review. The checked-in clean artifact was
generated by [`analyze.py`](analyze.py), whose whitelist and forbidden-material
scan fail closed on credentials and absolute user/temp paths.
