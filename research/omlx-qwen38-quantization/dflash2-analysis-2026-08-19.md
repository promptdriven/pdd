# DFlash2 versus the checked-in Qwen benchmark

**Report date and source access date:** 2026-08-19<br>
**Repository baseline:** merge commit `6d78a7d1a` / PR
[#2409](https://github.com/promptdriven/pdd/pull/2409)<br>
**Decision scope:** research only; no DFlash2 run was performed, and every local
DFlash2 number below is labeled as a projection.

## Executive decision

**DFlash2 could beat the tested decode throughput, but that is not established
on the existing machine.** The exact Apple M4 Max hardware is capable of running
a DFlash2 implementation, but the tested oMLX 0.6.1 runtime is not: the published
recipe requires a DFlash2-specific oMLX 0.6.2 fork or the project's MLX backend.
Compatibility of the exact locally converted non-strict oQ8e target is also
unproven.

The best current evidence is an author-run, end-to-end H200/SGLang benchmark in
which DFlash2 was **1.32–1.48x faster than native MTP** at concurrency 1. That is
not an Apple measurement. A conditional Apple planning model gives a
**0.76–1.45x decode range** versus the checked-in oQ8e+MTP arm, with 1.136x as a
base assumption. Because decode was only 41.6%, 18.5%, and 3.7% of measured
end-to-end latency at the 1K, 4K, and 16K prompt targets, that base assumption
becomes only **1.053x, 1.023x, and 1.004x end to end** if TTFT is unchanged.

**Recommendation:** do not change the checked-in recommendation and do not buy
CUDA hardware on this evidence. Run one paired 4K/128-token M4 Max experiment
using the same target and the same DFlash2-capable runtime for both MTP and
DFlash2. Stop if the custom oQ8e target cannot load unchanged. Only claim a
speedup if the paired decode ratio clears a prespecified confidence threshold and
greedy output parity holds.

## 1. What was actually checked in

The shorthand “Qwen 3 8B” would be wrong here. The artifact identifies itself as
`fcmeyer/Qwen3.8-27B-MLX-bf16-mtp`, pinned to revision
`fe34c8d6784c6d9b463756dd020492123137b732`.

| Requested fact | Evidence from the committed artifact |
| --- | --- |
| Model identity | `metadata.model_id` in all four result JSON files; source revision in `metadata.source_checkpoint_revision` |
| Parameter count | The committed JSON does not contain a count. The pinned Hugging Face API reports **27,781,427,952 BF16 tensor parameters** for the full checkpoint. This includes its VLM/MTP contents and is not an independently measured active-text parameter count. [Pinned API record](https://huggingface.co/api/models/fcmeyer/Qwen3.8-27B-MLX-bf16-mtp/revision/fe34c8d6784c6d9b463756dd020492123137b732) |
| Architecture | Embedded `target_config`: `Qwen3_5ForConditionalGeneration`, multimodal `qwen3_5`; 64 text layers, hidden size 5,120, MLP size 17,408, 48 linear-attention plus 16 full-attention layers, 24 query heads, 4 KV heads, full-attention head dimension 256, 262,144 configured maximum positions, and one MTP layer. No MoE/expert configuration is present. |
| BF16 arm | Source checkpoint in BF16 with native Lightning MTP enabled for the published throughput comparison |
| Quantized arm | Locally converted, **non-strict oQ8e**: affine 8-bit, group size 64, BF16 calibration, 503 imatrix applications. Embedding and tied LM head fell back to standard oQ8; MTP projections were quantized while `language_model.mtp.fc.weight` remained BF16. |
| Runtime and machine | oMLX 0.6.1; MacBook Pro, Apple M4 Max, 16 CPU cores, 128 GB unified memory; macOS 26.5.2 |
| Prompt/output shapes | Requested prompt targets 1,024, 4,096, and 16,384; requested generation 128. Actual prompt counts vary around 1,154, 4,370, and 15,704 in the raw rows. |
| Batch/concurrency | Harness sent `batch_sizes: []`; raw rows contain no batch field. Each recorded cell is one local endpoint request, so this is a single-user latency/decode study, not a continuous-batching throughput study. |
| Warmup and order | oMLX `warmup_mode: quick`; three repeats; fixed BF16-pre, oQ8e, BF16-post order. Compile/cache/cooldown policy is otherwise unspecified. |
| MTP and disabled features | Native MTP enabled. Logged native MTP uses up to three draft depths. TurboQuant KV, DFlash, SpecPrefill, VLM MTP, thinking, remote code, and ANE prefill were disabled. This is not the seven-draft-token MTP setup in the external H200 comparison. |
| Metrics | `gen_tps`, endpoint/TTFT-derived `processing_tps`, `ttft_ms`, `tpot_ms`, `e2e_latency_s`, total throughput, peak memory, load time, plus MTP acceptance/cycles from logs. `processing_tps` is not engine-only prefill throughput. |
| Raw artifacts | [`bf16_mtp_ab.json`](results/bf16_mtp_ab.json), [`bf16_mtp_pre.json`](results/bf16_mtp_pre.json), [`oq8e_mtp.json`](results/oq8e_mtp.json), and [`bf16_mtp_post.json`](results/bf16_mtp_post.json). [`artifact-sha256.txt`](artifact-sha256.txt) names source/conversion files that are not committed, so those external file hashes cannot be rechecked from this worktree. |

### Reproduced conclusions

Running the committed analysis script reproduced the README medians:

| Prompt target | BF16+MTP decode | oQ8e+MTP decode | oQ8e/BF16 decode | BF16 E2E | oQ8e E2E | oQ8e/BF16 E2E |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1K | 8.95 tok/s | 15.3 tok/s | 1.709x | 23.091 s | 21.336 s | 0.924x latency ratio |
| 4K | 10.15 tok/s | 15.2 tok/s | 1.498x | 51.237 s | 47.164 s | 0.921x latency ratio |
| 16K | 8.85 tok/s | 14.2 tok/s | 1.605x | 151.602 s | 170.584 s | **1.125x latency ratio** |

Thus oQ8e improved decode but lost at 16K end to end because TTFT/prefill
dominated. BF16's earlier MTP A/B arm reported MTP-versus-autoregressive decode
ratios of 1.84x, 2.18x, and 2.19x, but with only three noisy observations per
cell. The 1K BF16 bracket values ranged from 5.4 to 20.3 tok/s.

The resource conclusion also reproduces: model files were 51.75 versus 27.97
GiB, peak observed oMLX process footprint was 57.78–58.08 versus 37.53 GiB,
and load time was 10.78–14.71 versus 6.77 seconds for BF16 and oQ8e,
respectively.

The 20 HumanEval plus 20 MBPP smoke sample remained 37/40 for both targets,
with 35/40 exact raw/code matches and no pass/fail flips. It is partly
test-exposed and does not establish general quality parity.

## 2. What DFlash2 is—and is not

DFlash2 is a **speculative decoding system**, not an attention kernel. A small
block-diffusion draft model proposes several output tokens in parallel; the
target model verifies the proposal. Its claimed benefit is decode cycles per
accepted token. It does not replace target-model prefill, target weights, MLPs,
linear-attention layers, or memory traffic with an independently faster
attention primitive.

The released Qwen draft is pinned here as
[`dedf8df68...`](https://huggingface.co/incoai/Qwen3.8-27B-DFlash2/tree/dedf8df68adfb1afeaf7b7480c0a0243108177b4).
Its [config](https://huggingface.co/incoai/Qwen3.8-27B-DFlash2/blob/dedf8df68adfb1afeaf7b7480c0a0243108177b4/config.json)
and API metadata specify:

- **1,924,404,480 BF16 parameters**, five draft layers, hidden size 5,120;
- 32 query heads, 8 KV heads, draft head dimension 128;
- deliberately noncausal draft attention inside the proposal block;
- block size 8, top-16 candidates, selector rank 256;
- two-tap/group-16 dynamic convolutions;
- 262,144 configured maximum positions and a 2,048-token draft sliding window.

Those configured lengths are not demonstrated long-context performance limits.
The Qwen throughput card does not report prompt lengths and caps new tokens at
4,096.

The only paper linked by the project is the original
[`DFlash: Block Diffusion for Flash Speculative Decoding`](https://arxiv.org/html/2602.06036v2).
It covers DFlash, not DFlash2's selector and convolution additions. As of the
access date, the official blog, code, cards, and release do **not** link a
separate DFlash2 paper; DFlash2's primary technical description is the
[2026-08-18 Inco blog](https://inco.ai/blog/dflash2/).

## 3. External performance evidence

The strongest DFlash2 result is end-to-end **decode serving throughput**, not an
attention microbenchmark: one NVIDIA H200, SGLang, FlashAttention 3, BF16 draft,
block 8/seven proposals, default Qwen sampling, `xhigh` reasoning, and maximum
4,096 new tokens. The metric is total output tokens divided by end-to-end wall
time. No raw run files, repeat counts, intervals, power data, or prompt-length
breakdown are published in the model card.

| Task, concurrency 1 | Native MTP | DFlash2 | DFlash2/MTP |
| --- | ---: | ---: | ---: |
| GSM8K | 178.5 tok/s | 236.1 tok/s | 1.323x |
| MATH-500 | 172.8 tok/s | 230.7 tok/s | 1.335x |
| HumanEval | 151.9 tok/s | 214.6 tok/s | 1.413x |
| MBPP | 153.1 tok/s | 226.9 tok/s | 1.482x |
| MT-Bench | 134.9 tok/s | 184.0 tok/s | 1.364x |

Source: pinned [Qwen DFlash2 model card, Evaluation](https://huggingface.co/incoai/Qwen3.8-27B-DFlash2/blob/dedf8df68adfb1afeaf7b7480c0a0243108177b4/README.md#evaluation).
At concurrency 32, DFlash2 was only 1.01–1.45x autoregressive, while native MTP
was 0.77–1.04x; this is why single-user latency and batched throughput must stay
separate.

The blog's Qwen acceptance table reports mean acceptance length 4.80 for
DFlash2 versus 4.28 for native MTP (1.121x), using block size 8 and default
sampling. Acceptance is not throughput: cycle latency matters. The blog also
reports only about 1% added DFlash-to-DFlash2 cycle cost for the selector and
convolutions; that does not make the full five-layer drafter free relative to
native MTP.

### Platform, dtype, shape, and integration status

| Question | Current primary-source evidence | Assessment |
| --- | --- | --- |
| Exact Apple hardware | The project has an Apple-Silicon MLX path; the blog demonstrates M5 Max/oMLX and provides an arm64 build. Apple M4 Max shares the required Apple-Silicon/Metal platform, but no M4 measurement is published. | **Runnable in principle, unmeasured on the exact M4 Max.** |
| Exact runtime | The benchmark used stock oMLX 0.6.1. The recipe links a signed [`0.6.2-dflash2`](https://github.com/z-lab/omlx-fork/releases/tag/0.6.2-dflash2) fork, tag commit `46225aeb...`. | **No on 0.6.1; requires a different runtime/build.** |
| Exact target | Official Apple recipe uses `mlx-community/Qwen3.8-27B-4bit`, a 4-bit draft, block size 5, and verify mode `dflash`. | The custom BF16-MTP and non-strict oQ8e artifacts are **not documented compatible**. |
| NVIDIA GPU architectures | H200/Hopper is the only production-style DFlash2 benchmark found. SGLang's dependencies have broader CUDA support, but that is not DFlash2 validation. | Do not generalize to Turing, Ampere, Ada, or Blackwell without tests. |
| Dtypes/quantization | Official draft checkpoint is BF16. Apple paths expose 4-bit target/draft use. No official DFlash2 evaluation establishes FP16, FP8, FP4, or quantized-KV behavior. | Quantization changes compute, acceptance, memory, and parity; keep it fixed within a comparison. |
| Head dimensions | Released Qwen target uses full-attention head dim 256; draft uses 128. | These are model configs, not a DFlash2 kernel support matrix. Backend attention support governs other shapes. |
| Sequence lengths | Target/draft config maximum is 262K; draft window is 2,048; external output cap is 4,096 and prompt lengths are omitted. | 1K/4K/16K local prompts are not externally validated DFlash2 shapes. |
| SGLang | [DFlash2 PR #35371](https://github.com/sgl-project/sglang/pull/35371) merged on 2026-08-19, after release v0.5.17. Blog installs Git main. | Upstream merged but unreleased; moderate integration risk. |
| vLLM | [PR #52816](https://github.com/vllm-project/vllm/pull/52816) is open; blog installs the PR ref. A stacked [LM-head bug fix](https://github.com/vllm-project/vllm/pull/52883) is also open. | Experimental, especially for quantized targets. |
| llama.cpp | [PR #27342](https://github.com/ggml-org/llama.cpp/pull/27342) is open. Its small author test on M5 Pro/Q4 reported 1.77–1.85x over autoregressive decode. | Useful portability signal, not upstream or comparable to MTP/oQ8e. |
| MLX/MLX-LM | Project-owned [`dflash` MLX backend](https://github.com/z-lab/dflash/tree/07ebd93db9f472af339b644bb70221ad8428328a) pins MLX 0.32.0 and MLX-LM 0.31.3. No upstream MLX-LM DFlash2 integration was found. | Working project path, not mature upstream support. |

Two open project issues materially raise Apple risk: an
[M5 Max greedy divergence report](https://github.com/z-lab/dflash/issues/159)
under the official oMLX recipe, and an
[M1 Max acceptance-collapse report](https://github.com/z-lab/dflash/issues/160)
for `w4a16` that recovered with `w4a32`/BF16. These are third-party reports, not
confirmed root causes, but they make parity and acceptance gates mandatory.

## 4. Normalized answer to the five decision questions

### 4.1 Can it run on the exact hardware/runtime?

- **Hardware: yes in principle.** There is Apple-Silicon MLX code and an arm64
  oMLX DFlash2 build. Memory capacity should be sufficient for a controlled
  trial: the BF16 draft's raw tensor payload is about 3.58 GiB
  (`1,924,404,480 * 2 / 2^30`), or a theoretical 0.90 GiB at four bits before
  scales and runtime state, versus 128 GB installed. This is capacity arithmetic,
  not a measured footprint.
- **Exact oMLX 0.6.1 runtime: no.** Use of the special 0.6.2 fork means the old
  and new numbers cannot be compared without rerunning the MTP baseline in the
  new build.
- **Exact oQ8e target: unknown.** The fallback LM head, private oQ8e conversion
  format, and draft hidden-feature expectations may block or distort the path.
  Loading a different 4-bit target would answer a bridge question, not the exact
  existing-artifact question.

### 4.2 Does it accelerate the measured bottleneck?

It targets the sequential **decode** bottleneck and could outperform native MTP.
It does not claim faster prefill. On the nine local oQ8e throughput requests,
logged target-backbone time was 96.3–99.1% of accounted MTP cycle time and
native-MTP overhead had a median near 1.26%; replacing that cheap one-layer path
with a 1.924B/five-layer drafter is not automatically beneficial on Metal.

For short prompts and long outputs, fewer target verification cycles could win.
For the checked-in 128-token output and 16K input, TTFT already consumes 96.3%
of E2E time, so DFlash2 barely touches the measured bottleneck. It cannot repair
the oQ8e 16K prefill regression.

### 4.3 Credible conditional speed ranges

Use the speculative-decoding model

```text
decode speed ratio = (DFlash2/MTP accepted tokens per cycle)
                     / (DFlash2/MTP cycle latency)

E2E speed ratio = (P + D) / (rP * P + D / decode_speed_ratio)
```

where `P` is measured TTFT, `D = E2E - TTFT`, and `rP` is the DFlash2/MTP TTFT
ratio. The scenarios are deliberately explicit and are stored in
[`dflash2_projection_inputs.json`](dflash2_projection_inputs.json).

| Scenario | Tokens/cycle ratio | Cycle-latency ratio | Decode ratio | Interpretation |
| --- | ---: | ---: | ---: | --- |
| Worst | 0.95 | 1.25 | **0.76x** | Acceptance degrades and the Metal draft cycle costs 25% more. |
| Base | 1.25 | 1.10 | **1.136x** | Useful acceptance gain is partly offset by five-layer draft cost. |
| Best | 1.45 | 1.00 | **1.45x** | Caps planning upside near the upper H200 DFlash2/MTP observation and assumes cycle parity. |

Applied to the committed oQ8e+MTP medians, holding TTFT fixed:

| Prompt | Decode share | Worst decode / E2E | Base decode / E2E | Best decode / E2E |
| ---: | ---: | ---: | ---: | ---: |
| 1K | 41.6% | 11.63 tok/s / 0.884x | 17.39 tok/s / 1.053x | 22.19 tok/s / 1.148x |
| 4K | 18.5% | 11.55 tok/s / 0.945x | 17.27 tok/s / 1.023x | 22.04 tok/s / 1.061x |
| 16K | 3.7% | 10.79 tok/s / 0.988x | 16.14 tok/s / 1.004x | 20.59 tok/s / 1.012x |

A 5% TTFT penalty changes base E2E to 1.021x, 0.982x, and 0.958x, and even
changes best-case 16K E2E to 0.965x. These are sensitivity bounds, not forecasts
with statistical confidence. The H200 1.32–1.48x measurements remain external
priors because CUDA/FA3, BF16, block 8, seven-token MTP, concurrency, prompts,
and serving runtime all differ.

### 4.4 Cost, effort, and risk

| Item | Planning estimate / evidence |
| --- | --- |
| Hardware purchase | **None recommended.** The first decision can be made on the existing M4 Max. |
| Software/model cost | DFlash code is MIT; the draft is Apache-2.0. Downloads, local disk, and engineer time are the direct costs. |
| Small experiment effort | Roughly 1–2 engineer-days if the exact target loads: isolate the forked app, pin hashes, add telemetry, run paired trials, analyze, and restore state. This is a planning estimate. |
| Exact oQ8e integration | Add roughly 2–5 engineer-days if loader/LM-head/quantization work is needed; stop before this work unless the bridge test is promising. |
| Productionization | Unbounded by current evidence; upstream release pinning, parity, long-context, concurrency, cache, failure fallback, and security review remain. |
| Main risks | Runtime fork divergence, unproven oQ8e compatibility, quantized matmul inefficiency, draft memory/state overhead, lower acceptance on different tasks/contexts, warmup/compile artifacts, open parity issue, unreported TTFT changes, and no public raw DFlash2 runs or separate paper. |

Speculative decoding is intended to preserve greedy output and the sampling
distribution, so it should not require a quality trade. Runtime numerical bugs,
quantization, or incorrect rejection sampling can still change outputs. Treat
exact-token parity as a gate, not as an assumption.

### 4.5 Smallest apples-to-apples experiment

1. Install the signed DFlash2 oMLX build in isolation; record release/tag and a
   rollback path to the existing oMLX 0.6.1 app. Do not overwrite the current
   model artifact.
2. Try to load the exact pinned non-strict oQ8e target and DFlash2 draft pinned
   at `dedf8df68adfb1afeaf7b7480c0a0243108177b4`. If the target cannot load
   unchanged, **stop the exact-artifact experiment**. A separate bridge may use
   the recommended 4-bit target, but both MTP and DFlash2 arms must then be
   rerun on that same target and runtime.
3. Primary cell: same M4 Max, target, tokenizer, prompt token IDs, cache policy,
   batch/concurrency 1, 4K prompt target, and 128 generated tokens. Compare
   native MTP on/DFlash off with MTP off/DFlash2 on, quantized draft, block 5,
   verify mode `dflash`.
4. Run one compile/warmup request for each arm and shape and exclude it. Run at
   least 10 randomized paired AB/BA repetitions, up to 30 if the interval is
   unresolved. Hold cooldown, power, and memory-pressure policy constant.
5. Capture TTFT/prefill, decode time and tok/s, E2E, actual token counts,
   cycles, accepted tokens, cycle latency components, footprint, cache hits,
   thermal/power state, errors, stop reason, and output hash. Preserve raw JSON.
6. Before performance trials, compare temperature-zero output hashes to a pure
   autoregressive reference on at least the current 40-task smoke set and
   adversarial short/long prompts. Sampling runs require distributional tests,
   not exact output equality.
7. **Decision rule:** call it faster only if a paired bootstrap 95% interval for
   decode throughput is entirely above 1.05x, greedy hashes match, and neither
   TTFT nor E2E regresses more than 5%. Call it slower if the interval is wholly
   below 0.95x; otherwise call it inconclusive. Expand to 1K, 16K, longer
   outputs, and concurrency only after the 4K gate passes.

The adapter in [`analyze_dflash2.py`](analyze_dflash2.py) will accept a future
oMLX JSON only when it explicitly records `dflash_enabled: true`; projected
records remain `kind: projection`, while supplied raw runs are `kind:
measurement`.

## 5. Reproducibility

From the repository root:

```bash
direnv allow
eval "$(conda shell.zsh hook)"
conda activate pdd

# Reproduce the original report from its four raw JSON files.
python research/omlx-qwen38-quantization/analyze_results.py

# Recompute external ratios and conditional Apple projections as JSON or CSV.
python research/omlx-qwen38-quantization/analyze_dflash2.py
python research/omlx-qwen38-quantization/analyze_dflash2.py --format csv

# Normalize a future explicitly marked DFlash2 raw result without altering it.
python research/omlx-qwen38-quantization/analyze_dflash2.py \
  --dflash-results /path/to/dflash2_result.json

# Focused validation.
pytest -q tests/test_dflash2_analysis.py
python -m py_compile \
  research/omlx-qwen38-quantization/analyze_results.py \
  research/omlx-qwen38-quantization/analyze_dflash2.py
```

Primary-source identity checks used for this report:

```bash
curl -L --fail \
  https://huggingface.co/incoai/Qwen3.8-27B-DFlash2/resolve/dedf8df68adfb1afeaf7b7480c0a0243108177b4/config.json

git clone https://github.com/z-lab/dflash.git /tmp/dflash
git -C /tmp/dflash checkout 07ebd93db9f472af339b644bb70221ad8428328a
```

## 6. Evidence index

All external sources were accessed 2026-08-19.

- [Inco AI, “DFlash 2: Keep Drafting Parallel”](https://inco.ai/blog/dflash2/)
- [Pinned Qwen3.8-27B-DFlash2 model card](https://huggingface.co/incoai/Qwen3.8-27B-DFlash2/blob/dedf8df68adfb1afeaf7b7480c0a0243108177b4/README.md)
- [Pinned Qwen3.8-27B-DFlash2 config](https://huggingface.co/incoai/Qwen3.8-27B-DFlash2/blob/dedf8df68adfb1afeaf7b7480c0a0243108177b4/config.json)
- [Original DFlash paper, arXiv v2](https://arxiv.org/html/2602.06036v2)
- [DFlash code at inspected commit](https://github.com/z-lab/dflash/tree/07ebd93db9f472af339b644bb70221ad8428328a)
- [oMLX 0.6.2 DFlash2 fork release](https://github.com/z-lab/omlx-fork/releases/tag/0.6.2-dflash2)
- [SGLang DFlash2 PR #35371](https://github.com/sgl-project/sglang/pull/35371)
- [vLLM DFlash2 PR #52816](https://github.com/vllm-project/vllm/pull/52816)
- [llama.cpp DFlash2 PR #27342](https://github.com/ggml-org/llama.cpp/pull/27342)

The evidence supports **“worth a controlled Apple trial”**, not “DFlash2 is
faster than the checked-in result.”
