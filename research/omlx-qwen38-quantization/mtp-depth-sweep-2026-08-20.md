# oQ8e MTP maximum-depth sweep — 2026-08-20

## Result

On this Apple M4 Max and the existing `Qwen3.8-27B-MLX-oQ8e-mtp`
checkpoint, maximum MTP depth **4** is the best candidate from this directional
sweep. Its median decode throughput was 20.6–24.3% above the current semantic
default (maximum depth 3) at all three prompt targets. Depth 5 was faster at 1K,
but lost most of that advantage at longer prompts and was slower than depth 4
at 4K and 16K.

This result supports a longer paired validation of depth 4. It does not yet
support calling the gain production-grade: three repetitions are noisy, the
built-in benchmark adds a unique prefix to each request, and some generations
stopped before the 512-token target.

## Exact system and controls

- Hardware: MacBook Pro, Apple M4 Max, 16 CPU cores, 128 GB unified memory
- Runtime: oMLX 0.6.1
- Target: local `Qwen3.8-27B-MLX-oQ8e-mtp`
- Source checkpoint revision:
  `fe34c8d6784c6d9b463756dd020492123137b732`
- Quantization: non-strict enhanced oQ8e, 8-bit affine group 64; see the
  directory README for conversion and tensor-level details
- Workload: oMLX built-in `code_python`, concurrency/batch 1, prompt targets
  1,024/4,096/16,384, generation target 512, three repetitions
- Sampling: greedy (`temperature=0`, `top_p=1`, `top_k=0`), thinking off
- MTP on; maximum draft depth was the only intended arm difference
- TurboQuant KV, DFlash, SpecPrefill, VLM MTP, and Qwen ANE prefill off
- One eight-token quick warmup preceded each repetition
- External result upload was disabled

The original interactive settings were restored after the run: model loaded,
temperature 0.6, top-p 0.95, top-k 20, thinking on, MTP on, no active profile,
and `mtp_num_draft_tokens=null` (the runtime's semantic default of 3).

## Raw decode measurements

Values are generated tokens per second. Ratios use each cell's median and depth
3 as the denominator.

| Prompt target | Depth 3 observations | Depth 3 median | Depth 4 observations | Depth 4 median / ratio | Depth 5 observations | Depth 5 median / ratio |
| ---: | --- | ---: | --- | ---: | --- | ---: |
| 1K | 39.8, 13.9, 14.9 | 14.9 | 18.0, 19.3, 17.4 | 18.0 / **1.208x** | 19.7, 19.5, 15.1 | 19.5 / **1.309x** |
| 4K | 38.9, 12.2, 15.2 | 15.2 | 18.8, 18.9, 22.0 | 18.9 / **1.243x** | 23.6, 17.7, 13.8 | 17.7 / **1.164x** |
| 16K | 10.9, 15.5, 16.9 | 15.5 | 17.1, 19.5, 18.7 | 18.7 / **1.206x** | 19.7, 14.7, 16.0 | 16.0 / **1.032x** |

Across all nine observations, the medians were 15.2, 18.8, and 17.7 tok/s for
depths 3, 4, and 5 respectively. That pooled statistic favors depth 4 by 23.7%
over depth 3, but it is descriptive rather than a confidence interval.

The runtime logs prove the requested paths were active: depth-4 arms contain
`d4` proposal/acceptance counters and depth-5 arms contain `d5` counters. Depth
5 was used sparingly in several requests (for example, only 3–8 accepted level-5
drafts in some 512-token generations), while incurring a larger MTP timing cost.
That is consistent with its weaker longer-context result, but does not by itself
establish causality.

## Interpretation limits

The first depth-3 repetition reached 39.8 and 38.9 tok/s at 1K and 4K because
that generated trajectory achieved roughly 95–96% draft acceptance. Later
depth-3 trajectories were much slower. The benchmark's per-run UUID prefix
prevents token-identical paired prompts, so the median does not fully separate
depth from trajectory-dependent acceptance.

End-to-end latency is not an apples-to-apples decision metric in this artifact.
At 16K, completion lengths varied from 81 to 512 tokens, prompt token counts
also varied, and TTFT dominates. No accuracy arm was rerun because all arms use
the same target weights and verification method; nevertheless, output
equivalence should be checked in the follow-up before changing the default.

This experiment tests a Yukon-inspired tuning idea—allowing more native MTP
draft levels—not Yukon's fused kernels or DFlash2. It therefore provides direct
evidence about the current oMLX setup, not evidence that either external method
is faster.

## Recommendation and next gate

Use maximum depth 4 as the candidate, not depth 5. Before keeping it as the
interactive default, run at least ten randomized paired depth-3/depth-4 trials
using identical prompt token IDs, fixed 512-token completions (or compare only
equal-length completions), and recorded thermal/memory-pressure state. Require
a paired 95% interval above 1.05x for decode, matching greedy output hashes, and
no greater than 5% TTFT or end-to-end regression. If that gate fails, retain
the current default depth 3.

Engineering effort to try depth 4 is small, but oMLX 0.6.x has an API wrinkle:
its ordinary model-settings request silently omits `mtp_num_draft_tokens`.
The benchmark adapter therefore creates a private temporary profile, verifies
the reported depth, deletes the profile, and restores the original explicit
value (including `null`) through the same profile route.

## Reproduce

From the repository root, with the local oMLX server running:

```bash
direnv allow
eval "$(conda shell.zsh hook)"
conda activate pdd

python research/omlx-qwen38-quantization/benchmark.py \
  --single-model Qwen3.8-27B-MLX-oQ8e-mtp \
  --label oq8e_mtp \
  --mtp-depths 3,4,5 \
  --generation-length 512 \
  --throughput-only \
  --result-path \
    research/omlx-qwen38-quantization/results/oq8e_mtp_depth_sweep.json

pytest -q \
  tests/test_omlx_qwen38_benchmark.py \
  tests/test_dflash2_analysis.py
```

The raw record, including every endpoint result and captured MTP log line, is
[`results/oq8e_mtp_depth_sweep.json`](results/oq8e_mtp_depth_sweep.json).
