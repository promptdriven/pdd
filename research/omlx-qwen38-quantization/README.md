# Qwen3.8 27B BF16 vs non-strict oQ8e on Apple M4 Max

This directory records a **descriptive, single-session local observation** of
Qwen3.8-27B BF16+MTP versus a locally converted 8-bit affine group-64
oQ8e+MTP checkpoint in oMLX 0.6.1.

The strongest defensible result is narrow: the oQ8e checkpoint was about 46%
smaller on disk, used substantially less observed process memory, and decoded
about 1.5–1.7x faster in this session. It was **not faster at every workload**:
16K prefill, time to first token, and end-to-end latency were worse. The coding
sample had the same pass/fail result for both models, but it is small and partly
test-exposed, so it does not establish general accuracy parity.

Follow-up: the dated
[`DFlash2 comparison`](dflash2-analysis-2026-08-19.md) reconstructs these raw
results, evaluates current DFlash2 primary evidence, and defines the smallest
Apple M4 Max experiment needed before making any speedup claim.

## Environment

- MacBook Pro, Apple M4 Max, 16 CPU cores, 128 GB unified memory
- macOS 26.5.2
- oMLX 0.6.1
- Source checkpoint: `fcmeyer/Qwen3.8-27B-MLX-bf16-mtp`
- Pinned source revision: `fe34c8d6784c6d9b463756dd020492123137b732`
- Native Lightning MTP enabled; TurboQuant KV, DFlash, SpecPrefill, VLM MTP,
  thinking, and remote code disabled

No machine serial number, hardware UUID, API key, or unredacted home-directory
path is included in this repository.

## Artifact identity

The locally converted checkpoint used:

```json
{
  "oq_level": 8,
  "group_size": 64,
  "dtype": "bfloat16",
  "preserve_mtp": true,
  "text_only": false,
  "auto_proxy_sensitivity": true,
  "enhanced": true,
  "imatrix_reuse_cache": true,
  "imatrix_num_samples": 128,
  "imatrix_seq_length": 512,
  "imatrix_strict": false
}
```

Strict conversion first aborted because the imatrix lacked
`language_model.model.embed_tokens`. The completed artifact is therefore
**non-strict oQ8e**. Its report records 503 imatrix applications, with
`language_model.model.embed_tokens` and the tied `language_model.lm_head`
falling back to standard oQ8. The MTP projections are quantized, while
`language_model.mtp.fc.weight` remains BF16. “MTP enabled” here means the native
MTP path was active and logged draft acceptance/cycles; it does not imply that
BF16 and oQ8e produce bit-identical outputs.

The output contained six safetensors shards, 2,209 indexed tensors, exact
non-overlapping offsets, no trailing payload, and only regular non-executable
model files. Full source/config/cache/output hashes are in
[`artifact-sha256.txt`](artifact-sha256.txt). Those hashes identify this local
conversion; they do not claim that a public model repository contains the same
derived files.

## Throughput protocol

- Built-in oMLX `code_python` benchmark through the local OpenAI-compatible
  HTTP endpoint
- Prompt targets: 1,024, 4,096, and 16,384 tokens
- Generation target: 128 tokens
- Quick warmup, three repeats per run
- Fixed order: BF16 pre-bracket, oQ8e, BF16 post-bracket
- BF16 medians pool the three pre- and three post-bracket observations
- oQ8e medians use its three observations
- `processing_tps` is endpoint/TTFT-derived and is not raw engine-only prefill
  throughput

| Prompt target | BF16 decode median | oQ8e decode median | Decode ratio | BF16 processing median | oQ8e processing median | BF16 TTFT | oQ8e TTFT | BF16 E2E | oQ8e E2E |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1K | 8.95 tok/s | 15.3 tok/s | 1.71x | 117.8 tok/s | 93.1 tok/s | 9.84 s | 12.46 s | 23.09 s | 21.34 s |
| 4K | 10.15 tok/s | 15.2 tok/s | 1.50x | 113.3 tok/s | 113.7 tok/s | 38.61 s | 38.43 s | 51.24 s | 47.16 s |
| 16K | 8.85 tok/s | 14.2 tok/s | 1.60x | 110.0 tok/s | 95.6 tok/s | 143.09 s | 164.22 s | 151.60 s | 170.58 s |

At 16K, oQ8e decoded faster but took about 12.5% longer end to end because
prefill/TTFT dominated. This is why the result should be described as a decode
speedup, not a universal latency speedup.

The BF16 pre-bracket was noisy: its 1K decode observations were
`[20.3, 5.4, 10.0]` tok/s. Bracketing exposes drift but does not remove thermal,
cache, power, or order effects.

## Resource observations

| Metric | BF16+MTP | oQ8e+MTP |
| --- | ---: | ---: |
| Model files | 51.75 GiB | 27.97 GiB |
| Peak observed oMLX process footprint | 57.78–58.08 GiB | 37.53 GiB |
| Model load time | 10.78–14.71 s | 6.77 s |

The footprint is an observed process-level measurement from oMLX's admin
telemetry, not a model-only allocation measurement.

## Coding regression sample

The deterministic sample used 20 HumanEval and 20 MBPP tasks at temperature
zero with thinking disabled.

| Result | BF16+MTP | oQ8e+MTP |
| --- | ---: | ---: |
| HumanEval pass/fail | 20/20 | 20/20 |
| MBPP pass/fail | 17/20 | 17/20 |
| Combined pass/fail | 37/40 | 37/40 |
| Completion tokens | 4,681 | 4,779 |
| Sum of request time | 430.42 s | 342.95 s |

Both models failed the same three MBPP tasks and there were no pass/fail flips.
Raw responses and extracted code were exactly equal on 35/40 tasks; five tasks
produced different implementations that still passed their tests.

This is a **regression smoke sample, not a blind pass@1 or general coding
accuracy benchmark**. The MBPP prompt includes up to three entries from
`test_list`, and the scorer later executes that same test list. In addition,
40 tasks are too few to establish general quality equivalence, and the BF16
accuracy arm was not rerun in randomized paired order with oQ8e.

## Execution and security limitations

Generated Python ran with best-effort macOS Seatbelt restrictions, network and
home-directory reads denied, a 15-second timeout, and resource limits. This is
not a hardened sandbox: the candidate process is allowed to execute, and the
scorer treats exit code zero as success, so deliberately adversarial code could
false-pass (for example by terminating early). Do not use this harness to run
untrusted code when stronger isolation is required.

Inference requests were directed to loopback, and the benchmark records
`external_upload: false`. That is not proof of a machine-wide air gap or proof
that no process made any external connection.

The source checkpoint passed a static safetensors/config audit: local files
matched its pinned Hugging Face revision, no executable/pickle/remote-code hook
was present, and representative tensor bytes matched the official upstream
Qwen source conversion. Static inspection cannot exclude a behavioral
weight-level backdoor or a runtime vulnerability.

## Reproduce the analysis

Recompute every table value derived from committed JSON:

```bash
python research/omlx-qwen38-quantization/analyze_results.py
```

The harness defaults can be overridden without embedding local paths:

```bash
export OMLX_BASE_URL=http://127.0.0.1:8000
export OMLX_SETTINGS_PATH="$HOME/.omlx/settings.json"
export OMLX_LOG_PATH="$HOME/.omlx/logs/server.log"
export OMLX_EVAL_DATA_DIR=/Applications/oMLX.app/Contents/Resources/omlx/eval/data
export OMLX_SOURCE_REVISION=fe34c8d6784c6d9b463756dd020492123137b732

python research/omlx-qwen38-quantization/benchmark.py \
  --single-model Qwen3.8-27B-MLX-oQ8e-mtp \
  --label oq8e_mtp \
  --result-path /private/tmp/omlx_qwen38_oq8e_mtp_results.json
```

The harness changes model load/settings state and expects a running local oMLX
admin API. Review it before use. Preserve and restore the user's originally
loaded models around a benchmark session.

## Raw records

- [`results/bf16_mtp_ab.json`](results/bf16_mtp_ab.json): earlier same-checkpoint
  BF16 MTP-off/MTP-on comparison, including the BF16 coding sample used here
- [`results/bf16_mtp_pre.json`](results/bf16_mtp_pre.json): fresh BF16+MTP
  throughput bracket before oQ8e
- [`results/oq8e_mtp.json`](results/oq8e_mtp.json): oQ8e+MTP throughput and coding
  regression sample
- [`results/bf16_mtp_post.json`](results/bf16_mtp_post.json): BF16+MTP throughput
  bracket after oQ8e

## Recommendation boundary

For this M4 Max system, the result supports trying non-strict oQ8e+MTP when
decode speed, disk size, or memory headroom matter. It does **not** support a
universal replacement claim: BF16 may be preferable for fidelity-sensitive
work and was faster end to end in the measured 16K workload. A publication-grade
performance comparison should randomize/interleave model order, use at least ten
repetitions per cell, define cache/cooldown policy, and record thermal, power,
and memory-pressure telemetry. A general quality claim requires a much larger
held-out evaluation with hidden tests.
