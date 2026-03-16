# STT Benchmark Results

Date: 2026-03-15  
Machine: Apple Silicon Mac using the `video_editor` conda env  
Goal: Compare the current Stage 5 speech-to-text path against stronger local options that can use the Mac GPU.

## Summary

The best result on this machine was `mlx-community/whisper-large-v3-turbo`.

- It was faster than the current Stage 5 path on both benchmark clips.
- It also had the lowest WER on both benchmark clips.
- `mlx-community/whisper-large-v3-mlx` was slower and did not beat `large-v3-turbo` on these samples.

The remaining transcript errors are not just STT model weakness. A noticeable share of the mismatch is coming from the source TTS audio itself, especially in sections where Qwen produced unstable or garbled speech.

## Current Stage 5 Baseline

Current implementation in [sync_audio_pipeline.py](/Users/gregtanaka/Documents/pdd_cloud/pdd/video_editor_pdd/scripts/sync_audio_pipeline.py):

- Engine: `faster-whisper`
- Model: `base`
- Device: `cpu`
- Compute type: `int8`

## Benchmark Method

Helper script:

- [benchmark_stt_models.py](/Users/gregtanaka/Documents/pdd_cloud/pdd/video_editor_pdd/scripts/benchmark_stt_models.py)

Metrics:

- `wall_seconds`: elapsed transcription time
- `realtime_factor`: `audio_seconds / wall_seconds`
- `wer`: word error rate against concatenated `cleanText` from `outputs/tts/segments.json`

Benchmark sections:

1. `part4_precision_tradeoff`
   - audio: [narration.wav](/Users/gregtanaka/Documents/pdd_cloud/pdd/video_editor_pdd/remotion/public/part4_precision_tradeoff/narration.wav)
   - duration: `120.145s`
   - expected words: `232`
2. `cold_open`
   - audio: [narration.wav](/Users/gregtanaka/Documents/pdd_cloud/pdd/video_editor_pdd/remotion/public/cold_open/narration.wav)
   - duration: `21.938s`
   - expected words: `44`

Warm-cache result artifacts:

- [part4_precision_tradeoff](/Users/gregtanaka/Documents/pdd_cloud/pdd/video_editor_pdd/projects/pdd-explainer/outputs/benchmarks/stt_part4_precision_tradeoff_comparison_warm.json)
- [cold_open](/Users/gregtanaka/Documents/pdd_cloud/pdd/video_editor_pdd/projects/pdd-explainer/outputs/benchmarks/stt_cold_open_comparison_warm.json)

## Results

### part4_precision_tradeoff

| Model | Runtime | Wall s | Realtime x | WER |
| --- | --- | ---: | ---: | ---: |
| Stage 5 current | `faster-whisper base cpu int8` | 9.603 | 12.511x | 0.3578 |
| Recommended candidate | `mlx whisper-large-v3-turbo` | 4.073 | 29.498x | 0.3147 |
| Alternative | `mlx whisper-large-v3` | 6.156 | 19.515x | 0.3319 |

### cold_open

| Model | Runtime | Wall s | Realtime x | WER |
| --- | --- | ---: | ---: | ---: |
| Stage 5 current | `faster-whisper base cpu int8` | 2.624 | 8.360x | 0.2500 |
| Recommended candidate | `mlx whisper-large-v3-turbo` | 1.530 | 14.343x | 0.1818 |
| Alternative | `mlx whisper-large-v3` | 8.978 | 2.444x | 0.2500 |

## Interpretation

### 1. `whisper-large-v3-turbo` is the best upgrade candidate here

On both samples it beat the current Stage 5 setup on speed and WER.

- `part4_precision_tradeoff`
  - about `2.36x` faster than current
  - WER improved from `35.8%` to `31.5%`
- `cold_open`
  - about `1.72x` faster than current
  - WER improved from `25.0%` to `18.2%`

### 2. Full `large-v3` does not justify itself on these local TTS samples

It was slower than `large-v3-turbo` on both clips and did not improve WER enough to matter. On `cold_open`, it matched the baseline WER while being much slower.

### 3. The STT model is not the whole problem

The benchmark transcripts show obvious source-audio corruption in both samples, especially phrases like:

- `spit-er-eye socks`
- `what blue great avidem`
- long gibberish bursts in `part4_precision_tradeoff`

Those are signs that some of the error budget is caused by the TTS audio itself, not by the STT model. A stronger STT model helps, but it cannot fully recover from garbled speech.

## Attempted But Rejected Path

I also tested the `transformers` Whisper path on PyTorch `mps`.

Result:

- model load succeeded
- moving to `mps` succeeded
- inference stalled once transcription began, even on `whisper-base`

So those results were excluded from the benchmark report. On this machine, MLX is the viable Apple-GPU STT backend; the direct `transformers`+`mps` path is not healthy enough to recommend.

## Recommendation

If we upgrade Stage 5, the best next move is:

1. add an MLX-backed STT path for Apple Silicon
2. use `mlx-community/whisper-large-v3-turbo` as the default Mac GPU model
3. keep the current `faster-whisper base cpu` path as fallback

That should improve both speed and transcript quality for Mac users without forcing the slower full `large-v3` model.

## Commands Used

```bash
PYTHONNOUSERSITE=1 PYTHONPATH= \
/opt/homebrew/Caskroom/miniforge/base/envs/video_editor/bin/python \
scripts/benchmark_stt_models.py \
  --project-dir projects/pdd-explainer \
  --section-id part4_precision_tradeoff \
  --models stage5_current whisper_large_v3_turbo_mlx whisper_large_v3_mlx \
  --json-out projects/pdd-explainer/outputs/benchmarks/stt_part4_precision_tradeoff_comparison_warm.json
```

```bash
PYTHONNOUSERSITE=1 PYTHONPATH= \
/opt/homebrew/Caskroom/miniforge/base/envs/video_editor/bin/python \
scripts/benchmark_stt_models.py \
  --project-dir projects/pdd-explainer \
  --section-id cold_open \
  --models stage5_current whisper_large_v3_turbo_mlx whisper_large_v3_mlx \
  --json-out projects/pdd-explainer/outputs/benchmarks/stt_cold_open_comparison_warm.json
```
