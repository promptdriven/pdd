#!/usr/bin/env python3
"""Benchmark CPU vs MPS for Qwen3-TTS on M4 Max."""

import sys
sys.stdout.reconfigure(line_buffering=True)

import time
import numpy as np
import torch
import soundfile as sf
from pathlib import Path
from qwen_tts import Qwen3TTSModel

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
MODEL_PATH = PROJECT_ROOT / "models" / "Qwen3-TTS-12Hz-1.7B-CustomVoice"
OUTPUT_DIR = PROJECT_ROOT / "outputs" / "tts" / "benchmark"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

TEST_TEXTS = [
    "This isn't nostalgia. It's economics.",
    "Code just got that cheap. So why are we still patching?",
]

INSTRUCTION = "Speak with a confident, authoritative tone like a knowledgeable educator."
SPEAKER = "Aiden"


def benchmark_device(device_name: str, device: str, dtype: torch.dtype):
    """Benchmark TTS generation on a specific device."""
    print(f"\n{'='*60}")
    print(f"BENCHMARKING: {device_name} (device={device}, dtype={dtype})")
    print(f"{'='*60}")

    # Load model
    t0 = time.time()
    print(f"Loading model to {device}...", flush=True)
    model = Qwen3TTSModel.from_pretrained(
        str(MODEL_PATH),
        device_map=device,
        torch_dtype=dtype,
        attn_implementation="sdpa",
    )
    load_time = time.time() - t0
    print(f"Model loaded in {load_time:.1f}s", flush=True)

    # Warmup pass (first inference is slower due to compilation)
    print("Warmup pass...", flush=True)
    t0 = time.time()
    wavs, sr = model.generate_custom_voice(
        text="Hello, this is a warmup.",
        language="English",
        speaker=SPEAKER,
        instruct=INSTRUCTION,
    )
    warmup_time = time.time() - t0
    print(f"Warmup: {warmup_time:.1f}s", flush=True)

    # Benchmark passes
    times = []
    for i, text in enumerate(TEST_TEXTS):
        print(f"\nGenerating [{i+1}/{len(TEST_TEXTS)}]: {text[:50]}...", flush=True)
        t0 = time.time()
        wavs, sr = model.generate_custom_voice(
            text=text,
            language="English",
            speaker=SPEAKER,
            instruct=INSTRUCTION,
        )
        elapsed = time.time() - t0
        times.append(elapsed)

        duration = len(wavs[0]) / sr
        rtf = elapsed / duration  # real-time factor
        print(f"  Time: {elapsed:.2f}s | Audio: {duration:.2f}s | RTF: {rtf:.2f}x", flush=True)

        # Save output for quality comparison
        out_path = OUTPUT_DIR / f"{device_name}_sample_{i}.wav"
        sf.write(str(out_path), wavs[0], sr)

    avg_time = sum(times) / len(times)
    print(f"\n--- {device_name} SUMMARY ---")
    print(f"  Load time: {load_time:.1f}s")
    print(f"  Warmup: {warmup_time:.1f}s")
    print(f"  Avg generation: {avg_time:.2f}s")

    # Cleanup
    del model
    if device == "mps":
        torch.mps.empty_cache()

    return {"load": load_time, "warmup": warmup_time, "avg": avg_time, "times": times}


def main():
    print("Qwen3-TTS CPU vs MPS Benchmark")
    print(f"PyTorch: {torch.__version__}")
    print(f"MPS available: {torch.backends.mps.is_available()}")

    results = {}

    # Test CPU first
    results["cpu"] = benchmark_device("CPU", "cpu", torch.float32)

    # Test MPS
    if torch.backends.mps.is_available():
        results["mps"] = benchmark_device("MPS", "mps", torch.float32)

    # Summary
    print(f"\n{'='*60}")
    print("FINAL COMPARISON")
    print(f"{'='*60}")
    for name, r in results.items():
        print(f"  {name:>4}: load={r['load']:.1f}s  warmup={r['warmup']:.1f}s  avg={r['avg']:.2f}s")

    if "cpu" in results and "mps" in results:
        speedup = results["cpu"]["avg"] / results["mps"]["avg"]
        print(f"\n  MPS speedup: {speedup:.2f}x {'faster' if speedup > 1 else 'slower'}")
        if speedup > 1:
            print(f"  Recommendation: USE MPS")
        else:
            print(f"  Recommendation: KEEP CPU")


if __name__ == "__main__":
    main()
