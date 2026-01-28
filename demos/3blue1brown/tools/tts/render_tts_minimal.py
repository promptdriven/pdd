#!/usr/bin/env python3
"""Minimal TTS test - generate first 5 segments only."""

import sys
import time
from pathlib import Path

print("Starting minimal TTS render...", flush=True)
start_time = time.time()

import torch
print(f"PyTorch loaded in {time.time()-start_time:.1f}s", flush=True)

import soundfile as sf
import numpy as np
print(f"Imports done in {time.time()-start_time:.1f}s", flush=True)

from qwen_tts import Qwen3TTSModel
print(f"Qwen imported in {time.time()-start_time:.1f}s", flush=True)

# Use CPU
device = "cpu"
dtype = torch.float32

project_root = Path(__file__).resolve().parent.parent.parent
model_path = project_root / "models" / "Qwen3-TTS-12Hz-1.7B-CustomVoice"
print(f"Loading model from {model_path}...", flush=True)

load_start = time.time()
model = Qwen3TTSModel.from_pretrained(
    str(model_path),
    device_map=device,
    torch_dtype=dtype,
    attn_implementation="sdpa",
)
print(f"Model loaded in {time.time()-load_start:.1f}s (total: {time.time()-start_time:.1f}s)", flush=True)

# Test segments
test_segments = [
    ("If you use Cursor, or Claude Code, or Copilot...", "Speak casually and observationally."),
    ("you're getting really good at this.", "Speak with subtle appreciation."),
    ("But here's what your great-grandmother figured out sixty years ago.", "Speak knowingly, as if sharing an insider insight."),
    ("When socks got cheap enough... she stopped.", "Speak matter-of-factly with dry wit."),
    ("Code just got that cheap.", "Speak directly and punchily."),
]

output_dir = project_root / "outputs" / "tts"
output_dir.mkdir(exist_ok=True)

all_audio = []
sample_rate = 24000

for i, (text, instruction) in enumerate(test_segments):
    print(f"\n[{i+1}/5] Generating: {text[:40]}...", flush=True)
    gen_start = time.time()

    wavs, sr = model.generate_custom_voice(
        text=text,
        language="English",
        speaker="Aiden",
        instruct=f"Speak with a confident, authoritative tone. {instruction}",
    )

    sample_rate = sr
    gen_time = time.time() - gen_start
    duration = len(wavs[0]) / sr

    print(f"  Generated {duration:.1f}s audio in {gen_time:.1f}s", flush=True)

    sf.write(str(output_dir / f"test_segment_{i:02d}.wav"), wavs[0], sr)
    all_audio.append(wavs[0])

# Concatenate
final_audio = np.concatenate(all_audio)
sf.write(str(output_dir / "test_5_segments.wav"), final_audio, sample_rate)

total_time = time.time() - start_time
audio_duration = len(final_audio) / sample_rate

print(f"\n{'='*50}", flush=True)
print(f"Done! Generated {audio_duration:.1f}s of audio", flush=True)
print(f"Total time: {total_time:.1f}s ({total_time/60:.1f} min)", flush=True)
print(f"Time per segment: {(total_time - (time.time()-start_time)):.1f}s avg", flush=True)
print(f"\nEstimate for 79 segments: {79 * (total_time/5) / 60:.0f} minutes", flush=True)
