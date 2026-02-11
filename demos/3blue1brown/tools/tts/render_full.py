#!/usr/bin/env python3
"""Simple full render script - minimal complexity."""

import sys
sys.stdout.reconfigure(line_buffering=True)

import re
import time
from pathlib import Path

print("Starting...", flush=True)
start = time.time()

import numpy as np
import torch
import soundfile as sf
from qwen_tts import Qwen3TTSModel

print(f"Imports done in {time.time()-start:.1f}s", flush=True)

# Parse script
project_root = Path(__file__).resolve().parent.parent.parent
script_path = project_root / "narrative" / "tts_script.md"
content = script_path.read_text()

# Extract speech segments
parts = content.split('---')
if len(parts) > 2:
    content = '---'.join(parts[2:])

segments = []
current_tone = ""

for line in content.split('\n'):
    line = line.strip()
    if not line or line.startswith('#'):
        continue

    if line.startswith('[TONE:'):
        m = re.match(r'\[TONE:\s*([^\]]+)\]', line)
        if m:
            current_tone = m.group(1).strip()
        continue

    if line.startswith('['):  # Skip other annotations
        continue

    # Clean text
    text = re.sub(r'\[.*?\]', '', line)
    text = re.sub(r'\*\*([^*]+)\*\*', r'\1', text)
    text = re.sub(r'\*([^*]+)\*', r'\1', text)
    text = text.strip()

    if text and 'Total runtime' not in text:
        segments.append((text, current_tone))

print(f"Found {len(segments)} segments", flush=True)

# Load model
print("Loading model...", flush=True)
load_start = time.time()

model = Qwen3TTSModel.from_pretrained(
    "Qwen/Qwen3-TTS-12Hz-1.7B-CustomVoice",  # Load from HF hub (cached)
    device_map="cpu",
    torch_dtype=torch.float32,
    attn_implementation="sdpa",
)

print(f"Model loaded in {time.time()-load_start:.1f}s", flush=True)

# Generate
output_dir = project_root / "outputs" / "tts"
output_dir.mkdir(exist_ok=True)

all_audio = []
sample_rate = 24000

for i, (text, tone) in enumerate(segments):
    print(f"[{i+1}/{len(segments)}] {text[:50]}...", flush=True)

    instruction = f"Speak with a confident, authoritative tone like a knowledgeable educator."
    if tone:
        instruction += f" {tone}."

    wavs, sr = model.generate_custom_voice(
        text=text,
        language="English",
        speaker="Aiden",
        instruct=instruction,
    )

    sample_rate = sr
    all_audio.append(wavs[0])
    sf.write(str(output_dir / f"segment_{i:03d}.wav"), wavs[0], sr)
    print(f"  -> {len(wavs[0])/sr:.1f}s audio", flush=True)

# Concatenate
print("\nConcatenating...", flush=True)
final = np.concatenate(all_audio)
sf.write(str(output_dir / "pdd_intro_voiceover.wav"), final, sample_rate)

total_time = time.time() - start
print(f"\nDone! Total time: {total_time/60:.1f} minutes", flush=True)
print(f"Audio duration: {len(final)/sample_rate/60:.1f} minutes", flush=True)
