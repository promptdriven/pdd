#!/usr/bin/env python3
"""Test just the parsing + model load + first segment."""

import sys
import time
from pathlib import Path

LOG = Path(__file__).resolve().parent.parent.parent / "outputs" / "tts" / "diag2_log.txt"

def log(msg):
    ts = time.strftime("%H:%M:%S")
    line = f"[{ts}] {msg}"
    with open(LOG, "a") as f:
        f.write(line + "\n")
    print(line, flush=True)

# Clear log
with open(LOG, "w") as f:
    f.write("")

log("Step 1: Import render_tts parse function...")
sys.path.insert(0, str(Path(__file__).resolve().parent))
from render_tts import parse_tts_script, build_instruction
log("Step 2: parse_tts_script imported")

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
script_path = PROJECT_ROOT / "scripts" / "tts_script.md"

log(f"Step 3: Parsing {script_path}...")
segments = parse_tts_script(str(script_path))
log(f"Step 4: Found {len(segments)} segments")

for i, s in enumerate(segments[:3]):
    log(f"  Seg {i}: tone='{s.tone[:20] if s.tone else ''}' text='{s.text[:50]}'")

log("Step 5: Loading model...")
import torch
from qwen_tts import Qwen3TTSModel

MODEL_PATH = PROJECT_ROOT / "models" / "Qwen3-TTS-12Hz-1.7B-CustomVoice"
t0 = time.time()
model = Qwen3TTSModel.from_pretrained(
    str(MODEL_PATH),
    device_map="cpu",
    torch_dtype=torch.float32,
    attn_implementation="sdpa",
)
log(f"Step 6: Model loaded in {time.time()-t0:.1f}s")

log("Step 7: Generating segment 0...")
seg = segments[0]
instruction = build_instruction(seg)
log(f"  Text: {seg.text[:60]}")
log(f"  Instruction: {instruction[:60]}")

t0 = time.time()
wavs, sr = model.generate_custom_voice(
    text=seg.text,
    language="English",
    speaker="Aiden",
    instruct=instruction,
)
log(f"Step 8: Generated in {time.time()-t0:.1f}s, audio: {len(wavs[0])/sr:.1f}s")

import soundfile as sf
out = PROJECT_ROOT / "outputs" / "tts" / "segment_000.wav"
sf.write(str(out), wavs[0], sr)
log(f"Step 9: Saved to {out}")
log("DONE - Everything works!")
