#!/usr/bin/env python3
"""Quick test: load model and generate 1 segment, with file-based logging."""

import sys
import time
from pathlib import Path

LOG = Path(__file__).resolve().parent.parent.parent / "outputs" / "tts" / "diag_log.txt"

def log(msg):
    with open(LOG, "a") as f:
        f.write(f"[{time.time():.1f}] {msg}\n")
    print(msg, flush=True)

log("Starting diagnostic...")
log("Importing torch...")
import torch
log(f"Torch imported. Version: {torch.__version__}")

log("Importing Qwen3TTSModel...")
from qwen_tts import Qwen3TTSModel
log("Qwen3TTSModel imported")

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
MODEL_PATH = PROJECT_ROOT / "models" / "Qwen3-TTS-12Hz-1.7B-CustomVoice"

log(f"Loading model from {MODEL_PATH}...")
t0 = time.time()
model = Qwen3TTSModel.from_pretrained(
    str(MODEL_PATH),
    device_map="cpu",
    torch_dtype=torch.float32,
    attn_implementation="sdpa",
)
log(f"Model loaded in {time.time()-t0:.1f}s")

log("Generating test segment...")
t0 = time.time()
wavs, sr = model.generate_custom_voice(
    text="This is a test of the text to speech system.",
    language="English",
    speaker="Aiden",
    instruct="Speak with a confident, authoritative tone.",
)
log(f"Generated in {time.time()-t0:.1f}s, audio length: {len(wavs[0])/sr:.1f}s")

import soundfile as sf
out = PROJECT_ROOT / "outputs" / "tts" / "diag_test.wav"
sf.write(str(out), wavs[0], sr)
log(f"Saved to {out}")
log("DONE")
