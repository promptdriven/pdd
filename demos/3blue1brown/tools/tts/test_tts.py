#!/usr/bin/env python3
"""
Quick test of Qwen3-TTS to verify setup works.
"""

import sys
from pathlib import Path

print("Starting TTS test...", flush=True)

import torch
print(f"PyTorch version: {torch.__version__}", flush=True)
print(f"CUDA available: {torch.cuda.is_available()}", flush=True)
print(f"MPS available: {torch.backends.mps.is_available()}", flush=True)

import soundfile as sf
print("Soundfile imported OK", flush=True)

from qwen_tts import Qwen3TTSModel
print("Qwen TTS imported OK", flush=True)

# Determine device
if torch.cuda.is_available():
    device = "cuda:0"
    dtype = torch.bfloat16
    attn_impl = "flash_attention_2"
elif torch.backends.mps.is_available():
    device = "mps"
    dtype = torch.float32
    attn_impl = "sdpa"
else:
    device = "cpu"
    dtype = torch.float32
    attn_impl = "sdpa"

print(f"Using device: {device}, dtype: {dtype}, attn: {attn_impl}", flush=True)

project_root = Path(__file__).resolve().parent.parent.parent
model_path = project_root / "models" / "Qwen3-TTS-12Hz-1.7B-CustomVoice"
print(f"Model path: {model_path}", flush=True)
print(f"Model exists: {model_path.exists()}", flush=True)

print("Loading model (this may take a few minutes on first run)...", flush=True)

try:
    model = Qwen3TTSModel.from_pretrained(
        str(model_path),
        device_map=device,
        torch_dtype=dtype,
        attn_implementation=attn_impl,
    )
    print("Model loaded successfully!", flush=True)
except Exception as e:
    print(f"Error loading model: {e}", flush=True)
    import traceback
    traceback.print_exc()
    sys.exit(1)

# Test generation
test_text = "This is a test of the text to speech system. Prompt Driven Development is here."
instruction = "Speak with a confident, authoritative tone like a knowledgeable educator."

print(f"\nGenerating test audio...", flush=True)
print(f"Text: {test_text}", flush=True)
print(f"Instruction: {instruction}", flush=True)

try:
    wavs, sr = model.generate_custom_voice(
        text=test_text,
        language="English",
        speaker="Aiden",
        instruct=instruction,
    )

    output_path = project_root / "outputs" / "tts" / "test_output.wav"
    output_path.parent.mkdir(exist_ok=True)
    sf.write(str(output_path), wavs[0], sr)

    duration = len(wavs[0]) / sr
    print(f"\nSuccess! Audio saved to: {output_path}", flush=True)
    print(f"Duration: {duration:.2f} seconds", flush=True)
    print(f"Sample rate: {sr} Hz", flush=True)

except Exception as e:
    print(f"Error generating audio: {e}", flush=True)
    import traceback
    traceback.print_exc()
    sys.exit(1)

print("\nTest complete!", flush=True)
