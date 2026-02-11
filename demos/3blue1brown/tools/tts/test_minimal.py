#!/usr/bin/env python3
"""Minimal test - parse only, no imports from render_tts."""

import re
import time
from pathlib import Path
from dataclasses import dataclass

LOG = Path(__file__).resolve().parent.parent.parent / "outputs" / "tts" / "diag3_log.txt"

def log(msg):
    ts = time.strftime("%H:%M:%S")
    line = f"[{ts}] {msg}"
    with open(LOG, "a") as f:
        f.write(line + "\n")
    print(line, flush=True)

with open(LOG, "w") as f:
    f.write("")

@dataclass
class Segment:
    text: str
    tone: str = ""
    pace: str = ""
    emotion: str = ""
    pause_after: float = 0.0

def parse_tts_script(script_path):
    log("  parse: opening file...")
    with open(script_path, 'r') as f:
        content = f.read()
    log(f"  parse: read {len(content)} chars")

    parts = content.split('---')
    log(f"  parse: {len(parts)} parts after split")
    if len(parts) > 2:
        content = '---'.join(parts[2:])

    segments = []
    current_tone = ""
    current_pace = ""
    current_emotion = ""

    lines = content.split('\n')
    log(f"  parse: {len(lines)} lines to process")

    i = 0
    while i < len(lines):
        line = lines[i].strip()

        if line.startswith('##') or line.startswith('###') or not line:
            i += 1
            continue

        if line.startswith('[TONE:'):
            match = re.match(r'\[TONE:\s*([^\]]+)\]', line)
            if match:
                current_tone = match.group(1).strip()
            i += 1
            continue

        if line.startswith('[PACE:'):
            match = re.match(r'\[PACE:\s*([^\]]+)\]', line)
            if match:
                current_pace = match.group(1).strip()
            i += 1
            continue

        if line.startswith('[EMOTION:'):
            match = re.match(r'\[EMOTION:\s*([^\]]+)\]', line)
            if match:
                current_emotion = match.group(1).strip()
            i += 1
            continue

        if line.startswith('[PAUSE:'):
            match = re.match(r'\[PAUSE:\s*([\d.]+)s?\]', line)
            if match:
                pause_duration = float(match.group(1))
                if segments:
                    segments[-1].pause_after += pause_duration
            i += 1
            continue

        if line.startswith('[FADE'):
            i += 1
            continue

        text = line
        pause_after = 0.0

        inline_pauses = re.findall(r'\[PAUSE:\s*([\d.]+)s?\]', text)
        for pause in inline_pauses:
            pause_after += float(pause)
        text = re.sub(r'\[PAUSE:\s*[\d.]+s?\]', '', text)
        text = re.sub(r'\[TONE:\s*[^\]]+\]', '', text)
        text = re.sub(r'\[EMOTION:\s*[^\]]+\]', '', text)
        text = re.sub(r'\[PACE:\s*[^\]]+\]', '', text)
        text = re.sub(r'\*\*([^*]+)\*\*', r'\1', text)
        text = re.sub(r'\*([^*]+)\*', r'\1', text)

        text = text.strip()

        if text and not text.startswith('**Total runtime'):
            segments.append(Segment(
                text=text,
                tone=current_tone,
                pace=current_pace,
                emotion=current_emotion,
                pause_after=pause_after
            ))

        i += 1

    return segments

log("Step 1: Parsing script...")
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
script_path = PROJECT_ROOT / "narrative" / "tts_script.md"
segments = parse_tts_script(str(script_path))
log(f"Step 2: Found {len(segments)} segments")

for i, s in enumerate(segments[:3]):
    log(f"  Seg {i}: tone='{s.tone[:20] if s.tone else ''}' text='{s.text[:50]}'")

log("Step 3: Now importing torch and model...")
import torch
from qwen_tts import Qwen3TTSModel
log("Step 4: Imports done")

MODEL_PATH = PROJECT_ROOT / "models" / "Qwen3-TTS-12Hz-1.7B-CustomVoice"
log("Step 5: Loading model...")
t0 = time.time()
model = Qwen3TTSModel.from_pretrained(
    str(MODEL_PATH),
    device_map="cpu",
    torch_dtype=torch.float32,
    attn_implementation="sdpa",
)
log(f"Step 6: Model loaded in {time.time()-t0:.1f}s")

log("Step 7: Generating segment 0...")
from render_tts import build_instruction
seg = segments[0]
instruction = build_instruction(seg)

t0 = time.time()
wavs, sr = model.generate_custom_voice(
    text=seg.text,
    language="English",
    speaker="Aiden",
    instruct=instruction,
)
log(f"Step 8: Generated in {time.time()-t0:.1f}s")

log("Step 9: Generating segment 1...")
seg = segments[1]
instruction = build_instruction(seg)

t0 = time.time()
wavs, sr = model.generate_custom_voice(
    text=seg.text,
    language="English",
    speaker="Aiden",
    instruct=instruction,
)
log(f"Step 10: Generated in {time.time()-t0:.1f}s")

log("DONE - All works!")
