#!/usr/bin/env python3
"""Render TTS audio from annotated markdown script using Qwen3-TTS.

Parses the TTS script (narrative/tts_script.md) and generates audio segments
with voice instructions based on tone/pace/emotion annotations.

Usage:
    python render_tts.py                          # Render all segments
    python render_tts.py --start-segment 50       # Start numbering from segment 50
    python render_tts.py --script path/to/script   # Custom script path
"""

import argparse
import re
import sys
import time
from dataclasses import dataclass
from pathlib import Path

from utils import (
    PROJECT_ROOT, TTS_OUTPUT_DIR, NARRATIVE_DIR,
    load_project_config, emit_progress, emit_error, emit_done,
)


@dataclass
class Segment:
    """A segment of speech with its annotations."""
    text: str
    tone: str = ""
    pace: str = ""
    emotion: str = ""
    pause_after: float = 0.0


def parse_tts_script(script_path: str) -> list[Segment]:
    """Parse the TTS script markdown and extract segments."""
    with open(script_path) as f:
        content = f.read()

    # Skip the header/key section - start after the first ---
    parts = content.split("---")
    if len(parts) > 2:
        content = "---".join(parts[1:])

    segments = []
    current_tone = ""
    current_pace = ""
    current_emotion = ""

    for line in content.split("\n"):
        line = line.strip()

        if line.startswith("##") or line.startswith("###") or not line:
            continue

        if line.startswith("[TONE:"):
            match = re.match(r"\[TONE:\s*([^\]]+)\]", line)
            if match:
                current_tone = match.group(1).strip()
            continue

        if line.startswith("[PACE:"):
            match = re.match(r"\[PACE:\s*([^\]]+)\]", line)
            if match:
                current_pace = match.group(1).strip()
            continue

        if line.startswith("[EMOTION:"):
            match = re.match(r"\[EMOTION:\s*([^\]]+)\]", line)
            if match:
                current_emotion = match.group(1).strip()
            continue

        if line.startswith("[PAUSE:"):
            match = re.match(r"\[PAUSE:\s*([\d.]+)s?\]", line)
            if match and segments:
                segments[-1].pause_after += float(match.group(1))
            continue

        if line.startswith("[FADE"):
            continue

        # Speech text - clean inline annotations
        text = line
        pause_after = 0.0

        inline_pauses = re.findall(r"\[PAUSE:\s*([\d.]+)s?\]", text)
        for pause in inline_pauses:
            pause_after += float(pause)
        text = re.sub(r"\[PAUSE:\s*[\d.]+s?\]", "", text)
        text = re.sub(r"\[TONE:\s*[^\]]+\]", "", text)
        text = re.sub(r"\[EMOTION:\s*[^\]]+\]", "", text)
        text = re.sub(r"\[PACE:\s*[^\]]+\]", "", text)
        text = re.sub(r"\*\*([^*]+)\*\*", r"\1", text)
        text = re.sub(r"\*([^*]+)\*", r"\1", text)
        text = text.strip()

        if text and not text.startswith("**Total runtime"):
            segments.append(Segment(
                text=text,
                tone=current_tone,
                pace=current_pace,
                emotion=current_emotion,
                pause_after=pause_after,
            ))

    return segments


# Tone → voice instruction mapping
TONE_MAP = {
    "casual, observational": "in a relaxed, conversational manner",
    "slightly impressed": "with subtle appreciation",
    "knowing, conspiratorial": "as if sharing an insider insight",
    "matter-of-fact, dry": "with dry wit and understatement",
    "direct, punchy": "with sharp, decisive delivery",
    "challenging, curious": "with an inquisitive edge",
    "professorial, confident": "with academic authority",
    "explanatory": "clearly and instructively",
    "building momentum": "with increasing energy",
    "pivoting, direct": "transitioning with purpose",
    "historical, sweeping": "with grand perspective",
    "significant, emphatic": "with weight and importance",
    "appreciative but pivoting": "acknowledging then redirecting",
    "pointed, landing the blow": "delivering the key insight",
    "weary wisdom": "with experienced understanding",
    "revealing a secret": "as if unveiling hidden truth",
    "driving home the point": "with conviction",
    "curious, investigative": "with intellectual curiosity",
    "revelatory": "with the excitement of discovery",
    "building wonder": "with growing amazement",
    "setting up the insight": "building anticipation",
    "key insight, slower": "delivering crucial information slowly",
    "philosophical, important": "with gravitas",
    "contrasting": "highlighting the difference",
    "grand reveal": "with dramatic emphasis",
    "crystallizing the metaphor": "bringing the concept into focus",
    "getting technical, engaged": "with technical enthusiasm",
    "introducing key concept": "marking an important new idea",
    "explanatory, visual": "painting a picture with words",
    "key insight, emphatic": "with strong emphasis",
    "satisfying, resolving": "with a sense of completion",
    "building excitement": "with mounting enthusiasm",
    "comparative, driving home": "making a clear comparison",
    "moving to next concept": "transitioning smoothly",
    "clarifying": "making things clear",
    "subtle, insightful": "with nuanced understanding",
    "practical wisdom": "with practical authority",
    "introducing third concept": "introducing another key point",
    "synthesizing": "bringing ideas together",
    "emphatic, memorable": "for lasting impact",
    "intellectual, curious": "with thoughtful curiosity",
    "connecting to PDD": "drawing the connection",
    "liberating, positive": "with optimistic energy",
    "insight landing": "delivering the realization",
    "memorable phrase": "for retention",
    "strategic, analytical": "with analytical precision",
    "describing the old way": "explaining the traditional approach",
    "dismissive": "with mild dismissal",
    "building to contrast": "setting up comparison",
    "summarizing powerfully": "with conclusive force",
    "empathetic, reasonable": "with understanding",
    "same empathy, present day": "with continued understanding",
    "pivotal, serious": "with serious gravity",
    "wry, pointed": "with subtle irony",
    "addressing concerns, reassuring": "reassuringly",
    "insightful": "with keen observation",
    "empowering": "inspirationally",
    "crystallizing": "with clarity",
    "honest, grounded": "authentically",
    "wrapping up, reflective": "reflectively",
    "simple truth": "with straightforward honesty",
    "direct, present": "immediacy",
    "declarative, memorable": "with memorable weight",
    "accepting, matter-of-fact": "accepting reality",
    "final thesis, weight": "with ultimate significance",
    "conclusive, resonant": "with resonant finality",
}

PACE_MAP = {
    "moderate": "",
    "steady": "",
    "slightly slower": "Speak slightly slower.",
    "slightly slower for emphasis": "Speak more slowly for emphasis.",
    "slightly faster": "Speak with more energy and pace.",
    "accelerating slightly": "Gradually increase pace.",
    "deliberate": "Speak deliberately and clearly.",
    "measured, deliberate": "Speak with measured, deliberate pace.",
    "slower, giving each phrase weight": "Speak slowly, giving weight to each phrase.",
    "slow, deliberate": "Speak slowly and deliberately.",
}


def build_instruction(segment: Segment) -> str:
    """Build voice instruction from segment annotations."""
    base = "Speak with a confident, authoritative tone like a knowledgeable educator"
    parts = []

    if segment.tone and segment.tone in TONE_MAP:
        parts.append(TONE_MAP[segment.tone])
    if segment.pace and segment.pace in PACE_MAP and PACE_MAP[segment.pace]:
        parts.append(PACE_MAP[segment.pace])
    if segment.emotion:
        parts.append(f"with {segment.emotion} emotion")

    if parts:
        return f"{base}, {', '.join(parts)}."
    return f"{base}."


def generate_silence(duration: float, sample_rate: int = 24000):
    """Generate silence of specified duration."""
    import numpy as np
    return np.zeros(int(duration * sample_rate), dtype=np.float32)


def main():
    parser = argparse.ArgumentParser(description="Render TTS from annotated script")
    parser.add_argument("--script", help="Path to TTS script")
    parser.add_argument("--start-segment", type=int, default=0, help="Starting segment number")
    args = parser.parse_args()

    config = load_project_config()
    tts_config = config.get("tts", {})

    script_path = Path(args.script) if args.script else NARRATIVE_DIR / "tts_script.md"
    if not script_path.exists():
        emit_error("tts-render", f"TTS script not found: {script_path}")
        sys.exit(1)

    output_dir = TTS_OUTPUT_DIR
    output_dir.mkdir(parents=True, exist_ok=True)

    emit_progress("tts-render", 5, "Parsing TTS script...")
    segments = parse_tts_script(str(script_path))
    emit_progress("tts-render", 10, f"Found {len(segments)} speech segments")

    # Import heavy dependencies
    emit_progress("tts-render", 15, "Loading TTS model...")
    import numpy as np
    import torch
    import soundfile as sf
    from qwen_tts import Qwen3TTSModel

    if torch.cuda.is_available():
        device = "cuda:0"
        dtype = torch.bfloat16
        attn_impl = "flash_attention_2"
    else:
        device = "cpu"
        dtype = torch.float32
        attn_impl = "sdpa"

    model_path = PROJECT_ROOT / tts_config.get("modelPath", "models/Qwen3-TTS-12Hz-1.7B-CustomVoice")
    model = Qwen3TTSModel.from_pretrained(
        str(model_path),
        device_map=device,
        torch_dtype=dtype,
        attn_implementation=attn_impl,
    )

    speaker = tts_config.get("speaker", "Aiden")
    sample_rate = tts_config.get("sampleRate", 24000)
    all_audio = []

    emit_progress("tts-render", 20, f"Generating audio with speaker: {speaker}")

    for i, segment in enumerate(segments):
        pct = 20 + int(70 * (i / len(segments)))
        emit_progress("tts-render", pct, f"[{i+1}/{len(segments)}] {segment.text[:60]}...")

        try:
            wavs, sr = model.generate_custom_voice(
                text=segment.text,
                language="English",
                speaker=speaker,
                instruct=build_instruction(segment),
            )
            sample_rate = sr
            all_audio.append(wavs[0])

            if segment.pause_after > 0:
                all_audio.append(generate_silence(segment.pause_after, sample_rate))

            seg_num = i + args.start_segment
            sf.write(str(output_dir / f"segment_{seg_num:03d}.wav"), wavs[0], sr)

        except Exception as e:
            emit_progress("tts-render", pct, f"Error on segment {i}: {e}")
            all_audio.append(generate_silence(0.5, sample_rate))

    emit_progress("tts-render", 92, "Concatenating all segments...")
    final_audio = np.concatenate(all_audio)
    output_file = output_dir / "pdd_intro_voiceover.wav"
    sf.write(str(output_file), final_audio, sample_rate)

    duration_minutes = len(final_audio) / sample_rate / 60
    emit_done("tts-render", f"Done: {output_file.name} ({duration_minutes:.1f} min)")


if __name__ == "__main__":
    main()
