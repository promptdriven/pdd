#!/usr/bin/env python3
"""
Render the PDD intro TTS script using Qwen3-TTS.

Parses the annotated markdown script and generates audio segments
with appropriate voice instructions.
"""

import re
import sys
import time
from pathlib import Path
from dataclasses import dataclass

# Log file for monitoring progress when running in background
_LOG_FILE = None

def log(msg):
    """Print and write to log file for reliable progress monitoring."""
    ts = time.strftime("%H:%M:%S")
    line = f"[{ts}] {msg}"
    print(line, flush=True)
    if _LOG_FILE:
        with open(_LOG_FILE, "a") as f:
            f.write(line + "\n")


@dataclass
class Segment:
    """A segment of speech with its annotations."""
    text: str
    tone: str = ""
    pace: str = ""
    emotion: str = ""
    pause_after: float = 0.0  # seconds


def parse_tts_script(script_path: str) -> list[Segment]:
    """Parse the TTS script markdown and extract segments."""
    with open(script_path, 'r') as f:
        content = f.read()

    # Skip the header/key section - start after the first ---
    parts = content.split('---')
    if len(parts) > 2:
        content = '---'.join(parts[2:])  # Skip header and annotations key

    segments = []
    current_tone = ""
    current_pace = ""
    current_emotion = ""

    lines = content.split('\n')

    i = 0
    while i < len(lines):
        line = lines[i].strip()

        # Skip section headers and empty lines for now
        if line.startswith('##') or line.startswith('###') or not line:
            i += 1
            continue

        # Check for annotations
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
            # Standalone pause - add silence
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

        # This is actual speech text
        # Clean up the text - remove inline annotations
        text = line
        pause_after = 0.0

        # Extract inline pauses like [PAUSE: 0.5s]
        inline_pauses = re.findall(r'\[PAUSE:\s*([\d.]+)s?\]', text)
        for pause in inline_pauses:
            pause_after += float(pause)
        text = re.sub(r'\[PAUSE:\s*[\d.]+s?\]', '', text)

        # Remove inline tone/emotion markers
        text = re.sub(r'\[TONE:\s*[^\]]+\]', '', text)
        text = re.sub(r'\[EMOTION:\s*[^\]]+\]', '', text)
        text = re.sub(r'\[PACE:\s*[^\]]+\]', '', text)

        # Clean up markdown emphasis for TTS (keep the words, remove markers)
        # **word** -> word (strong emphasis - we'll handle via instruction)
        # *word* -> word (light emphasis)
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


def build_instruction(segment: Segment) -> str:
    """Build voice instruction from segment annotations."""
    parts = []

    # Base voice character for authoritative male voice
    base = "Speak with a confident, authoritative tone like a knowledgeable educator"

    # Map tones to instructions
    tone_map = {
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

    # Map pace to instructions
    pace_map = {
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

    # Build the instruction
    if segment.tone and segment.tone in tone_map:
        parts.append(tone_map[segment.tone])

    if segment.pace and segment.pace in pace_map and pace_map[segment.pace]:
        parts.append(pace_map[segment.pace])

    if segment.emotion:
        parts.append(f"with {segment.emotion} emotion")

    if parts:
        return f"{base}, {', '.join(parts)}."
    else:
        return f"{base}."


def generate_silence(duration: float, sample_rate: int = 24000):
    """Generate silence of specified duration."""
    import numpy as np
    num_samples = int(duration * sample_rate)
    return np.zeros(num_samples, dtype=np.float32)


def main():
    global _LOG_FILE
    project_root = Path(__file__).resolve().parent.parent.parent
    script_path = project_root / "scripts" / "tts_script.md"
    output_dir = project_root / "outputs" / "tts"
    output_dir.mkdir(exist_ok=True)

    # Set up log file for monitoring in background mode
    _LOG_FILE = str(output_dir / "render_log.txt")
    with open(_LOG_FILE, "w") as f:
        f.write("")  # Clear log

    log("Parsing TTS script...")
    segments = parse_tts_script(str(script_path))
    log(f"Found {len(segments)} speech segments")

    # Print first few segments for verification
    log("First 5 segments:")
    for i, seg in enumerate(segments[:5]):
        log(f"  {i+1}. [{seg.tone[:30] if seg.tone else 'no tone'}...] {seg.text[:50]}...")

    # Import heavy dependencies inside main
    log("Importing torch and model...")
    import numpy as np
    import torch
    import soundfile as sf
    from qwen_tts import Qwen3TTSModel
    log("Imports done")

    log("Loading Qwen3-TTS model...")

    # Determine device
    # Force CPU on Mac - MPS has long compilation times for this model
    if torch.cuda.is_available():
        device = "cuda:0"
        dtype = torch.bfloat16
        attn_impl = "flash_attention_2"
    else:
        # Use CPU - more reliable than MPS for large transformer models
        device = "cpu"
        dtype = torch.float32
        attn_impl = "sdpa"

    log(f"Using device: {device}, dtype: {dtype}")

    model_path = project_root / "models" / "Qwen3-TTS-12Hz-1.7B-CustomVoice"

    t0 = time.time()
    model = Qwen3TTSModel.from_pretrained(
        str(model_path),
        device_map=device,
        torch_dtype=dtype,
        attn_implementation=attn_impl,
    )
    log(f"Model loaded in {time.time()-t0:.1f}s")

    # Voice selection - using Aiden for authoritative American male voice
    speaker = "Aiden"

    all_audio = []
    sample_rate = 24000  # Qwen3-TTS uses 24kHz

    log(f"Generating audio with speaker: {speaker}")
    log("-" * 60)

    for i, segment in enumerate(segments):
        instruction = build_instruction(segment)

        log(f"[{i+1}/{len(segments)}] Generating: {segment.text[:60]}...")

        try:
            t0 = time.time()
            wavs, sr = model.generate_custom_voice(
                text=segment.text,
                language="English",
                speaker=speaker,
                instruct=instruction,
            )
            elapsed = time.time() - t0

            sample_rate = sr
            audio_dur = len(wavs[0]) / sr
            all_audio.append(wavs[0])

            # Add pause if specified
            if segment.pause_after > 0:
                silence = generate_silence(segment.pause_after, sample_rate)
                all_audio.append(silence)

            # Save individual segment
            segment_file = output_dir / f"segment_{i:03d}.wav"
            sf.write(str(segment_file), wavs[0], sr)
            log(f"  Done: {elapsed:.1f}s -> {audio_dur:.1f}s audio | {segment_file.name}")

        except Exception as e:
            log(f"  ERROR: {e}")
            import traceback
            log(f"  {traceback.format_exc()}")
            # Add a small silence as placeholder
            all_audio.append(generate_silence(0.5, sample_rate))

    # Concatenate all audio
    log("Concatenating all segments...")
    final_audio = np.concatenate(all_audio)

    # Save final output
    output_file = output_dir / "pdd_intro_voiceover.wav"
    sf.write(str(output_file), final_audio, sample_rate)

    duration_minutes = len(final_audio) / sample_rate / 60
    log(f"Done! Output saved to: {output_file}")
    log(f"Total duration: {duration_minutes:.1f} minutes")


if __name__ == "__main__":
    main()
