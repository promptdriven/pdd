#!/usr/bin/env python3
"""
Audio sync pipeline: concatenate TTS segments + transcribe with Whisper.

For each section of the video, this script:
1. Concatenates the relevant TTS segment WAV files with pauses
2. Runs faster-whisper to get word-level timestamps
3. Saves concatenated audio + timestamps JSON

Usage:
    python sync_audio_pipeline.py --section part1    # Process Part 1 only
    python sync_audio_pipeline.py --section all       # Process all sections
    python sync_audio_pipeline.py --section all --parallel  # All sections in parallel
"""

import argparse
import json
import os
import re
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

import numpy as np
import soundfile as sf

# Paths
SCRIPT_DIR = Path(__file__).parent
PROJECT_ROOT = SCRIPT_DIR.parent.parent
TTS_DIR = PROJECT_ROOT / "outputs" / "tts"
REMOTION_PUBLIC = PROJECT_ROOT / "remotion" / "public"
TTS_SCRIPT = PROJECT_ROOT / "scripts" / "tts_script.md"

SAMPLE_RATE = 24000  # Qwen3-TTS output rate


# Section definitions: name, segment range, output prefix, remotion folder mapping
# Segment ranges from TTS generation of tts_script.md (103 segments total).
# Separator segments (30, 46, 72, 81, 91) contain "---" text and are excluded.
# Segments 101-102 are junk ("---" and "Total runtime" text).
SECTIONS = {
    "part1": {
        "name": "Part 1: Economics of Darning",
        "seg_start": 0,
        "seg_end": 29,
        "output_prefix": "part1_economics",
        "output_dir": "01-economics",
    },
    "part2": {
        "name": "Part 2: Paradigm Shift",
        "seg_start": 31,
        "seg_end": 45,
        "output_prefix": "part2_paradigm_shift",
        "output_dir": "02-paradigm-shift",
    },
    "part3": {
        "name": "Part 3: Mold Has Three Parts",
        "seg_start": 47,
        "seg_end": 71,
        "output_prefix": "part3_mold",
        "output_dir": "03-mold-has-three-parts",
    },
    "part4": {
        "name": "Part 4: Precision Tradeoff",
        "seg_start": 73,
        "seg_end": 80,
        "output_prefix": "part4_precision",
        "output_dir": "04-precision-tradeoff",
    },
    "part5": {
        "name": "Part 5: Compound Returns",
        "seg_start": 82,
        "seg_end": 90,
        "output_prefix": "part5_compound",
        "output_dir": "05-compound-returns",
    },
    "closing": {
        "name": "Closing",
        "seg_start": 92,
        "seg_end": 100,
        "output_prefix": "closing",
        "output_dir": "06-closing",
    },
}


def parse_pause_durations() -> dict[int, float]:
    """Parse the TTS script to get pause durations after each segment."""
    with open(TTS_SCRIPT) as f:
        content = f.read()

    parts = content.split("---")
    if len(parts) > 2:
        content = "---".join(parts[2:])

    pauses = {}
    seg_idx = 0
    current_pause = 0.0

    lines = content.split("\n")
    for line in lines:
        line = line.strip()

        # Skip headers, empty lines
        if line.startswith("##") or line.startswith("###") or not line:
            continue

        # Standalone pause - accumulate
        if line.startswith("[PAUSE:"):
            match = re.match(r"\[PAUSE:\s*([\d.]+)s?\]", line)
            if match:
                current_pause += float(match.group(1))
            continue

        # Skip annotation lines
        if line.startswith("[TONE:") or line.startswith("[PACE:") or line.startswith("[EMOTION:") or line.startswith("[FADE"):
            continue

        # Speech text - extract inline pauses too
        text = line
        inline_pauses = re.findall(r"\[PAUSE:\s*([\d.]+)s?\]", text)
        inline_total = sum(float(p) for p in inline_pauses)

        # Clean the text
        text = re.sub(r"\[PAUSE:\s*[\d.]+s?\]", "", text)
        text = re.sub(r"\[TONE:\s*[^\]]+\]", "", text)
        text = re.sub(r"\[EMOTION:\s*[^\]]+\]", "", text)
        text = re.sub(r"\[PACE:\s*[^\]]+\]", "", text)
        text = re.sub(r"\*\*([^*]+)\*\*", r"\1", text)
        text = re.sub(r"\*([^*]+)\*", r"\1", text)
        text = text.strip()

        if text and not text.startswith("**Total runtime"):
            # This segment gets the accumulated pause before it as its "pause_before"
            # But we track pause_after for the PREVIOUS segment
            pauses[seg_idx] = current_pause + inline_total
            current_pause = 0.0
            seg_idx += 1

    return pauses


def generate_silence(duration: float) -> np.ndarray:
    """Generate silence of specified duration at SAMPLE_RATE."""
    return np.zeros(int(duration * SAMPLE_RATE), dtype=np.float32)


def concatenate_segments(section_key: str) -> Path:
    """Concatenate TTS segments for a section with pauses."""
    section = SECTIONS[section_key]
    pauses = parse_pause_durations()

    output_dir = TTS_DIR / section["output_dir"]
    output_dir.mkdir(parents=True, exist_ok=True)

    audio_parts = []
    concat_manifest = []

    for seg_idx in range(section["seg_start"], section["seg_end"] + 1):
        seg_file = TTS_DIR / f"segment_{seg_idx:03d}.wav"
        if not seg_file.exists():
            print(f"  Warning: {seg_file.name} not found, skipping")
            continue

        # Add pause before this segment (if not the first)
        if seg_idx > section["seg_start"] and seg_idx in pauses and pauses[seg_idx] > 0:
            pause_dur = pauses[seg_idx]
            audio_parts.append(generate_silence(pause_dur))
            concat_manifest.append(f"silence_{pause_dur}s")

        # Read and add the segment audio
        data, sr = sf.read(str(seg_file))
        if sr != SAMPLE_RATE:
            print(f"  Warning: {seg_file.name} has sr={sr}, expected {SAMPLE_RATE}")
        audio_parts.append(data.astype(np.float32))
        concat_manifest.append(seg_file.name)

    if not audio_parts:
        print(f"  Error: No audio segments found for {section['name']}")
        return None

    # Concatenate
    final_audio = np.concatenate(audio_parts)
    output_path = output_dir / f"{section['output_prefix']}_narration.wav"
    sf.write(str(output_path), final_audio, SAMPLE_RATE)

    duration = len(final_audio) / SAMPLE_RATE
    print(f"  Concatenated {section['seg_end'] - section['seg_start'] + 1} segments → {output_path.name} ({duration:.1f}s)")

    # Save manifest
    manifest_path = output_dir / "concat_manifest.txt"
    with open(manifest_path, "w") as f:
        f.write("\n".join(concat_manifest))

    # Copy to Remotion public dir
    remotion_path = REMOTION_PUBLIC / f"{section['output_prefix']}_narration.wav"
    import shutil
    shutil.copy2(output_path, remotion_path)
    print(f"  Copied to {remotion_path.name}")

    return output_path


def transcribe_audio(audio_path: Path, section_key: str) -> Path:
    """Transcribe audio with word-level timestamps using faster-whisper."""
    from faster_whisper import WhisperModel

    section = SECTIONS[section_key]
    output_dir = audio_path.parent

    print(f"  Transcribing {audio_path.name}...")
    model = WhisperModel("base", compute_type="int8")
    segments_iter, info = model.transcribe(
        str(audio_path),
        word_timestamps=True,
    )

    words = []
    segs = []
    for seg in segments_iter:
        segs.append({
            "start": round(seg.start, 2),
            "end": round(seg.end, 2),
            "text": seg.text.strip(),
        })
        for w in seg.words:
            words.append({
                "word": w.word.strip(),
                "start": round(w.start, 2),
                "end": round(w.end, 2),
                "probability": round(w.probability, 3),
            })

    timestamps_path = output_dir / "word_timestamps.json"
    with open(timestamps_path, "w") as f:
        json.dump({
            "section": section["name"],
            "audio_file": audio_path.name,
            "duration": round(info.duration, 2),
            "language": info.language,
            "words": words,
            "segments": segs,
        }, f, indent=2)

    print(f"  Transcribed: {len(words)} words, {len(segs)} segments → {timestamps_path.name}")
    return timestamps_path


def process_section(section_key: str) -> tuple[str, bool, str]:
    """Full pipeline for one section: concatenate + transcribe."""
    section = SECTIONS[section_key]
    print(f"\n{'='*60}")
    print(f"Processing: {section['name']}")
    print(f"Segments: {section['seg_start']:03d}-{section['seg_end']:03d}")
    print(f"{'='*60}")

    try:
        # Step 1: Concatenate
        audio_path = concatenate_segments(section_key)
        if not audio_path:
            return (section_key, False, "Concatenation failed")

        # Step 2: Transcribe
        timestamps_path = transcribe_audio(audio_path, section_key)

        return (section_key, True, f"Done → {timestamps_path}")

    except Exception as e:
        import traceback
        traceback.print_exc()
        return (section_key, False, str(e))


def main():
    parser = argparse.ArgumentParser(description="Audio sync pipeline")
    parser.add_argument("--section", default="all",
                        choices=list(SECTIONS.keys()) + ["all"],
                        help="Section to process")
    parser.add_argument("--parallel", action="store_true",
                        help="Process sections in parallel")
    parser.add_argument("--concat-only", action="store_true",
                        help="Only concatenate, skip transcription")
    args = parser.parse_args()

    sections_to_process = list(SECTIONS.keys()) if args.section == "all" else [args.section]

    results = {}

    if args.parallel and len(sections_to_process) > 1:
        print(f"Processing {len(sections_to_process)} sections in parallel...")
        with ThreadPoolExecutor(max_workers=len(sections_to_process)) as executor:
            futures = {
                executor.submit(process_section, key): key
                for key in sections_to_process
            }
            for future in as_completed(futures):
                key, success, msg = future.result()
                results[key] = (success, msg)
                status = "OK" if success else "FAILED"
                print(f"\n[{key}] {status}: {msg}")
    else:
        for key in sections_to_process:
            key, success, msg = process_section(key)
            results[key] = (success, msg)

    # Summary
    print(f"\n{'='*60}")
    print("Pipeline Summary")
    print(f"{'='*60}")
    for key, (success, msg) in results.items():
        status = "OK" if success else "FAILED"
        print(f"  {key}: {status}")

    succeeded = sum(1 for s, _ in results.values() if s)
    print(f"\n  Total: {succeeded}/{len(results)} succeeded")

    if succeeded < len(results):
        sys.exit(1)


if __name__ == "__main__":
    main()
