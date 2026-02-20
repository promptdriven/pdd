#!/usr/bin/env python3
"""Audio sync pipeline: concatenate TTS segments + transcribe with Whisper.

For each section, this script:
1. Concatenates the relevant TTS segment WAV files with pauses
2. Runs faster-whisper for word-level timestamps
3. Saves concatenated audio + timestamps JSON
4. Copies narration to Remotion public dir

Usage:
    python sync_audio.py --section part1_economics   # Single section
    python sync_audio.py --section all               # All sections
    python sync_audio.py --section all --parallel     # Parallel processing
"""

import argparse
import json
import re
import shutil
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

import numpy as np
import soundfile as sf

from utils import (
    PROJECT_ROOT, TTS_OUTPUT_DIR, NARRATIVE_DIR, REMOTION_PUBLIC,
    load_project_config, emit_progress, emit_error, emit_done,
)

SAMPLE_RATE = 24000


def build_section_map() -> dict:
    """Build section processing map from project.json audioSync config."""
    config = load_project_config()
    audio_sync = config.get("audioSync", {})
    section_groups = audio_sync.get("sectionGroups", {})
    sections = {s["id"]: s for s in config.get("sections", [])}

    result = {}
    for section_id, group in section_groups.items():
        section = sections.get(section_id)
        if not section:
            continue
        result[section_id] = {
            "name": section["label"],
            "startSegment": group["startSegment"],
            "endSegment": group["endSegment"],
            "outputPrefix": section_id,
            "outputDir": section["specDir"],
        }
    return result


def parse_segment_range(start_seg: str, end_seg: str) -> tuple[int, int]:
    """Parse segment names like 'cold_open_001' into numeric indices.

    Convention: segment files are named segment_NNN.wav where NNN is 0-padded.
    The audioSync config stores logical names. We need the TTS output dir
    to figure out which segment files correspond.
    """
    # Extract the numeric suffix from segment names
    start_match = re.search(r"(\d+)$", start_seg)
    end_match = re.search(r"(\d+)$", end_seg)
    if start_match and end_match:
        return int(start_match.group(1)), int(end_match.group(1))
    return 0, 0


def generate_silence(duration: float) -> np.ndarray:
    """Generate silence of specified duration at SAMPLE_RATE."""
    return np.zeros(int(duration * SAMPLE_RATE), dtype=np.float32)


def parse_pause_durations(script_path: Path) -> dict[int, float]:
    """Parse the TTS script to get pause durations after each segment."""
    if not script_path.exists():
        return {}

    with open(script_path) as f:
        content = f.read()

    parts = content.split("---")
    if len(parts) > 2:
        content = "---".join(parts[2:])

    pauses = {}
    seg_idx = 0
    current_pause = 0.0

    for line in content.split("\n"):
        line = line.strip()
        if line.startswith("##") or line.startswith("###") or not line:
            continue
        if line.startswith("[PAUSE:"):
            match = re.match(r"\[PAUSE:\s*([\d.]+)s?\]", line)
            if match:
                current_pause += float(match.group(1))
            continue
        if line.startswith(("[TONE:", "[PACE:", "[EMOTION:", "[FADE")):
            continue

        text = line
        inline_pauses = re.findall(r"\[PAUSE:\s*([\d.]+)s?\]", text)
        inline_total = sum(float(p) for p in inline_pauses)
        text = re.sub(r"\[PAUSE:\s*[\d.]+s?\]", "", text)
        text = re.sub(r"\[TONE:\s*[^\]]+\]", "", text)
        text = re.sub(r"\[EMOTION:\s*[^\]]+\]", "", text)
        text = re.sub(r"\[PACE:\s*[^\]]+\]", "", text)
        text = re.sub(r"\*\*([^*]+)\*\*", r"\1", text)
        text = re.sub(r"\*([^*]+)\*", r"\1", text)
        text = text.strip()

        if text and not text.startswith("**Total runtime"):
            pauses[seg_idx] = current_pause + inline_total
            current_pause = 0.0
            seg_idx += 1

    return pauses


def concatenate_segments(section_id: str, section_info: dict) -> Path | None:
    """Concatenate TTS segments for a section with pauses."""
    script_path = NARRATIVE_DIR / "tts_script.md"
    pauses = parse_pause_durations(script_path)

    output_dir = TTS_OUTPUT_DIR / section_info["outputDir"]
    output_dir.mkdir(parents=True, exist_ok=True)

    seg_start, seg_end = parse_segment_range(
        section_info["startSegment"], section_info["endSegment"]
    )

    audio_parts = []
    for seg_idx in range(seg_start, seg_end + 1):
        seg_file = TTS_OUTPUT_DIR / f"segment_{seg_idx:03d}.wav"
        if not seg_file.exists():
            continue

        if seg_idx > seg_start and seg_idx in pauses and pauses[seg_idx] > 0:
            audio_parts.append(generate_silence(pauses[seg_idx]))

        data, sr = sf.read(str(seg_file))
        if sr != SAMPLE_RATE:
            emit_progress("audio-sync", -1, f"Warning: {seg_file.name} sr={sr}, expected {SAMPLE_RATE}")
        audio_parts.append(data.astype(np.float32))

    if not audio_parts:
        return None

    final_audio = np.concatenate(audio_parts)
    output_path = output_dir / f"{section_info['outputPrefix']}_narration.wav"
    sf.write(str(output_path), final_audio, SAMPLE_RATE)

    # Copy to Remotion public dir
    REMOTION_PUBLIC.mkdir(parents=True, exist_ok=True)
    remotion_path = REMOTION_PUBLIC / f"{section_info['outputPrefix']}_narration.wav"
    shutil.copy2(output_path, remotion_path)

    duration = len(final_audio) / SAMPLE_RATE
    return output_path


def transcribe_audio(audio_path: Path, section_info: dict) -> Path:
    """Transcribe audio with word-level timestamps using faster-whisper."""
    from faster_whisper import WhisperModel

    output_dir = audio_path.parent

    model = WhisperModel("base", compute_type="int8")
    segments_iter, info = model.transcribe(str(audio_path), word_timestamps=True)

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
            "section": section_info["name"],
            "audio_file": audio_path.name,
            "duration": round(info.duration, 2),
            "language": info.language,
            "words": words,
            "segments": segs,
        }, f, indent=2)

    return timestamps_path


def process_section(section_id: str, section_info: dict) -> tuple[str, bool, str]:
    """Full pipeline for one section: concatenate + transcribe."""
    try:
        audio_path = concatenate_segments(section_id, section_info)
        if not audio_path:
            return (section_id, False, "No audio segments found")

        timestamps_path = transcribe_audio(audio_path, section_info)
        return (section_id, True, f"Done: {timestamps_path}")

    except Exception as e:
        import traceback
        traceback.print_exc()
        return (section_id, False, str(e))


def main():
    parser = argparse.ArgumentParser(description="Audio sync pipeline")
    parser.add_argument("--section", default="all", help="Section ID or 'all'")
    parser.add_argument("--parallel", action="store_true", help="Process in parallel")
    parser.add_argument("--concat-only", action="store_true", help="Skip transcription")
    args = parser.parse_args()

    section_map = build_section_map()
    if not section_map:
        emit_error("audio-sync", "No sections found in project.json audioSync config")
        sys.exit(1)

    if args.section == "all":
        sections_to_process = list(section_map.keys())
    elif args.section in section_map:
        sections_to_process = [args.section]
    else:
        emit_error("audio-sync", f"Unknown section: {args.section}. Available: {list(section_map.keys())}")
        sys.exit(1)

    emit_progress("audio-sync", 5, f"Processing {len(sections_to_process)} section(s)")

    results = {}

    if args.parallel and len(sections_to_process) > 1:
        with ThreadPoolExecutor(max_workers=len(sections_to_process)) as executor:
            futures = {
                executor.submit(process_section, key, section_map[key]): key
                for key in sections_to_process
            }
            for future in as_completed(futures):
                key, success, msg = future.result()
                results[key] = (success, msg)
                pct = int(90 * len(results) / len(sections_to_process))
                emit_progress("audio-sync", pct, f"[{key}] {'OK' if success else 'FAILED'}: {msg}")
    else:
        for i, key in enumerate(sections_to_process):
            pct = int(90 * (i / len(sections_to_process)))
            emit_progress("audio-sync", pct, f"Processing {key}...")
            key, success, msg = process_section(key, section_map[key])
            results[key] = (success, msg)

    succeeded = sum(1 for s, _ in results.values() if s)
    total = len(results)

    if succeeded == total:
        emit_done("audio-sync", f"All {total} sections processed successfully")
    else:
        emit_error("audio-sync", f"{succeeded}/{total} sections succeeded")
        sys.exit(1)


if __name__ == "__main__":
    main()
