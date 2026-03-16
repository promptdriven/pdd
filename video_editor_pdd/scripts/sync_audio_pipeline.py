#!/usr/bin/env python3
"""
scripts/sync_audio_pipeline.py

Standalone Python script invoked by the Next.js audio sync API route to:
1. Concatenate TTS segment WAV files into per-section WAV files.
2. Generate word-level timestamps via Faster-Whisper.
3. Copy concatenated audio to Remotion public directory.
4. Print JSON progress lines to stdout for each section.
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile
import re
from difflib import SequenceMatcher
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


def _expand_segment_range(
    section_id: str, start_seg: str, end_seg: str, output_dir: str
) -> List[str]:
    """Expand a startSegment/endSegment range into a list of segment IDs.

    Scans the output directory for WAV files matching the section prefix
    and returns those within the numeric range [start, end].
    """
    # Extract numeric suffix from segment IDs
    start_num = int(start_seg.rsplit("_", 1)[-1])
    end_num = int(end_seg.rsplit("_", 1)[-1])

    result = []
    for num in range(start_num, end_num + 1):
        seg_id = f"{section_id}_{num:03d}"
        seg_path = Path(output_dir) / f"{seg_id}.wav"
        if seg_path.exists():
            result.append(seg_id)
    return result


def load_project(project_dir: str) -> Dict[str, Any]:
    """Load and validate project.json, normalizing sectionGroups access."""
    project_path = Path(project_dir) / "project.json"
    if not project_path.exists():
        raise FileNotFoundError(f"project.json not found at {project_path}")

    with open(project_path, "r", encoding="utf-8") as f:
        project = json.load(f)

    section_groups = project.get("sectionGroups")
    if section_groups is None:
        section_groups = project.get("audioSync", {}).get("sectionGroups")
    if section_groups is None:
        env_groups = os.environ.get("SECTION_GROUPS")
        if env_groups:
            section_groups = json.loads(env_groups)

    if section_groups is None:
        raise ValueError("project.json must include sectionGroups")
    if not isinstance(section_groups, dict):
        raise ValueError("sectionGroups must be a dictionary")

    normalized_project = dict(project)
    normalized_project["sectionGroups"] = section_groups
    return normalized_project


def _coerce_section_groups(
    raw: Dict[str, Any], output_dir: str
) -> Dict[str, List[str]]:
    """Normalize list/range sectionGroups into section_id -> segment_id list."""
    if not isinstance(raw, dict):
        raise ValueError("sectionGroups must be a dictionary")

    section_groups: Dict[str, List[str]] = {}
    for section_id, value in raw.items():
        if isinstance(value, list):
            section_groups[section_id] = value
        elif isinstance(value, dict):
            start_seg = value.get("startSegment", "")
            end_seg = value.get("endSegment", "")
            if start_seg and end_seg:
                section_groups[section_id] = _expand_segment_range(
                    section_id, start_seg, end_seg, output_dir
                )
            else:
                section_groups[section_id] = []
        else:
            section_groups[section_id] = []

    return section_groups


def load_section_groups(
    project_dir: str, output_dir: str
) -> Dict[str, List[str]]:
    """Load section groups from SECTION_GROUPS env var or project.json.

    Returns a dict mapping section_id to a list of segment IDs.
    Handles both formats:
      - List format: {"cold_open": ["cold_open_001", "cold_open_002"]}
      - Range format: {"cold_open": {"startSegment": "...", "endSegment": "..."}}
    """
    # Try SECTION_GROUPS env var first
    env_groups = os.environ.get("SECTION_GROUPS")
    if env_groups:
        raw = json.loads(env_groups)
    else:
        raw = load_project(project_dir).get("sectionGroups", {})

    if not raw:
        raise ValueError("No sectionGroups found")

    return _coerce_section_groups(raw, output_dir)


def get_segment_wav_path(output_dir: str, segment_id: str) -> Path:
    """Construct the path to a segment's WAV file.

    Args:
        output_dir: Base output directory containing segment WAVs.
        segment_id: The segment identifier.

    Returns:
        Path to the segment WAV file.
    """
    return Path(output_dir) / f"{segment_id}.wav"


def get_wav_duration(wav_path: Path) -> float:
    """Get the duration of a WAV file in seconds using ffprobe.

    Falls back to pydub if ffprobe is not available.

    Args:
        wav_path: Path to the WAV file.

    Returns:
        Duration in seconds.
    """
    try:
        result = subprocess.run(
            [
                "ffprobe",
                "-v", "quiet",
                "-show_entries", "format=duration",
                "-of", "csv=p=0",
                str(wav_path),
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        return float(result.stdout.strip())
    except (subprocess.CalledProcessError, FileNotFoundError, ValueError):
        # Fallback to pydub
        from pydub import AudioSegment
        audio = AudioSegment.from_wav(str(wav_path))
        return len(audio) / 1000.0


def concatenate_wavs_ffmpeg(segment_paths: List[Path], output_path: Path) -> None:
    """Concatenate WAV files using ffmpeg's concat demuxer.

    Args:
        segment_paths: Ordered list of WAV file paths to concatenate.
        output_path: Path for the concatenated output WAV.

    Raises:
        subprocess.CalledProcessError: If ffmpeg fails.
        RuntimeError: If ffmpeg is not available and pydub fallback also fails.
    """
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".txt", delete=False, encoding="utf-8"
    ) as filelist:
        for seg_path in segment_paths:
            # Escape single quotes in path for ffmpeg concat format
            escaped = str(seg_path.resolve()).replace("'", "'\\''")
            filelist.write(f"file '{escaped}'\n")
        filelist_path = filelist.name

    try:
        subprocess.run(
            [
                "ffmpeg",
                "-y",
                "-f", "concat",
                "-safe", "0",
                "-i", filelist_path,
                "-c", "copy",
                str(output_path),
            ],
            capture_output=True,
            text=True,
            check=True,
        )
    except FileNotFoundError:
        # ffmpeg not found, fall back to pydub
        _concatenate_wavs_pydub(segment_paths, output_path)
    finally:
        try:
            os.unlink(filelist_path)
        except OSError:
            pass


def _concatenate_wavs_pydub(segment_paths: List[Path], output_path: Path) -> None:
    """Fallback concatenation using pydub.

    Args:
        segment_paths: Ordered list of WAV file paths to concatenate.
        output_path: Path for the concatenated output WAV.
    """
    from pydub import AudioSegment

    combined = AudioSegment.empty()
    for seg_path in segment_paths:
        segment_audio = AudioSegment.from_wav(str(seg_path))
        combined += segment_audio

    combined.export(str(output_path), format="wav")


def copy_to_remotion(source_path: Path, remotion_public: str, section_id: str) -> Path:
    """Copy concatenated WAV to the Remotion public directory.

    Args:
        source_path: Path to the concatenated WAV file.
        remotion_public: Base Remotion public directory.
        section_id: The section identifier.

    Returns:
        Path to the copied file in the Remotion public directory.
    """
    import shutil

    dest_dir = Path(remotion_public) / section_id
    os.makedirs(dest_dir, exist_ok=True)
    dest_path = dest_dir / "narration.wav"
    shutil.copy2(str(source_path), str(dest_path))
    return dest_path


def generate_word_timestamps(
    wav_path: Path,
    segment_ids: List[str],
    segment_durations: List[float],
) -> List[Dict[str, Any]]:
    """Generate word-level timestamps using Faster-Whisper.

    Each word is mapped back to its originating segment by tracking
    cumulative audio duration boundaries.

    Args:
        wav_path: Path to the concatenated WAV file.
        segment_ids: Ordered list of segment IDs that were concatenated.
        segment_durations: Ordered list of durations (seconds) for each segment.

    Returns:
        List of word timestamp dictionaries with keys:
        word, start, end, segmentId.
    """
    from faster_whisper import WhisperModel

    model = WhisperModel("base", device="cpu", compute_type="int8")

    segments_iter, _info = model.transcribe(
        str(wav_path),
        word_timestamps=True,
        language="en",
    )

    # Build cumulative duration boundaries for segment mapping
    cumulative_boundaries: List[Tuple[float, float, str]] = []
    cumulative = 0.0
    for seg_id, duration in zip(segment_ids, segment_durations):
        cumulative_boundaries.append((cumulative, cumulative + duration, seg_id))
        cumulative += duration

    word_timestamps: List[Dict[str, Any]] = []

    for segment in segments_iter:
        if segment.words is None:
            continue
        for word_info in segment.words:
            # Determine which segment this word belongs to based on its start time
            word_start = word_info.start
            word_end = word_info.end
            matched_segment_id = segment_ids[-1] if segment_ids else "unknown"

            for boundary_start, boundary_end, seg_id in cumulative_boundaries:
                if boundary_start <= word_start < boundary_end:
                    matched_segment_id = seg_id
                    break

            word_timestamps.append({
                "word": word_info.word.strip(),
                "start": round(word_start, 3),
                "end": round(word_end, 3),
                "segmentId": matched_segment_id,
            })

    return word_timestamps


def normalize_transcript_text(text: str) -> str:
    """Normalize transcript/script text for mismatch comparison."""
    collapsed = re.sub(r"[\u2018\u2019']", "", text.lower())
    collapsed = re.sub(r"[^a-z0-9\s]", " ", collapsed)
    return re.sub(r"\s+", " ", collapsed).strip()


def load_segment_script_manifest(output_dir: str) -> Dict[str, str]:
    """Load expected cleanText values from outputs/tts/segments.json."""
    manifest_path = Path(output_dir) / "segments.json"
    if not manifest_path.exists():
        return {}

    try:
        with open(manifest_path, "r", encoding="utf-8") as f:
            manifest = json.load(f)
    except (OSError, json.JSONDecodeError):
        return {}

    segments = manifest.get("segments")
    if not isinstance(segments, list):
        return {}

    expected_map: Dict[str, str] = {}
    for segment in segments:
        if not isinstance(segment, dict):
            continue
        segment_id = segment.get("id")
        clean_text = segment.get("cleanText") or segment.get("text") or ""
        if isinstance(segment_id, str) and isinstance(clean_text, str) and clean_text.strip():
            expected_map[segment_id] = clean_text.strip()
    return expected_map


def build_segment_validation_report(
    segment_ids: List[str],
    output_dir: str,
    word_timestamps: List[Dict[str, Any]],
) -> Dict[str, Any]:
    """Compare STT output against expected segment text from the TTS manifest."""
    expected_map = load_segment_script_manifest(output_dir)

    actual_by_segment: Dict[str, str] = {segment_id: "" for segment_id in segment_ids}
    for word_info in word_timestamps:
        segment_id = word_info.get("segmentId")
        word = word_info.get("word")
        if (
            isinstance(segment_id, str)
            and segment_id in actual_by_segment
            and isinstance(word, str)
            and word.strip()
        ):
            actual_by_segment[segment_id] = (
                f"{actual_by_segment[segment_id]} {word.strip()}".strip()
            )

    rows: List[Dict[str, Any]] = []
    summary = {
        "passCount": 0,
        "warnCount": 0,
        "failCount": 0,
        "skipCount": 0,
    }

    for segment_id in segment_ids:
        expected_text = expected_map.get(segment_id, "")
        actual_text = actual_by_segment.get(segment_id, "")
        normalized_expected = normalize_transcript_text(expected_text)
        normalized_actual = normalize_transcript_text(actual_text)
        expected_word_count = len(normalized_expected.split()) if normalized_expected else 0
        actual_word_count = len(normalized_actual.split()) if normalized_actual else 0

        if not normalized_expected:
            status = "skip"
            match_ratio: Optional[float] = None
        else:
            match_ratio = round(
                SequenceMatcher(None, normalized_expected, normalized_actual).ratio(),
                3,
            )
            if match_ratio >= 0.94:
                status = "pass"
            elif match_ratio >= 0.8:
                status = "warn"
            else:
                status = "fail"

        summary[f"{status}Count"] += 1
        rows.append(
            {
                "segmentId": segment_id,
                "expectedText": expected_text,
                "actualText": actual_text,
                "normalizedExpectedText": normalized_expected,
                "normalizedActualText": normalized_actual,
                "matchRatio": match_ratio,
                "status": status,
                "expectedWordCount": expected_word_count,
                "actualWordCount": actual_word_count,
            }
        )

    return {"segments": rows, "summary": summary}


def process_section(
    section_id: str,
    segment_ids: List[str],
    output_dir: str,
    remotion_public: str,
) -> Dict[str, Any]:
    """Process a single section: concatenate, copy, transcribe.

    Args:
        section_id: The section identifier.
        segment_ids: Ordered list of segment IDs belonging to this section.
        output_dir: Base output directory containing segment WAVs.
        remotion_public: Base Remotion public directory.

    Returns:
        Progress dictionary with sectionId, status, and wordCount or error.
    """
    # Validate segment WAV files exist
    segment_paths: List[Path] = []
    missing_segments: List[str] = []

    for seg_id in segment_ids:
        seg_path = get_segment_wav_path(output_dir, seg_id)
        if seg_path.exists():
            segment_paths.append(seg_path)
        else:
            missing_segments.append(seg_id)

    if not segment_paths:
        error_msg = f"No segment WAV files found for section '{section_id}'"
        if missing_segments:
            error_msg += f". Missing segments: {missing_segments}"
        return {
            "sectionId": section_id,
            "status": "error",
            "error": error_msg,
        }

    if missing_segments:
        # Log warning but continue with available segments
        pass

    # Create output subdirectory for this section
    section_output_dir = Path(output_dir) / section_id
    os.makedirs(section_output_dir, exist_ok=True)

    # Concatenate WAV files
    concatenated_path = section_output_dir / "concatenated.wav"
    try:
        concatenate_wavs_ffmpeg(segment_paths, concatenated_path)
    except (subprocess.CalledProcessError, RuntimeError, Exception) as e:
        return {
            "sectionId": section_id,
            "status": "error",
            "error": f"Failed to concatenate WAV files: {e}",
        }

    # Copy to Remotion public directory
    try:
        copy_to_remotion(concatenated_path, remotion_public, section_id)
    except Exception as e:
        return {
            "sectionId": section_id,
            "status": "error",
            "error": f"Failed to copy to Remotion public directory: {e}",
        }

    # Get individual segment durations for word-to-segment mapping
    segment_durations: List[float] = []
    actual_segment_ids: List[str] = []
    for seg_path in segment_paths:
        try:
            duration = get_wav_duration(seg_path)
            segment_durations.append(duration)
            # Extract segment ID from filename
            actual_segment_ids.append(seg_path.stem)
        except Exception:
            segment_durations.append(0.0)
            actual_segment_ids.append(seg_path.stem)

    # Generate word-level timestamps
    try:
        word_timestamps = generate_word_timestamps(
            concatenated_path,
            actual_segment_ids,
            segment_durations,
        )
    except Exception as e:
        return {
            "sectionId": section_id,
            "status": "error",
            "error": f"Failed to generate word timestamps: {e}",
        }

    # Write word_timestamps.json
    timestamps_path = section_output_dir / "word_timestamps.json"
    try:
        with open(timestamps_path, "w", encoding="utf-8") as f:
            json.dump(word_timestamps, f, indent=2, ensure_ascii=False)
    except Exception as e:
        return {
            "sectionId": section_id,
            "status": "error",
            "error": f"Failed to write word_timestamps.json: {e}",
        }

    validation_report = build_segment_validation_report(
        actual_segment_ids,
        output_dir,
        word_timestamps,
    )
    validation_path = section_output_dir / "segment_validation.json"
    try:
        with open(validation_path, "w", encoding="utf-8") as f:
            json.dump(validation_report, f, indent=2, ensure_ascii=False)
    except Exception as e:
        return {
            "sectionId": section_id,
            "status": "error",
            "error": f"Failed to write segment_validation.json: {e}",
        }

    return {
        "sectionId": section_id,
        "status": "done",
        "wordCount": len(word_timestamps),
        "validationSummary": validation_report["summary"],
    }


def main() -> None:
    """Main entry point for the audio sync pipeline."""
    parser = argparse.ArgumentParser(
        description=(
            "Concatenate TTS segment WAV files into per-section WAV files "
            "and generate word-level timestamps via Faster-Whisper."
        )
    )
    parser.add_argument(
        "--project-dir",
        default=".",
        help="Directory containing project.json (default: current directory)",
    )
    parser.add_argument(
        "--output-dir",
        default="outputs/tts/",
        help="Directory containing segment WAV files (default: outputs/tts/)",
    )
    parser.add_argument(
        "--remotion-public",
        default="remotion/public/",
        help="Remotion public directory for output (default: remotion/public/)",
    )

    args = parser.parse_args()

    # Load section groups configuration
    try:
        project = load_project(args.project_dir)
        raw_section_groups = (
            json.loads(os.environ["SECTION_GROUPS"])
            if os.environ.get("SECTION_GROUPS")
            else project["sectionGroups"]
        )
        section_groups = _coerce_section_groups(raw_section_groups, args.output_dir)
    except (FileNotFoundError, json.JSONDecodeError, ValueError) as e:
        error_result = {
            "sectionId": "__global__",
            "status": "error",
            "error": f"Failed to load section groups: {e}",
        }
        print(json.dumps(error_result), flush=True)
        sys.exit(1)

    if not section_groups:
        error_result = {
            "sectionId": "__global__",
            "status": "error",
            "error": "No sections found in sectionGroups",
        }
        print(json.dumps(error_result), flush=True)
        sys.exit(1)

    any_failed = False

    for section_id, segment_ids in section_groups.items():
        result = process_section(
            section_id=section_id,
            segment_ids=segment_ids,
            output_dir=args.output_dir,
            remotion_public=args.remotion_public,
        )

        # Print JSON progress line to stdout
        print(json.dumps(result), flush=True)

        if result["status"] == "error":
            any_failed = True

    sys.exit(1 if any_failed else 0)


if __name__ == "__main__":
    main()
