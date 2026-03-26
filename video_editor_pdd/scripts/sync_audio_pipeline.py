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
import importlib
import json
import os
import platform
import subprocess
import sys
import tempfile
import re
from difflib import SequenceMatcher
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


DEFAULT_FASTER_WHISPER_MODEL = "base"
DEFAULT_FASTER_WHISPER_DEVICE = "cpu"
DEFAULT_FASTER_WHISPER_COMPUTE_TYPE = "int8"
DEFAULT_MLX_WHISPER_MODEL = "mlx-community/whisper-large-v3-turbo"
DEFAULT_VALIDATION_MAX_FAIL_COUNT = 2
DEFAULT_VALIDATION_MAX_FAIL_RATIO = 0.15
DEFAULT_VALIDATION_MAX_WARN_COUNT = 6
DEFAULT_VALIDATION_MAX_WARN_RATIO = 0.35
NUMBER_NORMALIZATION_PATTERN = re.compile(
    r"\b(?:"
    r"zero|one|two|three|four|five|six|seven|eight|nine|ten|"
    r"eleven|twelve|thirteen|fourteen|fifteen|sixteen|seventeen|eighteen|nineteen|"
    r"twenty|thirty|forty|fifty|sixty|seventy|eighty|ninety|"
    r"hundred|thousand|million|billion|percent|"
    r"\d+(?:\.\d+)?"
    r")\b",
    re.IGNORECASE,
)


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


def _parse_segment_index(segment_id: str) -> Optional[int]:
    try:
        return int(segment_id.rsplit("_", 1)[-1])
    except (TypeError, ValueError):
        return None


def _extract_requested_segment_numbers(value: Any) -> List[int]:
    numbers: List[int] = []
    if isinstance(value, list):
        for segment_id in value:
            if isinstance(segment_id, str):
                index = _parse_segment_index(segment_id)
                if index is not None:
                    numbers.append(index)
    elif isinstance(value, dict):
        start_seg = value.get("startSegment")
        end_seg = value.get("endSegment")
        start_num = _parse_segment_index(start_seg) if isinstance(start_seg, str) else None
        end_num = _parse_segment_index(end_seg) if isinstance(end_seg, str) else None
        if start_num is not None and end_num is not None and end_num >= start_num:
            numbers.extend(list(range(start_num, end_num + 1)))
    return numbers


def _load_manifest_sections(output_dir: str) -> Dict[str, List[str]]:
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

    section_map: Dict[str, List[str]] = {}
    for segment in segments:
        if not isinstance(segment, dict):
            continue
        segment_id = segment.get("id")
        section_id = segment.get("sectionId")
        if isinstance(segment_id, str) and isinstance(section_id, str):
            section_map.setdefault(section_id, []).append(segment_id)
    return section_map


def _normalize_section_key(section_id: str) -> str:
    return re.sub(r"[^a-z0-9]+", " ", section_id.lower()).strip()


def _resolve_manifest_section_alias(
    section_id: str,
    requested_numbers: List[int],
    manifest_sections: Dict[str, List[str]],
    project: Dict[str, Any],
) -> Optional[str]:
    if section_id in manifest_sections:
        return section_id

    candidates = list(manifest_sections.keys())
    project_sections = project.get("sections")
    if isinstance(project_sections, list):
        preferred = [
            section.get("id")
            for section in project_sections
            if isinstance(section, dict)
            and isinstance(section.get("id"), str)
            and section.get("id") in manifest_sections
        ]
        if preferred:
            candidates = preferred

    raw_norm = _normalize_section_key(section_id)
    requested_set = set(requested_numbers)
    best_candidate: Optional[str] = None
    best_score: Tuple[float, int] = (0.0, -1)

    for candidate in candidates:
        candidate_norm = _normalize_section_key(candidate)
        similarity = SequenceMatcher(None, raw_norm, candidate_norm).ratio()
        candidate_numbers = {
            index
            for index in (_parse_segment_index(seg_id) for seg_id in manifest_sections[candidate])
            if index is not None
        }
        overlap = len(requested_set & candidate_numbers) if requested_set else 0
        score = (similarity, overlap)
        if score > best_score:
            best_candidate = candidate
            best_score = score

    if best_candidate is None:
        return None

    similarity, overlap = best_score
    if requested_set and overlap <= 0:
        return None
    if similarity < 0.65:
        return None
    return best_candidate


def _resolve_section_groups_with_manifest(
    project: Dict[str, Any],
    raw: Dict[str, Any],
    output_dir: str,
) -> Dict[str, List[str]]:
    section_groups = _coerce_section_groups(raw, output_dir)
    manifest_sections = _load_manifest_sections(output_dir)
    if not manifest_sections:
        return section_groups

    normalized: Dict[str, List[str]] = {}
    for section_id, value in raw.items():
        direct_segment_ids = section_groups.get(section_id, [])
        requested_numbers = _extract_requested_segment_numbers(value)
        if not requested_numbers:
            requested_numbers = [
                index
                for index in (_parse_segment_index(segment_id) for segment_id in direct_segment_ids)
                if index is not None
            ]

        target_section_id = (
            section_id
            if section_id in manifest_sections
            else _resolve_manifest_section_alias(
                section_id,
                requested_numbers,
                manifest_sections,
                project,
            )
        )

        if target_section_id and target_section_id in manifest_sections:
            requested_set = set(requested_numbers)
            mapped_segment_ids = [
                segment_id
                for segment_id in manifest_sections[target_section_id]
                if not requested_set
                or _parse_segment_index(segment_id) in requested_set
            ]
            if mapped_segment_ids:
                normalized[target_section_id] = mapped_segment_ids
                continue

        normalized[section_id] = direct_segment_ids

    return normalized


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

    project = load_project(project_dir)
    return _resolve_section_groups_with_manifest(project, raw, output_dir)


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


def is_apple_silicon_mac() -> bool:
    """Return True when running on Apple Silicon macOS."""
    return sys.platform == "darwin" and platform.machine().lower() in {"arm64", "aarch64"}


def resolve_stt_backend() -> Dict[str, str]:
    """Choose the speech-to-text backend for Stage 5.

    Defaults:
    - Apple Silicon macOS with mlx-whisper installed -> mlx-whisper large-v3-turbo
    - otherwise -> faster-whisper base on CPU
    """
    requested_backend = os.environ.get("SYNC_AUDIO_STT_BACKEND", "auto").strip().lower()
    if requested_backend not in {"auto", "faster-whisper", "mlx-whisper"}:
        requested_backend = "auto"

    if requested_backend == "mlx-whisper" and not is_apple_silicon_mac():
        raise RuntimeError("mlx-whisper requires Apple Silicon macOS")

    if requested_backend in {"auto", "mlx-whisper"} and is_apple_silicon_mac():
        try:
            importlib.import_module("mlx_whisper")
        except ImportError as exc:
            if requested_backend == "mlx-whisper":
                raise RuntimeError("mlx-whisper requested but unavailable") from exc
        else:
            return {
                "backend": "mlx-whisper",
                "model_id": os.environ.get("SYNC_AUDIO_MLX_MODEL", DEFAULT_MLX_WHISPER_MODEL),
                "device": "apple-gpu",
            }

    return {
        "backend": "faster-whisper",
        "model_id": os.environ.get("SYNC_AUDIO_FASTER_WHISPER_MODEL", DEFAULT_FASTER_WHISPER_MODEL),
        "device": os.environ.get("SYNC_AUDIO_FASTER_WHISPER_DEVICE", DEFAULT_FASTER_WHISPER_DEVICE),
        "compute_type": os.environ.get(
            "SYNC_AUDIO_FASTER_WHISPER_COMPUTE_TYPE",
            DEFAULT_FASTER_WHISPER_COMPUTE_TYPE,
        ),
    }


def _transcribe_words_faster_whisper(
    wav_path: Path, backend_config: Dict[str, str]
) -> List[Dict[str, float | str]]:
    from faster_whisper import WhisperModel

    model = WhisperModel(
        backend_config["model_id"],
        device=backend_config["device"],
        compute_type=backend_config["compute_type"],
    )

    segments_iter, _info = model.transcribe(
        str(wav_path),
        word_timestamps=True,
        language="en",
    )

    words: List[Dict[str, float | str]] = []
    for segment in segments_iter:
        if segment.words is None:
            continue
        for word_info in segment.words:
            word = word_info.word.strip()
            if not word:
                continue
            words.append(
                {
                    "word": word,
                    "start": float(word_info.start),
                    "end": float(word_info.end),
                }
            )
    return words


def _transcribe_words_mlx_whisper(
    wav_path: Path, backend_config: Dict[str, str]
) -> List[Dict[str, float | str]]:
    mlx_whisper = importlib.import_module("mlx_whisper")

    result = mlx_whisper.transcribe(
        str(wav_path),
        path_or_hf_repo=backend_config["model_id"],
        language="en",
        task="transcribe",
        word_timestamps=True,
        verbose=False,
    )

    words: List[Dict[str, float | str]] = []
    for segment in result.get("segments", []):
        if not isinstance(segment, dict):
            continue
        for word_info in segment.get("words") or []:
            if not isinstance(word_info, dict):
                continue
            word = str(word_info.get("word", "")).strip()
            if not word:
                continue
            words.append(
                {
                    "word": word,
                    "start": float(word_info.get("start", 0.0)),
                    "end": float(word_info.get("end", 0.0)),
                }
            )
    return words


def generate_word_timestamps(
    wav_path: Path,
    segment_ids: List[str],
    segment_durations: List[float],
) -> List[Dict[str, Any]]:
    """Generate word-level timestamps using the selected STT backend.

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
    backend_config = resolve_stt_backend()
    if backend_config["backend"] == "mlx-whisper":
        transcribed_words = _transcribe_words_mlx_whisper(wav_path, backend_config)
    else:
        transcribed_words = _transcribe_words_faster_whisper(wav_path, backend_config)

    # Build cumulative duration boundaries for segment mapping
    cumulative_boundaries: List[Tuple[float, float, str]] = []
    cumulative = 0.0
    for seg_id, duration in zip(segment_ids, segment_durations):
        cumulative_boundaries.append((cumulative, cumulative + duration, seg_id))
        cumulative += duration

    word_timestamps: List[Dict[str, Any]] = []

    for word_info in transcribed_words:
        # Determine which segment this word belongs to based on its start time
        word_start = float(word_info["start"])
        word_end = float(word_info["end"])
        matched_segment_id = segment_ids[-1] if segment_ids else "unknown"

        for boundary_start, boundary_end, seg_id in cumulative_boundaries:
            if boundary_start <= word_start < boundary_end:
                matched_segment_id = seg_id
                break

        word_timestamps.append({
            "word": str(word_info["word"]).strip(),
            "start": round(word_start, 3),
            "end": round(word_end, 3),
            "segmentId": matched_segment_id,
        })

    return word_timestamps


def normalize_transcript_text(text: str) -> str:
    """Normalize transcript/script text for mismatch comparison."""
    collapsed = text.lower()
    collapsed = re.sub(r"\b\d+(?:\.\d+)?\s*%", " num ", collapsed)
    collapsed = collapsed.replace("%", " percent ")
    collapsed = re.sub(r"(?<=\w)[-–](?=\w)", " ", collapsed)
    collapsed = re.sub(r"[\u2018\u2019']", "", collapsed)
    collapsed = NUMBER_NORMALIZATION_PATTERN.sub(" num ", collapsed)
    collapsed = re.sub(r"[^a-z0-9\s]", " ", collapsed)
    collapsed = re.sub(r"\bnum(?:\s+(?:and\s+)?num)+\b", " num ", collapsed)
    return re.sub(r"\s+", " ", collapsed).strip()


def compute_transcript_match_ratio(expected_text: str, actual_text: str) -> float:
    """Compare expected vs actual transcript using token-level similarity."""
    normalized_expected = normalize_transcript_text(expected_text)
    normalized_actual = normalize_transcript_text(actual_text)

    expected_tokens = normalized_expected.split()
    actual_tokens = normalized_actual.split()

    if not expected_tokens and not actual_tokens:
        return 1.0
    if not expected_tokens or not actual_tokens:
        return 0.0

    return round(
        SequenceMatcher(None, expected_tokens, actual_tokens).ratio(),
        3,
    )


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
            match_ratio = compute_transcript_match_ratio(expected_text, actual_text)
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


def _coerce_int(value: Any, default: int) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def _coerce_float(value: Any, default: float) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def resolve_validation_policy(project: Dict[str, Any]) -> Dict[str, Any]:
    """Resolve transcript validation thresholds from project config or env."""
    audio_sync = project.get("audioSync")
    config = audio_sync if isinstance(audio_sync, dict) else {}

    return {
        "maxFailCount": max(
            0,
            _coerce_int(
                config.get(
                    "validationMaxFailCount",
                    os.environ.get(
                        "SYNC_AUDIO_VALIDATION_MAX_FAIL_COUNT",
                        DEFAULT_VALIDATION_MAX_FAIL_COUNT,
                    ),
                ),
                DEFAULT_VALIDATION_MAX_FAIL_COUNT,
            ),
        ),
        "maxFailRatio": max(
            0.0,
            _coerce_float(
                config.get(
                    "validationMaxFailRatio",
                    os.environ.get(
                        "SYNC_AUDIO_VALIDATION_MAX_FAIL_RATIO",
                        DEFAULT_VALIDATION_MAX_FAIL_RATIO,
                    ),
                ),
                DEFAULT_VALIDATION_MAX_FAIL_RATIO,
            ),
        ),
        "maxWarnCount": max(
            0,
            _coerce_int(
                config.get(
                    "validationMaxWarnCount",
                    os.environ.get(
                        "SYNC_AUDIO_VALIDATION_MAX_WARN_COUNT",
                        DEFAULT_VALIDATION_MAX_WARN_COUNT,
                    ),
                ),
                DEFAULT_VALIDATION_MAX_WARN_COUNT,
            ),
        ),
        "maxWarnRatio": max(
            0.0,
            _coerce_float(
                config.get(
                    "validationMaxWarnRatio",
                    os.environ.get(
                        "SYNC_AUDIO_VALIDATION_MAX_WARN_RATIO",
                        DEFAULT_VALIDATION_MAX_WARN_RATIO,
                    ),
                ),
                DEFAULT_VALIDATION_MAX_WARN_RATIO,
            ),
        ),
    }


def evaluate_validation_gate(
    validation_report: Dict[str, Any],
    validation_policy: Optional[Dict[str, Any]],
) -> Optional[str]:
    """Return an error message when transcript validation exceeds allowed thresholds."""
    if not validation_policy:
        return None

    summary = validation_report.get("summary")
    if not isinstance(summary, dict):
        return None

    pass_count = _coerce_int(summary.get("passCount"), 0)
    warn_count = _coerce_int(summary.get("warnCount"), 0)
    fail_count = _coerce_int(summary.get("failCount"), 0)
    compared_count = pass_count + warn_count + fail_count

    if compared_count <= 0:
        return None

    fail_ratio = fail_count / compared_count
    warn_ratio = warn_count / compared_count
    max_fail_count = _coerce_int(
        validation_policy.get("maxFailCount"),
        DEFAULT_VALIDATION_MAX_FAIL_COUNT,
    )
    max_fail_ratio = _coerce_float(
        validation_policy.get("maxFailRatio"),
        DEFAULT_VALIDATION_MAX_FAIL_RATIO,
    )
    max_warn_count = _coerce_int(
        validation_policy.get("maxWarnCount"),
        DEFAULT_VALIDATION_MAX_WARN_COUNT,
    )
    max_warn_ratio = _coerce_float(
        validation_policy.get("maxWarnRatio"),
        DEFAULT_VALIDATION_MAX_WARN_RATIO,
    )

    reasons: List[str] = []
    if fail_count > max_fail_count:
        reasons.append(f"failCount {fail_count} > {max_fail_count}")
    if fail_ratio > max_fail_ratio:
        reasons.append(f"failRatio {fail_ratio:.3f} > {max_fail_ratio:.3f}")
    if warn_count > max_warn_count and warn_ratio > max_warn_ratio:
        reasons.append(
            f"warnCount {warn_count} > {max_warn_count} "
            f"and warnRatio {warn_ratio:.3f} > {max_warn_ratio:.3f}"
        )

    if not reasons:
        return None

    failing_segments: List[str] = []
    for row in validation_report.get("segments") or []:
        if isinstance(row, dict) and row.get("status") == "fail":
            segment_id = row.get("segmentId")
            if isinstance(segment_id, str):
                failing_segments.append(segment_id)

    segment_suffix = (
        f" Failing segments: {', '.join(failing_segments[:5])}."
        if failing_segments
        else ""
    )
    return (
        "Transcript validation failed: "
        f"{'; '.join(reasons)}."
        f"{segment_suffix}"
    )


def process_section(
    section_id: str,
    segment_ids: List[str],
    output_dir: str,
    remotion_public: str,
    validation_policy: Optional[Dict[str, Any]] = None,
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

    timestamps_path = section_output_dir / "word_timestamps.json"
    validation_path = section_output_dir / "segment_validation.json"
    failed_timestamps_path = section_output_dir / "word_timestamps.failed.json"
    failed_validation_path = section_output_dir / "segment_validation.failed.json"

    validation_report = build_segment_validation_report(
        actual_segment_ids,
        output_dir,
        word_timestamps,
    )
    validation_error = evaluate_validation_gate(validation_report, validation_policy)

    if validation_error:
        try:
            with open(failed_timestamps_path, "w", encoding="utf-8") as f:
                json.dump(word_timestamps, f, indent=2, ensure_ascii=False)
            with open(failed_validation_path, "w", encoding="utf-8") as f:
                json.dump(validation_report, f, indent=2, ensure_ascii=False)
        except Exception as e:
            return {
                "sectionId": section_id,
                "status": "error",
                "error": f"Failed to write validation failure artifacts: {e}",
                "validationSummary": validation_report["summary"],
            }

        return {
            "sectionId": section_id,
            "status": "error",
            "error": validation_error,
            "validationSummary": validation_report["summary"],
        }

    # Write accepted artifacts only after validation passes.
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

    try:
        with open(validation_path, "w", encoding="utf-8") as f:
            json.dump(validation_report, f, indent=2, ensure_ascii=False)
    except Exception as e:
        return {
            "sectionId": section_id,
            "status": "error",
            "error": f"Failed to write segment_validation.json: {e}",
        }

    for failed_path in (failed_timestamps_path, failed_validation_path):
        try:
            if failed_path.exists():
                failed_path.unlink()
        except OSError:
            pass

    # Copy to Remotion public directory after validation passes.
    try:
        copy_to_remotion(concatenated_path, remotion_public, section_id)
    except Exception as e:
        return {
            "sectionId": section_id,
            "status": "error",
            "error": f"Failed to copy to Remotion public directory: {e}",
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
        section_groups = load_section_groups(args.project_dir, args.output_dir)
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
    validation_policy = resolve_validation_policy(project)

    for section_id, segment_ids in section_groups.items():
        result = process_section(
            section_id=section_id,
            segment_ids=segment_ids,
            output_dir=args.output_dir,
            remotion_public=args.remotion_public,
            validation_policy=validation_policy,
        )

        # Print JSON progress line to stdout
        print(json.dumps(result), flush=True)

        if result["status"] == "error":
            any_failed = True

    sys.exit(1 if any_failed else 0)


if __name__ == "__main__":
    main()
