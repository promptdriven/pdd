#!/usr/bin/env python3
"""
scripts/render_tts.py

Standalone Python script for batch TTS synthesis using Qwen3-TTS.
Reads narrative/tts_script.md, parses NARRATOR: blocks with inline
annotation tags, and generates one WAV file per segment.

Prints JSON progress lines to stdout for consumption by the calling
API route (streamed as SSE log events).
"""

import argparse
import json
import os
import re
import sys
import time
import wave
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

DEFAULT_MODEL = "Qwen/Qwen3-TTS-12Hz-1.7B-CustomVoice"
DEFAULT_OUTPUT_DIR = "outputs/tts/"
DEFAULT_PROJECT_DIR = "."
SEGMENTS_MANIFEST_FILENAME = "segments.json"
SAMPLE_RATE = 24000  # Qwen TTS models typically output 24kHz audio

# Annotation tag patterns
TAG_PATTERN = re.compile(
    r"\[(?:TONE|PACE|PAUSE|EMOTION|INSTRUCT)\s*:\s*[^\]]*\]", re.IGNORECASE
)
NARRATOR_LABEL_PATTERN = re.compile(
    r"^\s*(?:\*{1,2}|_{1,2})?NARRATOR:(?:\*{1,2}|_{1,2})?\s*",
    re.IGNORECASE | re.MULTILINE,
)
MARKDOWN_FORMATTING_PATTERN = re.compile(r"(\*\*|__|~~|`)")
CONTROL_HEADING_PATTERN = re.compile(
    r"^(?:#{1,6}\s*)?(?:[-*+]\s*)?"
    r"(?:block|beat|scene|section|segment|shot|part|chapter)\s+"
    r"(?:\d+[a-z]?|[ivxlcdm]+|[a-z])(?:\s*[-–—:]\s*.+)?\:?\s*$",
    re.IGNORECASE,
)
PAUSE_PATTERN = re.compile(
    r"\[PAUSE\s*:\s*([\d.]+)\s*s?\]", re.IGNORECASE
)
TONE_PATTERN = re.compile(
    r"\[TONE\s*:\s*([^\]]+)\]", re.IGNORECASE
)
PACE_PATTERN = re.compile(
    r"\[PACE\s*:\s*([^\]]+)\]", re.IGNORECASE
)
EMOTION_PATTERN = re.compile(
    r"\[EMOTION\s*:\s*([^\]]+)\]", re.IGNORECASE
)
INSTRUCT_PATTERN = re.compile(
    r"\[INSTRUCT\s*:\s*([^\]]+)\]", re.IGNORECASE
)

# Pattern to match NARRATOR: blocks
NARRATOR_PATTERN = re.compile(
    r"^NARRATOR\s*:\s*(.+?)(?=^NARRATOR\s*:|\Z)",
    re.MULTILINE | re.DOTALL,
)


def _normalize_spoken_text(text: str) -> str:
    """Strip control markup and collapse formatting whitespace for TTS."""
    stripped = TAG_PATTERN.sub("", text)
    stripped = NARRATOR_LABEL_PATTERN.sub("", stripped)
    kept_lines = []
    for line in stripped.splitlines():
        line_without_formatting = MARKDOWN_FORMATTING_PATTERN.sub("", line).strip()
        if CONTROL_HEADING_PATTERN.match(line_without_formatting):
            continue
        kept_lines.append(line_without_formatting)
    stripped = "\n".join(kept_lines)
    return re.sub(r"\s+", " ", stripped).strip()


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

class Segment:
    """Represents a single NARRATOR: segment with parsed metadata."""

    def __init__(self, segment_id: str, raw_text: str):
        self.segment_id = segment_id
        self.raw_text = raw_text.strip()
        self.annotations = self._extract_annotations()
        self.text_chunks = self._split_by_pauses()

    def _extract_annotations(self) -> Dict[str, str]:
        """Extract annotation metadata (TONE, PACE, EMOTION) from raw text."""
        annotations: Dict[str, str] = {}
        tone_match = TONE_PATTERN.search(self.raw_text)
        if tone_match:
            annotations["tone"] = tone_match.group(1).strip()
        pace_match = PACE_PATTERN.search(self.raw_text)
        if pace_match:
            annotations["pace"] = pace_match.group(1).strip()
        emotion_match = EMOTION_PATTERN.search(self.raw_text)
        if emotion_match:
            annotations["emotion"] = emotion_match.group(1).strip()
        instruct_match = INSTRUCT_PATTERN.search(self.raw_text)
        if instruct_match:
            annotations["instruct"] = instruct_match.group(1).strip()
        return annotations

    def _split_by_pauses(self) -> List[Dict[str, Any]]:
        """
        Split the raw text into chunks separated by PAUSE tags.
        Returns a list of dicts:
          {"type": "text", "content": "..."} or
          {"type": "pause", "duration": 1.2}
        """
        chunks: List[Dict[str, Any]] = []
        last_end = 0
        for match in PAUSE_PATTERN.finditer(self.raw_text):
            # Text before the pause
            before = self.raw_text[last_end:match.start()]
            clean = _normalize_spoken_text(before)
            if clean:
                chunks.append({"type": "text", "content": clean})
            # The pause itself
            try:
                duration = float(match.group(1))
            except ValueError:
                duration = 0.5
            chunks.append({"type": "pause", "duration": duration})
            last_end = match.end()

        # Remaining text after last pause
        remaining = self.raw_text[last_end:]
        clean = _normalize_spoken_text(remaining)
        if clean:
            chunks.append({"type": "text", "content": clean})

        # If no chunks were produced (edge case), use full cleaned text
        if not chunks:
            clean_all = _normalize_spoken_text(self.raw_text)
            if clean_all:
                chunks.append({"type": "text", "content": clean_all})

        return chunks

    @property
    def clean_text(self) -> str:
        """Full text with all annotation tags stripped."""
        return _normalize_spoken_text(self.raw_text)


def build_segments_manifest(
    segments: List["Segment"],
    word_timestamps_by_section: Optional[Dict[str, List[Dict[str, Any]]]] = None,
) -> List[Dict[str, Any]]:
    """Build a JSON-serializable manifest for the parsed TTS segments.

    When *word_timestamps_by_section* is provided, each segment is enriched
    with ``startSeconds`` / ``endSeconds`` derived from the min/max of
    matching words (keyed by ``segmentId``).
    """
    manifest: List[Dict[str, Any]] = []
    for segment in segments:
        segment_id = segment.segment_id
        base_id, _, counter = segment_id.rpartition("_")
        split_index = None
        if counter.isdigit():
            split_index = int(counter)

        entry: Dict[str, Any] = {
            "id": segment_id,
            "sectionId": base_id or segment_id,
            "splitIndex": split_index,
            "text": segment.raw_text,
            "cleanText": segment.clean_text,
            "annotations": segment.annotations,
        }

        # Enrich with per-segment timing from word timestamps
        if word_timestamps_by_section is not None:
            section_id = base_id or segment_id
            words = word_timestamps_by_section.get(section_id, [])
            matching = [
                w for w in words
                if w.get("segmentId") == segment_id
            ]
            if matching:
                entry["startSeconds"] = min(w["start"] for w in matching)
                entry["endSeconds"] = max(w["end"] for w in matching)

        manifest.append(entry)

    return manifest


def _load_word_timestamps_by_section(output_dir: str, segments: List["Segment"]) -> Dict[str, List[Dict[str, Any]]]:
    """Load per-section word_timestamps.json files for all sections referenced by segments."""
    section_ids: set = set()
    for seg in segments:
        base_id, _, counter = seg.segment_id.rpartition("_")
        if counter.isdigit() and base_id:
            section_ids.add(base_id)
        else:
            section_ids.add(seg.segment_id)

    result: Dict[str, List[Dict[str, Any]]] = {}
    for section_id in section_ids:
        ts_path = os.path.join(output_dir, section_id, "word_timestamps.json")
        if not os.path.isfile(ts_path):
            continue
        try:
            with open(ts_path, encoding="utf-8") as f:
                parsed = json.load(f)
            words = parsed if isinstance(parsed, list) else parsed.get("words", [])
            result[section_id] = words
        except (json.JSONDecodeError, OSError):
            continue
    return result


def write_segments_manifest(output_dir: str, segments: List["Segment"]) -> str:
    """Persist the parsed segment manifest beside the generated WAV files."""
    os.makedirs(output_dir, exist_ok=True)
    word_timestamps = _load_word_timestamps_by_section(output_dir, segments)
    manifest_path = os.path.join(output_dir, SEGMENTS_MANIFEST_FILENAME)
    with open(manifest_path, "w", encoding="utf-8") as f:
        json.dump(
            {"segments": build_segments_manifest(segments, word_timestamps or None)},
            f,
            indent=2,
        )
    return manifest_path


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------

def _load_section_ids(project_dir: str) -> Dict[str, str]:
    """Load section label-to-id mapping from project.json."""
    project_path = os.path.join(project_dir, "project.json")
    mapping: Dict[str, str] = {}
    if os.path.exists(project_path):
        with open(project_path, encoding="utf-8") as f:
            proj = json.load(f)
        for section in proj.get("sections", []):
            label = section.get("label", "").upper()
            sid = section.get("id", "")
            if label and sid:
                mapping[label] = sid
    return mapping


def _section_heading_to_id(heading: str, section_map: Optional[Dict[str, str]] = None) -> str:
    """Convert a section heading like 'COLD OPEN (0:00 - 2:00)' to 'cold_open'.

    First tries to match against project.json section labels, then falls back
    to a generic snake_case conversion.
    """
    # Strip timestamp portion in parens
    clean_heading = re.sub(r"\(.*?\)", "", heading).strip().upper()

    # Try exact match against project.json labels
    if section_map:
        for label, sid in section_map.items():
            if label == clean_heading:
                return sid
            # Try fuzzy: label words are subset of heading words
            label_words = set(label.split())
            heading_words = set(clean_heading.split())
            # Match "Part 1: Economics" → heading "PART 1: THE ECONOMICS OF DARNING"
            if label_words and label_words.issubset(heading_words):
                return sid

    # Fallback: strip 'PART N:' prefix and snake_case
    clean = re.sub(r"^PART\s+\d+\s*:\s*", "", clean_heading, flags=re.IGNORECASE).strip()
    clean = re.sub(r"[^a-zA-Z0-9]+", "_", clean).strip("_").lower()
    return clean


# Pattern for section headings like ## COLD OPEN (0:00 - 2:00)
SECTION_HEADING_PATTERN = re.compile(r"^##\s+(.+)$", re.MULTILINE)


def _parse_section_based(content: str, project_dir: str = ".") -> List[Segment]:
    """
    Parse section-heading-based TTS script format.
    Splits each section into multiple segments at major pause boundaries (>= 1.0s).
    Segment IDs follow the pattern: {section_id}_{NNN}.
    """
    section_map = _load_section_ids(project_dir)

    # Find all section headings and their positions
    headings = list(SECTION_HEADING_PATTERN.finditer(content))
    if not headings:
        return []

    segments: List[Segment] = []

    for i, match in enumerate(headings):
        heading_text = match.group(1).strip()
        section_id = _section_heading_to_id(heading_text, section_map)
        if not section_id:
            continue

        # Extract section body (from after heading to next heading or end)
        start = match.end()
        end = headings[i + 1].start() if i + 1 < len(headings) else len(content)
        body = content[start:end].strip()

        # Skip separator lines
        body = re.sub(r"^---+\s*$", "", body, flags=re.MULTILINE).strip()

        if not body:
            continue

        # Split into sub-segments at major pauses (>= 1.0s) or double newlines
        # with significant text between them
        parts = re.split(r"\[PAUSE\s*:\s*(?:[1-9]\d*\.?\d*|0\.\d*[5-9]\d*)\s*s?\]", body)

        seg_counter = 0
        for part in parts:
            clean = _normalize_spoken_text(part)
            if len(clean) < 10:
                continue  # Skip trivially short fragments
            seg_counter += 1
            seg_id = f"{section_id}_{seg_counter:03d}"
            segments.append(Segment(seg_id, part.strip()))

        # If no sub-segments were created, use the whole section as one segment
        if seg_counter == 0:
            clean = _normalize_spoken_text(body)
            if clean:
                segments.append(Segment(f"{section_id}_001", body))

    return segments


def parse_tts_script(script_path: str, project_dir: str = ".") -> List[Segment]:
    """
    Parse the tts_script.md file and extract segments.

    Supports two formats:
    1. NARRATOR: blocks (original format)
    2. Section-heading-based format (## SECTION_NAME)

    Args:
        script_path: Path to the tts_script.md file.
        project_dir: Project root directory (for reading project.json).

    Returns:
        List of Segment objects in order of appearance.

    Raises:
        FileNotFoundError: If the script file does not exist.
        ValueError: If no segments are found.
    """
    path = Path(script_path)
    if not path.exists():
        raise FileNotFoundError(f"TTS script not found: {script_path}")

    content = path.read_text(encoding="utf-8")

    # Try NARRATOR: block format first
    matches = NARRATOR_PATTERN.findall(content)
    if matches:
        segments: List[Segment] = []
        for idx, raw_text in enumerate(matches, start=1):
            segment_id = f"seg_{idx:03d}"
            segments.append(Segment(segment_id, raw_text))
        return segments

    # Fallback to section-heading-based format
    segments = _parse_section_based(content, project_dir)
    if segments:
        return segments

    raise ValueError(
        f"No NARRATOR: blocks or section headings found in {script_path}."
    )


# ---------------------------------------------------------------------------
# Audio utilities
# ---------------------------------------------------------------------------

def generate_silence(duration_seconds: float, sample_rate: int = SAMPLE_RATE):
    """Generate silence as a numpy float32 array."""
    import numpy as np
    num_samples = int(sample_rate * duration_seconds)
    return np.zeros(num_samples, dtype=np.float32)


def generate_silence_wav_bytes(
    duration_seconds: float, sample_rate: int = SAMPLE_RATE
) -> bytes:
    """Generate raw 16-bit PCM silence bytes for the given duration."""
    num_samples = int(sample_rate * duration_seconds)
    return b"\x00\x00" * num_samples


def concatenate_pcm(chunks: List[bytes]) -> bytes:
    """Concatenate raw PCM byte chunks in order."""
    return b"".join(chunks)


def _audio_to_pcm_bytes(audio: Any) -> bytes:
    """Normalize TTS engine output to 16-bit mono PCM bytes."""
    if isinstance(audio, (bytes, bytearray)):
        return bytes(audio)

    import numpy as np

    array = np.asarray(audio)
    if array.size == 0:
        return b""

    # Downmix multi-channel audio to mono if needed.
    if array.ndim > 1:
        array = array.mean(axis=1)

    if array.dtype.kind == "f":
        clipped = np.clip(array, -1.0, 1.0)
        pcm = (clipped * 32767).astype(np.int16)
    else:
        pcm = array.astype(np.int16)

    return pcm.tobytes()


def write_wav(filepath: str, audio: Any, sample_rate: int = SAMPLE_RATE) -> float:
    """Write raw PCM bytes or array-like audio to a mono 16-bit WAV file."""
    pcm_bytes = _audio_to_pcm_bytes(audio)
    os.makedirs(os.path.dirname(filepath) or ".", exist_ok=True)

    with wave.open(filepath, "wb") as wav_file:
        wav_file.setnchannels(1)
        wav_file.setsampwidth(2)
        wav_file.setframerate(sample_rate)
        wav_file.writeframes(pcm_bytes)

    return len(pcm_bytes) / (sample_rate * 2)


def read_wav_float32(filepath: str) -> "np.ndarray":
    """Read a mono/stereo PCM WAV file and return float32 mono samples."""
    import numpy as np

    with wave.open(filepath, "rb") as wav_file:
        channels = wav_file.getnchannels()
        sampwidth = wav_file.getsampwidth()
        frames = wav_file.getnframes()
        raw = wav_file.readframes(frames)

    if sampwidth != 2:
        raise RuntimeError(f"Unsupported WAV sample width: {sampwidth * 8} bits")

    audio = np.frombuffer(raw, dtype=np.int16).astype(np.float32) / 32768.0

    if channels > 1:
        audio = audio.reshape(-1, channels).mean(axis=1)

    return audio


def apply_speaking_rate(audio: Any, speaking_rate: float) -> "np.ndarray":
    """Apply simple time scaling to mono audio while preserving sample rate."""
    import numpy as np

    try:
        rate = float(speaking_rate)
    except (TypeError, ValueError):
        rate = 1.0

    if rate <= 0:
        rate = 1.0

    if isinstance(audio, (bytes, bytearray)):
        array = np.frombuffer(audio, dtype=np.int16).astype(np.float32) / 32768.0
    else:
        array = np.asarray(audio, dtype=np.float32)

    if array.size == 0 or abs(rate - 1.0) < 1e-6:
        return array.astype(np.float32)

    if array.ndim > 1:
        array = array.mean(axis=1)

    target_length = max(1, int(round(len(array) / rate)))
    source_positions = np.arange(len(array), dtype=np.float32)
    target_positions = np.linspace(0, len(array) - 1, target_length, dtype=np.float32)
    return np.interp(target_positions, source_positions, array).astype(np.float32)


def _coerce_bool(value: Any) -> Optional[bool]:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        normalized = value.strip().lower()
        if normalized in {"true", "1", "yes", "on"}:
            return True
        if normalized in {"false", "0", "no", "off"}:
            return False
    return None


def _resolve_model_reference(model_ref: str, project_dir: str) -> str:
    """Resolve local model paths against the project or app root when present."""
    if not model_ref:
        return model_ref

    if os.path.isabs(model_ref):
        return model_ref

    app_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    candidates = [
        os.path.join(project_dir, model_ref),
        os.path.join(app_root, model_ref),
    ]
    for candidate in candidates:
        if os.path.exists(candidate):
            return os.path.abspath(candidate)

    return model_ref


def _extract_qwen_generation_kwargs(tts_config: Dict[str, Any]) -> Dict[str, Any]:
    """Map project.json TTS tuning fields to qwen_tts generation kwargs."""
    specs = {
        "do_sample": (("doSample", "do_sample"), _coerce_bool),
        "top_k": (("topK", "top_k"), int),
        "top_p": (("topP", "top_p"), float),
        "temperature": (("temperature",), float),
        "repetition_penalty": (("repetitionPenalty", "repetition_penalty"), float),
        "max_new_tokens": (("maxNewTokens", "max_new_tokens"), int),
        "non_streaming_mode": (("nonStreamingMode", "non_streaming_mode"), _coerce_bool),
    }

    generation_kwargs: Dict[str, Any] = {}
    for output_key, (input_keys, coercer) in specs.items():
        raw_value = None
        for input_key in input_keys:
            if input_key in tts_config:
                raw_value = tts_config[input_key]
                break
        if raw_value is None:
            continue
        try:
            coerced = coercer(raw_value)
        except (TypeError, ValueError):
            continue
        if coerced is None:
            continue
        generation_kwargs[output_key] = coerced

    return generation_kwargs


def load_tts_runtime_config(project_dir: str, cli_model: str) -> Dict[str, Any]:
    """Load Stage 4 runtime config from project.json with safe defaults."""
    config: Dict[str, Any] = {
        "model_id": cli_model,
        "speaker": "Aiden",
        "edge_voice": os.environ.get("RENDER_TTS_EDGE_VOICE", "en-US-AndrewMultilingualNeural"),
        "language": "English",
        "speaking_rate": 1.0,
        "generation_kwargs": {},
    }

    project_json_path = os.path.join(project_dir, "project.json")
    if not os.path.exists(project_json_path):
        return config

    with open(project_json_path, encoding="utf-8") as f:
        project_config = json.load(f)

    tts_config = project_config.get("tts", {})
    if not isinstance(tts_config, dict):
        return config

    speaker = tts_config.get("speaker")
    if isinstance(speaker, str) and speaker.strip():
        config["speaker"] = speaker.strip()

    edge_voice = os.environ.get("RENDER_TTS_EDGE_VOICE")
    if isinstance(edge_voice, str) and edge_voice.strip():
        config["edge_voice"] = edge_voice.strip()
    else:
        project_edge_voice = tts_config.get("edgeVoice")
        if isinstance(project_edge_voice, str) and project_edge_voice.strip():
            config["edge_voice"] = project_edge_voice.strip()

    language = tts_config.get("language")
    if isinstance(language, str) and language.strip():
        config["language"] = language.strip()

    try:
        speaking_rate = float(tts_config.get("speakingRate", 1.0))
        if speaking_rate > 0:
            config["speaking_rate"] = speaking_rate
    except (TypeError, ValueError):
        pass

    model_path = tts_config.get("modelPath")
    if (
        isinstance(model_path, str)
        and model_path.strip()
        and cli_model == DEFAULT_MODEL
    ):
        config["model_id"] = _resolve_model_reference(model_path.strip(), project_dir)

    config["generation_kwargs"] = _extract_qwen_generation_kwargs(tts_config)
    return config


def apply_qwen_decode_warmup_patch(
    model: Any,
    sample_rate: int = SAMPLE_RATE,
    warmup_seconds: float = 0.25,
) -> bool:
    """Patch Qwen speech-tokenizer decode to reduce cold-start onset artifacts."""
    if os.environ.get("RENDER_TTS_DISABLE_QWEN_WARMUP_PATCH") == "1":
        return False

    speech_tokenizer = getattr(getattr(model, "model", None), "speech_tokenizer", None)
    if speech_tokenizer is None:
        return False
    if getattr(speech_tokenizer, "_video_editor_warmup_patch_applied", False):
        return False
    if not hasattr(speech_tokenizer, "encode") or not hasattr(speech_tokenizer, "decode"):
        return False

    try:
        import numpy as np
        import torch

        silence_audio = np.zeros(int(sample_rate * warmup_seconds), dtype=np.float32)
        silence_encoding = speech_tokenizer.encode(silence_audio, sr=sample_rate)
        silence_codes_list = getattr(silence_encoding, "audio_codes", None)
        if not silence_codes_list:
            return False

        silence_codes = silence_codes_list[0]
        if hasattr(silence_codes, "cpu"):
            silence_codes = silence_codes.cpu()
        silence_codes = torch.as_tensor(silence_codes)
        if silence_codes.ndim == 0 or silence_codes.shape[0] <= 0:
            return False

        original_decode = speech_tokenizer.decode
        trim_seconds = float(warmup_seconds)

        def decode_with_warmup(encoded_list: Any, **kwargs: Any) -> Tuple[List[Any], int]:
            patched_list = []
            for item in encoded_list:
                if not isinstance(item, dict) or "audio_codes" not in item:
                    patched_list.append(item)
                    continue

                audio_codes = torch.as_tensor(item["audio_codes"])
                silence_prefix = silence_codes.to(device=audio_codes.device, dtype=audio_codes.dtype)
                patched_item = dict(item)
                patched_item["audio_codes"] = torch.cat([silence_prefix, audio_codes], dim=0)
                patched_list.append(patched_item)

            wavs, fs = original_decode(patched_list, **kwargs)
            trim_samples = max(0, int(round(trim_seconds * fs)))
            if trim_samples == 0:
                return wavs, fs

            trimmed_wavs = []
            for wav in wavs:
                array = np.asarray(wav)
                if trim_samples >= len(array):
                    trimmed_wavs.append(array[:0].astype(np.float32))
                else:
                    trimmed_wavs.append(array[trim_samples:].astype(np.float32))
            return trimmed_wavs, fs

        speech_tokenizer.decode = decode_with_warmup
        speech_tokenizer._video_editor_warmup_patch_applied = True
        return True
    except Exception:
        return False


# ---------------------------------------------------------------------------
# Voice instruction mapping (from 3blue1brown demo)
# ---------------------------------------------------------------------------

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

BASE_INSTRUCTION = "Speak with a confident, authoritative tone like a knowledgeable educator"


def _normalize_annotation_value(value: Optional[str]) -> Optional[str]:
    """Normalize annotation strings for stable instruction lookup."""
    if value is None:
        return None
    normalized = re.sub(r"\s+", " ", value).strip().lower()
    return normalized or None


def build_instruction(tone: Optional[str] = None, pace: Optional[str] = None,
                      emotion: Optional[str] = None) -> str:
    """Build a voice instruction string from annotation values."""
    parts: List[str] = []
    normalized_tone = _normalize_annotation_value(tone)
    normalized_pace = _normalize_annotation_value(pace)

    if normalized_tone:
        mapped_tone = TONE_MAP.get(normalized_tone)
        if mapped_tone:
            parts.append(mapped_tone)
        else:
            parts.append(f"with a {normalized_tone} tone")

    if normalized_pace and normalized_pace in PACE_MAP and PACE_MAP[normalized_pace]:
        parts.append(PACE_MAP[normalized_pace])

    if emotion:
        parts.append(f"with {emotion} emotion")

    if parts:
        return f"{BASE_INSTRUCTION}, {', '.join(parts)}."
    return f"{BASE_INSTRUCTION}."


# ---------------------------------------------------------------------------
# TTS Engine
# ---------------------------------------------------------------------------

class TTSEngine:
    """
    Wrapper around the Qwen3-TTS model for text-to-speech synthesis.

    Uses the official `qwen-tts` package with Qwen3TTSModel API.
    Returns numpy float32 arrays (native model output).
    """

    def __init__(
        self,
        model_id: str,
        speaker: str = "Aiden",
        language: str = "English",
        speaking_rate: float = 1.0,
        generation_kwargs: Optional[Dict[str, Any]] = None,
    ):
        self.model_id = model_id
        self.speaker = speaker
        self.language = language
        self.speaking_rate = speaking_rate
        self.generation_kwargs = generation_kwargs or {}
        self.model = None
        self.sample_rate = SAMPLE_RATE
        self._load_model()

    def _load_model(self) -> None:
        """Load the Qwen3-TTS model via qwen-tts package."""
        import torch
        from qwen_tts import Qwen3TTSModel

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

        self.model = Qwen3TTSModel.from_pretrained(
            self.model_id,
            device_map=device,
            dtype=dtype,
            attn_implementation=attn_impl,
        )
        apply_qwen_decode_warmup_patch(self.model, sample_rate=self.sample_rate)
        self.sample_rate = SAMPLE_RATE

    def synthesize(self, text: str, **kwargs: Any) -> "np.ndarray":
        """
        Synthesize speech from text using Qwen3-TTS generate_custom_voice.

        Returns a numpy float32 array (native model output, no int16 conversion).
        """
        import numpy as np

        if not text.strip():
            return generate_silence(0.1)

        explicit_instruct = kwargs.get("instruct")
        instruct = (
            explicit_instruct.strip()
            if isinstance(explicit_instruct, str) and explicit_instruct.strip()
            else build_instruction(
                tone=kwargs.get("tone"),
                pace=kwargs.get("pace"),
                emotion=kwargs.get("emotion"),
            )
        )

        generation_kwargs = dict(getattr(self, "generation_kwargs", {}))
        wavs, sr = self.model.generate_custom_voice(
            text=text,
            speaker=self.speaker,
            language=self.language,
            instruct=instruct,
            **generation_kwargs,
        )

        if sr and sr != self.sample_rate:
            self.sample_rate = sr

        return apply_speaking_rate(wavs[0], getattr(self, "speaking_rate", 1.0))


class EdgeTTSEngine:
    """
    Fallback TTS engine using Microsoft Edge TTS (edge-tts).
    No model download required — uses Microsoft's online API.
    """

    def __init__(
        self,
        voice: str = "en-US-AndrewMultilingualNeural",
        speaking_rate: float = 1.0,
    ):
        self.voice = voice
        self.speaking_rate = speaking_rate
        self.sample_rate = SAMPLE_RATE
        try:
            import edge_tts  # type: ignore
        except ImportError as exc:
            raise RuntimeError("edge-tts is not installed. pip install edge-tts") from exc
        self._edge_tts = edge_tts

    def synthesize(self, text: str, **kwargs: Any) -> "np.ndarray":
        """Synthesize speech using edge-tts, return numpy float32 array."""
        import asyncio
        import tempfile
        import numpy as np

        if not text.strip():
            return generate_silence(0.1)

        async def _synth() -> "np.ndarray":
            communicate = self._edge_tts.Communicate(text, self.voice)
            with tempfile.NamedTemporaryFile(suffix=".mp3", delete=False) as tmp:
                tmp_path = tmp.name
            try:
                await communicate.save(tmp_path)
                import subprocess
                wav_path = tmp_path.replace(".mp3", ".wav")
                result = subprocess.run(
                    ["ffmpeg", "-y", "-i", tmp_path,
                     "-ac", "1", "-ar", str(SAMPLE_RATE), wav_path],
                    capture_output=True, timeout=30,
                )
                if result.returncode != 0:
                    raise RuntimeError(f"ffmpeg conversion failed: {result.stderr.decode()[:200]}")
                return read_wav_float32(wav_path)
            finally:
                for p in (tmp_path, tmp_path.replace(".mp3", ".wav")):
                    if os.path.exists(p):
                        os.unlink(p)

        loop = asyncio.new_event_loop()
        try:
            return apply_speaking_rate(
                loop.run_until_complete(_synth()),
                self.speaking_rate,
            )
        finally:
            loop.close()


class DeterministicFallbackTTSEngine:
    """Offline fallback engine that emits deterministic placeholder audio."""

    def __init__(self, speaking_rate: float = 1.0):
        self.sample_rate = SAMPLE_RATE
        self.speaking_rate = speaking_rate

    def synthesize(self, text: str, **kwargs: Any) -> "np.ndarray":
        import numpy as np

        if not text.strip():
            return generate_silence(0.1)

        word_count = max(1, len(text.split()))
        duration_seconds = min(6.0, max(0.45, word_count * 0.22))
        num_samples = int(self.sample_rate * duration_seconds)
        timeline = np.linspace(0, duration_seconds, num_samples, endpoint=False)

        # Low-amplitude tone with a light envelope so downstream WAV consumers
        # get deterministic non-empty audio even when online engines are absent.
        envelope = np.clip(np.linspace(0.0, 1.0, num_samples), 0.0, 1.0)
        tone = 0.08 * np.sin(2 * np.pi * 220 * timeline) * envelope
        return apply_speaking_rate(tone.astype(np.float32), self.speaking_rate)


# ---------------------------------------------------------------------------
# Segment rendering
# ---------------------------------------------------------------------------

def render_segment(
    engine: TTSEngine,
    segment: Segment,
    output_dir: str,
) -> Dict[str, Any]:
    """
    Render a single segment to a WAV file.

    Args:
        engine: The TTS engine instance.
        segment: The Segment to render.
        output_dir: Directory to write the output WAV file.

    Returns:
        A dict with segmentId, status, and duration (or error).
    """
    output_path = os.path.join(output_dir, f"{segment.segment_id}.wav")

    try:
        audio_chunks: List[bytes] = []

        for chunk in segment.text_chunks:
            if chunk["type"] == "pause":
                audio_chunks.append(
                    generate_silence_wav_bytes(chunk["duration"], engine.sample_rate)
                )
            elif chunk["type"] == "text":
                synthesized = engine.synthesize(
                    chunk["content"],
                    tone=segment.annotations.get("tone"),
                    pace=segment.annotations.get("pace"),
                    emotion=segment.annotations.get("emotion"),
                    instruct=segment.annotations.get("instruct"),
                )
                audio_chunks.append(_audio_to_pcm_bytes(synthesized))

        if not audio_chunks:
            audio_chunks.append(generate_silence_wav_bytes(0.1, engine.sample_rate))

        combined = concatenate_pcm(audio_chunks)
        duration = write_wav(output_path, combined, engine.sample_rate)

        return {
            "segmentId": segment.segment_id,
            "status": "done",
            "duration": round(duration, 2),
        }

    except Exception as e:
        return {
            "segmentId": segment.segment_id,
            "status": "error",
            "error": str(e),
        }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    """Build the argument parser for the render_tts script."""
    parser = argparse.ArgumentParser(
        description="Batch TTS synthesis using Qwen3-TTS. "
        "Reads narrative/tts_script.md and generates WAV files per segment.",
    )
    parser.add_argument(
        "--segments",
        type=str,
        default=None,
        help="Comma-separated segment IDs to render (e.g. seg_001,seg_003). "
        "Default: render all segments.",
    )
    parser.add_argument(
        "--segment",
        action="append",
        default=None,
        dest="segment_list",
        help="Segment ID to render (can be specified multiple times).",
    )
    parser.add_argument(
        "--output-dir",
        type=str,
        default=DEFAULT_OUTPUT_DIR,
        help=f"Output directory for WAV files. Default: {DEFAULT_OUTPUT_DIR}",
    )
    parser.add_argument(
        "--project-dir",
        type=str,
        default=DEFAULT_PROJECT_DIR,
        help=f"Project root directory. Default: {DEFAULT_PROJECT_DIR}",
    )
    parser.add_argument(
        "--model",
        type=str,
        default=DEFAULT_MODEL,
        help=f"Qwen3-TTS model ID. Default: {DEFAULT_MODEL}",
    )
    parser.add_argument(
        "--manifest-only",
        action="store_true",
        help="Parse tts_script.md and write outputs/tts/segments.json without rendering audio.",
    )
    return parser


def main() -> None:
    """Main entry point for the render_tts script."""
    parser = build_parser()
    args = parser.parse_args()

    project_dir = os.path.abspath(args.project_dir)
    output_dir = os.path.join(project_dir, args.output_dir) if not os.path.isabs(args.output_dir) else args.output_dir
    script_path = os.path.join(project_dir, "narrative", "tts_script.md")

    # Create output directory
    os.makedirs(output_dir, exist_ok=True)

    # Parse the TTS script
    try:
        all_segments = parse_tts_script(script_path, project_dir)
    except (FileNotFoundError, ValueError) as e:
        error_result = {
            "segmentId": "global",
            "status": "error",
            "error": str(e),
        }
        print(json.dumps(error_result), flush=True)
        sys.exit(1)

    write_segments_manifest(output_dir, all_segments)

    # Filter segments if --segments or --segment is specified
    requested_ids: Optional[set] = None
    if args.segments:
        requested_ids = {s.strip() for s in args.segments.split(",") if s.strip()}
    elif args.segment_list:
        requested_ids = set(args.segment_list)

    if requested_ids:
        segments_to_render = [s for s in all_segments if s.segment_id in requested_ids]
    else:
        segments_to_render = all_segments

    if args.manifest_only:
        sys.exit(0)

    if not segments_to_render:
        # No segments to render — this is not an error, just nothing to do
        sys.exit(0)

    runtime_config = load_tts_runtime_config(project_dir, args.model)

    # Load the TTS engine
    try:
        engine = TTSEngine(
            runtime_config["model_id"],
            speaker=runtime_config["speaker"],
            language=runtime_config["language"],
            speaking_rate=runtime_config["speaking_rate"],
            generation_kwargs=runtime_config["generation_kwargs"],
        )
    except Exception as e:
        allow_edge_fallback = os.environ.get("RENDER_TTS_ALLOW_EDGE_FALLBACK") == "1"
        if not allow_edge_fallback:
            error_result = {
                "segmentId": "global",
                "status": "error",
                "error": str(e),
            }
            print(json.dumps(error_result), flush=True)
            sys.exit(1)
        print(
            f"Qwen3-TTS unavailable ({e}); falling back to EdgeTTS",
            file=sys.stderr,
            flush=True,
        )
        try:
            engine = EdgeTTSEngine(
                voice=runtime_config["edge_voice"],
                speaking_rate=runtime_config["speaking_rate"],
            )
            print("Using EdgeTTS engine", file=sys.stderr, flush=True)
        except Exception as e2:
            print(
                f"EdgeTTS unavailable ({e2}); falling back to deterministic offline audio",
                file=sys.stderr,
                flush=True,
            )
            engine = DeterministicFallbackTTSEngine(
                speaking_rate=runtime_config["speaking_rate"]
            )

    # Render each segment
    has_errors = False
    for segment in segments_to_render:
        result = render_segment(engine, segment, output_dir)
        print(json.dumps(result), flush=True)
        if result["status"] == "error":
            has_errors = True

    sys.exit(1 if has_errors else 0)


if __name__ == "__main__":
    main()
