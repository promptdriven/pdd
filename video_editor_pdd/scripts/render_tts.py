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
import struct
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

DEFAULT_MODEL = "Qwen/Qwen3-TTS"
DEFAULT_OUTPUT_DIR = "outputs/tts/"
DEFAULT_PROJECT_DIR = "."
SAMPLE_RATE = 24000  # Qwen TTS models typically output 24kHz audio

# Annotation tag patterns
TAG_PATTERN = re.compile(
    r"\[(?:TONE|PACE|PAUSE|EMOTION)\s*:\s*[^\]]*\]", re.IGNORECASE
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

# Pattern to match NARRATOR: blocks
NARRATOR_PATTERN = re.compile(
    r"^NARRATOR\s*:\s*(.+?)(?=^NARRATOR\s*:|\Z)",
    re.MULTILINE | re.DOTALL,
)


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
            clean = TAG_PATTERN.sub("", before).strip()
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
        clean = TAG_PATTERN.sub("", remaining).strip()
        if clean:
            chunks.append({"type": "text", "content": clean})

        # If no chunks were produced (edge case), use full cleaned text
        if not chunks:
            clean_all = TAG_PATTERN.sub("", self.raw_text).strip()
            if clean_all:
                chunks.append({"type": "text", "content": clean_all})

        return chunks

    @property
    def clean_text(self) -> str:
        """Full text with all annotation tags stripped."""
        return TAG_PATTERN.sub("", self.raw_text).strip()


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------

def parse_tts_script(script_path: str) -> List[Segment]:
    """
    Parse the tts_script.md file and extract NARRATOR: blocks.

    Args:
        script_path: Path to the tts_script.md file.

    Returns:
        List of Segment objects in order of appearance.

    Raises:
        FileNotFoundError: If the script file does not exist.
        ValueError: If no NARRATOR blocks are found.
    """
    path = Path(script_path)
    if not path.exists():
        raise FileNotFoundError(f"TTS script not found: {script_path}")

    content = path.read_text(encoding="utf-8")
    matches = NARRATOR_PATTERN.findall(content)

    if not matches:
        raise ValueError(
            f"No NARRATOR: blocks found in {script_path}. "
            "Expected format: 'NARRATOR: <text>'"
        )

    segments: List[Segment] = []
    for idx, raw_text in enumerate(matches, start=1):
        segment_id = f"seg_{idx:03d}"
        segments.append(Segment(segment_id, raw_text))

    return segments


# ---------------------------------------------------------------------------
# Audio utilities
# ---------------------------------------------------------------------------

def generate_silence_wav_bytes(duration_seconds: float, sample_rate: int = SAMPLE_RATE) -> bytes:
    """
    Generate raw PCM silence bytes (16-bit mono) for the given duration.

    Args:
        duration_seconds: Duration of silence in seconds.
        sample_rate: Audio sample rate.

    Returns:
        Raw PCM bytes representing silence.
    """
    num_samples = int(sample_rate * duration_seconds)
    return struct.pack(f"<{num_samples}h", *([0] * num_samples))


def write_wav(filepath: str, audio_data: bytes, sample_rate: int = SAMPLE_RATE) -> float:
    """
    Write raw PCM 16-bit mono audio data to a WAV file.

    Args:
        filepath: Output WAV file path.
        audio_data: Raw PCM bytes (16-bit signed, little-endian, mono).
        sample_rate: Audio sample rate.

    Returns:
        Duration of the audio in seconds.
    """
    num_samples = len(audio_data) // 2  # 16-bit = 2 bytes per sample
    duration = num_samples / sample_rate

    with wave.open(filepath, "wb") as wf:
        wf.setnchannels(1)
        wf.setsampwidth(2)  # 16-bit
        wf.setframerate(sample_rate)
        wf.writeframes(audio_data)

    return duration


def concatenate_pcm(chunks: List[bytes]) -> bytes:
    """Concatenate multiple raw PCM byte chunks."""
    return b"".join(chunks)


# ---------------------------------------------------------------------------
# TTS Engine
# ---------------------------------------------------------------------------

class TTSEngine:
    """
    Wrapper around the Qwen3-TTS model for text-to-speech synthesis.

    Handles model loading and inference, converting text to raw PCM audio bytes.
    """

    def __init__(self, model_id: str):
        self.model_id = model_id
        self.processor = None
        self.model = None
        self.sample_rate = SAMPLE_RATE
        self._load_model()

    def _load_model(self) -> None:
        """Load the TTS model and processor."""
        try:
            from transformers import AutoProcessor, AutoModelForTextToWaveform
        except ImportError:
            try:
                from transformers import AutoTokenizer, AutoModel
                self._use_fallback = True
            except ImportError:
                raise RuntimeError(
                    "transformers library is not installed. "
                    "Install it with: pip install transformers"
                )
            else:
                self._use_fallback = True
                self._load_model_fallback()
                return

        self._use_fallback = False
        try:
            self.processor = AutoProcessor.from_pretrained(
                self.model_id, trust_remote_code=True
            )
            self.model = AutoModelForTextToWaveform.from_pretrained(
                self.model_id, trust_remote_code=True
            )
        except Exception:
            # Fall back to generic Auto classes
            self._use_fallback = True
            self._load_model_fallback()

    def _load_model_fallback(self) -> None:
        """Fallback model loading using AutoTokenizer + AutoModel."""
        from transformers import AutoTokenizer, AutoModel

        self.processor = AutoTokenizer.from_pretrained(
            self.model_id, trust_remote_code=True
        )
        self.model = AutoModel.from_pretrained(
            self.model_id, trust_remote_code=True
        )

    def synthesize(self, text: str, **kwargs: Any) -> bytes:
        """
        Synthesize speech from text.

        Args:
            text: The text to synthesize.
            **kwargs: Additional parameters (tone, pace, emotion) for
                      voice control if supported by the model.

        Returns:
            Raw PCM audio bytes (16-bit signed, little-endian, mono).
        """
        import torch
        import numpy as np

        if not text.strip():
            # Return a tiny bit of silence for empty text
            return generate_silence_wav_bytes(0.1)

        try:
            if self._use_fallback:
                inputs = self.processor(text, return_tensors="pt")
            else:
                inputs = self.processor(
                    text=text, return_tensors="pt"
                )

            with torch.no_grad():
                output = self.model(**inputs)

            # Extract waveform from model output
            if hasattr(output, "waveform"):
                waveform = output.waveform
            elif hasattr(output, "audio"):
                waveform = output.audio
            elif isinstance(output, dict):
                for key in ("waveform", "audio", "wav"):
                    if key in output:
                        waveform = output[key]
                        break
                else:
                    waveform = list(output.values())[0]
            elif isinstance(output, (tuple, list)):
                waveform = output[0]
            else:
                waveform = output

            # Convert to numpy
            if isinstance(waveform, torch.Tensor):
                audio_np = waveform.squeeze().cpu().numpy()
            elif isinstance(waveform, np.ndarray):
                audio_np = waveform.squeeze()
            else:
                audio_np = np.array(waveform, dtype=np.float32).squeeze()

            # Normalize to 16-bit PCM range
            if audio_np.dtype in (np.float32, np.float64):
                max_val = np.max(np.abs(audio_np))
                if max_val > 0:
                    audio_np = audio_np / max_val
                audio_np = (audio_np * 32767).astype(np.int16)
            elif audio_np.dtype != np.int16:
                audio_np = audio_np.astype(np.int16)

            return audio_np.tobytes()

        except Exception as e:
            raise RuntimeError(f"TTS synthesis failed for text: {e}") from e


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
    start_time = time.time()

    try:
        audio_chunks: List[bytes] = []

        for chunk in segment.text_chunks:
            if chunk["type"] == "pause":
                silence = generate_silence_wav_bytes(chunk["duration"])
                audio_chunks.append(silence)
            elif chunk["type"] == "text":
                pcm = engine.synthesize(
                    chunk["content"],
                    tone=segment.annotations.get("tone"),
                    pace=segment.annotations.get("pace"),
                    emotion=segment.annotations.get("emotion"),
                )
                audio_chunks.append(pcm)

        if not audio_chunks:
            # Edge case: segment had no renderable content
            audio_chunks.append(generate_silence_wav_bytes(0.1))

        combined = concatenate_pcm(audio_chunks)
        duration = write_wav(output_path, combined)

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
        all_segments = parse_tts_script(script_path)
    except (FileNotFoundError, ValueError) as e:
        error_result = {
            "segmentId": "global",
            "status": "error",
            "error": str(e),
        }
        print(json.dumps(error_result), flush=True)
        sys.exit(1)

    # Filter segments if --segments is specified
    if args.segments:
        requested_ids = {s.strip() for s in args.segments.split(",") if s.strip()}
        segments_to_render = [s for s in all_segments if s.segment_id in requested_ids]
    else:
        segments_to_render = all_segments

    if not segments_to_render:
        # No segments to render — this is not an error, just nothing to do
        sys.exit(0)

    # Load the TTS model
    try:
        engine = TTSEngine(args.model)
    except Exception as e:
        error_result = {
            "segmentId": "global",
            "status": "error",
            "error": f"Failed to load TTS model '{args.model}': {e}",
        }
        print(json.dumps(error_result), flush=True)
        sys.exit(1)

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