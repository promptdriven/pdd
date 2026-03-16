#!/usr/bin/env python3
"""
Benchmark STT models against a section narration WAV and expected TTS text.

This is a reproducible local benchmark helper for evaluating potential Stage 5
audio-sync model upgrades on the current machine.
"""

from __future__ import annotations

import argparse
import json
import math
import subprocess
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any


ROOT_DIR = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class BenchmarkConfig:
    key: str
    kind: str
    model_id: str
    device: str
    compute_type: str | None = None
    torch_dtype: str | None = None
    chunk_length_s: int = 30
    batch_size: int = 8


@dataclass
class BenchmarkResult:
    key: str
    kind: str
    model_id: str
    device: str
    wall_seconds: float
    audio_seconds: float
    realtime_factor: float
    wer: float
    expected_word_count: int
    actual_word_count: int
    normalized_expected: str
    normalized_actual: str
    notes: str = ""


BENCHMARKS: list[BenchmarkConfig] = [
    BenchmarkConfig(
        key="stage5_current",
        kind="faster-whisper",
        model_id="base",
        device="cpu",
        compute_type="int8",
    ),
    BenchmarkConfig(
        key="whisper_large_v3_turbo_mlx",
        kind="mlx-whisper",
        model_id="mlx-community/whisper-large-v3-turbo",
        device="apple-gpu",
    ),
    BenchmarkConfig(
        key="whisper_large_v3_mlx",
        kind="mlx-whisper",
        model_id="mlx-community/whisper-large-v3-mlx",
        device="apple-gpu",
    ),
]


def get_audio_seconds(audio_path: Path) -> float:
    output = subprocess.check_output(
        [
            "ffprobe",
            "-v",
            "error",
            "-show_entries",
            "format=duration",
            "-of",
            "default=nokey=1:noprint_wrappers=1",
            str(audio_path),
        ],
        text=True,
    ).strip()
    return float(output)


def normalize_text(text: str) -> str:
    lowered = text.lower()
    lowered = lowered.replace("\u2018", "").replace("\u2019", "").replace("'", "")
    normalized = []
    for ch in lowered:
        normalized.append(ch if ch.isalnum() or ch.isspace() else " ")
    collapsed = "".join(normalized)
    return " ".join(collapsed.split())


def word_error_rate(expected: str, actual: str) -> float:
    expected_words = expected.split()
    actual_words = actual.split()

    if not expected_words:
        return 0.0 if not actual_words else 1.0

    rows = len(expected_words) + 1
    cols = len(actual_words) + 1
    dp = [[0] * cols for _ in range(rows)]

    for i in range(rows):
        dp[i][0] = i
    for j in range(cols):
        dp[0][j] = j

    for i in range(1, rows):
        for j in range(1, cols):
            cost = 0 if expected_words[i - 1] == actual_words[j - 1] else 1
            dp[i][j] = min(
                dp[i - 1][j] + 1,
                dp[i][j - 1] + 1,
                dp[i - 1][j - 1] + cost,
            )

    return dp[-1][-1] / len(expected_words)


def load_expected_text(project_dir: Path, section_id: str) -> str:
    manifest_path = project_dir / "outputs" / "tts" / "segments.json"
    manifest = json.loads(manifest_path.read_text())
    segments = manifest.get("segments", [])
    parts: list[str] = []
    for segment in segments:
        if segment.get("sectionId") == section_id:
            clean_text = segment.get("cleanText") or segment.get("text") or ""
            if isinstance(clean_text, str) and clean_text.strip():
                parts.append(clean_text.strip())
    return " ".join(parts)


def transcribe_faster_whisper(config: BenchmarkConfig, audio_path: Path) -> str:
    from faster_whisper import WhisperModel

    model = WhisperModel(
        config.model_id,
        device=config.device,
        compute_type=config.compute_type or "int8",
    )
    segments_iter, _info = model.transcribe(
        str(audio_path),
        language="en",
        word_timestamps=False,
    )
    return " ".join(segment.text.strip() for segment in segments_iter if segment.text)


def transcribe_transformers(config: BenchmarkConfig, audio_path: Path) -> str:
    import torch
    from transformers import AutoModelForSpeechSeq2Seq, AutoProcessor, pipeline

    torch_dtype = torch.float16 if config.torch_dtype == "float16" else torch.float32

    model = AutoModelForSpeechSeq2Seq.from_pretrained(
        config.model_id,
        torch_dtype=torch_dtype,
        low_cpu_mem_usage=True,
        use_safetensors=True,
    )
    model.to(config.device)
    processor = AutoProcessor.from_pretrained(config.model_id)

    pipe = pipeline(
        "automatic-speech-recognition",
        model=model,
        tokenizer=processor.tokenizer,
        feature_extractor=processor.feature_extractor,
        torch_dtype=torch_dtype,
        device=config.device,
    )

    result = pipe(
        str(audio_path),
        chunk_length_s=config.chunk_length_s,
        batch_size=config.batch_size,
        return_timestamps=False,
        generate_kwargs={"language": "english", "task": "transcribe"},
    )
    text = result["text"] if isinstance(result, dict) else str(result)
    return text.strip()


def transcribe_mlx_whisper(config: BenchmarkConfig, audio_path: Path) -> str:
    import mlx_whisper

    result = mlx_whisper.transcribe(
        str(audio_path),
        path_or_hf_repo=config.model_id,
        language="en",
        task="transcribe",
        verbose=False,
        word_timestamps=False,
    )
    text = result["text"] if isinstance(result, dict) else str(result)
    return text.strip()


def run_benchmark(
    config: BenchmarkConfig,
    audio_path: Path,
    expected_text: str,
    audio_seconds: float,
) -> BenchmarkResult:
    start = time.perf_counter()
    if config.kind == "faster-whisper":
        actual_text = transcribe_faster_whisper(config, audio_path)
    elif config.kind == "transformers":
        actual_text = transcribe_transformers(config, audio_path)
    elif config.kind == "mlx-whisper":
        actual_text = transcribe_mlx_whisper(config, audio_path)
    else:
        raise ValueError(f"Unsupported benchmark kind: {config.kind}")
    wall_seconds = time.perf_counter() - start

    normalized_expected = normalize_text(expected_text)
    normalized_actual = normalize_text(actual_text)
    wer = word_error_rate(normalized_expected, normalized_actual)
    realtime_factor = audio_seconds / wall_seconds if wall_seconds > 0 else math.inf

    return BenchmarkResult(
        key=config.key,
        kind=config.kind,
        model_id=config.model_id,
        device=config.device,
        wall_seconds=round(wall_seconds, 3),
        audio_seconds=round(audio_seconds, 3),
        realtime_factor=round(realtime_factor, 3),
        wer=round(wer, 4),
        expected_word_count=len(normalized_expected.split()),
        actual_word_count=len(normalized_actual.split()),
        normalized_expected=normalized_expected,
        normalized_actual=normalized_actual,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Benchmark local STT model options.")
    parser.add_argument("--project-dir", required=True, help="Project directory path.")
    parser.add_argument("--section-id", required=True, help="Section ID to benchmark.")
    parser.add_argument(
        "--audio-path",
        help="Optional explicit narration WAV path. Defaults to remotion/public/<section>/narration.wav",
    )
    parser.add_argument(
        "--models",
        nargs="*",
        default=[config.key for config in BENCHMARKS],
        help="Subset of benchmark keys to run.",
    )
    parser.add_argument(
        "--json-out",
        help="Optional output path for benchmark JSON.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    project_dir = Path(args.project_dir).resolve()
    audio_path = (
        Path(args.audio_path).resolve()
        if args.audio_path
        else ROOT_DIR / "remotion" / "public" / args.section_id / "narration.wav"
    )

    expected_text = load_expected_text(project_dir, args.section_id)
    if not expected_text:
        raise SystemExit(f"No expected text found for section {args.section_id}")
    if not audio_path.exists():
        raise SystemExit(f"Audio file not found: {audio_path}")

    audio_seconds = get_audio_seconds(audio_path)
    configs = [config for config in BENCHMARKS if config.key in set(args.models)]
    results: list[BenchmarkResult] = []

    for config in configs:
        try:
            print(f"[benchmark] Running {config.key} ({config.model_id} on {config.device})...")
            result = run_benchmark(config, audio_path, expected_text, audio_seconds)
        except Exception as exc:  # pragma: no cover - benchmark helper
            result = BenchmarkResult(
                key=config.key,
                kind=config.kind,
                model_id=config.model_id,
                device=config.device,
                wall_seconds=0.0,
                audio_seconds=round(audio_seconds, 3),
                realtime_factor=0.0,
                wer=1.0,
                expected_word_count=len(normalize_text(expected_text).split()),
                actual_word_count=0,
                normalized_expected=normalize_text(expected_text),
                normalized_actual="",
                notes=f"FAILED: {type(exc).__name__}: {exc}",
            )
        results.append(result)

    payload = {
        "projectDir": str(project_dir),
        "sectionId": args.section_id,
        "audioPath": str(audio_path),
        "results": [asdict(result) for result in results],
    }

    if args.json_out:
        Path(args.json_out).write_text(json.dumps(payload, indent=2))

    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
