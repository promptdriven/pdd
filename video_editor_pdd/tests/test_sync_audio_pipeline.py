"""
Tests for scripts/sync_audio_pipeline.py

PDD Principle: The prompt file is the source of truth.
These tests verify that the code conforms to the specification in
prompts/sync_audio_pipeline_python.prompt.

Spec requirements verified:
  1. Reads project.json from --project-dir to get sectionGroups
  2. For each section:
     a. Reads segment WAV files from --output-dir/{segmentId}.wav
     b. Concatenates in order using ffmpeg or pydub
     c. Copies result to --remotion-public/{sectionId}/narration.wav
     d. Runs Faster-Whisper on concatenated WAV for word-level timestamps
     e. Writes word_timestamps.json to --output-dir/{sectionId}/word_timestamps.json
  3. Prints JSON progress lines to stdout per section (done/error format)
  4. CLI args: --project-dir, --output-dir, --remotion-public with defaults
  5. Exits with code 0 on success; non-zero if any section failed
  6. word_timestamps.json format: [{"word", "start", "end", "segmentId"}, ...]
  7. Maps words back to originating segment via cumulative audio duration
  8. Missing segment WAVs: print error for that section, continue
  9. Creates output/remotion subdirectories as needed
 10. Uses faster_whisper.WhisperModel with word_timestamps=True
 11. Uses argparse for CLI parsing
 12. Import guard: if __name__ == '__main__': main()
"""

import json
import os
import struct
import sys
import tempfile
import wave
from pathlib import Path
from typing import Any, Dict, List
from unittest import mock

import pytest

# Add scripts/ directory to path so we can import sync_audio_pipeline
TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(TESTS_DIR)
SCRIPTS_DIR = os.path.join(PROJECT_ROOT, "scripts")
sys.path.insert(0, SCRIPTS_DIR)

from sync_audio_pipeline import (
    build_segment_validation_report,
    compute_transcript_match_ratio,
    evaluate_validation_gate,
    normalize_transcript_text,
    load_project,
    load_section_groups,
    get_segment_wav_path,
    get_wav_duration,
    concatenate_wavs_ffmpeg,
    _concatenate_wavs_pydub,
    copy_to_remotion,
    generate_word_timestamps,
    is_apple_silicon_mac,
    resolve_stt_backend,
    process_section,
    main,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _create_dummy_wav(path: str, duration_ms: int = 1000, sample_rate: int = 16000) -> None:
    """Create a minimal valid WAV file with silence."""
    num_samples = int(sample_rate * duration_ms / 1000)
    data_size = num_samples * 2  # 16-bit = 2 bytes per sample
    with open(path, "wb") as f:
        f.write(b"RIFF")
        f.write(struct.pack("<I", 36 + data_size))
        f.write(b"WAVE")
        f.write(b"fmt ")
        f.write(struct.pack("<I", 16))       # chunk size
        f.write(struct.pack("<H", 1))        # PCM format
        f.write(struct.pack("<H", 1))        # mono
        f.write(struct.pack("<I", sample_rate))
        f.write(struct.pack("<I", sample_rate * 2))  # byte rate
        f.write(struct.pack("<H", 2))        # block align
        f.write(struct.pack("<H", 16))       # bits per sample
        f.write(b"data")
        f.write(struct.pack("<I", data_size))
        f.write(b"\x00" * data_size)


def _write_project_json(project_dir: str, section_groups: Dict[str, List[str]]) -> None:
    """Write a project.json with the given sectionGroups."""
    project = {"sectionGroups": section_groups}
    with open(os.path.join(project_dir, "project.json"), "w") as f:
        json.dump(project, f)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def tmp_project(tmp_path):
    """Create a temporary project directory with project.json and segment WAVs."""
    section_groups = {
        "intro": ["seg_001", "seg_002"],
        "section2": ["seg_003"],
    }
    _write_project_json(str(tmp_path), section_groups)

    # Create output dir with segment WAVs
    output_dir = tmp_path / "outputs" / "tts"
    output_dir.mkdir(parents=True)
    _create_dummy_wav(str(output_dir / "seg_001.wav"), duration_ms=1500)
    _create_dummy_wav(str(output_dir / "seg_002.wav"), duration_ms=2000)
    _create_dummy_wav(str(output_dir / "seg_003.wav"), duration_ms=1000)

    # Create remotion public dir
    remotion_dir = tmp_path / "remotion" / "public"
    remotion_dir.mkdir(parents=True)

    return tmp_path


@pytest.fixture
def output_dir(tmp_path):
    """Create a temporary output directory."""
    out = tmp_path / "outputs" / "tts"
    out.mkdir(parents=True)
    return out


@pytest.fixture(autouse=True)
def force_test_stt_backend(monkeypatch):
    """Keep the existing suite deterministic regardless of local MLX availability."""
    monkeypatch.setenv("SYNC_AUDIO_STT_BACKEND", "faster-whisper")


# ---------------------------------------------------------------------------
# Mock helpers for Faster-Whisper
# ---------------------------------------------------------------------------

class MockWordInfo:
    """Mock word info returned by Faster-Whisper."""
    def __init__(self, word: str, start: float, end: float):
        self.word = word
        self.start = start
        self.end = end


class MockSegment:
    """Mock transcription segment returned by Faster-Whisper."""
    def __init__(self, words: list):
        self.words = words


def make_mock_whisper_model(words_data: List[Dict[str, Any]] = None):
    """Create a mock WhisperModel that returns predefined words."""
    if words_data is None:
        words_data = [
            {"word": " Hello", "start": 0.1, "end": 0.4},
            {"word": " world", "start": 0.5, "end": 0.9},
            {"word": " testing", "start": 1.6, "end": 2.0},
        ]

    mock_words = [MockWordInfo(w["word"], w["start"], w["end"]) for w in words_data]
    mock_segment = MockSegment(mock_words)

    mock_model = mock.MagicMock()
    mock_model.transcribe.return_value = (iter([mock_segment]), mock.MagicMock())
    return mock_model


# ===========================================================================
# Tests: load_project
# ===========================================================================

class TestLoadProject:
    """Verify project.json loading and validation."""

    def test_loads_valid_project(self, tmp_path):
        """Spec: Reads project.json from --project-dir to get sectionGroups."""
        _write_project_json(str(tmp_path), {"intro": ["seg_001"]})
        project = load_project(str(tmp_path))
        assert "sectionGroups" in project
        assert project["sectionGroups"]["intro"] == ["seg_001"]

    def test_returns_full_project_dict(self, tmp_path):
        project_data = {
            "sectionGroups": {"intro": ["seg_001"]},
            "title": "Test",
        }
        with open(tmp_path / "project.json", "w") as f:
            json.dump(project_data, f)
        project = load_project(str(tmp_path))
        assert project["title"] == "Test"

    def test_missing_project_json_raises(self, tmp_path):
        with pytest.raises(FileNotFoundError, match="project.json not found"):
            load_project(str(tmp_path))

    def test_invalid_json_raises(self, tmp_path):
        (tmp_path / "project.json").write_text("not valid json {{")
        with pytest.raises(json.JSONDecodeError):
            load_project(str(tmp_path))

    def test_missing_section_groups_raises(self, tmp_path):
        (tmp_path / "project.json").write_text('{"title": "No sections"}')
        with pytest.raises(ValueError, match="sectionGroups"):
            load_project(str(tmp_path))


class TestLoadSectionGroups:
    """Verify section-group normalization against the current narration manifest."""

    def test_normalizes_stale_section_id_to_manifest_section(self, tmp_path):
        project = {
            "sections": [
                {
                    "id": "part3_mold_has_three_parts",
                    "specDir": "part3_mold_has_three_parts",
                }
            ],
            "audioSync": {
                "sectionGroups": {
                    "part3_mold_three_parts": {
                        "startSegment": "part3_mold_three_parts_001",
                        "endSegment": "part3_mold_three_parts_002",
                    }
                }
            },
        }
        (tmp_path / "project.json").write_text(json.dumps(project), encoding="utf-8")

        output_dir = tmp_path / "outputs" / "tts"
        output_dir.mkdir(parents=True)
        (output_dir / "segments.json").write_text(
            json.dumps(
                {
                    "segments": [
                        {
                            "id": "part3_mold_has_three_parts_001",
                            "sectionId": "part3_mold_has_three_parts",
                            "cleanText": "First line.",
                        },
                        {
                            "id": "part3_mold_has_three_parts_002",
                            "sectionId": "part3_mold_has_three_parts",
                            "cleanText": "Second line.",
                        },
                    ]
                }
            ),
            encoding="utf-8",
        )
        _create_dummy_wav(str(output_dir / "part3_mold_has_three_parts_001.wav"))
        _create_dummy_wav(str(output_dir / "part3_mold_has_three_parts_002.wav"))

        section_groups = load_section_groups(str(tmp_path), str(output_dir))

        assert section_groups == {
            "part3_mold_has_three_parts": [
                "part3_mold_has_three_parts_001",
                "part3_mold_has_three_parts_002",
            ]
        }

    def test_prunes_obsolete_section_groups_that_are_not_current_project_sections(self, tmp_path):
        project = {
            "sections": [
                {
                    "id": "part3_mold_parts",
                    "specDir": "part3_mold_parts",
                }
            ],
            "audioSync": {
                "sectionGroups": {
                    "part3_mold_has_three_parts": {
                        "startSegment": "part3_mold_has_three_parts_001",
                        "endSegment": "part3_mold_has_three_parts_002",
                    },
                    "part3_mold_parts": {
                        "startSegment": "part3_mold_parts_001",
                        "endSegment": "part3_mold_parts_002",
                    },
                }
            },
        }
        (tmp_path / "project.json").write_text(json.dumps(project), encoding="utf-8")

        output_dir = tmp_path / "outputs" / "tts"
        output_dir.mkdir(parents=True)
        (output_dir / "segments.json").write_text(
            json.dumps(
                {
                    "segments": [
                        {
                            "id": "part3_mold_parts_001",
                            "sectionId": "part3_mold_parts",
                            "cleanText": "First line.",
                        },
                        {
                            "id": "part3_mold_parts_002",
                            "sectionId": "part3_mold_parts",
                            "cleanText": "Second line.",
                        },
                    ]
                }
            ),
            encoding="utf-8",
        )
        _create_dummy_wav(str(output_dir / "part3_mold_parts_001.wav"))
        _create_dummy_wav(str(output_dir / "part3_mold_parts_002.wav"))

        section_groups = load_section_groups(str(tmp_path), str(output_dir))

        assert section_groups == {
            "part3_mold_parts": [
                "part3_mold_parts_001",
                "part3_mold_parts_002",
            ]
        }

    def test_prunes_obsolete_section_groups_even_when_stale_wavs_still_exist(self, tmp_path):
        project = {
            "sections": [
                {
                    "id": "part3_mold_parts",
                    "specDir": "part3_mold_parts",
                }
            ],
            "audioSync": {
                "sectionGroups": {
                    "part3_mold_has_three_parts": {
                        "startSegment": "part3_mold_has_three_parts_001",
                        "endSegment": "part3_mold_has_three_parts_002",
                    },
                    "part3_mold_parts": {
                        "startSegment": "part3_mold_parts_001",
                        "endSegment": "part3_mold_parts_002",
                    },
                }
            },
        }
        (tmp_path / "project.json").write_text(json.dumps(project), encoding="utf-8")

        output_dir = tmp_path / "outputs" / "tts"
        output_dir.mkdir(parents=True)
        (output_dir / "segments.json").write_text(
            json.dumps(
                {
                    "segments": [
                        {
                            "id": "part3_mold_parts_001",
                            "sectionId": "part3_mold_parts",
                            "cleanText": "First line.",
                        },
                        {
                            "id": "part3_mold_parts_002",
                            "sectionId": "part3_mold_parts",
                            "cleanText": "Second line.",
                        },
                    ]
                }
            ),
            encoding="utf-8",
        )
        _create_dummy_wav(str(output_dir / "part3_mold_parts_001.wav"))
        _create_dummy_wav(str(output_dir / "part3_mold_parts_002.wav"))
        _create_dummy_wav(str(output_dir / "part3_mold_has_three_parts_001.wav"))
        _create_dummy_wav(str(output_dir / "part3_mold_has_three_parts_002.wav"))

        section_groups = load_section_groups(str(tmp_path), str(output_dir))

        assert section_groups == {
            "part3_mold_parts": [
                "part3_mold_parts_001",
                "part3_mold_parts_002",
            ]
        }

    def test_drops_unresolved_obsolete_section_groups_instead_of_returning_empty_sections(self, tmp_path):
        project = {
            "sections": [
                {
                    "id": "part3_mold_parts",
                    "specDir": "part3_mold_parts",
                }
            ],
            "audioSync": {
                "sectionGroups": {
                    "part3_mold_has_three_parts": {
                        "startSegment": "part3_mold_has_three_parts_001",
                        "endSegment": "part3_mold_has_three_parts_030",
                    },
                    "part3_mold_parts": {
                        "startSegment": "part3_mold_parts_001",
                        "endSegment": "part3_mold_parts_022",
                    },
                }
            },
        }
        (tmp_path / "project.json").write_text(json.dumps(project), encoding="utf-8")

        output_dir = tmp_path / "outputs" / "tts"
        output_dir.mkdir(parents=True)
        (output_dir / "segments.json").write_text(
            json.dumps(
                {
                    "segments": [
                        {
                            "id": "part3_mold_parts_001",
                            "sectionId": "part3_mold_parts",
                            "cleanText": "First line.",
                        },
                        {
                            "id": "part3_mold_parts_022",
                            "sectionId": "part3_mold_parts",
                            "cleanText": "Last line.",
                        },
                    ]
                }
            ),
            encoding="utf-8",
        )
        _create_dummy_wav(str(output_dir / "part3_mold_parts_001.wav"))
        _create_dummy_wav(str(output_dir / "part3_mold_parts_022.wav"))

        section_groups = load_section_groups(str(tmp_path), str(output_dir))

        assert "part3_mold_has_three_parts" not in section_groups
        assert "part3_mold_parts" in section_groups

    def test_prefers_most_similar_manifest_section_over_broader_numeric_overlap(self, tmp_path):
        project = {
            "sections": [
                {"id": "part1_economics", "specDir": "part1_economics"},
                {"id": "part3_mold_parts", "specDir": "part3_mold_parts"},
            ],
            "audioSync": {
                "sectionGroups": {
                    "part3_mold_has_three_parts": {
                        "startSegment": "part3_mold_has_three_parts_001",
                        "endSegment": "part3_mold_has_three_parts_030",
                    }
                }
            },
        }
        (tmp_path / "project.json").write_text(json.dumps(project), encoding="utf-8")

        output_dir = tmp_path / "outputs" / "tts"
        output_dir.mkdir(parents=True)
        segments = []
        for i in range(1, 29):
            segments.append(
                {
                    "id": f"part1_economics_{i:03d}",
                    "sectionId": "part1_economics",
                    "cleanText": f"Part 1 line {i}.",
                }
            )
            _create_dummy_wav(str(output_dir / f"part1_economics_{i:03d}.wav"))
        for i in range(1, 23):
            segments.append(
                {
                    "id": f"part3_mold_parts_{i:03d}",
                    "sectionId": "part3_mold_parts",
                    "cleanText": f"Part 3 line {i}.",
                }
            )
            _create_dummy_wav(str(output_dir / f"part3_mold_parts_{i:03d}.wav"))

        (output_dir / "segments.json").write_text(
            json.dumps({"segments": segments}),
            encoding="utf-8",
        )

        section_groups = load_section_groups(str(tmp_path), str(output_dir))

        assert list(section_groups.keys()) == ["part3_mold_parts"]
        assert section_groups["part3_mold_parts"][0] == "part3_mold_parts_001"
        assert section_groups["part3_mold_parts"][-1] == "part3_mold_parts_022"

    def test_section_groups_not_dict_raises(self, tmp_path):
        (tmp_path / "project.json").write_text('{"sectionGroups": ["a", "b"]}')
        with pytest.raises(ValueError, match="dictionary"):
            load_project(str(tmp_path))

    def test_section_groups_multiple_sections(self, tmp_path):
        """Spec: sectionGroups map like {"intro": ["seg_001", "seg_002"], "section2": ["seg_003"]}."""
        section_groups = {
            "intro": ["seg_001", "seg_002"],
            "section2": ["seg_003"],
        }
        _write_project_json(str(tmp_path), section_groups)
        project = load_project(str(tmp_path))
        assert len(project["sectionGroups"]) == 2
        assert project["sectionGroups"]["intro"] == ["seg_001", "seg_002"]
        assert project["sectionGroups"]["section2"] == ["seg_003"]


# ===========================================================================
# Tests: get_segment_wav_path
# ===========================================================================

class TestGetSegmentWavPath:
    """Verify segment WAV path construction."""

    def test_constructs_correct_path(self):
        """Spec: Reads segment WAV files from --output-dir/{segmentId}.wav."""
        path = get_segment_wav_path("/output/tts", "seg_001")
        assert path == Path("/output/tts/seg_001.wav")

    def test_returns_path_object(self):
        path = get_segment_wav_path("outputs/tts", "seg_042")
        assert isinstance(path, Path)
        assert path.name == "seg_042.wav"

    def test_relative_output_dir(self):
        path = get_segment_wav_path("outputs/tts/", "seg_001")
        assert str(path) == "outputs/tts/seg_001.wav"


# ===========================================================================
# Tests: get_wav_duration
# ===========================================================================

class TestGetWavDuration:
    """Verify WAV duration retrieval with ffprobe / pydub fallback."""

    def test_ffprobe_returns_duration(self, tmp_path):
        """Test duration via ffprobe mock."""
        wav_path = tmp_path / "test.wav"
        _create_dummy_wav(str(wav_path), duration_ms=2000)

        mock_result = mock.MagicMock()
        mock_result.stdout = "2.000000\n"

        with mock.patch("sync_audio_pipeline.subprocess.run", return_value=mock_result) as mock_run:
            duration = get_wav_duration(wav_path)
            assert duration == pytest.approx(2.0, abs=0.01)
            mock_run.assert_called_once()

    def test_ffprobe_failure_falls_back_to_pydub(self, tmp_path):
        """Spec: Falls back to pydub if ffprobe is not available."""
        wav_path = tmp_path / "test.wav"
        _create_dummy_wav(str(wav_path), duration_ms=1000)

        mock_audio = mock.MagicMock()
        mock_audio.__len__ = mock.MagicMock(return_value=1000)  # 1000ms

        mock_pydub = mock.MagicMock()
        mock_pydub.AudioSegment.from_wav.return_value = mock_audio

        with mock.patch(
            "sync_audio_pipeline.subprocess.run",
            side_effect=FileNotFoundError("ffprobe not found"),
        ):
            with mock.patch.dict("sys.modules", {"pydub": mock_pydub}):
                duration = get_wav_duration(wav_path)
                assert duration == pytest.approx(1.0, abs=0.01)


# ===========================================================================
# Tests: concatenate_wavs_ffmpeg
# ===========================================================================

class TestConcatenateWavsFfmpeg:
    """Verify WAV concatenation."""

    def test_calls_ffmpeg_with_concat_demuxer(self, tmp_path):
        """Spec: Concatenates using ffmpeg -f concat -safe 0 -i filelist.txt -c copy output.wav."""
        seg1 = tmp_path / "seg_001.wav"
        seg2 = tmp_path / "seg_002.wav"
        _create_dummy_wav(str(seg1))
        _create_dummy_wav(str(seg2))
        out = tmp_path / "output.wav"

        with mock.patch("sync_audio_pipeline.subprocess.run") as mock_run:
            concatenate_wavs_ffmpeg([seg1, seg2], out)
            call_args = mock_run.call_args[0][0]
            assert "ffmpeg" in call_args
            assert "-f" in call_args
            assert "concat" in call_args
            assert "-safe" in call_args
            assert "0" in call_args
            assert "-c" in call_args
            assert "copy" in call_args

    def test_creates_filelist_with_segment_paths(self, tmp_path):
        """Verify the temp filelist contains the segment paths."""
        seg1 = tmp_path / "seg_001.wav"
        _create_dummy_wav(str(seg1))
        out = tmp_path / "output.wav"

        written_content = []

        original_named_temp = tempfile.NamedTemporaryFile

        def capture_filelist(*args, **kwargs):
            tf = original_named_temp(*args, **kwargs)
            original_write = tf.write

            def capturing_write(data):
                written_content.append(data)
                return original_write(data)

            tf.write = capturing_write
            return tf

        with mock.patch("sync_audio_pipeline.tempfile.NamedTemporaryFile", side_effect=capture_filelist):
            with mock.patch("sync_audio_pipeline.subprocess.run"):
                concatenate_wavs_ffmpeg([seg1], out)

        filelist_text = "".join(written_content)
        assert "seg_001.wav" in filelist_text

    def test_ffmpeg_not_found_falls_back_to_pydub(self, tmp_path):
        """Spec: Falls back to pydub if ffmpeg is not available."""
        seg1 = tmp_path / "seg_001.wav"
        _create_dummy_wav(str(seg1))
        out = tmp_path / "output.wav"

        with mock.patch(
            "sync_audio_pipeline.subprocess.run",
            side_effect=FileNotFoundError("ffmpeg not found"),
        ):
            with mock.patch("sync_audio_pipeline._concatenate_wavs_pydub") as mock_pydub:
                concatenate_wavs_ffmpeg([seg1], out)
                mock_pydub.assert_called_once_with([seg1], out)

    def test_cleans_up_temp_filelist(self, tmp_path):
        """Verify temporary filelist is cleaned up after ffmpeg run."""
        seg1 = tmp_path / "seg_001.wav"
        _create_dummy_wav(str(seg1))
        out = tmp_path / "output.wav"

        filelist_paths = []
        original_unlink = os.unlink

        def track_unlink(path):
            filelist_paths.append(path)
            original_unlink(path)

        with mock.patch("sync_audio_pipeline.subprocess.run"):
            with mock.patch("sync_audio_pipeline.os.unlink", side_effect=track_unlink):
                concatenate_wavs_ffmpeg([seg1], out)

        assert len(filelist_paths) == 1
        assert filelist_paths[0].endswith(".txt")


# ===========================================================================
# Tests: copy_to_remotion
# ===========================================================================

class TestCopyToRemotion:
    """Verify copying to Remotion public directory."""

    def test_copies_to_correct_path(self, tmp_path):
        """Spec: Copies result to --remotion-public/{sectionId}/narration.wav."""
        source = tmp_path / "source.wav"
        _create_dummy_wav(str(source))
        remotion_public = str(tmp_path / "remotion" / "public")

        dest = copy_to_remotion(source, remotion_public, "intro")

        expected = Path(remotion_public) / "intro" / "narration.wav"
        assert dest == expected
        assert expected.exists()

    def test_creates_remotion_subdirectory(self, tmp_path):
        """Spec: Create remotion public subdirectories as needed."""
        source = tmp_path / "source.wav"
        _create_dummy_wav(str(source))
        remotion_public = str(tmp_path / "remotion" / "public")
        # Directory does not exist yet
        assert not os.path.exists(remotion_public)

        copy_to_remotion(source, remotion_public, "intro")

        assert os.path.isdir(os.path.join(remotion_public, "intro"))

    def test_output_filename_is_narration_wav(self, tmp_path):
        source = tmp_path / "source.wav"
        _create_dummy_wav(str(source))
        remotion_public = str(tmp_path / "remotion" / "public")

        dest = copy_to_remotion(source, remotion_public, "section2")
        assert dest.name == "narration.wav"


# ===========================================================================
# Tests: generate_word_timestamps
# ===========================================================================

class TestGenerateWordTimestamps:
    """Verify word-level timestamp generation with Faster-Whisper."""

    def test_uses_whisper_model_with_word_timestamps(self, tmp_path):
        """Spec: Uses faster_whisper.WhisperModel with word_timestamps=True."""
        wav_path = tmp_path / "test.wav"
        _create_dummy_wav(str(wav_path))

        mock_model = make_mock_whisper_model()

        with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
            generate_word_timestamps(wav_path, ["seg_001"], [3.0])

        mock_model.transcribe.assert_called_once()
        call_kwargs = mock_model.transcribe.call_args[1]
        assert call_kwargs["word_timestamps"] is True

    def test_returns_correct_format(self, tmp_path):
        """Spec: word_timestamps.json format: [{"word", "start", "end", "segmentId"}, ...]."""
        wav_path = tmp_path / "test.wav"
        _create_dummy_wav(str(wav_path))

        mock_model = make_mock_whisper_model([
            {"word": " Hello", "start": 0.12, "end": 0.45},
        ])

        with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
            result = generate_word_timestamps(wav_path, ["seg_001"], [3.0])

        assert len(result) == 1
        word = result[0]
        assert "word" in word
        assert "start" in word
        assert "end" in word
        assert "segmentId" in word

    def test_word_text_is_stripped(self, tmp_path):
        """Verify leading/trailing whitespace is stripped from word text."""
        wav_path = tmp_path / "test.wav"
        _create_dummy_wav(str(wav_path))

        mock_model = make_mock_whisper_model([
            {"word": " Hello ", "start": 0.1, "end": 0.4},
        ])

        with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
            result = generate_word_timestamps(wav_path, ["seg_001"], [3.0])

        assert result[0]["word"] == "Hello"

    def test_timestamps_are_rounded(self, tmp_path):
        """Verify timestamps are rounded to 3 decimal places."""
        wav_path = tmp_path / "test.wav"
        _create_dummy_wav(str(wav_path))

        mock_model = make_mock_whisper_model([
            {"word": "Test", "start": 0.123456, "end": 0.789012},
        ])

        with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
            result = generate_word_timestamps(wav_path, ["seg_001"], [3.0])

        assert result[0]["start"] == 0.123
        assert result[0]["end"] == 0.789

    def test_maps_words_to_segments_by_cumulative_duration(self, tmp_path):
        """Spec: Map each word back to its originating segment by tracking cumulative audio duration."""
        wav_path = tmp_path / "test.wav"
        _create_dummy_wav(str(wav_path))

        # seg_001: 0-1.5s, seg_002: 1.5-3.5s
        mock_model = make_mock_whisper_model([
            {"word": "Hello", "start": 0.1, "end": 0.4},     # seg_001
            {"word": "world", "start": 0.5, "end": 0.9},     # seg_001
            {"word": "testing", "start": 1.6, "end": 2.0},   # seg_002
            {"word": "more", "start": 3.0, "end": 3.4},      # seg_002
        ])

        with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
            result = generate_word_timestamps(
                wav_path,
                ["seg_001", "seg_002"],
                [1.5, 2.0],
            )

        assert result[0]["segmentId"] == "seg_001"
        assert result[1]["segmentId"] == "seg_001"
        assert result[2]["segmentId"] == "seg_002"
        assert result[3]["segmentId"] == "seg_002"

    def test_word_at_boundary_maps_to_next_segment(self, tmp_path):
        """Word starting exactly at segment boundary maps to the next segment."""
        wav_path = tmp_path / "test.wav"
        _create_dummy_wav(str(wav_path))

        # seg_001: 0-1.5s, seg_002: 1.5-3.0s
        mock_model = make_mock_whisper_model([
            {"word": "boundary", "start": 1.5, "end": 2.0},  # exactly at boundary
        ])

        with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
            result = generate_word_timestamps(
                wav_path,
                ["seg_001", "seg_002"],
                [1.5, 1.5],
            )

        assert result[0]["segmentId"] == "seg_002"

    def test_handles_segment_with_no_words(self, tmp_path):
        """Handle transcription segments with words=None."""
        wav_path = tmp_path / "test.wav"
        _create_dummy_wav(str(wav_path))

        mock_segment_no_words = MockSegment(None)
        mock_model = mock.MagicMock()
        mock_model.transcribe.return_value = (iter([mock_segment_no_words]), mock.MagicMock())

        with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
            result = generate_word_timestamps(wav_path, ["seg_001"], [3.0])

        assert result == []

    def test_single_segment_all_words_mapped(self, tmp_path):
        """Single segment: all words map to that segment."""
        wav_path = tmp_path / "test.wav"
        _create_dummy_wav(str(wav_path))

        mock_model = make_mock_whisper_model([
            {"word": "word1", "start": 0.0, "end": 0.3},
            {"word": "word2", "start": 0.4, "end": 0.7},
        ])

        with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
            result = generate_word_timestamps(wav_path, ["seg_001"], [3.0])

        for word in result:
            assert word["segmentId"] == "seg_001"

    def test_can_use_mlx_whisper_with_word_timestamps(self, tmp_path, monkeypatch):
        """Apple Silicon path uses mlx-whisper when explicitly requested."""
        wav_path = tmp_path / "test.wav"
        _create_dummy_wav(str(wav_path))

        monkeypatch.setenv("SYNC_AUDIO_STT_BACKEND", "mlx-whisper")
        mock_mlx = mock.MagicMock()
        mock_mlx.transcribe.return_value = {
            "segments": [
                {
                    "words": [
                        {"word": " Hello", "start": 0.1, "end": 0.4},
                        {"word": " world", "start": 0.5, "end": 0.8},
                    ]
                }
            ]
        }

        with mock.patch("sync_audio_pipeline.is_apple_silicon_mac", return_value=True):
            with mock.patch("sync_audio_pipeline.importlib.import_module", return_value=mock_mlx):
                result = generate_word_timestamps(wav_path, ["seg_001"], [1.0])

        assert result == [
            {"word": "Hello", "start": 0.1, "end": 0.4, "segmentId": "seg_001"},
            {"word": "world", "start": 0.5, "end": 0.8, "segmentId": "seg_001"},
        ]
        mock_mlx.transcribe.assert_called_once()
        call_kwargs = mock_mlx.transcribe.call_args.kwargs
        assert call_kwargs["word_timestamps"] is True
        assert call_kwargs["task"] == "transcribe"
        assert call_kwargs["language"] == "en"


class TestSttBackendSelection:
    """Verify Stage 5 STT backend selection logic."""

    def test_detects_apple_silicon_mac(self):
        with mock.patch("sync_audio_pipeline.sys.platform", "darwin"):
            with mock.patch("sync_audio_pipeline.platform.machine", return_value="arm64"):
                assert is_apple_silicon_mac() is True

    def test_resolve_stt_backend_prefers_mlx_on_apple_silicon(self, monkeypatch):
        monkeypatch.delenv("SYNC_AUDIO_STT_BACKEND", raising=False)
        mock_mlx = mock.MagicMock()

        with mock.patch("sync_audio_pipeline.is_apple_silicon_mac", return_value=True):
            with mock.patch("sync_audio_pipeline.importlib.import_module", return_value=mock_mlx):
                backend = resolve_stt_backend()

        assert backend["backend"] == "mlx-whisper"
        assert backend["model_id"] == "mlx-community/whisper-large-v3-turbo"

    def test_resolve_stt_backend_falls_back_to_faster_whisper(self, monkeypatch):
        monkeypatch.delenv("SYNC_AUDIO_STT_BACKEND", raising=False)

        with mock.patch("sync_audio_pipeline.is_apple_silicon_mac", return_value=True):
            with mock.patch(
                "sync_audio_pipeline.importlib.import_module",
                side_effect=ImportError("no mlx"),
            ):
                backend = resolve_stt_backend()

        assert backend["backend"] == "faster-whisper"
        assert backend["model_id"] == "base"
        assert backend["device"] == "cpu"
        assert backend["compute_type"] == "int8"

    def test_resolve_stt_backend_honors_explicit_faster_whisper_override(self, monkeypatch):
        monkeypatch.setenv("SYNC_AUDIO_STT_BACKEND", "faster-whisper")

        with mock.patch("sync_audio_pipeline.is_apple_silicon_mac", return_value=True):
            backend = resolve_stt_backend()

        assert backend["backend"] == "faster-whisper"

    def test_resolve_stt_backend_raises_if_forced_mlx_is_unavailable(self, monkeypatch):
        monkeypatch.setenv("SYNC_AUDIO_STT_BACKEND", "mlx-whisper")

        with mock.patch("sync_audio_pipeline.is_apple_silicon_mac", return_value=True):
            with mock.patch(
                "sync_audio_pipeline.importlib.import_module",
                side_effect=ImportError("no mlx"),
            ):
                with pytest.raises(RuntimeError, match="mlx-whisper requested but unavailable"):
                    resolve_stt_backend()

    def test_resolve_stt_backend_raises_if_forced_mlx_on_non_apple_silicon(self, monkeypatch):
        monkeypatch.setenv("SYNC_AUDIO_STT_BACKEND", "mlx-whisper")

        with mock.patch("sync_audio_pipeline.is_apple_silicon_mac", return_value=False):
            with pytest.raises(RuntimeError, match="mlx-whisper requires Apple Silicon macOS"):
                resolve_stt_backend()


# ===========================================================================
# Tests: process_section
# ===========================================================================

class TestProcessSection:
    """Verify per-section processing pipeline."""

    def test_success_returns_done_status(self, tmp_project):
        """Spec: On success, {"sectionId": ..., "status": "done", "wordCount": ...}."""
        output_dir = str(tmp_project / "outputs" / "tts")
        remotion_public = str(tmp_project / "remotion" / "public")

        mock_model = make_mock_whisper_model()

        def fake_concat(segment_paths, output_path):
            _create_dummy_wav(str(output_path))

        with mock.patch("sync_audio_pipeline.concatenate_wavs_ffmpeg", side_effect=fake_concat):
            with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
                with mock.patch("sync_audio_pipeline.get_wav_duration", return_value=1.5):
                    result = process_section("intro", ["seg_001", "seg_002"], output_dir, remotion_public)

        assert result["sectionId"] == "intro"
        assert result["status"] == "done"
        assert "wordCount" in result
        assert isinstance(result["wordCount"], int)

    def test_creates_output_subdirectory(self, tmp_project):
        """Spec: Create output subdirectories as needed."""
        output_dir = str(tmp_project / "outputs" / "tts")
        remotion_public = str(tmp_project / "remotion" / "public")

        mock_model = make_mock_whisper_model()

        def fake_concat(segment_paths, output_path):
            _create_dummy_wav(str(output_path))

        with mock.patch("sync_audio_pipeline.concatenate_wavs_ffmpeg", side_effect=fake_concat):
            with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
                with mock.patch("sync_audio_pipeline.get_wav_duration", return_value=1.0):
                    process_section("intro", ["seg_001"], output_dir, remotion_public)

        assert os.path.isdir(os.path.join(output_dir, "intro"))

    def test_writes_word_timestamps_json(self, tmp_project):
        """Spec: Writes word_timestamps.json to --output-dir/{sectionId}/word_timestamps.json."""
        output_dir = str(tmp_project / "outputs" / "tts")
        remotion_public = str(tmp_project / "remotion" / "public")

        mock_model = make_mock_whisper_model([
            {"word": "Hello", "start": 0.1, "end": 0.4},
        ])

        def fake_concat(segment_paths, output_path):
            _create_dummy_wav(str(output_path))

        with mock.patch("sync_audio_pipeline.concatenate_wavs_ffmpeg", side_effect=fake_concat):
            with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
                with mock.patch("sync_audio_pipeline.get_wav_duration", return_value=1.5):
                    process_section("intro", ["seg_001"], output_dir, remotion_public)

        timestamps_path = os.path.join(output_dir, "intro", "word_timestamps.json")
        assert os.path.exists(timestamps_path)

        with open(timestamps_path) as f:
            data = json.load(f)
        assert isinstance(data, list)
        assert len(data) == 1
        assert data[0]["word"] == "Hello"

    def test_word_timestamps_json_format(self, tmp_project):
        """Spec: [{"word": "Hello", "start": 0.12, "end": 0.45, "segmentId": "seg_001"}, ...]."""
        output_dir = str(tmp_project / "outputs" / "tts")
        remotion_public = str(tmp_project / "remotion" / "public")

        mock_model = make_mock_whisper_model([
            {"word": "Hello", "start": 0.12, "end": 0.45},
        ])

        def fake_concat(segment_paths, output_path):
            _create_dummy_wav(str(output_path))

        with mock.patch("sync_audio_pipeline.concatenate_wavs_ffmpeg", side_effect=fake_concat):
            with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
                with mock.patch("sync_audio_pipeline.get_wav_duration", return_value=1.5):
                    process_section("intro", ["seg_001"], output_dir, remotion_public)

        timestamps_path = os.path.join(output_dir, "intro", "word_timestamps.json")
        with open(timestamps_path) as f:
            data = json.load(f)

        entry = data[0]
        assert set(entry.keys()) == {"word", "start", "end", "segmentId"}
        assert entry["segmentId"] == "seg_001"

    def test_missing_all_segments_returns_error(self, tmp_path):
        """Spec: If a section has no segment WAVs present, print an error for that section."""
        output_dir = str(tmp_path / "outputs" / "tts")
        os.makedirs(output_dir, exist_ok=True)
        remotion_public = str(tmp_path / "remotion" / "public")

        result = process_section("intro", ["missing_001", "missing_002"], output_dir, remotion_public)

        assert result["sectionId"] == "intro"
        assert result["status"] == "error"
        assert "error" in result
        assert "No segment WAV files found" in result["error"]

    def test_missing_some_segments_continues(self, tmp_project):
        """Spec: Continue with available segments if some are missing."""
        output_dir = str(tmp_project / "outputs" / "tts")
        remotion_public = str(tmp_project / "remotion" / "public")

        mock_model = make_mock_whisper_model()

        def fake_concat(segment_paths, output_path):
            _create_dummy_wav(str(output_path))

        with mock.patch("sync_audio_pipeline.concatenate_wavs_ffmpeg", side_effect=fake_concat):
            with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
                with mock.patch("sync_audio_pipeline.get_wav_duration", return_value=1.0):
                    # seg_001 exists, missing_seg does not
                    result = process_section(
                        "intro", ["seg_001", "missing_seg"], output_dir, remotion_public
                    )

        # Should succeed with available segments
        assert result["status"] == "done"

    def test_concatenation_failure_returns_error(self, tmp_project):
        """Test error handling when concatenation fails."""
        output_dir = str(tmp_project / "outputs" / "tts")
        remotion_public = str(tmp_project / "remotion" / "public")

        with mock.patch(
            "sync_audio_pipeline.concatenate_wavs_ffmpeg",
            side_effect=RuntimeError("concat failed"),
        ):
            result = process_section("intro", ["seg_001"], output_dir, remotion_public)

        assert result["status"] == "error"
        assert "Failed to concatenate" in result["error"]

    def test_copies_to_remotion_public(self, tmp_project):
        """Spec: Copies result to --remotion-public/{sectionId}/narration.wav."""
        output_dir = str(tmp_project / "outputs" / "tts")
        remotion_public = str(tmp_project / "remotion" / "public")

        mock_model = make_mock_whisper_model()

        def fake_concat(segment_paths, output_path):
            _create_dummy_wav(str(output_path))

        with mock.patch("sync_audio_pipeline.concatenate_wavs_ffmpeg", side_effect=fake_concat):
            with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
                with mock.patch("sync_audio_pipeline.get_wav_duration", return_value=1.0):
                    process_section("intro", ["seg_001"], output_dir, remotion_public)

        narration_path = os.path.join(remotion_public, "intro", "narration.wav")
        assert os.path.exists(narration_path)

    def test_whisper_failure_returns_error(self, tmp_project):
        """Test error handling when Faster-Whisper fails."""
        output_dir = str(tmp_project / "outputs" / "tts")
        remotion_public = str(tmp_project / "remotion" / "public")

        def fake_concat(segment_paths, output_path):
            _create_dummy_wav(str(output_path))

        with mock.patch("sync_audio_pipeline.concatenate_wavs_ffmpeg", side_effect=fake_concat):
            with mock.patch(
                "faster_whisper.WhisperModel",
                side_effect=RuntimeError("whisper failed"),
            ):
                with mock.patch("sync_audio_pipeline.get_wav_duration", return_value=1.0):
                    result = process_section("intro", ["seg_001"], output_dir, remotion_public)

        assert result["status"] == "error"
        assert "Failed to generate word timestamps" in result["error"]

    def test_writes_segment_validation_report(self, tmp_project):
        """Writes segment_validation.json alongside word_timestamps.json."""
        output_dir = str(tmp_project / "outputs" / "tts")
        remotion_public = str(tmp_project / "remotion" / "public")

        manifest = {
            "segments": [
                {"id": "seg_001", "cleanText": "Hello world."},
            ]
        }
        with open(os.path.join(output_dir, "segments.json"), "w", encoding="utf-8") as f:
            json.dump(manifest, f)

        mock_model = make_mock_whisper_model([
            {"word": "Hello", "start": 0.1, "end": 0.4},
            {"word": "world", "start": 0.5, "end": 0.8},
        ])

        def fake_concat(segment_paths, output_path):
            _create_dummy_wav(str(output_path))

        with mock.patch("sync_audio_pipeline.concatenate_wavs_ffmpeg", side_effect=fake_concat):
            with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
                with mock.patch("sync_audio_pipeline.get_wav_duration", return_value=1.0):
                    process_section("intro", ["seg_001"], output_dir, remotion_public)

        validation_path = os.path.join(output_dir, "intro", "segment_validation.json")
        assert os.path.exists(validation_path)
        with open(validation_path, "r", encoding="utf-8") as f:
            validation = json.load(f)

        assert validation["segments"][0]["segmentId"] == "seg_001"
        assert validation["segments"][0]["status"] == "pass"
        assert validation["summary"]["passCount"] == 1

    def test_done_result_includes_validation_summary(self, tmp_project):
        """Successful section processing includes transcript-validation counts."""
        output_dir = str(tmp_project / "outputs" / "tts")
        remotion_public = str(tmp_project / "remotion" / "public")

        manifest = {
            "segments": [
                {"id": "seg_001", "cleanText": "Correct words."},
            ]
        }
        with open(os.path.join(output_dir, "segments.json"), "w", encoding="utf-8") as f:
            json.dump(manifest, f)

        mock_model = make_mock_whisper_model([
            {"word": "Totally", "start": 0.1, "end": 0.3},
            {"word": "different", "start": 0.4, "end": 0.7},
        ])

        def fake_concat(segment_paths, output_path):
            _create_dummy_wav(str(output_path))

        with mock.patch("sync_audio_pipeline.concatenate_wavs_ffmpeg", side_effect=fake_concat):
            with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
                with mock.patch("sync_audio_pipeline.get_wav_duration", return_value=1.0):
                    result = process_section("intro", ["seg_001"], output_dir, remotion_public)

        assert result["status"] == "done"
        assert result["validationSummary"]["failCount"] == 1
        assert result["validationSummary"]["passCount"] == 0

    def test_returns_error_when_validation_gate_rejects_section(self, tmp_project):
        """Validation gating should fail the section without promoting bad artifacts."""
        output_dir = str(tmp_project / "outputs" / "tts")
        remotion_public = str(tmp_project / "remotion" / "public")

        manifest = {
            "segments": [
                {"id": "seg_001", "cleanText": "Correct words."},
            ]
        }
        with open(os.path.join(output_dir, "segments.json"), "w", encoding="utf-8") as f:
            json.dump(manifest, f)

        section_output_dir = Path(output_dir) / "intro"
        section_output_dir.mkdir(parents=True, exist_ok=True)
        accepted_timestamps = [
            {"word": "accepted", "start": 0.0, "end": 0.2, "segmentId": "seg_001"},
        ]
        (section_output_dir / "word_timestamps.json").write_text(
            json.dumps(accepted_timestamps),
            encoding="utf-8",
        )

        remotion_section_dir = Path(remotion_public) / "intro"
        remotion_section_dir.mkdir(parents=True, exist_ok=True)
        accepted_narration_path = remotion_section_dir / "narration.wav"
        _create_dummy_wav(str(accepted_narration_path), duration_ms=250)
        accepted_narration_bytes = accepted_narration_path.read_bytes()

        mock_model = make_mock_whisper_model([
            {"word": "Totally", "start": 0.1, "end": 0.3},
            {"word": "different", "start": 0.4, "end": 0.7},
        ])

        def fake_concat(segment_paths, output_path):
            _create_dummy_wav(str(output_path), duration_ms=1000)

        with mock.patch("sync_audio_pipeline.concatenate_wavs_ffmpeg", side_effect=fake_concat):
            with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
                with mock.patch("sync_audio_pipeline.get_wav_duration", return_value=1.0):
                    result = process_section(
                        "intro",
                        ["seg_001"],
                        output_dir,
                        remotion_public,
                        validation_policy={
                            "maxFailCount": 0,
                            "maxFailRatio": 0.0,
                            "maxWarnCount": 0,
                        },
                    )

        assert result["status"] == "error"
        assert "Transcript validation failed" in result["error"]
        assert result["validationSummary"]["failCount"] == 1
        assert json.loads((section_output_dir / "word_timestamps.json").read_text(encoding="utf-8")) == accepted_timestamps
        assert accepted_narration_path.read_bytes() == accepted_narration_bytes
        assert (section_output_dir / "word_timestamps.failed.json").exists()
        assert (section_output_dir / "segment_validation.failed.json").exists()


class TestSegmentValidation:
    """Verify transcript-vs-script validation helpers."""

    def test_normalize_transcript_text_collapses_case_and_punctuation(self):
        assert normalize_transcript_text("Hello,  WORLD!!") == "hello world"

    def test_normalize_transcript_text_normalizes_numeric_variants(self):
        assert normalize_transcript_text("Fifteen lines, 200 bugs, 55%!") == "num lines num bugs num"

    def test_normalize_transcript_text_collapses_multi_word_number_phrases(self):
        assert (
            normalize_transcript_text("Two hundred lines of generated code.")
            == "num lines of generated code"
        )

    def test_build_segment_validation_report_marks_random_speech_as_fail(self, tmp_path):
        output_dir = tmp_path / "outputs" / "tts"
        output_dir.mkdir(parents=True)

        manifest = {
            "segments": [
                {"id": "intro_001", "cleanText": "The quick brown fox jumps over the lazy dog."},
                {"id": "intro_002", "cleanText": "A second sentence for comparison."},
            ]
        }
        (output_dir / "segments.json").write_text(json.dumps(manifest), encoding="utf-8")

        report = build_segment_validation_report(
            ["intro_001", "intro_002"],
            str(output_dir),
            [
                {"word": "random", "start": 0.0, "end": 0.2, "segmentId": "intro_001"},
                {"word": "words", "start": 0.2, "end": 0.4, "segmentId": "intro_001"},
                {"word": "A", "start": 0.5, "end": 0.6, "segmentId": "intro_002"},
                {"word": "second", "start": 0.6, "end": 0.7, "segmentId": "intro_002"},
                {"word": "sentence", "start": 0.7, "end": 0.9, "segmentId": "intro_002"},
                {"word": "for", "start": 0.9, "end": 1.0, "segmentId": "intro_002"},
                {"word": "comparison", "start": 1.0, "end": 1.2, "segmentId": "intro_002"},
            ],
        )

        first = report["segments"][0]
        second = report["segments"][1]
        assert first["status"] == "fail"
        assert first["matchRatio"] < 0.8
        assert second["status"] == "pass"
        assert report["summary"]["failCount"] == 1

    def test_build_segment_validation_report_skips_missing_manifest_text(self, tmp_path):
        output_dir = tmp_path / "outputs" / "tts"
        output_dir.mkdir(parents=True)
        (output_dir / "segments.json").write_text('{"segments":[]}', encoding="utf-8")

        report = build_segment_validation_report(
            ["intro_001"],
            str(output_dir),
            [{"word": "hello", "start": 0.0, "end": 0.2, "segmentId": "intro_001"}],
        )

        assert report["segments"][0]["status"] == "skip"
        assert report["summary"]["skipCount"] == 1

    def test_build_segment_validation_report_treats_numeric_variants_as_match(self, tmp_path):
        output_dir = tmp_path / "outputs" / "tts"
        output_dir.mkdir(parents=True)
        manifest = {
            "segments": [
                {"id": "intro_001", "cleanText": "Fifteen lines of prompt. Two hundred lines of generated code."},
            ]
        }
        (output_dir / "segments.json").write_text(json.dumps(manifest), encoding="utf-8")

        report = build_segment_validation_report(
            ["intro_001"],
            str(output_dir),
            [
                {"word": "15", "start": 0.0, "end": 0.2, "segmentId": "intro_001"},
                {"word": "lines", "start": 0.2, "end": 0.3, "segmentId": "intro_001"},
                {"word": "of", "start": 0.3, "end": 0.4, "segmentId": "intro_001"},
                {"word": "prompt", "start": 0.4, "end": 0.5, "segmentId": "intro_001"},
                {"word": "200", "start": 0.5, "end": 0.7, "segmentId": "intro_001"},
                {"word": "lines", "start": 0.7, "end": 0.8, "segmentId": "intro_001"},
                {"word": "of", "start": 0.8, "end": 0.9, "segmentId": "intro_001"},
                {"word": "generated", "start": 0.9, "end": 1.0, "segmentId": "intro_001"},
                {"word": "code", "start": 1.0, "end": 1.1, "segmentId": "intro_001"},
            ],
        )

        assert report["segments"][0]["status"] == "pass"
        assert report["summary"]["failCount"] == 0

    def test_build_segment_validation_report_treats_spelled_out_and_numeric_counts_as_match(
        self,
        tmp_path,
    ):
        output_dir = tmp_path / "outputs" / "tts"
        output_dir.mkdir(parents=True)
        manifest = {
            "segments": [
                {"id": "intro_001", "cleanText": "Two hundred lines of generated code."},
            ]
        }
        (output_dir / "segments.json").write_text(json.dumps(manifest), encoding="utf-8")

        report = build_segment_validation_report(
            ["intro_001"],
            str(output_dir),
            [
                {"word": "200", "start": 0.0, "end": 0.2, "segmentId": "intro_001"},
                {"word": "lines", "start": 0.2, "end": 0.3, "segmentId": "intro_001"},
                {"word": "of", "start": 0.3, "end": 0.4, "segmentId": "intro_001"},
                {"word": "generated", "start": 0.4, "end": 0.5, "segmentId": "intro_001"},
                {"word": "code", "start": 0.5, "end": 0.6, "segmentId": "intro_001"},
            ],
        )

        assert report["segments"][0]["status"] == "pass"
        assert report["segments"][0]["matchRatio"] == 1.0
        assert report["summary"]["failCount"] == 0

    def test_compute_transcript_match_ratio_penalizes_boundary_hallucinated_words(self):
        ratio = compute_transcript_match_ratio(
            "If you use Cursor, or Claude Code, or Copilot...",
            "Cripple if you use cursor or Claude Code or Copilot.",
        )

        assert ratio < 0.94
        assert ratio >= 0.8

    def test_compute_transcript_match_ratio_penalizes_missing_boundary_words(self):
        ratio = compute_transcript_match_ratio(
            "If you use Cursor, or Claude Code, or Copilot...",
            "you use cursor or Claude Code or Copilot.",
        )

        assert ratio < 0.94
        assert ratio >= 0.8

    def test_build_segment_validation_report_marks_boundary_hallucination_as_warn(self, tmp_path):
        output_dir = tmp_path / "outputs" / "tts"
        output_dir.mkdir(parents=True)
        manifest = {
            "segments": [
                {
                    "id": "cold_open_001",
                    "cleanText": "If you use Cursor, or Claude Code, or Copilot...",
                },
            ]
        }
        (output_dir / "segments.json").write_text(json.dumps(manifest), encoding="utf-8")

        report = build_segment_validation_report(
            ["cold_open_001"],
            str(output_dir),
            [
                {"word": "Cripple", "start": 0.0, "end": 0.52, "segmentId": "cold_open_001"},
                {"word": "if", "start": 0.52, "end": 0.76, "segmentId": "cold_open_001"},
                {"word": "you", "start": 0.76, "end": 0.88, "segmentId": "cold_open_001"},
                {"word": "use", "start": 0.88, "end": 1.24, "segmentId": "cold_open_001"},
                {"word": "cursor", "start": 1.24, "end": 1.68, "segmentId": "cold_open_001"},
                {"word": "or", "start": 1.68, "end": 2.10, "segmentId": "cold_open_001"},
                {"word": "Claude", "start": 2.10, "end": 2.54, "segmentId": "cold_open_001"},
                {"word": "Code", "start": 2.54, "end": 2.78, "segmentId": "cold_open_001"},
                {"word": "or", "start": 2.78, "end": 3.02, "segmentId": "cold_open_001"},
                {"word": "Copilot", "start": 3.02, "end": 3.40, "segmentId": "cold_open_001"},
            ],
        )

        assert report["segments"][0]["status"] == "warn"
        assert report["segments"][0]["matchRatio"] < 0.94

    def test_build_segment_validation_report_uses_token_level_similarity(self, tmp_path):
        output_dir = tmp_path / "outputs" / "tts"
        output_dir.mkdir(parents=True)
        manifest = {
            "segments": [
                {
                    "id": "intro_001",
                    "cleanText": (
                        "When Uplevel tracked almost eight hundred developers across real enterprise "
                        "work for a full year no change in throughput forty one percent more bugs."
                    ),
                },
            ]
        }
        (output_dir / "segments.json").write_text(json.dumps(manifest), encoding="utf-8")

        report = build_segment_validation_report(
            ["intro_001"],
            str(output_dir),
            [
                {"word": "up", "start": 0.0, "end": 0.1, "segmentId": "intro_001"},
                {"word": "level", "start": 0.1, "end": 0.2, "segmentId": "intro_001"},
                {"word": "tracked", "start": 0.2, "end": 0.3, "segmentId": "intro_001"},
                {"word": "almost", "start": 0.3, "end": 0.4, "segmentId": "intro_001"},
                {"word": "800", "start": 0.4, "end": 0.5, "segmentId": "intro_001"},
                {"word": "developers", "start": 0.5, "end": 0.6, "segmentId": "intro_001"},
                {"word": "across", "start": 0.6, "end": 0.7, "segmentId": "intro_001"},
                {"word": "real", "start": 0.7, "end": 0.8, "segmentId": "intro_001"},
                {"word": "enterprise", "start": 0.8, "end": 0.9, "segmentId": "intro_001"},
                {"word": "work", "start": 0.9, "end": 1.0, "segmentId": "intro_001"},
                {"word": "for", "start": 1.0, "end": 1.1, "segmentId": "intro_001"},
                {"word": "a", "start": 1.1, "end": 1.2, "segmentId": "intro_001"},
                {"word": "full", "start": 1.2, "end": 1.3, "segmentId": "intro_001"},
                {"word": "year", "start": 1.3, "end": 1.4, "segmentId": "intro_001"},
                {"word": "no", "start": 1.4, "end": 1.5, "segmentId": "intro_001"},
                {"word": "change", "start": 1.5, "end": 1.6, "segmentId": "intro_001"},
                {"word": "in", "start": 1.6, "end": 1.7, "segmentId": "intro_001"},
                {"word": "throughput", "start": 1.7, "end": 1.8, "segmentId": "intro_001"},
                {"word": "41", "start": 1.8, "end": 1.9, "segmentId": "intro_001"},
                {"word": "percent", "start": 1.9, "end": 2.0, "segmentId": "intro_001"},
                {"word": "more", "start": 2.0, "end": 2.1, "segmentId": "intro_001"},
                {"word": "bugs", "start": 2.1, "end": 2.2, "segmentId": "intro_001"},
            ],
        )

        assert report["segments"][0]["status"] in {"pass", "warn"}
        assert report["segments"][0]["matchRatio"] >= 0.8

    def test_evaluate_validation_gate_allows_warns_when_warn_ratio_is_low(self):
        validation_report = {
            "summary": {
                "passCount": 24,
                "warnCount": 9,
                "failCount": 0,
                "skipCount": 0,
            },
            "segments": [],
        }

        error = evaluate_validation_gate(
            validation_report,
            {
                "maxFailCount": 2,
                "maxFailRatio": 0.15,
                "maxWarnCount": 6,
                "maxWarnRatio": 0.35,
            },
        )

        assert error is None


# ===========================================================================
# Tests: main() CLI and integration
# ===========================================================================

class TestMainCLI:
    """Verify CLI argument parsing and defaults."""

    def test_default_project_dir(self):
        """Spec: --project-dir default is '.'."""
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project", side_effect=FileNotFoundError("test")):
                with pytest.raises(SystemExit):
                    main()

    def test_default_output_dir(self):
        """Spec: --output-dir default is 'outputs/tts/'."""
        # Verified through argparse defaults
        import argparse
        parser = argparse.ArgumentParser()
        # Re-create the parser to check defaults
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {"sectionGroups": {"intro": ["seg_001"]}}
                with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                    mock_proc.return_value = {"sectionId": "intro", "status": "done", "wordCount": 5}
                    with pytest.raises(SystemExit) as exc_info:
                        main()
                    assert exc_info.value.code == 0
                    # Check that process_section was called with default output_dir
                    call_kwargs = mock_proc.call_args[1]
                    assert call_kwargs["output_dir"] == "outputs/tts/"

    def test_default_remotion_public(self):
        """Spec: --remotion-public default is 'remotion/public/'."""
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {"sectionGroups": {"intro": ["seg_001"]}}
                with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                    mock_proc.return_value = {"sectionId": "intro", "status": "done", "wordCount": 5}
                    with pytest.raises(SystemExit) as exc_info:
                        main()
                    assert exc_info.value.code == 0
                    call_kwargs = mock_proc.call_args[1]
                    assert call_kwargs["remotion_public"] == "remotion/public/"

    def test_custom_args(self):
        """Spec: CLI args --project-dir, --output-dir, --remotion-public."""
        with mock.patch("sys.argv", [
            "sync_audio_pipeline.py",
            "--project-dir", "/my/project",
            "--output-dir", "/my/output",
            "--remotion-public", "/my/remotion",
        ]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {"sectionGroups": {"intro": ["seg_001"]}}
                with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                    mock_proc.return_value = {"sectionId": "intro", "status": "done", "wordCount": 5}
                    with pytest.raises(SystemExit) as exc_info:
                        main()
                    assert exc_info.value.code == 0
                    mock_load.assert_called_with("/my/project")
                    call_kwargs = mock_proc.call_args[1]
                    assert call_kwargs["output_dir"] == "/my/output"
                    assert call_kwargs["remotion_public"] == "/my/remotion"


class TestMainExitCodes:
    """Verify exit codes per spec."""

    def test_exit_zero_on_success(self):
        """Spec: Exits with code 0 on complete success."""
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {"sectionGroups": {"intro": ["seg_001"]}}
                with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                    mock_proc.return_value = {"sectionId": "intro", "status": "done", "wordCount": 5}
                    with pytest.raises(SystemExit) as exc_info:
                        main()
                    assert exc_info.value.code == 0

    def test_exit_nonzero_on_failure(self):
        """Spec: Non-zero if any section failed."""
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {"sectionGroups": {"intro": ["seg_001"]}}
                with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                    mock_proc.return_value = {
                        "sectionId": "intro",
                        "status": "error",
                        "error": "something failed",
                    }
                    with pytest.raises(SystemExit) as exc_info:
                        main()
                    assert exc_info.value.code == 1

    def test_exit_zero_on_validation_failures_when_tolerance_enabled(self):
        with mock.patch.dict(os.environ, {"SYNC_AUDIO_ALLOW_VALIDATION_FAILURES": "1"}, clear=False):
            with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
                with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                    mock_load.return_value = {"sectionGroups": {"intro": ["seg_001"]}}
                    with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                        mock_proc.return_value = {
                            "sectionId": "intro",
                            "status": "error",
                            "error": "Transcript validation failed: failCount 3 > 2.",
                        }
                        with pytest.raises(SystemExit) as exc_info:
                            main()
                        assert exc_info.value.code == 0

    def test_exit_nonzero_on_non_validation_failures_even_when_tolerance_enabled(self):
        with mock.patch.dict(os.environ, {"SYNC_AUDIO_ALLOW_VALIDATION_FAILURES": "1"}, clear=False):
            with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
                with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                    mock_load.return_value = {"sectionGroups": {"intro": ["seg_001"]}}
                    with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                        mock_proc.return_value = {
                            "sectionId": "intro",
                            "status": "error",
                            "error": "Failed to concatenate WAV files: boom",
                        }
                        with pytest.raises(SystemExit) as exc_info:
                            main()
                        assert exc_info.value.code == 1

    def test_exit_nonzero_if_any_section_fails(self):
        """Spec: Non-zero if ANY section failed (even if others succeed)."""
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {
                    "sectionGroups": {
                        "intro": ["seg_001"],
                        "section2": ["seg_002"],
                    }
                }
                with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                    mock_proc.side_effect = [
                        {"sectionId": "intro", "status": "done", "wordCount": 5},
                        {"sectionId": "section2", "status": "error", "error": "fail"},
                    ]
                    with pytest.raises(SystemExit) as exc_info:
                        main()
                    assert exc_info.value.code == 1

    def test_exit_nonzero_on_missing_project_json(self):
        """Spec: Prints error and exits non-zero if project.json not found."""
        with mock.patch("sys.argv", ["sync_audio_pipeline.py", "--project-dir", "/nonexistent"]):
            with mock.patch(
                "sync_audio_pipeline.load_project",
                side_effect=FileNotFoundError("project.json not found"),
            ):
                with pytest.raises(SystemExit) as exc_info:
                    main()
                assert exc_info.value.code == 1

    def test_exit_nonzero_on_empty_section_groups(self):
        """Spec: Error if no sections in sectionGroups."""
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {"sectionGroups": {}}
                with pytest.raises(SystemExit) as exc_info:
                    main()
                assert exc_info.value.code == 1

    def test_main_passes_validation_policy_from_audio_sync_config(self):
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {
                    "sectionGroups": {"intro": ["seg_001"]},
                    "audioSync": {
                        "validationMaxFailCount": 2,
                        "validationMaxFailRatio": 0.25,
                        "validationMaxWarnCount": 4,
                    },
                }
                with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                    mock_proc.return_value = {"sectionId": "intro", "status": "done", "wordCount": 5}
                    with pytest.raises(SystemExit) as exc_info:
                        main()
                    assert exc_info.value.code == 0

        call_kwargs = mock_proc.call_args[1]
        assert call_kwargs["validation_policy"] == {
            "maxFailCount": 2,
            "maxFailRatio": 0.25,
            "maxWarnCount": 4,
            "maxWarnRatio": 0.35,
        }

    def test_main_uses_manifest_normalized_section_groups(self):
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {
                    "sectionGroups": {
                        "part3_mold_has_three_parts": ["part3_mold_has_three_parts_001"],
                    }
                }
                with mock.patch("sync_audio_pipeline.load_section_groups") as mock_groups:
                    mock_groups.return_value = {
                        "part3_mold_parts": ["part3_mold_parts_001"],
                    }
                    with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                        mock_proc.return_value = {
                            "sectionId": "part3_mold_parts",
                            "status": "done",
                            "wordCount": 5,
                        }
                        with pytest.raises(SystemExit) as exc_info:
                            main()
                        assert exc_info.value.code == 0

        mock_groups.assert_called_once_with(".", "outputs/tts/")
        assert mock_proc.call_args[1]["section_id"] == "part3_mold_parts"
        assert mock_proc.call_args[1]["segment_ids"] == ["part3_mold_parts_001"]


class TestMainJsonOutput:
    """Verify JSON progress lines printed to stdout."""

    def test_prints_json_done_line(self, capsys):
        """Spec: {"sectionId": "intro", "status": "done", "wordCount": 142}."""
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {"sectionGroups": {"intro": ["seg_001"]}}
                with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                    mock_proc.return_value = {"sectionId": "intro", "status": "done", "wordCount": 42}
                    with pytest.raises(SystemExit):
                        main()

        captured = capsys.readouterr()
        data = json.loads(captured.out.strip())
        assert data["sectionId"] == "intro"
        assert data["status"] == "done"
        assert data["wordCount"] == 42

    def test_prints_json_error_line(self, capsys):
        """Spec: {"sectionId": "intro", "status": "error", "error": "..."}."""
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {"sectionGroups": {"intro": ["seg_001"]}}
                with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                    mock_proc.return_value = {
                        "sectionId": "intro",
                        "status": "error",
                        "error": "No WAV files",
                    }
                    with pytest.raises(SystemExit):
                        main()

        captured = capsys.readouterr()
        data = json.loads(captured.out.strip())
        assert data["sectionId"] == "intro"
        assert data["status"] == "error"
        assert "error" in data
        assert isinstance(data["error"], str)

    def test_prints_one_line_per_section(self, capsys):
        """Spec: Prints JSON progress lines to stdout per section."""
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {
                    "sectionGroups": {
                        "intro": ["seg_001"],
                        "section2": ["seg_002"],
                    }
                }
                with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                    mock_proc.side_effect = [
                        {"sectionId": "intro", "status": "done", "wordCount": 10},
                        {"sectionId": "section2", "status": "done", "wordCount": 20},
                    ]
                    with pytest.raises(SystemExit):
                        main()

        captured = capsys.readouterr()
        lines = [l for l in captured.out.strip().split("\n") if l.strip()]
        assert len(lines) == 2
        for line in lines:
            data = json.loads(line)
            assert "sectionId" in data
            assert "status" in data

    def test_project_load_error_prints_global_json(self, capsys):
        """Spec: Global errors print with sectionId __global__."""
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch(
                "sync_audio_pipeline.load_project",
                side_effect=FileNotFoundError("project.json not found"),
            ):
                with pytest.raises(SystemExit):
                    main()

        captured = capsys.readouterr()
        data = json.loads(captured.out.strip())
        assert data["sectionId"] == "__global__"
        assert data["status"] == "error"

    def test_empty_section_groups_prints_global_error(self, capsys):
        """Spec: Error if sectionGroups is empty."""
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {"sectionGroups": {}}
                with mock.patch("sync_audio_pipeline.load_section_groups") as mock_groups:
                    mock_groups.return_value = {}
                    with pytest.raises(SystemExit):
                        main()

        captured = capsys.readouterr()
        data = json.loads(captured.out.strip())
        assert data["status"] == "error"
        assert "No sections" in data["error"]


# ===========================================================================
# Tests: Import Guard
# ===========================================================================

class TestImportGuard:
    """Spec: Import guard: if __name__ == '__main__': main()."""

    def test_import_guard_exists(self):
        script_path = os.path.join(SCRIPTS_DIR, "sync_audio_pipeline.py")
        with open(script_path, "r") as f:
            content = f.read()
        assert ('if __name__ == "__main__":' in content or
                "if __name__ == '__main__':" in content)


# ===========================================================================
# Tests: Edge Cases
# ===========================================================================

class TestEdgeCases:
    """Edge case tests."""

    def test_section_with_single_segment(self, tmp_project):
        """Single segment section should work correctly."""
        output_dir = str(tmp_project / "outputs" / "tts")
        remotion_public = str(tmp_project / "remotion" / "public")

        mock_model = make_mock_whisper_model([
            {"word": "only", "start": 0.1, "end": 0.4},
        ])

        def fake_concat(segment_paths, output_path):
            _create_dummy_wav(str(output_path))

        with mock.patch("sync_audio_pipeline.concatenate_wavs_ffmpeg", side_effect=fake_concat):
            with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
                with mock.patch("sync_audio_pipeline.get_wav_duration", return_value=1.0):
                    result = process_section("section2", ["seg_003"], output_dir, remotion_public)

        assert result["status"] == "done"
        assert result["wordCount"] == 1

    def test_word_past_all_boundaries_maps_to_last_segment(self, tmp_path):
        """Word beyond all segment boundaries maps to last segment."""
        wav_path = tmp_path / "test.wav"
        _create_dummy_wav(str(wav_path))

        mock_model = make_mock_whisper_model([
            {"word": "late", "start": 10.0, "end": 10.5},
        ])

        with mock.patch("faster_whisper.WhisperModel", return_value=mock_model):
            result = generate_word_timestamps(
                wav_path,
                ["seg_001", "seg_002"],
                [1.5, 2.0],
            )

        # Should default to last segment
        assert result[0]["segmentId"] == "seg_002"

    def test_process_section_with_empty_segment_list(self, tmp_path):
        """Empty segment list should return error (no WAVs found)."""
        output_dir = str(tmp_path / "outputs" / "tts")
        os.makedirs(output_dir, exist_ok=True)
        remotion_public = str(tmp_path / "remotion" / "public")

        result = process_section("intro", [], output_dir, remotion_public)
        assert result["status"] == "error"

    def test_multiple_sections_processed_independently(self, capsys):
        """Each section is processed independently."""
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {
                    "sectionGroups": {
                        "intro": ["seg_001"],
                        "chapter1": ["seg_002"],
                        "outro": ["seg_003"],
                    }
                }
                with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                    mock_proc.side_effect = [
                        {"sectionId": "intro", "status": "done", "wordCount": 10},
                        {"sectionId": "chapter1", "status": "done", "wordCount": 20},
                        {"sectionId": "outro", "status": "done", "wordCount": 5},
                    ]
                    with pytest.raises(SystemExit) as exc_info:
                        main()
                    assert exc_info.value.code == 0

        captured = capsys.readouterr()
        lines = [l for l in captured.out.strip().split("\n") if l.strip()]
        assert len(lines) == 3

    def test_error_section_continues_to_next(self, capsys):
        """Spec: If a section has no segment WAVs, print error and continue."""
        with mock.patch("sys.argv", ["sync_audio_pipeline.py"]):
            with mock.patch("sync_audio_pipeline.load_project") as mock_load:
                mock_load.return_value = {
                    "sectionGroups": {
                        "intro": ["seg_001"],
                        "chapter1": ["seg_002"],
                    }
                }
                with mock.patch("sync_audio_pipeline.process_section") as mock_proc:
                    mock_proc.side_effect = [
                        {"sectionId": "intro", "status": "error", "error": "No WAVs"},
                        {"sectionId": "chapter1", "status": "done", "wordCount": 20},
                    ]
                    with pytest.raises(SystemExit):
                        main()

        captured = capsys.readouterr()
        lines = [l for l in captured.out.strip().split("\n") if l.strip()]
        # Both sections should have output (error continues to next)
        assert len(lines) == 2
        assert json.loads(lines[0])["status"] == "error"
        assert json.loads(lines[1])["status"] == "done"

    def test_uses_argparse(self):
        """Spec: Uses argparse for CLI parsing."""
        script_path = os.path.join(SCRIPTS_DIR, "sync_audio_pipeline.py")
        with open(script_path, "r") as f:
            content = f.read()
        assert "argparse" in content
        assert "ArgumentParser" in content
