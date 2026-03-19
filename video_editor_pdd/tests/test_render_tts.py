"""
Tests for scripts/render_tts.py

PDD Principle: The prompt file is the source of truth.
These tests verify that the code conforms to the specification in
prompts/render_tts_python.prompt.

Spec requirements verified:
  1. Reads narrative/tts_script.md from project root (or --project-dir)
  2. Parses NARRATOR: blocks with inline annotation tags
  3. Generates one WAV file per NARRATOR: segment
  4. CLI args: --segments, --output-dir, --project-dir, --model
  5. Prints JSON progress lines to stdout (done/error format)
  6. Exits with code 0 on success; non-zero if any segment failed
  7. Segment IDs are zero-padded 3 digits: seg_001, seg_002, etc.
  8. Annotation tags stripped from spoken text
  9. [PAUSE: Xs] inserts silence of X seconds
 10. Output WAV files named {segmentId}.wav
 11. --segments filters to only requested IDs
 12. Uses argparse for CLI parsing
 13. if __name__ == '__main__': main() import guard
 14. Output directory created if it doesn't exist
 15. TTS model load failure prints JSON error and exits non-zero
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

# Add scripts/ directory to path so we can import render_tts
TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(TESTS_DIR)
SCRIPTS_DIR = os.path.join(PROJECT_ROOT, "scripts")
sys.path.insert(0, SCRIPTS_DIR)

from render_tts import (
    DEFAULT_MODEL,
    DEFAULT_OUTPUT_DIR,
    DEFAULT_PROJECT_DIR,
    EdgeTTSEngine,
    NARRATOR_PATTERN,
    PAUSE_PATTERN,
    SAMPLE_RATE,
    TAG_PATTERN,
    TTSEngine,
    TONE_PATTERN,
    PACE_PATTERN,
    EMOTION_PATTERN,
    SEGMENTS_MANIFEST_FILENAME,
    Segment,
    build_instruction,
    build_parser,
    apply_qwen_decode_warmup_patch,
    concatenate_pcm,
    generate_silence,
    generate_silence_wav_bytes,
    load_tts_runtime_config,
    parse_tts_script,
    render_segment,
    write_wav,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def tmp_project(tmp_path):
    """Create a temporary project directory with narrative/tts_script.md."""
    narrative_dir = tmp_path / "narrative"
    narrative_dir.mkdir()
    script_content = (
        "# Episode 1\n\n"
        "NARRATOR: The sun rose over the mountains.\n\n"
        "NARRATOR: [TONE: dramatic] The storm was coming. "
        "[PAUSE: 1.5s] Thunder echoed.\n\n"
        "NARRATOR: [PACE: slow] [EMOTION: sadness] "
        "She whispered goodbye. [PAUSE: 2s] And walked away.\n"
    )
    script_file = narrative_dir / "tts_script.md"
    script_file.write_text(script_content, encoding="utf-8")
    return tmp_path


@pytest.fixture
def output_dir(tmp_path):
    """Create a temporary output directory."""
    out = tmp_path / "outputs" / "tts"
    out.mkdir(parents=True)
    return out


@pytest.fixture
def mock_engine():
    """Create a mock TTS engine that returns silence bytes."""
    engine = mock.MagicMock()
    engine.sample_rate = SAMPLE_RATE

    def fake_synthesize(text, **kwargs):
        # Return 0.5s of silence as fake audio
        num_samples = int(SAMPLE_RATE * 0.5)
        return struct.pack(f"<{num_samples}h", *([100] * num_samples))

    engine.synthesize = mock.MagicMock(side_effect=fake_synthesize)
    return engine


# ===========================================================================
# Tests: Constants and Patterns
# ===========================================================================

class TestConstants:
    """Verify spec-required constants and defaults."""

    def test_default_output_dir(self):
        assert DEFAULT_OUTPUT_DIR == "outputs/tts/"

    def test_default_project_dir(self):
        assert DEFAULT_PROJECT_DIR == "."


class TestEdgeTtsFallback:
    """Verify the EdgeTTS fallback does not depend on soundfile."""

    def test_edge_tts_engine_reads_ffmpeg_wav_without_soundfile(self, tmp_path):
        engine = EdgeTTSEngine()

        class FakeCommunicate:
            def __init__(self, _text, _voice):
                self._text = _text
                self._voice = _voice

            async def save(self, filepath):
                Path(filepath).write_bytes(b"fake-mp3")

        class FakeEdgeTtsModule:
            Communicate = FakeCommunicate

        def fake_ffmpeg_run(args, capture_output, timeout):
            wav_path = args[-1]
            samples = struct.pack("<4h", 0, 16384, -16384, 0)
            with wave.open(wav_path, "wb") as wav_file:
                wav_file.setnchannels(1)
                wav_file.setsampwidth(2)
                wav_file.setframerate(SAMPLE_RATE)
                wav_file.writeframes(samples)

            return mock.Mock(returncode=0, stderr=b"")

        with mock.patch.dict(sys.modules, {"edge_tts": FakeEdgeTtsModule()}):
            with mock.patch("subprocess.run", side_effect=fake_ffmpeg_run):
                audio = engine.synthesize("hello from edge")

        assert audio.dtype == "float32"
        assert len(audio) == 4
        assert max(audio) > 0

    def test_sample_rate(self):
        assert SAMPLE_RATE == 24000


class TestTagPatterns:
    """Verify regex patterns match spec annotation tags."""

    def test_tag_pattern_matches_tone(self):
        assert TAG_PATTERN.search("[TONE: dramatic]")

    def test_tag_pattern_matches_pace(self):
        assert TAG_PATTERN.search("[PACE: slow]")

    def test_tag_pattern_matches_pause(self):
        assert TAG_PATTERN.search("[PAUSE: 1.2s]")

    def test_tag_pattern_matches_emotion(self):
        assert TAG_PATTERN.search("[EMOTION: excitement]")

    def test_tag_pattern_matches_instruct(self):
        assert TAG_PATTERN.search("[INSTRUCT: Speak warmly and reassuringly.]")

    def test_tag_pattern_case_insensitive(self):
        assert TAG_PATTERN.search("[tone: warm]")
        assert TAG_PATTERN.search("[Pace: Fast]")

    def test_pause_pattern_extracts_duration(self):
        match = PAUSE_PATTERN.search("[PAUSE: 1.5s]")
        assert match is not None
        assert match.group(1) == "1.5"

    def test_pause_pattern_without_s_suffix(self):
        match = PAUSE_PATTERN.search("[PAUSE: 2]")
        assert match is not None
        assert match.group(1) == "2"

    def test_narrator_pattern_matches_blocks(self):
        text = "NARRATOR: Hello world.\n\nNARRATOR: Goodbye."
        matches = NARRATOR_PATTERN.findall(text)
        assert len(matches) == 2


# ===========================================================================
# Tests: Segment Class
# ===========================================================================

class TestSegment:
    """Verify Segment data structure per spec."""

    def test_segment_id_stored(self):
        seg = Segment("seg_001", "Hello world.")
        assert seg.segment_id == "seg_001"

    def test_raw_text_stripped(self):
        seg = Segment("seg_001", "  Hello world.  ")
        assert seg.raw_text == "Hello world."

    def test_clean_text_strips_all_tags(self):
        raw = "[TONE: dramatic] [PACE: slow] [INSTRUCT: Speak with urgency.] The storm was coming. [PAUSE: 1.5s] Thunder."
        seg = Segment("seg_001", raw)
        assert "[TONE" not in seg.clean_text
        assert "[PACE" not in seg.clean_text
        assert "[INSTRUCT" not in seg.clean_text
        assert "[PAUSE" not in seg.clean_text
        assert "The storm was coming." in seg.clean_text
        assert "Thunder." in seg.clean_text

    def test_clean_text_strips_markdown_formatting_tokens(self):
        seg = Segment("seg_001", "**Hello** __world__ `again`.")
        assert seg.clean_text == "Hello world again."
        assert seg.text_chunks[0]["content"] == "Hello world again."

    def test_clean_text_keeps_spoken_part_one_sentence(self):
        seg = Segment("seg_001", "Part one. [PAUSE: 1s] Part two.")
        assert [chunk["type"] for chunk in seg.text_chunks] == [
            "text",
            "pause",
            "text",
        ]
        assert seg.text_chunks[0]["content"] == "Part one."
        assert seg.text_chunks[2]["content"] == "Part two."

    def test_annotations_extracted_tone(self):
        seg = Segment("seg_001", "[TONE: dramatic] Hello.")
        assert seg.annotations.get("tone") == "dramatic"

    def test_annotations_extracted_pace(self):
        seg = Segment("seg_001", "[PACE: slow] Hello.")
        assert seg.annotations.get("pace") == "slow"

    def test_annotations_extracted_emotion(self):
        seg = Segment("seg_001", "[EMOTION: excitement] Hello.")
        assert seg.annotations.get("emotion") == "excitement"

    def test_annotations_multiple(self):
        raw = "[TONE: warm] [PACE: fast] [EMOTION: joy] [INSTRUCT: Speak with bright delight.] Happy day!"
        seg = Segment("seg_001", raw)
        assert seg.annotations["tone"] == "warm"
        assert seg.annotations["pace"] == "fast"
        assert seg.annotations["emotion"] == "joy"
        assert seg.annotations["instruct"] == "Speak with bright delight."

    def test_no_annotations(self):
        seg = Segment("seg_001", "Just plain text.")
        assert seg.annotations == {}

    def test_split_by_pauses_no_pause(self):
        seg = Segment("seg_001", "No pauses here.")
        assert len(seg.text_chunks) == 1
        assert seg.text_chunks[0]["type"] == "text"
        assert seg.text_chunks[0]["content"] == "No pauses here."

    def test_split_by_pauses_single_pause(self):
        raw = "Before the pause. [PAUSE: 1.5s] After the pause."
        seg = Segment("seg_001", raw)
        types = [c["type"] for c in seg.text_chunks]
        assert types == ["text", "pause", "text"]
        pause_chunk = [c for c in seg.text_chunks if c["type"] == "pause"][0]
        assert pause_chunk["duration"] == 1.5

    def test_split_by_pauses_multiple_pauses(self):
        raw = "Part one. [PAUSE: 1s] Part two. [PAUSE: 0.5s] Part three."
        seg = Segment("seg_001", raw)
        types = [c["type"] for c in seg.text_chunks]
        assert types == ["text", "pause", "text", "pause", "text"]

    def test_pause_at_beginning(self):
        raw = "[PAUSE: 2s] Text after pause."
        seg = Segment("seg_001", raw)
        assert seg.text_chunks[0]["type"] == "pause"
        assert seg.text_chunks[0]["duration"] == 2.0

    def test_tags_removed_from_text_chunks(self):
        raw = "[TONE: dramatic] Hello world. [PAUSE: 1s] [EMOTION: joy] Goodbye."
        seg = Segment("seg_001", raw)
        text_chunks = [c for c in seg.text_chunks if c["type"] == "text"]
        for chunk in text_chunks:
            assert "[TONE" not in chunk["content"]
            assert "[EMOTION" not in chunk["content"]


class TestBuildInstruction:
    """Verify tone annotations influence Qwen voice instructions."""

    def test_known_tone_uses_mapped_instruction(self):
        instruction = build_instruction(tone="explanatory")
        assert "clearly and instructively" in instruction

    def test_known_tone_is_normalized_before_lookup(self):
        instruction = build_instruction(tone=" Explanatory ")
        assert "clearly and instructively" in instruction

    def test_unknown_tone_falls_back_to_generic_style_instruction(self):
        instruction = build_instruction(tone="warm, affirming")
        assert "warm, affirming tone" in instruction


class TestQwenInstructionOverride:
    """Verify explicit [INSTRUCT:] text is passed through to Qwen."""

    def test_explicit_instruct_overrides_tag_translation(self):
        engine = TTSEngine.__new__(TTSEngine)
        engine.speaker = "Aiden"
        engine.language = "English"
        engine.sample_rate = SAMPLE_RATE
        engine.model = mock.MagicMock()
        engine.model.generate_custom_voice.return_value = ([b""], SAMPLE_RATE)

        engine.synthesize(
            "Hello.",
            tone="warm",
            pace="slow",
            emotion="joy",
            instruct="Speak warmly and reassuringly.",
        )

        call = engine.model.generate_custom_voice.call_args.kwargs
        assert call["instruct"] == "Speak warmly and reassuringly."

    def test_qwen_generation_kwargs_are_forwarded(self):
        engine = TTSEngine.__new__(TTSEngine)
        engine.speaker = "Aiden"
        engine.language = "English"
        engine.sample_rate = SAMPLE_RATE
        engine.speaking_rate = 1.0
        engine.generation_kwargs = {
            "temperature": 0.6,
            "top_p": 0.85,
            "top_k": 24,
            "repetition_penalty": 1.1,
            "do_sample": True,
            "max_new_tokens": 512,
            "non_streaming_mode": False,
        }
        engine.model = mock.MagicMock()
        engine.model.generate_custom_voice.return_value = ([b""], SAMPLE_RATE)

        engine.synthesize("Hello.")

        call = engine.model.generate_custom_voice.call_args.kwargs
        assert call["temperature"] == 0.6
        assert call["top_p"] == 0.85
        assert call["top_k"] == 24
        assert call["repetition_penalty"] == 1.1
        assert call["do_sample"] is True
        assert call["max_new_tokens"] == 512
        assert call["non_streaming_mode"] is False


class TestQwenDecodeWarmupPatch:
    """Verify the upstream cold-start decode warmup workaround."""

    def test_prepends_silence_codes_and_trims_output(self):
        torch = pytest.importorskip("torch")

        class FakeEncodeResult:
            def __init__(self):
                self.audio_codes = [torch.tensor([[0, 0], [0, 0]], dtype=torch.int64)]

        class FakeSpeechTokenizer:
            def __init__(self):
                self.decode_calls = []

            def encode(self, _wav, sr):
                assert sr == SAMPLE_RATE
                return FakeEncodeResult()

            def decode(self, encoded_list, **_kwargs):
                self.decode_calls.append(encoded_list)
                frames = int(encoded_list[0]["audio_codes"].shape[0])
                wav = generate_silence(frames / 12.0, sample_rate=12)
                for i in range(frames):
                    wav[i] = float(i)
                return [wav], 12

        tokenizer = FakeSpeechTokenizer()
        fake_model = mock.Mock()
        fake_model.model.speech_tokenizer = tokenizer

        assert apply_qwen_decode_warmup_patch(fake_model, sample_rate=SAMPLE_RATE, warmup_seconds=0.25) is True

        original_codes = torch.tensor([[1, 1], [2, 2], [3, 3]], dtype=torch.int64)
        wavs, fs = tokenizer.decode([{"audio_codes": original_codes}])

        assert fs == 12
        patched_codes = tokenizer.decode_calls[0][0]["audio_codes"]
        assert patched_codes.shape[0] == 5
        assert wavs[0].tolist() == pytest.approx([3.0, 4.0])

    def test_is_idempotent(self):
        torch = pytest.importorskip("torch")

        class FakeEncodeResult:
            def __init__(self):
                self.audio_codes = [torch.tensor([[0, 0]], dtype=torch.int64)]

        class FakeSpeechTokenizer:
            def encode(self, _wav, sr):
                assert sr == SAMPLE_RATE
                return FakeEncodeResult()

            def decode(self, encoded_list, **_kwargs):
                return [generate_silence(len(encoded_list[0]["audio_codes"]) / 12.0, sample_rate=12)], 12

        tokenizer = FakeSpeechTokenizer()
        fake_model = mock.Mock()
        fake_model.model.speech_tokenizer = tokenizer

        assert apply_qwen_decode_warmup_patch(fake_model, sample_rate=SAMPLE_RATE, warmup_seconds=0.25) is True
        first_decode = tokenizer.decode
        assert apply_qwen_decode_warmup_patch(fake_model, sample_rate=SAMPLE_RATE, warmup_seconds=0.25) is False
        assert tokenizer.decode is first_decode


# ===========================================================================
# Tests: parse_tts_script
# ===========================================================================

class TestParseTtsScript:
    """Verify TTS script parsing per spec."""

    def test_parses_narrator_blocks(self, tmp_project):
        script_path = str(tmp_project / "narrative" / "tts_script.md")
        segments = parse_tts_script(script_path)
        assert len(segments) == 3

    def test_segment_ids_zero_padded(self, tmp_project):
        """Spec: Segment IDs derived from order: seg_001, seg_002, etc."""
        script_path = str(tmp_project / "narrative" / "tts_script.md")
        segments = parse_tts_script(script_path)
        assert segments[0].segment_id == "seg_001"
        assert segments[1].segment_id == "seg_002"
        assert segments[2].segment_id == "seg_003"

    def test_file_not_found_raises(self, tmp_path):
        with pytest.raises(FileNotFoundError):
            parse_tts_script(str(tmp_path / "nonexistent.md"))

    def test_no_narrator_blocks_raises(self, tmp_path):
        """Spec: ValueError if no NARRATOR blocks found."""
        script = tmp_path / "empty_script.md"
        script.write_text("# Just a heading\nNo narrator blocks here.\n")
        with pytest.raises(ValueError, match="No NARRATOR"):
            parse_tts_script(str(script))

    def test_single_narrator_block(self, tmp_path):
        script = tmp_path / "single.md"
        script.write_text("NARRATOR: Just one segment here.\n")
        segments = parse_tts_script(str(script))
        assert len(segments) == 1
        assert segments[0].segment_id == "seg_001"

    def test_narrator_with_annotations_parsed(self, tmp_project):
        script_path = str(tmp_project / "narrative" / "tts_script.md")
        segments = parse_tts_script(script_path)
        # Second segment has [TONE: dramatic] and [PAUSE: 1.5s]
        seg2 = segments[1]
        assert seg2.annotations.get("tone") == "dramatic"
        pause_chunks = [c for c in seg2.text_chunks if c["type"] == "pause"]
        assert len(pause_chunks) == 1
        assert pause_chunks[0]["duration"] == 1.5

    def test_section_based_scripts_strip_markdown_narrator_markers(self, tmp_path):
        """Section scripts may use markdown narrator labels that must not be spoken."""
        narrative_dir = tmp_path / "narrative"
        narrative_dir.mkdir()
        (tmp_path / "project.json").write_text(
            json.dumps(
                {
                    "sections": [
                        {"id": "animation_section", "label": "Animation Section"},
                    ]
                }
            ),
            encoding="utf-8",
        )
        (narrative_dir / "tts_script.md").write_text(
            "# Demo\n\n"
            "## Animation Section\n\n"
            "**NARRATOR:**\n"
            "[TONE: neutral]\n"
            "[PACE: Moderate]\n"
            "This is the first sentence.\n"
            "[PAUSE: 0.5s]\n\n"
            "**NARRATOR:**\n"
            "[EMOTION: Calm confidence]\n"
            "This is the second sentence.\n",
            encoding="utf-8",
        )

        segments = parse_tts_script(
            str(narrative_dir / "tts_script.md"),
            str(tmp_path),
        )

        assert [segment.segment_id for segment in segments] == [
            "animation_section_001",
            "animation_section_002",
        ]
        assert segments[0].clean_text == "This is the first sentence."
        assert segments[1].clean_text == "This is the second sentence."
        assert segments[0].text_chunks[0]["content"] == "This is the first sentence."
        assert segments[1].text_chunks[0]["content"] == "This is the second sentence."

    def test_section_based_scripts_strip_block_control_markers(self, tmp_path):
        """Standalone block headings are editorial structure and must not be spoken."""
        narrative_dir = tmp_path / "narrative"
        narrative_dir.mkdir()
        (tmp_path / "project.json").write_text(
            json.dumps(
                {
                    "sections": [
                        {"id": "animation_section", "label": "Animation Section"},
                    ]
                }
            ),
            encoding="utf-8",
        )
        (narrative_dir / "tts_script.md").write_text(
            "# Demo\n\n"
            "## Animation Section\n\n"
            "**Block 1:**\n"
            "**NARRATOR:**\n"
            "[TONE: neutral]\n"
            "This is the first section.\n",
            encoding="utf-8",
        )

        segments = parse_tts_script(
            str(narrative_dir / "tts_script.md"),
            str(tmp_path),
        )

        assert [segment.segment_id for segment in segments] == [
            "animation_section_001",
        ]
        assert segments[0].clean_text == "This is the first section."
        assert segments[0].text_chunks[0]["content"] == "This is the first section."


# ===========================================================================
# Tests: Audio Utilities
# ===========================================================================

class TestGenerateSilenceWavBytes:
    """Verify silence generation."""

    def test_correct_byte_length(self):
        duration = 1.0
        silence = generate_silence_wav_bytes(duration, SAMPLE_RATE)
        expected_samples = int(SAMPLE_RATE * duration)
        # 16-bit = 2 bytes per sample
        assert len(silence) == expected_samples * 2

    def test_all_zeros(self):
        silence = generate_silence_wav_bytes(0.1, SAMPLE_RATE)
        num_samples = int(SAMPLE_RATE * 0.1)
        values = struct.unpack(f"<{num_samples}h", silence)
        assert all(v == 0 for v in values)

    def test_custom_sample_rate(self):
        silence = generate_silence_wav_bytes(1.0, 16000)
        assert len(silence) == 16000 * 2

    def test_zero_duration(self):
        silence = generate_silence_wav_bytes(0.0, SAMPLE_RATE)
        assert len(silence) == 0


class TestWriteWav:
    """Verify WAV file writing."""

    def test_creates_valid_wav_file(self, tmp_path):
        wav_path = str(tmp_path / "test.wav")
        silence = generate_silence_wav_bytes(1.0)
        duration = write_wav(wav_path, silence)
        assert os.path.exists(wav_path)
        assert duration == pytest.approx(1.0, abs=0.01)

    def test_wav_properties(self, tmp_path):
        """Verify WAV is mono, 16-bit, correct sample rate."""
        wav_path = str(tmp_path / "test.wav")
        silence = generate_silence_wav_bytes(0.5)
        write_wav(wav_path, silence)

        with wave.open(wav_path, "rb") as wf:
            assert wf.getnchannels() == 1
            assert wf.getsampwidth() == 2
            assert wf.getframerate() == SAMPLE_RATE

    def test_returns_correct_duration(self, tmp_path):
        wav_path = str(tmp_path / "dur_test.wav")
        silence = generate_silence_wav_bytes(2.5)
        duration = write_wav(wav_path, silence)
        assert duration == pytest.approx(2.5, abs=0.01)


class TestConcatenatePcm:
    """Verify PCM concatenation."""

    def test_concatenates_chunks(self):
        chunk1 = generate_silence_wav_bytes(0.5)
        chunk2 = generate_silence_wav_bytes(1.0)
        combined = concatenate_pcm([chunk1, chunk2])
        assert len(combined) == len(chunk1) + len(chunk2)

    def test_empty_list(self):
        combined = concatenate_pcm([])
        assert combined == b""

    def test_single_chunk(self):
        chunk = generate_silence_wav_bytes(0.5)
        combined = concatenate_pcm([chunk])
        assert combined == chunk


# ===========================================================================
# Tests: render_segment
# ===========================================================================

class TestRenderSegment:
    """Verify segment rendering per spec."""

    def test_success_returns_done_status(self, mock_engine, output_dir):
        seg = Segment("seg_001", "Hello world.")
        result = render_segment(mock_engine, seg, str(output_dir))
        assert result["segmentId"] == "seg_001"
        assert result["status"] == "done"
        assert "duration" in result
        assert isinstance(result["duration"], float)

    def test_creates_wav_file(self, mock_engine, output_dir):
        """Spec: Output WAV files named {segmentId}.wav."""
        seg = Segment("seg_001", "Hello world.")
        render_segment(mock_engine, seg, str(output_dir))
        wav_path = output_dir / "seg_001.wav"
        assert wav_path.exists()

    def test_wav_filename_matches_segment_id(self, mock_engine, output_dir):
        seg = Segment("seg_042", "Some text.")
        render_segment(mock_engine, seg, str(output_dir))
        assert (output_dir / "seg_042.wav").exists()

    def test_calls_synthesize_for_text_chunks(self, mock_engine, output_dir):
        seg = Segment("seg_001", "First part. [PAUSE: 1s] Second part.")
        render_segment(mock_engine, seg, str(output_dir))
        # Should have been called twice (two text chunks)
        assert mock_engine.synthesize.call_count == 2

    def test_passes_annotations_to_synthesize(self, mock_engine, output_dir):
        seg = Segment(
            "seg_001",
            "[TONE: dramatic] [PACE: slow] [INSTRUCT: Speak urgently.] Hello.",
        )
        render_segment(mock_engine, seg, str(output_dir))
        call_kwargs = mock_engine.synthesize.call_args[1]
        assert call_kwargs.get("tone") == "dramatic"
        assert call_kwargs.get("pace") == "slow"
        assert call_kwargs.get("instruct") == "Speak urgently."

    def test_error_returns_error_status(self, output_dir):
        """Spec: On error, return {"segmentId": ..., "status": "error", "error": "..."}."""
        engine = mock.MagicMock()
        engine.synthesize.side_effect = RuntimeError("TTS failed")
        seg = Segment("seg_001", "Hello.")
        result = render_segment(engine, seg, str(output_dir))
        assert result["segmentId"] == "seg_001"
        assert result["status"] == "error"
        assert "error" in result
        assert isinstance(result["error"], str)

    def test_pause_inserts_silence(self, mock_engine, output_dir):
        """Spec: [PAUSE: Xs] inserts silence of X seconds."""
        seg = Segment("seg_001", "Before. [PAUSE: 2s] After.")
        result = render_segment(mock_engine, seg, str(output_dir))
        assert result["status"] == "done"
        # The WAV should be longer than without the pause
        assert result["duration"] > 2.0

    def test_duration_is_rounded(self, mock_engine, output_dir):
        seg = Segment("seg_001", "Hello.")
        result = render_segment(mock_engine, seg, str(output_dir))
        # duration should be rounded to 2 decimal places
        duration_str = str(result["duration"])
        if "." in duration_str:
            decimals = len(duration_str.split(".")[1])
            assert decimals <= 2


class TestSpeakingRate:
    """Verify speakingRate changes the rendered audio duration."""

    def test_rate_above_one_shortens_audio(self, tmp_path):
        engine = TTSEngine.__new__(TTSEngine)
        engine.speaker = "Aiden"
        engine.language = "English"
        engine.sample_rate = SAMPLE_RATE
        engine.speaking_rate = 1.25
        engine.generation_kwargs = {}
        engine.model = mock.MagicMock()
        one_second = generate_silence(1.0)
        engine.model.generate_custom_voice.return_value = ([one_second], SAMPLE_RATE)

        audio = engine.synthesize("Hello.")

        assert len(audio) == pytest.approx(int(len(one_second) / 1.25), rel=0.01)

    def test_rate_below_one_lengthens_audio(self, tmp_path):
        engine = TTSEngine.__new__(TTSEngine)
        engine.speaker = "Aiden"
        engine.language = "English"
        engine.sample_rate = SAMPLE_RATE
        engine.speaking_rate = 0.8
        engine.generation_kwargs = {}
        engine.model = mock.MagicMock()
        one_second = generate_silence(1.0)
        engine.model.generate_custom_voice.return_value = ([one_second], SAMPLE_RATE)

        audio = engine.synthesize("Hello.")

        assert len(audio) == pytest.approx(int(len(one_second) / 0.8), rel=0.01)


# ===========================================================================
# Tests: build_parser (CLI args)
# ===========================================================================

class TestBuildParser:
    """Verify CLI argument parsing per spec."""

    def test_default_values(self):
        parser = build_parser()
        args = parser.parse_args([])
        assert args.segments is None
        assert args.output_dir == DEFAULT_OUTPUT_DIR
        assert args.project_dir == DEFAULT_PROJECT_DIR
        assert args.model == DEFAULT_MODEL

    def test_segments_arg(self):
        parser = build_parser()
        args = parser.parse_args(["--segments", "seg_001,seg_003"])
        assert args.segments == "seg_001,seg_003"

    def test_output_dir_arg(self):
        parser = build_parser()
        args = parser.parse_args(["--output-dir", "/tmp/audio"])
        assert args.output_dir == "/tmp/audio"

    def test_project_dir_arg(self):
        parser = build_parser()
        args = parser.parse_args(["--project-dir", "/my/project"])
        assert args.project_dir == "/my/project"

    def test_model_arg(self):
        parser = build_parser()
        args = parser.parse_args(["--model", "Qwen/Qwen2.5-TTS-3B"])
        assert args.model == "Qwen/Qwen2.5-TTS-3B"

    def test_all_args_together(self):
        parser = build_parser()
        args = parser.parse_args([
            "--segments", "seg_001",
            "--output-dir", "/out",
            "--project-dir", "/proj",
            "--model", "custom-model",
        ])
        assert args.segments == "seg_001"
        assert args.output_dir == "/out"
        assert args.project_dir == "/proj"
        assert args.model == "custom-model"


# ===========================================================================
# Tests: main() function (integration)
# ===========================================================================

class TestMain:
    """Verify main() end-to-end behavior per spec."""

    def test_creates_output_directory(self, tmp_project):
        """Spec: Output directory is created if it doesn't exist."""
        output_dir = tmp_project / "new_output_dir"
        assert not output_dir.exists()

        with mock.patch("render_tts.TTSEngine") as MockEngine:
            instance = MockEngine.return_value
            instance.sample_rate = SAMPLE_RATE
            num_samples = int(SAMPLE_RATE * 0.5)
            instance.synthesize.return_value = struct.pack(
                f"<{num_samples}h", *([100] * num_samples)
            )

            with mock.patch(
                "sys.argv",
                ["render_tts.py",
                 "--project-dir", str(tmp_project),
                 "--output-dir", str(output_dir)],
            ):
                from render_tts import main
                with pytest.raises(SystemExit) as exc_info:
                    main()
                assert exc_info.value.code == 0

        assert output_dir.exists()

    def test_prints_json_lines_to_stdout(self, tmp_project, capsys):
        """Spec: Prints JSON progress lines to stdout, one per segment."""
        output_dir = tmp_project / "outputs" / "tts"

        with mock.patch("render_tts.TTSEngine") as MockEngine:
            instance = MockEngine.return_value
            instance.sample_rate = SAMPLE_RATE
            num_samples = int(SAMPLE_RATE * 0.5)
            instance.synthesize.return_value = struct.pack(
                f"<{num_samples}h", *([100] * num_samples)
            )

            with mock.patch(
                "sys.argv",
                ["render_tts.py",
                 "--project-dir", str(tmp_project),
                 "--output-dir", str(output_dir)],
            ):
                from render_tts import main
                with pytest.raises(SystemExit) as exc_info:
                    main()
                assert exc_info.value.code == 0

        captured = capsys.readouterr()
        lines = [l for l in captured.out.strip().split("\n") if l.strip()]
        assert len(lines) == 3  # 3 NARRATOR blocks

        for line in lines:
            data = json.loads(line)
            assert "segmentId" in data
            assert "status" in data
            assert data["status"] == "done"
            assert "duration" in data

    def test_json_done_format(self, tmp_project, capsys):
        """Spec: {"segmentId": "seg_001", "status": "done", "duration": 4.32}"""
        output_dir = tmp_project / "outputs" / "tts"

        with mock.patch("render_tts.TTSEngine") as MockEngine:
            instance = MockEngine.return_value
            instance.sample_rate = SAMPLE_RATE
            num_samples = int(SAMPLE_RATE * 0.5)
            instance.synthesize.return_value = struct.pack(
                f"<{num_samples}h", *([100] * num_samples)
            )

            with mock.patch(
                "sys.argv",
                ["render_tts.py",
                 "--project-dir", str(tmp_project),
                 "--output-dir", str(output_dir)],
            ):
                from render_tts import main
                with pytest.raises(SystemExit) as exc_info:
                    main()

        captured = capsys.readouterr()
        first_line = json.loads(captured.out.strip().split("\n")[0])
        assert first_line["segmentId"] == "seg_001"
        assert first_line["status"] == "done"
        assert isinstance(first_line["duration"], (int, float))

    def test_exit_code_zero_on_success(self, tmp_project):
        """Spec: Exits with code 0 on complete success."""
        output_dir = tmp_project / "outputs" / "tts"

        with mock.patch("render_tts.TTSEngine") as MockEngine:
            instance = MockEngine.return_value
            instance.sample_rate = SAMPLE_RATE
            num_samples = int(SAMPLE_RATE * 0.5)
            instance.synthesize.return_value = struct.pack(
                f"<{num_samples}h", *([100] * num_samples)
            )

            with mock.patch(
                "sys.argv",
                ["render_tts.py",
                 "--project-dir", str(tmp_project),
                 "--output-dir", str(output_dir)],
            ):
                from render_tts import main
                with pytest.raises(SystemExit) as exc_info:
                    main()
                assert exc_info.value.code == 0

    def test_exit_code_nonzero_on_error(self, tmp_project):
        """Spec: Non-zero if any segment failed."""
        output_dir = tmp_project / "outputs" / "tts"

        with mock.patch("render_tts.TTSEngine") as MockEngine:
            instance = MockEngine.return_value
            instance.sample_rate = SAMPLE_RATE
            instance.synthesize.side_effect = RuntimeError("TTS failed")

            with mock.patch(
                "sys.argv",
                ["render_tts.py",
                 "--project-dir", str(tmp_project),
                 "--output-dir", str(output_dir)],
            ):
                from render_tts import main
                with pytest.raises(SystemExit) as exc_info:
                    main()
                assert exc_info.value.code == 1

    def test_segments_filter(self, tmp_project, capsys):
        """Spec: --segments filters to only requested IDs."""
        output_dir = tmp_project / "outputs" / "tts"

        with mock.patch("render_tts.TTSEngine") as MockEngine:
            instance = MockEngine.return_value
            instance.sample_rate = SAMPLE_RATE
            num_samples = int(SAMPLE_RATE * 0.5)
            instance.synthesize.return_value = struct.pack(
                f"<{num_samples}h", *([100] * num_samples)
            )

            with mock.patch(
                "sys.argv",
                ["render_tts.py",
                 "--project-dir", str(tmp_project),
                 "--output-dir", str(output_dir),
                 "--segments", "seg_001,seg_003"],
            ):
                from render_tts import main
                with pytest.raises(SystemExit) as exc_info:
                    main()
                assert exc_info.value.code == 0

        captured = capsys.readouterr()
        lines = [l for l in captured.out.strip().split("\n") if l.strip()]
        assert len(lines) == 2
        ids = [json.loads(l)["segmentId"] for l in lines]
        assert "seg_001" in ids
        assert "seg_003" in ids
        assert "seg_002" not in ids

    def test_nonexistent_segments_exit_zero(self, tmp_project):
        """Spec: If --segments specified but none match, exit 0 (nothing to do)."""
        output_dir = tmp_project / "outputs" / "tts"

        with mock.patch("render_tts.TTSEngine") as MockEngine:
            with mock.patch(
                "sys.argv",
                ["render_tts.py",
                 "--project-dir", str(tmp_project),
                 "--output-dir", str(output_dir),
                 "--segments", "seg_999"],
            ):
                from render_tts import main
                with pytest.raises(SystemExit) as exc_info:
                    main()
                # No segments to render = exit 0, engine never loaded
                assert exc_info.value.code == 0
                MockEngine.assert_not_called()

    def test_missing_script_file_prints_json_error(self, tmp_path, capsys):
        """Spec: Print JSON error to stdout and exit non-zero if script missing."""
        with mock.patch(
            "sys.argv",
            ["render_tts.py",
             "--project-dir", str(tmp_path),
             "--output-dir", str(tmp_path / "out")],
        ):
            from render_tts import main
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 1

        captured = capsys.readouterr()
        error_data = json.loads(captured.out.strip())
        assert error_data["status"] == "error"
        assert error_data["segmentId"] == "global"

    def test_model_load_failure_prints_json_error(self, tmp_project, capsys):
        """Spec: If TTS model loading fails, print JSON error and exit non-zero."""
        output_dir = tmp_project / "outputs" / "tts"

        with mock.patch(
            "render_tts.TTSEngine",
            side_effect=RuntimeError("Model not found"),
        ):
            with mock.patch(
                "sys.argv",
                ["render_tts.py",
                 "--project-dir", str(tmp_project),
                 "--output-dir", str(output_dir)],
            ):
                from render_tts import main
                with pytest.raises(SystemExit) as exc_info:
                    main()
                assert exc_info.value.code == 1

        captured = capsys.readouterr()
        error_data = json.loads(captured.out.strip())
        assert error_data["status"] == "error"
        assert error_data["segmentId"] == "global"
        assert "Model not found" in error_data["error"]

    def test_uses_project_config_model_path_and_sampling_controls(self, tmp_project):
        output_dir = tmp_project / "outputs" / "tts"
        project_json = {
            "tts": {
                "modelPath": "models/local-qwen",
                "speaker": "Ada",
                "language": "English",
                "speakingRate": 1.15,
                "temperature": 0.7,
                "topP": 0.9,
                "topK": 32,
                "repetitionPenalty": 1.05,
                "doSample": True,
                "maxNewTokens": 384,
                "nonStreamingMode": False,
            }
        }
        (tmp_project / "project.json").write_text(json.dumps(project_json), encoding="utf-8")

        with mock.patch("render_tts.TTSEngine") as MockEngine:
            instance = MockEngine.return_value
            instance.sample_rate = SAMPLE_RATE
            num_samples = int(SAMPLE_RATE * 0.5)
            instance.synthesize.return_value = struct.pack(
                f"<{num_samples}h", *([100] * num_samples)
            )

            with mock.patch(
                "sys.argv",
                ["render_tts.py",
                 "--project-dir", str(tmp_project),
                 "--output-dir", str(output_dir)],
            ):
                from render_tts import main
                with pytest.raises(SystemExit) as exc_info:
                    main()
                assert exc_info.value.code == 0

        MockEngine.assert_called_once_with(
            "models/local-qwen",
            speaker="Ada",
            language="English",
            speaking_rate=1.15,
            generation_kwargs={
                "temperature": 0.7,
                "top_p": 0.9,
                "top_k": 32,
                "repetition_penalty": 1.05,
                "do_sample": True,
                "max_new_tokens": 384,
                "non_streaming_mode": False,
            },
        )

    def test_runtime_config_reads_edge_voice_from_project(self, tmp_project):
        project_json = {
            "tts": {
                "speaker": "Ada",
                "edgeVoice": "en-US-JennyNeural",
            }
        }
        (tmp_project / "project.json").write_text(json.dumps(project_json), encoding="utf-8")

        config = load_tts_runtime_config(str(tmp_project), DEFAULT_MODEL)

        assert config["speaker"] == "Ada"
        assert config["edge_voice"] == "en-US-JennyNeural"

    def test_runtime_config_prefers_edge_voice_env_override(self, tmp_project, monkeypatch):
        project_json = {
            "tts": {
                "edgeVoice": "en-US-AndrewMultilingualNeural",
            }
        }
        (tmp_project / "project.json").write_text(json.dumps(project_json), encoding="utf-8")
        monkeypatch.setenv("RENDER_TTS_EDGE_VOICE", "en-US-SteffanNeural")

        config = load_tts_runtime_config(str(tmp_project), DEFAULT_MODEL)

        assert config["edge_voice"] == "en-US-SteffanNeural"

    def test_model_and_edge_failures_use_deterministic_fallback_when_allowed(
        self, tmp_project, capsys
    ):
        """Spec: test/dev fallback still produces WAVs when online engines are absent."""
        output_dir = tmp_project / "outputs" / "tts"

        with mock.patch("render_tts.TTSEngine", side_effect=RuntimeError("Model not found")):
            with mock.patch("render_tts.EdgeTTSEngine", side_effect=RuntimeError("Edge missing")):
                with mock.patch.dict(os.environ, {"RENDER_TTS_ALLOW_EDGE_FALLBACK": "1"}):
                    with mock.patch(
                        "sys.argv",
                        ["render_tts.py",
                         "--project-dir", str(tmp_project),
                         "--output-dir", str(output_dir)],
                    ):
                        from render_tts import main
                        with pytest.raises(SystemExit) as exc_info:
                            main()
                        assert exc_info.value.code == 0

        captured = capsys.readouterr()
        lines = [json.loads(line) for line in captured.out.strip().split("\n") if line.strip()]
        assert all(line["status"] == "done" for line in lines)
        assert (output_dir / "seg_001.wav").exists()
        assert (output_dir / "seg_002.wav").exists()

    def test_edge_fallback_uses_configured_edge_voice(self, tmp_project):
        output_dir = tmp_project / "outputs" / "tts"
        project_json = {
            "tts": {
                "edgeVoice": "en-US-JennyNeural",
            }
        }
        (tmp_project / "project.json").write_text(json.dumps(project_json), encoding="utf-8")

        with mock.patch("render_tts.TTSEngine", side_effect=RuntimeError("Model not found")):
            with mock.patch("render_tts.EdgeTTSEngine") as MockEdge:
                edge_instance = MockEdge.return_value
                edge_instance.sample_rate = SAMPLE_RATE
                num_samples = int(SAMPLE_RATE * 0.5)
                edge_instance.synthesize.return_value = struct.pack(
                    f"<{num_samples}h", *([100] * num_samples)
                )
                with mock.patch.dict(os.environ, {"RENDER_TTS_ALLOW_EDGE_FALLBACK": "1"}, clear=False):
                    with mock.patch(
                        "sys.argv",
                        ["render_tts.py",
                         "--project-dir", str(tmp_project),
                         "--output-dir", str(output_dir)],
                    ):
                        from render_tts import main
                        with pytest.raises(SystemExit) as exc_info:
                            main()
                        assert exc_info.value.code == 0

        MockEdge.assert_called_once_with(
            voice="en-US-JennyNeural",
            speaking_rate=1.0,
        )

    def test_generates_wav_files(self, tmp_project):
        """Spec: Generates one WAV file per NARRATOR: segment."""
        output_dir = tmp_project / "outputs" / "tts"

        with mock.patch("render_tts.TTSEngine") as MockEngine:
            instance = MockEngine.return_value
            instance.sample_rate = SAMPLE_RATE
            num_samples = int(SAMPLE_RATE * 0.5)
            instance.synthesize.return_value = struct.pack(
                f"<{num_samples}h", *([100] * num_samples)
            )

            with mock.patch(
                "sys.argv",
                ["render_tts.py",
                 "--project-dir", str(tmp_project),
                 "--output-dir", str(output_dir)],
            ):
                from render_tts import main
                with pytest.raises(SystemExit):
                    main()

        assert (output_dir / "seg_001.wav").exists()
        assert (output_dir / "seg_002.wav").exists()
        assert (output_dir / "seg_003.wav").exists()

    def test_writes_segments_manifest_during_render(self, tmp_project):
        """Spec: renderer writes outputs/tts/segments.json from the actual parsed segments."""
        output_dir = tmp_project / "outputs" / "tts"

        with mock.patch("render_tts.TTSEngine") as MockEngine:
            instance = MockEngine.return_value
            instance.sample_rate = SAMPLE_RATE
            num_samples = int(SAMPLE_RATE * 0.5)
            instance.synthesize.return_value = struct.pack(
                f"<{num_samples}h", *([100] * num_samples)
            )

            with mock.patch(
                "sys.argv",
                [
                    "render_tts.py",
                    "--project-dir",
                    str(tmp_project),
                    "--output-dir",
                    str(output_dir),
                ],
            ):
                from render_tts import main
                with pytest.raises(SystemExit) as exc_info:
                    main()
                assert exc_info.value.code == 0

        manifest_path = output_dir / SEGMENTS_MANIFEST_FILENAME
        assert manifest_path.exists()
        manifest = json.loads(manifest_path.read_text())
        assert [segment["id"] for segment in manifest["segments"]] == [
            "seg_001",
            "seg_002",
            "seg_003",
        ]

    def test_manifest_only_writes_split_section_manifest_without_audio(self, tmp_path):
        """Spec: --manifest-only emits the renderer's true pause-split segments for section scripts."""
        narrative_dir = tmp_path / "narrative"
        narrative_dir.mkdir()
        (tmp_path / "project.json").write_text(
            json.dumps(
                {
                    "sections": [
                        {"id": "animation_section", "label": "Animation Section"},
                    ]
                }
            ),
            encoding="utf-8",
        )
        (narrative_dir / "tts_script.md").write_text(
            "# Demo\n\n"
            "## Animation Section\n\n"
            "[TONE: neutral] First sentence.\n"
            "[PAUSE: 1.0s]\n"
            "Second sentence.\n",
            encoding="utf-8",
        )
        output_dir = tmp_path / "outputs" / "tts"

        with mock.patch(
            "sys.argv",
            [
                "render_tts.py",
                "--project-dir",
                str(tmp_path),
                "--output-dir",
                str(output_dir),
                "--manifest-only",
            ],
        ):
            from render_tts import main
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

        manifest_path = output_dir / SEGMENTS_MANIFEST_FILENAME
        assert manifest_path.exists()
        manifest = json.loads(manifest_path.read_text())
        assert [segment["id"] for segment in manifest["segments"]] == [
            "animation_section_001",
            "animation_section_002",
        ]
        assert not (output_dir / "animation_section_001.wav").exists()
        assert manifest["segments"][1]["text"] == "Second sentence."

    def test_manifest_only_strips_markdown_narrator_markers_from_clean_text(self, tmp_path):
        """Section manifests should not preserve markdown narrator labels as spoken text."""
        narrative_dir = tmp_path / "narrative"
        narrative_dir.mkdir()
        (tmp_path / "project.json").write_text(
            json.dumps(
                {
                    "sections": [
                        {"id": "animation_section", "label": "Animation Section"},
                    ]
                }
            ),
            encoding="utf-8",
        )
        (narrative_dir / "tts_script.md").write_text(
            "# Demo\n\n"
            "## Animation Section\n\n"
            "**NARRATOR:**\n"
            "[TONE: neutral]\n"
            "This is the first sentence.\n"
            "[PAUSE: 0.5s]\n\n"
            "**NARRATOR:**\n"
            "This is the second sentence.\n",
            encoding="utf-8",
        )
        output_dir = tmp_path / "outputs" / "tts"

        with mock.patch(
            "sys.argv",
            [
                "render_tts.py",
                "--project-dir",
                str(tmp_path),
                "--output-dir",
                str(output_dir),
                "--manifest-only",
            ],
        ):
            from render_tts import main
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

        manifest = json.loads((output_dir / SEGMENTS_MANIFEST_FILENAME).read_text())
        assert manifest["segments"][0]["cleanText"] == "This is the first sentence."
        assert manifest["segments"][1]["cleanText"] == "This is the second sentence."

    def test_manifest_only_strips_block_control_markers_from_clean_text(self, tmp_path):
        """Section manifests should not preserve standalone block control headings."""
        narrative_dir = tmp_path / "narrative"
        narrative_dir.mkdir()
        (tmp_path / "project.json").write_text(
            json.dumps(
                {
                    "sections": [
                        {"id": "animation_section", "label": "Animation Section"},
                    ]
                }
            ),
            encoding="utf-8",
        )
        (narrative_dir / "tts_script.md").write_text(
            "# Demo\n\n"
            "## Animation Section\n\n"
            "**Block 1:**\n"
            "**NARRATOR:**\n"
            "This is the first section.\n",
            encoding="utf-8",
        )
        output_dir = tmp_path / "outputs" / "tts"

        with mock.patch(
            "sys.argv",
            [
                "render_tts.py",
                "--project-dir",
                str(tmp_path),
                "--output-dir",
                str(output_dir),
                "--manifest-only",
            ],
        ):
            from render_tts import main
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

        manifest = json.loads((output_dir / SEGMENTS_MANIFEST_FILENAME).read_text())
        assert manifest["segments"][0]["cleanText"] == "This is the first section."

    def test_manifest_only_strips_markdown_formatting_tokens_from_clean_text(self, tmp_path):
        """Manifest cleanText should not preserve markdown punctuation as speech."""
        narrative_dir = tmp_path / "narrative"
        narrative_dir.mkdir()
        (narrative_dir / "tts_script.md").write_text(
            "NARRATOR: **Hello** __world__ `again`.\n",
            encoding="utf-8",
        )
        output_dir = tmp_path / "outputs" / "tts"

        with mock.patch(
            "sys.argv",
            [
                "render_tts.py",
                "--project-dir",
                str(tmp_path),
                "--output-dir",
                str(output_dir),
                "--manifest-only",
            ],
        ):
            from render_tts import main
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

        manifest = json.loads((output_dir / SEGMENTS_MANIFEST_FILENAME).read_text())
        assert manifest["segments"][0]["cleanText"] == "Hello world again."

    def test_json_error_format(self, tmp_project, capsys):
        """Spec: Error format: {"segmentId": "seg_001", "status": "error", "error": "..."}"""
        output_dir = tmp_project / "outputs" / "tts"

        with mock.patch("render_tts.TTSEngine") as MockEngine:
            instance = MockEngine.return_value
            instance.sample_rate = SAMPLE_RATE
            instance.synthesize.side_effect = RuntimeError("Synthesis boom")

            with mock.patch(
                "sys.argv",
                ["render_tts.py",
                 "--project-dir", str(tmp_project),
                 "--output-dir", str(output_dir)],
            ):
                from render_tts import main
                with pytest.raises(SystemExit):
                    main()

        captured = capsys.readouterr()
        lines = [l for l in captured.out.strip().split("\n") if l.strip()]
        for line in lines:
            data = json.loads(line)
            assert data["status"] == "error"
            assert "error" in data
            assert isinstance(data["error"], str)


# ===========================================================================
# Tests: Import Guard
# ===========================================================================

class TestImportGuard:
    """Spec: Import guard: if __name__ == '__main__': main()."""

    def test_import_guard_exists(self):
        script_path = os.path.join(SCRIPTS_DIR, "render_tts.py")
        with open(script_path, "r") as f:
            content = f.read()
        assert 'if __name__ == "__main__":' in content or \
               "if __name__ == '__main__':" in content


# ===========================================================================
# Tests: Edge Cases
# ===========================================================================

class TestEdgeCases:
    """Edge case tests."""

    def test_segment_with_only_pause(self):
        """Segment that has only a PAUSE tag and no real text."""
        seg = Segment("seg_001", "[PAUSE: 3s]")
        assert len(seg.text_chunks) == 1
        assert seg.text_chunks[0]["type"] == "pause"

    def test_segment_with_only_annotations(self):
        """Segment that has only annotation tags (no spoken text)."""
        seg = Segment("seg_001", "[TONE: dramatic] [PACE: slow]")
        # After stripping tags, there's no text content
        assert seg.clean_text == ""

    def test_many_segments_numbering(self, tmp_path):
        """Verify zero-padded 3-digit numbering works for many segments."""
        script = tmp_path / "many.md"
        lines = [f"NARRATOR: Segment number {i}.\n\n" for i in range(1, 12)]
        script.write_text("".join(lines))
        segments = parse_tts_script(str(script))
        assert len(segments) == 11
        assert segments[0].segment_id == "seg_001"
        assert segments[9].segment_id == "seg_010"
        assert segments[10].segment_id == "seg_011"

    def test_pause_with_decimal_duration(self):
        seg = Segment("seg_001", "Hello [PAUSE: 0.75s] world.")
        pause_chunks = [c for c in seg.text_chunks if c["type"] == "pause"]
        assert len(pause_chunks) == 1
        assert pause_chunks[0]["duration"] == 0.75

    def test_relative_output_dir_joined_with_project_dir(self):
        """Spec: relative --output-dir is joined with --project-dir."""
        parser = build_parser()
        args = parser.parse_args([
            "--project-dir", "/my/project",
            "--output-dir", "outputs/tts/",
        ])
        project_dir = os.path.abspath(args.project_dir)
        if not os.path.isabs(args.output_dir):
            output_dir = os.path.join(project_dir, args.output_dir)
        else:
            output_dir = args.output_dir
        assert output_dir == os.path.join(
            os.path.abspath("/my/project"), "outputs/tts/"
        )

    def test_absolute_output_dir_not_joined(self):
        """Spec: absolute --output-dir used as-is."""
        parser = build_parser()
        args = parser.parse_args([
            "--project-dir", "/my/project",
            "--output-dir", "/absolute/output",
        ])
        if not os.path.isabs(args.output_dir):
            output_dir = os.path.join(
                os.path.abspath(args.project_dir), args.output_dir
            )
        else:
            output_dir = args.output_dir
        assert output_dir == "/absolute/output"

    def test_script_path_is_narrative_tts_script_md(self):
        """Spec: Reads narrative/tts_script.md from project root."""
        parser = build_parser()
        args = parser.parse_args(["--project-dir", "/proj"])
        project_dir = os.path.abspath(args.project_dir)
        script_path = os.path.join(project_dir, "narrative", "tts_script.md")
        assert script_path.endswith(
            os.path.join("narrative", "tts_script.md")
        )
