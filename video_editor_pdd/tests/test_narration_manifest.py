"""
Tests for narration manifest timing enrichment in scripts/render_tts.py

These tests verify that build_segments_manifest() can enrich segments
with per-segment startSeconds/endSeconds derived from word_timestamps.json.
"""

import json
import os
import sys
import tempfile
from typing import Any, Dict, List

import pytest

# Add scripts/ directory to path so we can import render_tts
TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(TESTS_DIR)
SCRIPTS_DIR = os.path.join(PROJECT_ROOT, "scripts")
sys.path.insert(0, SCRIPTS_DIR)

from render_tts import Segment, build_segments_manifest, write_segments_manifest


def _make_segment(segment_id: str, raw_text: str) -> "Segment":
    """Create a Segment with the given ID and text."""
    return Segment(segment_id, raw_text)


def _make_word_timestamps(
    words: List[Dict[str, Any]],
) -> List[Dict[str, Any]]:
    """Build a list of word timestamp entries."""
    return words


class TestBuildSegmentsManifestTiming:
    """Tests for per-segment timing enrichment via word_timestamps."""

    def test_build_segments_manifest_includes_start_end_from_word_timestamps(self):
        """Segment gets startSeconds/endSeconds from min/max of matching words."""
        segments = [
            _make_segment("cold_open_001", "Welcome to the show."),
            _make_segment("cold_open_002", "Let's dive in."),
        ]
        word_timestamps_by_section = {
            "cold_open": [
                {"word": "Welcome", "start": 0.0, "end": 0.4, "segmentId": "cold_open_001"},
                {"word": "to", "start": 0.4, "end": 0.5, "segmentId": "cold_open_001"},
                {"word": "the", "start": 0.5, "end": 0.6, "segmentId": "cold_open_001"},
                {"word": "show", "start": 0.6, "end": 1.1, "segmentId": "cold_open_001"},
                {"word": "Let's", "start": 1.2, "end": 1.5, "segmentId": "cold_open_002"},
                {"word": "dive", "start": 1.5, "end": 1.8, "segmentId": "cold_open_002"},
                {"word": "in", "start": 1.8, "end": 2.1, "segmentId": "cold_open_002"},
            ],
        }

        result = build_segments_manifest(segments, word_timestamps_by_section)

        assert result[0]["startSeconds"] == 0.0
        assert result[0]["endSeconds"] == 1.1
        assert result[1]["startSeconds"] == 1.2
        assert result[1]["endSeconds"] == 2.1

    def test_build_segments_manifest_null_timing_when_no_word_timestamps(self):
        """Backward compatible: no timing fields when word_timestamps not provided."""
        segments = [_make_segment("intro_001", "Hello world.")]

        result = build_segments_manifest(segments)

        assert "startSeconds" not in result[0]
        assert "endSeconds" not in result[0]
        # Core fields still present
        assert result[0]["id"] == "intro_001"
        assert result[0]["sectionId"] == "intro"

    def test_segment_timing_spans_correct_word_boundaries(self):
        """cold_open_002 start = first word start, end = last word end."""
        segments = [
            _make_segment("cold_open_001", "First segment."),
            _make_segment("cold_open_002", "Second segment with more words."),
        ]
        word_timestamps_by_section = {
            "cold_open": [
                {"word": "First", "start": 0.0, "end": 0.3, "segmentId": "cold_open_001"},
                {"word": "segment", "start": 0.3, "end": 0.8, "segmentId": "cold_open_001"},
                {"word": "Second", "start": 1.0, "end": 1.3, "segmentId": "cold_open_002"},
                {"word": "segment", "start": 1.3, "end": 1.6, "segmentId": "cold_open_002"},
                {"word": "with", "start": 1.6, "end": 1.8, "segmentId": "cold_open_002"},
                {"word": "more", "start": 1.8, "end": 2.0, "segmentId": "cold_open_002"},
                {"word": "words", "start": 2.0, "end": 2.5, "segmentId": "cold_open_002"},
            ],
        }

        result = build_segments_manifest(segments, word_timestamps_by_section)

        # cold_open_002 spans from 1.0 to 2.5
        assert result[1]["startSeconds"] == 1.0
        assert result[1]["endSeconds"] == 2.5

    def test_segment_timing_handles_missing_segmentId_in_words(self):
        """Words without segmentId are skipped — no crash, no false timing."""
        segments = [_make_segment("intro_001", "Hello world.")]
        word_timestamps_by_section = {
            "intro": [
                {"word": "Hello", "start": 0.0, "end": 0.3, "segmentId": "intro_001"},
                {"word": "world", "start": 0.3, "end": 0.6},  # no segmentId
                {"word": "extra", "start": 0.8, "end": 1.0, "segmentId": "intro_002"},
            ],
        }

        result = build_segments_manifest(segments, word_timestamps_by_section)

        # Only the word with matching segmentId contributes
        assert result[0]["startSeconds"] == 0.0
        assert result[0]["endSeconds"] == 0.3


class TestWriteSegmentsManifestTiming:
    """Tests that write_segments_manifest properly loads word_timestamps and passes them."""

    def test_write_segments_manifest_loads_word_timestamps(self):
        """write_segments_manifest loads per-section word_timestamps.json and enriches segments."""
        with tempfile.TemporaryDirectory() as tmpdir:
            output_dir = os.path.join(tmpdir, "outputs", "tts")
            os.makedirs(output_dir, exist_ok=True)

            # Write word_timestamps for section "demo"
            section_dir = os.path.join(output_dir, "demo")
            os.makedirs(section_dir, exist_ok=True)
            word_ts = [
                {"word": "Hello", "start": 0.0, "end": 0.3, "segmentId": "demo_001"},
                {"word": "world", "start": 0.3, "end": 0.7, "segmentId": "demo_001"},
            ]
            with open(os.path.join(section_dir, "word_timestamps.json"), "w") as f:
                json.dump(word_ts, f)

            segments = [_make_segment("demo_001", "Hello world.")]
            manifest_path = write_segments_manifest(output_dir, segments)

            with open(manifest_path) as f:
                manifest = json.load(f)

            seg = manifest["segments"][0]
            assert seg["startSeconds"] == 0.0
            assert seg["endSeconds"] == 0.7
