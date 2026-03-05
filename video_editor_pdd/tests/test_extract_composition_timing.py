"""
Tests for scripts/extract_composition_timing.py

Verifies keyword matching from composition IDs to word timestamps
and correct timing extraction for sub-compositions.
"""

import json
import os
import sys

import pytest

TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(TESTS_DIR)
SCRIPTS_DIR = os.path.join(PROJECT_ROOT, "scripts")
sys.path.insert(0, SCRIPTS_DIR)

from extract_composition_timing import (
    extract_keyword,
    find_keyword_timestamp,
    extract_timing_for_section,
    load_word_timestamps,
)


class TestExtractKeyword:
    """Extract keyword and type from composition IDs."""

    def test_stat_callout(self):
        keyword, comp_type = extract_keyword("part1_economics_stat_callout_gitclear", "part1_economics")
        assert keyword == "gitclear"
        assert comp_type == "stat_callout"

    def test_title_card(self):
        keyword, comp_type = extract_keyword("cold_open_title_card", "cold_open")
        assert keyword == ""
        assert comp_type == "title_card"

    def test_main(self):
        keyword, comp_type = extract_keyword("part2_paradigm_shift_main", "part2_paradigm_shift")
        assert keyword == ""
        assert comp_type == "main"

    def test_split(self):
        keyword, comp_type = extract_keyword("part1_economics_split_perception_vs_reality", "part1_economics")
        assert keyword == "reality"
        assert comp_type == "split"

    def test_split_multi_word(self):
        keyword, comp_type = extract_keyword("part5_compound_split_patching_vs_pdd", "part5_compound")
        assert keyword == "pdd"
        assert comp_type == "split"

    def test_stat_callout_multi_word(self):
        keyword, comp_type = extract_keyword("part3_mold_stat_callout_nl_context", "part3_mold")
        assert keyword == "nl_context"
        assert comp_type == "stat_callout"


class TestFindKeywordTimestamp:
    """Find keyword in word timestamp arrays."""

    def test_exact_match(self):
        words = [
            {"word": "Hello", "start": 0.0, "end": 0.5},
            {"word": "GitClear", "start": 5.0, "end": 5.5},
        ]
        assert find_keyword_timestamp("gitclear", words) == 5.0

    def test_case_insensitive(self):
        words = [{"word": "GitHub", "start": 3.0, "end": 3.5}]
        assert find_keyword_timestamp("github", words) == 3.0

    def test_strips_punctuation(self):
        words = [{"word": "maintenance.", "start": 10.0, "end": 10.5}]
        assert find_keyword_timestamp("maintenance", words) == 10.0

    def test_no_match_returns_none(self):
        words = [{"word": "hello", "start": 0.0, "end": 0.5}]
        assert find_keyword_timestamp("gitclear", words) is None

    def test_first_occurrence(self):
        words = [
            {"word": "GitClear", "start": 5.0, "end": 5.5},
            {"word": "GitClear", "start": 20.0, "end": 20.5},
        ]
        assert find_keyword_timestamp("gitclear", words) == 5.0

    def test_substring_match(self):
        words = [{"word": "DORA", "start": 8.0, "end": 8.5}]
        assert find_keyword_timestamp("dora", words) == 8.0

    def test_underscore_keyword_tries_parts(self):
        """Multi-word keywords like 'nl_context' try each part."""
        words = [
            {"word": "the", "start": 0.0, "end": 0.2},
            {"word": "context", "start": 10.0, "end": 10.5},
        ]
        assert find_keyword_timestamp("nl_context", words) == 10.0

    def test_short_parts_skipped(self):
        """Parts shorter than 4 chars are skipped to avoid false positives."""
        words = [
            {"word": "it", "start": 0.0, "end": 0.2},
            {"word": "no-match", "start": 5.0, "end": 5.5},
        ]
        assert find_keyword_timestamp("nl_it", words) is None


class TestExtractTimingForSection:
    """End-to-end timing extraction for a section."""

    def test_title_card_starts_at_zero(self, tmp_path):
        # Create word timestamps file
        words_dir = tmp_path / "outputs" / "tts" / "cold_open"
        words_dir.mkdir(parents=True)
        (words_dir / "word_timestamps.json").write_text(json.dumps([
            {"word": "Hello", "start": 0.0, "end": 0.5, "segmentId": "cold_open_001"},
        ]))

        section = {"id": "cold_open", "durationSeconds": 15, "compositions": ["cold_open_title_card"]}
        result = extract_timing_for_section(section, str(tmp_path))

        assert len(result) == 1
        assert result[0]["id"] == "cold_open_title_card"
        assert result[0]["startSeconds"] == 0.0
        assert result[0]["durationSeconds"] == 5.0

    def test_stat_callout_keyword_match(self, tmp_path):
        words_dir = tmp_path / "outputs" / "tts" / "part1_economics"
        words_dir.mkdir(parents=True)
        (words_dir / "word_timestamps.json").write_text(json.dumps([
            {"word": "Code", "start": 0.0, "end": 0.5, "segmentId": "s001"},
            {"word": "GitClear", "start": 126.0, "end": 126.5, "segmentId": "s012"},
        ]))

        section = {
            "id": "part1_economics",
            "durationSeconds": 382,
            "compositions": ["part1_economics_stat_callout_gitclear"],
        }
        result = extract_timing_for_section(section, str(tmp_path), duration=5, lead=1)

        assert result[0]["id"] == "part1_economics_stat_callout_gitclear"
        assert result[0]["startSeconds"] == 125.0  # 126 - 1s lead
        assert result[0]["durationSeconds"] == 5.0

    def test_no_match_keeps_string(self, tmp_path):
        words_dir = tmp_path / "outputs" / "tts" / "part1_economics"
        words_dir.mkdir(parents=True)
        (words_dir / "word_timestamps.json").write_text(json.dumps([
            {"word": "Hello", "start": 0.0, "end": 0.5, "segmentId": "s001"},
        ]))

        section = {
            "id": "part1_economics",
            "durationSeconds": 382,
            "compositions": ["part1_economics_stat_callout_unknown"],
        }
        result = extract_timing_for_section(section, str(tmp_path))

        # Should remain a string (no timing)
        assert result[0] == "part1_economics_stat_callout_unknown"

    def test_main_gets_full_section_duration(self, tmp_path):
        words_dir = tmp_path / "outputs" / "tts" / "part2_paradigm_shift"
        words_dir.mkdir(parents=True)
        (words_dir / "word_timestamps.json").write_text(json.dumps([]))

        section = {
            "id": "part2_paradigm_shift",
            "durationSeconds": 195.8,
            "compositions": ["part2_paradigm_shift_main"],
        }
        result = extract_timing_for_section(section, str(tmp_path))

        assert result[0]["startSeconds"] == 0.0
        assert result[0]["durationSeconds"] == 195.8

    def test_duration_clamped_to_section_length(self, tmp_path):
        words_dir = tmp_path / "outputs" / "tts" / "sec"
        words_dir.mkdir(parents=True)
        (words_dir / "word_timestamps.json").write_text(json.dumps([
            {"word": "keyword", "start": 13.0, "end": 13.5, "segmentId": "s001"},
        ]))

        section = {
            "id": "sec",
            "durationSeconds": 15,
            "compositions": ["sec_stat_callout_keyword"],
        }
        # keyword at 13s, lead 1s → start at 12s, duration 5 would exceed 15s
        result = extract_timing_for_section(section, str(tmp_path), duration=5, lead=1)

        assert result[0]["startSeconds"] == 12.0
        assert result[0]["durationSeconds"] == 3.0  # clamped: 15 - 12 = 3

    def test_no_word_timestamps_file(self, tmp_path):
        """When no word timestamps exist, title_card/main still get timing."""
        section = {
            "id": "cold_open",
            "durationSeconds": 15,
            "compositions": ["cold_open_title_card"],
        }
        result = extract_timing_for_section(section, str(tmp_path))

        # title_card doesn't need word timestamps
        assert result[0]["id"] == "cold_open_title_card"
        assert result[0]["startSeconds"] == 0.0

    def test_trigger_keyword_override(self, tmp_path):
        """Explicit triggerKeyword overrides auto-extracted keyword."""
        words_dir = tmp_path / "outputs" / "tts" / "part1_economics"
        words_dir.mkdir(parents=True)
        (words_dir / "word_timestamps.json").write_text(json.dumps([
            {"word": "211", "start": 110.0, "end": 110.5, "segmentId": "s012"},
            {"word": "million", "start": 111.0, "end": 111.5, "segmentId": "s012"},
        ]))

        section = {
            "id": "part1_economics",
            "durationSeconds": 382,
            "compositions": [
                {"id": "part1_economics_stat_callout_gitclear", "triggerKeyword": "million"},
            ],
        }
        result = extract_timing_for_section(section, str(tmp_path), lead=1)

        assert result[0]["id"] == "part1_economics_stat_callout_gitclear"
        assert result[0]["startSeconds"] == 110.0  # 111 - 1s lead
