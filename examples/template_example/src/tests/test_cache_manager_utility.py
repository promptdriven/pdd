from pathlib import Path

import pytest
from z3 import Int, Solver, sat

from edit_file_tool.cache_manager_utility import should_use_cache

SMALL_FILE_BYTES = 1024
LARGE_FILE_BYTES = 4096
MEDIUM_FALLBACK_BYTES = 3072


def test_always_string_override_enables_cache():
    decision = should_use_cache("some/path.py", 0, "AlWaYs")
    assert decision is True


def test_true_override_enables_cache_without_file_read():
    decision = should_use_cache("unused", 500, True)
    assert decision is True


def test_never_string_override_disables_cache():
    decision = should_use_cache("some/path", 10_000, "never")
    assert decision is False


def test_false_override_disables_cache_even_for_large_files():
    decision = should_use_cache("unused", 10_000, False)
    assert decision is False


def test_small_size_auto_disables_cache_without_reading_file():
    decision = should_use_cache("nonexistent", SMALL_FILE_BYTES - 1, "auto")
    assert decision is False


def test_medium_size_high_complexity_enables_cache(tmp_path):
    path = tmp_path / "complex.txt"
    lines = [
        f"payload_line_{i:02d}_" + "x" * 35 for i in range(70)
    ]  # longer lines keep complexity metrics high.
    content = "\n".join(lines)
    path.write_text(content, encoding="utf-8")
    size = path.stat().st_size
    assert SMALL_FILE_BYTES <= size <= LARGE_FILE_BYTES
    assert should_use_cache(str(path), size, "auto") is True


def test_medium_size_low_complexity_disables_cache(tmp_path):
    path = tmp_path / "simple.txt"
    # Many whitespace-only lines keep non-empty ratio at zero while still producing
    # a medium-sized payload with fewer than 80 lines.
    lines = [" " * 40 for _ in range(64)]
    content = "\n".join(lines)
    path.write_text(content, encoding="utf-8")
    size = path.stat().st_size
    assert SMALL_FILE_BYTES <= size <= LARGE_FILE_BYTES
    assert size < MEDIUM_FALLBACK_BYTES
    decision = should_use_cache(str(path), size, "auto")
    assert decision is False


def test_medium_missing_file_falls_back_on_size_only():
    decision = should_use_cache("does_not_exist.txt", 2500, "auto")
    assert decision is False

    decision_high = should_use_cache("does_not_exist.txt", 4000, "auto")
    assert decision_high is True


def test_invalid_use_cache_string_raises_value_error():
    with pytest.raises(ValueError):
        should_use_cache("file.py", 100, "sometimes")


def test_invalid_file_size_type_raises():
    with pytest.raises(ValueError):
        should_use_cache("file.py", -1, "auto")
    with pytest.raises(ValueError):
        should_use_cache("file.py", True, "auto")


def test_empty_file_path_raises_value_error():
    with pytest.raises(ValueError):
        should_use_cache("   ", 100, "auto")


def test_z3_small_size_never_enables_cache():
    solver = Solver()
    size = Int("size")
    solver.add(size >= 0, size < SMALL_FILE_BYTES)
    seen = set()
    while solver.check() == sat:
        model = solver.model()
        candidate = model[size].as_long()
        if candidate in seen:
            break
        seen.add(candidate)
        solver.add(size != candidate)
        assert should_use_cache("irrelevant", candidate, "auto") is False
    assert len(seen) == SMALL_FILE_BYTES
