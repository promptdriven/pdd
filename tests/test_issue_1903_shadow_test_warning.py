"""Regression tests for the shadow-test warning (issue #1903).

`pdd generate`/`change`/`sync` can write a module's unit test to a canonical
path the project's test runner does not collect while a real test already lives
beside the module, so PDD maintains a second, parallel "shadow" test that drifts
from the real one (a false-green). These tests cover the language-agnostic
detector (`find_module_test_siblings`) and the warning choke point
(`_warn_on_shadow_test`). Fully hermetic: no network, no LLM.
"""
from __future__ import annotations

import logging
from pathlib import Path

from pdd import content_selector
from pdd.content_selector import (
    _effective_test_write_target,
    _warn_on_shadow_test,
    find_module_test_siblings,
)


def _write(path: Path, text: str = "// placeholder\n") -> Path:
    """Create *path* (and parents) with *text*; return it."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def test_find_siblings_detects_colocated_jest_test(tmp_path: Path) -> None:
    """A co-located jest test (`__test__/page.test.tsx`) is detected."""
    page = _write(tmp_path / "contributions" / "page.tsx")
    colocated = _write(tmp_path / "contributions" / "__test__" / "page.test.tsx")

    siblings = find_module_test_siblings(page)

    assert colocated.resolve() in {p.resolve() for p in siblings}


def test_find_siblings_detects_python_test(tmp_path: Path) -> None:
    """A sibling `test_foo.py` is detected for `foo.py`."""
    module = _write(tmp_path / "foo.py", "x = 1\n")
    sibling = _write(tmp_path / "test_foo.py", "def test_x():\n    assert True\n")

    siblings = find_module_test_siblings(module)

    assert sibling.resolve() in {p.resolve() for p in siblings}


def test_find_siblings_empty_when_only_module_exists(tmp_path: Path) -> None:
    """No siblings are returned when only the module file exists (no test)."""
    module = _write(tmp_path / "solo.tsx")

    assert find_module_test_siblings(module) == []


def test_warn_returns_message_for_shadow_fork(tmp_path: Path) -> None:
    """A canonical output path different from the existing test warns loudly."""
    page = _write(tmp_path / "contributions" / "page.tsx")
    colocated = _write(tmp_path / "contributions" / "__test__" / "page.test.tsx")
    shadow_output = tmp_path / "tests" / "test_contributions_page.tsx"

    message = _warn_on_shadow_test(str(page), str(shadow_output), quiet=True)

    assert message is not None
    assert str(colocated) in message


def test_warn_returns_none_when_output_is_existing_sibling(tmp_path: Path) -> None:
    """No warning when PDD's output path IS the existing co-located test."""
    page = _write(tmp_path / "contributions" / "page.tsx")
    colocated = _write(tmp_path / "contributions" / "__test__" / "page.test.tsx")

    message = _warn_on_shadow_test(str(page), str(colocated), quiet=True)

    assert message is None


def test_warn_greenfield_jsts_outside_module_dir_warns(tmp_path: Path) -> None:
    """Greenfield JS/TS: a test written outside the module dir warns (uncollected)."""
    page = _write(tmp_path / "contributions" / "page.tsx")  # no test yet
    outside_output = tmp_path / "tests" / "test_contributions_page.tsx"

    message = _warn_on_shadow_test(str(page), str(outside_output), quiet=True)

    assert message is not None
    assert "uncollected" in message.lower()
    assert str(outside_output) in message


def test_warn_greenfield_silent_when_colocated(tmp_path: Path) -> None:
    """Greenfield JS/TS: an output UNDER the module dir is co-located → silent."""
    page = _write(tmp_path / "contributions" / "page.tsx")  # no test yet
    colocated_output = tmp_path / "contributions" / "__test__" / "page.test.tsx"

    message = _warn_on_shadow_test(str(page), str(colocated_output), quiet=True)

    assert message is None


def test_warn_greenfield_python_silent(tmp_path: Path) -> None:
    """Greenfield Python is exempt: a central tests/ dir is idiomatic."""
    module = _write(tmp_path / "foo.py", "x = 1\n")  # no test yet
    outside_output = tmp_path / "tests" / "test_foo.py"

    assert _warn_on_shadow_test(str(module), str(outside_output), quiet=True) is None


def test_effective_write_target_native_merge_uses_existing_test(tmp_path: Path) -> None:
    """Native merge writes existing_tests[0]; agentic/non-merge write output."""
    canonical = tmp_path / "tests" / "test_contributions_page.tsx"
    sibling = tmp_path / "contributions" / "__test__" / "page.test.tsx"

    # Native merge appends to the existing test.
    assert _effective_test_write_target(
        str(canonical), True, [str(sibling)], agentic=False
    ) == str(sibling)
    # Non-merge writes the canonical output path.
    assert _effective_test_write_target(
        str(canonical), False, [str(sibling)], agentic=False
    ) == str(canonical)


def test_warn_no_false_shadow_when_native_merge_targets_existing(tmp_path: Path) -> None:
    """No false warning: native --merge writes to the real co-located test itself."""
    page = _write(tmp_path / "contributions" / "page.tsx")
    sibling = _write(tmp_path / "contributions" / "__test__" / "page.test.tsx")
    canonical = tmp_path / "tests" / "test_contributions_page.tsx"  # differs from sibling

    target = _effective_test_write_target(str(canonical), True, [str(sibling)], agentic=False)

    assert _warn_on_shadow_test(str(page), target, quiet=True) is None


def test_warn_fires_for_agentic_merge_shadow(tmp_path: Path) -> None:
    """Agentic merge (e.g. JS/TS) writes the canonical path, so the fork warns."""
    page = _write(tmp_path / "contributions" / "page.tsx")
    colocated = _write(tmp_path / "contributions" / "__test__" / "page.test.tsx")
    canonical = tmp_path / "tests" / "test_contributions_page.tsx"  # differs from sibling

    # The agentic branch ignores existing_tests[0] and writes the canonical path.
    target = _effective_test_write_target(str(canonical), True, [str(colocated)], agentic=True)
    assert target == str(canonical)

    message = _warn_on_shadow_test(str(page), target, quiet=True)
    assert message is not None
    assert str(colocated) in message


def test_warn_dedupes_repeated_prints_but_returns_stable(tmp_path: Path, monkeypatch) -> None:
    """Repeat calls for the same fork print once but always return the message."""
    page = _write(tmp_path / "contributions" / "page.tsx")
    _write(tmp_path / "contributions" / "__test__" / "page.test.tsx")
    shadow_output = tmp_path / "tests" / "test_contributions_page.tsx"

    prints: list[tuple] = []
    monkeypatch.setattr(content_selector.console, "print", lambda *a, **k: prints.append(a))

    first = _warn_on_shadow_test(str(page), str(shadow_output), quiet=False)
    second = _warn_on_shadow_test(str(page), str(shadow_output), quiet=False)

    assert first is not None
    assert second is not None
    assert first == second
    assert len(prints) == 1


def test_warn_logs_message_even_when_quiet(tmp_path: Path, caplog) -> None:
    """quiet=True still logs the fork warning (WARNING); no fork logs nothing."""
    page = _write(tmp_path / "contributions" / "page.tsx")
    colocated = _write(tmp_path / "contributions" / "__test__" / "page.test.tsx")
    shadow_output = tmp_path / "tests" / "test_contributions_page.tsx"

    with caplog.at_level(logging.WARNING, logger="pdd.content_selector"):
        message = _warn_on_shadow_test(str(page), str(shadow_output), quiet=True)

    assert message is not None
    logged = "\n".join(r.getMessage() for r in caplog.records)
    assert "Shadow test warning (issue #1903)" in logged
    assert str(colocated) in logged

    # Nothing to warn about → nothing logged (Python greenfield is exempt).
    caplog.clear()
    lone = _write(tmp_path / "solo" / "widget.py", "x = 1\n")
    with caplog.at_level(logging.WARNING, logger="pdd.content_selector"):
        assert _warn_on_shadow_test(
            str(lone), str(tmp_path / "tests" / "test_widget.py"), quiet=True
        ) is None

    assert caplog.records == []


def test_find_siblings_detects_spec_convention(tmp_path: Path) -> None:
    """`.spec.` tests are detected — co-located and beside the module (`widget.ts`)."""
    module = _write(tmp_path / "pkg" / "widget.ts")
    colocated_spec = _write(tmp_path / "pkg" / "__test__" / "widget.spec.ts")
    beside_spec = _write(tmp_path / "pkg" / "widget.spec.ts")

    resolved = {p.resolve() for p in find_module_test_siblings(module)}

    assert colocated_spec.resolve() in resolved
    assert beside_spec.resolve() in resolved


def test_warn_logger_dedupes_repeat_fork_calls(tmp_path: Path, caplog) -> None:
    """Two identical fork calls log exactly once but both return the message."""
    page = _write(tmp_path / "contributions" / "page.tsx")
    _write(tmp_path / "contributions" / "__test__" / "page.test.tsx")
    shadow_output = tmp_path / "tests" / "test_contributions_page.tsx"

    # _SHADOW_WARNING_PRINTED is module-global; isolate this test so prior
    # tests' keys can't suppress the first log and skew the count.
    content_selector._SHADOW_WARNING_PRINTED.clear()
    try:
        with caplog.at_level(logging.WARNING, logger="pdd.content_selector"):
            first = _warn_on_shadow_test(str(page), str(shadow_output), quiet=True)
            second = _warn_on_shadow_test(str(page), str(shadow_output), quiet=True)

        assert first is not None
        assert second is not None
        assert first == second
        assert len(caplog.records) == 1
    finally:
        content_selector._SHADOW_WARNING_PRINTED.clear()


def test_warn_emits_manual_review_marker_for_fork(tmp_path: Path, capsys) -> None:
    """A fork warning prints one MANUAL_REVIEW: stdout line naming the output path."""
    content_selector._SHADOW_WARNING_PRINTED.clear()
    page = _write(tmp_path / "contributions" / "page.tsx")
    _write(tmp_path / "contributions" / "__test__" / "page.test.tsx")
    shadow_output = tmp_path / "tests" / "test_contributions_page.tsx"

    _warn_on_shadow_test(str(page), str(shadow_output), quiet=True)

    marker_lines = [
        ln for ln in capsys.readouterr().out.splitlines()
        if ln.startswith("MANUAL_REVIEW:")
    ]
    assert len(marker_lines) == 1
    assert str(shadow_output) in marker_lines[0]


def test_warn_emits_manual_review_marker_for_greenfield(tmp_path: Path, capsys) -> None:
    """A greenfield JS/TS uncollected warning also prints a MANUAL_REVIEW: line."""
    content_selector._SHADOW_WARNING_PRINTED.clear()
    page = _write(tmp_path / "contributions" / "page.tsx")  # no test yet
    outside_output = tmp_path / "tests" / "test_contributions_page.tsx"

    _warn_on_shadow_test(str(page), str(outside_output), quiet=True)

    marker_lines = [
        ln for ln in capsys.readouterr().out.splitlines()
        if ln.startswith("MANUAL_REVIEW:")
    ]
    assert len(marker_lines) == 1
    assert str(outside_output) in marker_lines[0]
    assert str(page) in marker_lines[0]  # names the source module (self-sufficient)


def test_warn_no_manual_review_when_silent(tmp_path: Path, capsys) -> None:
    """No MANUAL_REVIEW: line on the silent paths (Python greenfield, co-located)."""
    content_selector._SHADOW_WARNING_PRINTED.clear()

    py = _write(tmp_path / "foo.py", "x = 1\n")  # Python greenfield is exempt
    assert _warn_on_shadow_test(
        str(py), str(tmp_path / "tests" / "test_foo.py"), quiet=True
    ) is None

    page = _write(tmp_path / "contributions" / "page.tsx")  # co-located output
    colocated = tmp_path / "contributions" / "__test__" / "page.test.tsx"
    assert _warn_on_shadow_test(str(page), str(colocated), quiet=True) is None

    assert "MANUAL_REVIEW:" not in capsys.readouterr().out


def test_manual_review_marker_is_collected_by_orchestrator(tmp_path: Path, capsys) -> None:
    """The emitted MANUAL_REVIEW line is collectable into the PR body."""
    from pdd.agentic_change_orchestrator import _collect_manual_review_lines

    content_selector._SHADOW_WARNING_PRINTED.clear()
    page = _write(tmp_path / "contributions" / "page.tsx")
    _write(tmp_path / "contributions" / "__test__" / "page.test.tsx")
    shadow_output = tmp_path / "tests" / "test_contributions_page.tsx"

    _warn_on_shadow_test(str(page), str(shadow_output), quiet=True)

    collected = _collect_manual_review_lines(capsys.readouterr().out)
    assert "MANUAL_REVIEW:" in collected
    assert str(shadow_output) in collected


def test_find_siblings_unsupported_language_no_false_positive(tmp_path: Path) -> None:
    """Bug A: a non-JS/TS, non-Python module doesn't borrow an unrelated test_*.py."""
    go_module = _write(tmp_path / "foo.go", "package main\n")
    _write(tmp_path / "test_foo.py", "def test_x():\n    assert True\n")

    assert find_module_test_siblings(go_module) == []


def test_warn_no_false_positive_for_unsupported_language(tmp_path: Path, capsys) -> None:
    """Bug A: a Go module next to an unrelated py test → no warning, no marker."""
    content_selector._SHADOW_WARNING_PRINTED.clear()
    go_module = _write(tmp_path / "foo.go", "package main\n")
    _write(tmp_path / "test_foo.py", "def test_x():\n    assert True\n")

    result = _warn_on_shadow_test(
        str(go_module), str(tmp_path / "tests" / "foo_test.go"), quiet=True
    )

    assert result is None
    assert "MANUAL_REVIEW:" not in capsys.readouterr().out


def test_manual_review_marker_includes_existing_sibling_path(tmp_path: Path, capsys) -> None:
    """Bug B: the fork MANUAL_REVIEW line carries the existing sibling path (self-sufficient)."""
    content_selector._SHADOW_WARNING_PRINTED.clear()
    page = _write(tmp_path / "contributions" / "page.tsx")
    colocated = _write(tmp_path / "contributions" / "__test__" / "page.test.tsx")
    shadow_output = tmp_path / "tests" / "test_contributions_page.tsx"

    _warn_on_shadow_test(str(page), str(shadow_output), quiet=True)

    marker_lines = [
        ln for ln in capsys.readouterr().out.splitlines()
        if ln.startswith("MANUAL_REVIEW:")
    ]
    assert len(marker_lines) == 1
    assert str(shadow_output) in marker_lines[0]
    assert str(colocated) in marker_lines[0]
    assert str(page) in marker_lines[0]  # names the source module too (Bug Y)


def test_manual_review_marker_survives_quiet_logger(tmp_path: Path, capsys) -> None:
    """Bug B: with the `pdd` logger raised to ERROR (as `--quiet` does), the marker still emits."""
    content_selector._SHADOW_WARNING_PRINTED.clear()
    page = _write(tmp_path / "contributions" / "page.tsx")
    colocated = _write(tmp_path / "contributions" / "__test__" / "page.test.tsx")
    shadow_output = tmp_path / "tests" / "test_contributions_page.tsx"

    pdd_logger = logging.getLogger("pdd")
    prev_level = pdd_logger.level
    pdd_logger.setLevel(logging.ERROR)  # simulate `pdd --quiet` suppressing warnings
    try:
        _warn_on_shadow_test(str(page), str(shadow_output), quiet=True)
    finally:
        pdd_logger.setLevel(prev_level)

    marker_lines = [
        ln for ln in capsys.readouterr().out.splitlines()
        if ln.startswith("MANUAL_REVIEW:")
    ]
    assert len(marker_lines) == 1
    assert str(colocated) in marker_lines[0]


def test_warn_silent_when_output_is_one_of_multiple_siblings(tmp_path: Path, capsys) -> None:
    """Bug X: output IS a collected sibling → no warning even if other siblings exist."""
    content_selector._SHADOW_WARNING_PRINTED.clear()
    widget = _write(tmp_path / "pkg" / "widget.ts")
    test_sib = _write(tmp_path / "pkg" / "widget.test.ts")
    _write(tmp_path / "pkg" / "widget.spec.ts")  # a second collected sibling

    result = _warn_on_shadow_test(str(widget), str(test_sib), quiet=True)

    assert result is None
    assert "MANUAL_REVIEW:" not in capsys.readouterr().out


def test_warn_fork_when_output_differs_from_all_siblings(tmp_path: Path, capsys) -> None:
    """Bug X: output is none of the siblings → fork warning listing the collected sibling(s)."""
    content_selector._SHADOW_WARNING_PRINTED.clear()
    widget = _write(tmp_path / "pkg" / "widget.ts")
    test_sib = _write(tmp_path / "pkg" / "widget.test.ts")
    spec_sib = _write(tmp_path / "pkg" / "widget.spec.ts")
    canonical = tmp_path / "tests" / "test_widget.ts"  # none of the siblings

    message = _warn_on_shadow_test(str(widget), str(canonical), quiet=True)

    assert message is not None
    assert str(test_sib) in message and str(spec_sib) in message

    marker_lines = [
        ln for ln in capsys.readouterr().out.splitlines()
        if ln.startswith("MANUAL_REVIEW:")
    ]
    assert len(marker_lines) == 1
    assert str(test_sib) in marker_lines[0] and str(spec_sib) in marker_lines[0]
