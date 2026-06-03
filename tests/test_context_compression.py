"""Regression tests for context-compression env wiring (issue #877)."""

from __future__ import annotations

import os
from pathlib import Path
from unittest.mock import patch

import click
import pytest
import yaml

from pdd.compression_reporting import (
    CompressionFallbackError,
    clear_compression_fallback_events,
    format_compression_summary_lines,
    record_compression_fallback,
)
from pdd.config_resolution import apply_compression_env, resolve_effective_config
from pdd.construct_paths import construct_paths
from pdd.preprocess import preprocess
from pdd.pytest_output import _count_skipped_by_compression, _test_context_compression_active


def test_apply_compression_env_exports_pddrc_defaults(monkeypatch: pytest.MonkeyPatch) -> None:
    """`.pddrc` compression defaults must reach os.environ for preprocess."""
    monkeypatch.delenv("PDD_CONTEXT_COMPRESSION", raising=False)
    monkeypatch.delenv("PDD_COMPRESS_EXAMPLES", raising=False)
    monkeypatch.delenv("PDD_COMPRESSION_FALLBACK", raising=False)

    apply_compression_env(
        {
            "context_compression": "examples",
            "compress_examples": True,
            "compression_fallback": "error",
        }
    )

    assert os.environ["PDD_CONTEXT_COMPRESSION"] == "examples"
    assert os.environ["PDD_COMPRESS_EXAMPLES"] == "1"
    assert os.environ["PDD_COMPRESSION_FALLBACK"] == "error"


def test_construct_paths_applies_pddrc_compression_to_env(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """construct_paths must export .pddrc compression keys without polluting output_locations."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_CONTEXT_COMPRESSION", raising=False)
    monkeypatch.delenv("PDD_COMPRESS_EXAMPLES", raising=False)

    pddrc = tmp_path / ".pddrc"
    pddrc.write_text(
        yaml.safe_dump(
            {
                "version": 1,
                "contexts": {
                    "default": {
                        "defaults": {
                            "context_compression": "examples",
                            "compress_examples": True,
                        }
                    }
                },
            }
        )
    )

    prompt_file = tmp_path / "demo_python.prompt"
    prompt_file.write_text("prompt body")

    mock_output = {"output": str(tmp_path / "out.py")}

    with patch("pdd.construct_paths.generate_output_paths", return_value=mock_output) as mock_gen:
        construct_paths(
            {"prompt_file": str(prompt_file)},
            force=True,
            quiet=True,
            command="generate",
            command_options={},
        )

    mock_gen.assert_called_once()
    assert "context_compression" not in mock_gen.call_args.kwargs["output_locations"]
    assert os.environ.get("PDD_CONTEXT_COMPRESSION") == "examples"
    assert os.environ.get("PDD_COMPRESS_EXAMPLES") == "1"


def test_preprocess_auto_interface_mode_for_examples_dir(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """PDD_CONTEXT_COMPRESSION=examples shrinks example includes to signatures."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_QUIET", "1")
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "examples")

    examples_dir = tmp_path / "examples"
    examples_dir.mkdir()
    example_py = examples_dir / "widget_example.py"
    example_py.write_text(
        "def run_widget():\n"
        "    return 42\n"
    )

    prompt = f"<include>examples/{example_py.name}</include>"
    result = preprocess(prompt, recursive=False, double_curly_brackets=False, examples_dir="examples")

    assert "def run_widget" in result
    assert "return 42" not in result
    assert "..." in result


def test_apply_compression_env_off_unsets_context_compression(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "examples")
    apply_compression_env({"context_compression": "off"})
    assert "PDD_CONTEXT_COMPRESSION" not in os.environ


def _cli_ctx_with_unset_compression() -> click.Context:
    """Simulate global CLI entry without compression flags."""
    ctx = click.Context(click.Command("pdd"))
    ctx.obj = {
        "compress_examples": None,
        "compress_test_context": None,
        "context_compression": None,
        "compression_fallback": None,
    }
    return ctx


def test_resolve_effective_config_uses_pddrc_when_global_compression_unset(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Unset ctx.obj compression keys must not shadow .pddrc defaults."""
    monkeypatch.delenv("PDD_COMPRESS_TEST_CONTEXT", raising=False)
    monkeypatch.delenv("PDD_CONTEXT_COMPRESSION", raising=False)
    monkeypatch.delenv("PDD_COMPRESS_EXAMPLES", raising=False)

    resolved_config = {
        "compress_test_context": True,
        "context_compression": "test",
        "compress_examples": True,
        "compression_fallback": "error",
    }
    effective = resolve_effective_config(
        _cli_ctx_with_unset_compression(),
        resolved_config,
        param_overrides={},
    )

    assert effective["compress_test_context"] is True
    assert effective["context_compression"] == "test"
    assert effective["compress_examples"] is True
    assert effective["compression_fallback"] == "error"
    assert os.environ.get("PDD_COMPRESS_TEST_CONTEXT") == "1"
    assert os.environ.get("PDD_CONTEXT_COMPRESSION") == "test"
    assert os.environ.get("PDD_COMPRESS_EXAMPLES") == "1"
    assert os.environ.get("PDD_COMPRESSION_FALLBACK") == "error"


def test_resolve_effective_config_cli_compression_overrides_pddrc(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.delenv("PDD_COMPRESS_TEST_CONTEXT", raising=False)

    ctx = _cli_ctx_with_unset_compression()
    ctx.obj["compress_test_context"] = True

    resolved_config = {"compress_test_context": False}
    effective = resolve_effective_config(ctx, resolved_config, param_overrides={})

    assert effective["compress_test_context"] is True
    assert os.environ.get("PDD_COMPRESS_TEST_CONTEXT") == "1"


def test_resolve_effective_config_fix_command_local_flag_overrides_pddrc(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Command-local fix flags must beat .pddrc when explicitly set."""
    monkeypatch.delenv("PDD_COMPRESS_TEST_CONTEXT", raising=False)

    resolved_config = {"compress_test_context": True}
    effective = resolve_effective_config(
        _cli_ctx_with_unset_compression(),
        resolved_config,
        param_overrides={"compress_test_context": False},
    )

    assert effective["compress_test_context"] is False
    assert "PDD_COMPRESS_TEST_CONTEXT" not in os.environ


def test_fix_main_preserves_pddrc_compress_test_context(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """pdd fix without compression CLI flags must keep .pddrc test compression."""
    from pdd.fix_main import fix_main

    monkeypatch.delenv("PDD_COMPRESS_TEST_CONTEXT", raising=False)
    monkeypatch.delenv("PDD_CONTEXT_COMPRESSION", raising=False)

    prompt_file = tmp_path / "demo_python.prompt"
    code_file = tmp_path / "demo.py"
    test_file = tmp_path / "test_demo.py"
    error_file = tmp_path / "error.txt"
    prompt_file.write_text("prompt", encoding="utf-8")
    code_file.write_text("x = 1\n", encoding="utf-8")
    test_file.write_text("def test_demo():\n    assert x == 2\n", encoding="utf-8")
    error_file.write_text("AssertionError\n", encoding="utf-8")

    ctx = click.Context(click.Command("fix"))
    ctx.obj = {
        "force": True,
        "quiet": True,
        "local": True,
        "compress_examples": None,
        "compress_test_context": None,
        "context_compression": None,
        "compression_fallback": None,
    }

    resolved_config = {
        "compress_test_context": True,
        "context_compression": "test",
        "compress_examples": False,
        "compression_fallback": "full",
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
    }
    input_strings = {
        "prompt_file": prompt_file.read_text(encoding="utf-8"),
        "code_file": code_file.read_text(encoding="utf-8"),
        "unit_test_file": test_file.read_text(encoding="utf-8"),
        "error_file": error_file.read_text(encoding="utf-8"),
    }

    with patch(
        "pdd.fix_main.construct_paths",
        return_value=(resolved_config, input_strings, {}, None),
    ), patch(
        "pdd.fix_main.fix_errors_from_unit_tests",
        return_value=(False, False, "", "", None, 0.0, "test-model"),
    ):
        fix_main(
            ctx,
            str(prompt_file),
            str(code_file),
            str(test_file),
            str(error_file),
            output_test=None,
            output_code=None,
            output_results=None,
            loop=False,
            verification_program=None,
            max_attempts=3,
            budget=5.0,
            auto_submit=False,
            compress_test_context=None,
        )

    assert os.environ.get("PDD_COMPRESS_TEST_CONTEXT") == "1"
    assert os.environ.get("PDD_CONTEXT_COMPRESSION") == "test"


def test_preprocess_test_compression_without_failing_tests_keeps_full(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Preprocess must not erase test includes when compression is on but metadata is missing."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_QUIET", "1")
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "test")
    monkeypatch.delenv("PDD_FAILING_TESTS", raising=False)
    clear_compression_fallback_events()

    (tmp_path / "tests").mkdir()
    (tmp_path / "tests" / "test_sample.py").write_text(
        "def test_sample():\n    assert True\n",
        encoding="utf-8",
    )

    result = preprocess(
        "<include>tests/test_sample.py</include>",
        recursive=False,
        double_curly_brackets=False,
        tests_dir="tests",
    )
    assert "def test_sample" in result
    assert "assert True" in result


def test_preprocess_test_interface_keeps_only_failing_test(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_QUIET", "1")
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "test")
    monkeypatch.setenv("PDD_FAILING_TESTS", "tests/test_sample.py::test_fails")

    (tmp_path / "tests").mkdir()
    (tmp_path / "tests" / "test_sample.py").write_text(
        "import pytest\n\n"
        "@pytest.fixture\n"
        "def widget():\n"
        "    return 1\n\n"
        "def test_passes():\n"
        "    assert True\n\n"
        "def test_fails(widget):\n"
        "    assert widget == 2\n"
    )

    result = preprocess(
        "<include>tests/test_sample.py</include>",
        recursive=False,
        double_curly_brackets=False,
        tests_dir="tests",
    )
    assert "def test_fails" in result
    assert "def test_passes" not in result


def test_preprocess_contracts_mode_strips_non_rules(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_QUIET", "1")
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "contracts")
    (tmp_path / "rules.prompt").write_text(
        "Narrative intro.\nR1 - Always validate input.\n- MUST reject invalid tokens.\n"
    )
    result = preprocess("<include>rules.prompt</include>", recursive=False, double_curly_brackets=False)
    assert "R1 - Always validate input." in result
    assert "Narrative intro" not in result


def test_preprocess_compression_fallback_error_raises(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_QUIET", "1")
    monkeypatch.setenv("PDD_COMPRESSION_FALLBACK", "error")
    (tmp_path / "module.py").write_text("def foo():\n    return 1\n")
    with patch("pdd.content_selector.ContentSelector") as mock_cs:
        mock_cs.return_value.select.side_effect = ValueError("function 'missing' not found")
        with pytest.raises(CompressionFallbackError, match="missing"):
            preprocess('<include select="def:missing">module.py</include>', recursive=False, double_curly_brackets=False)


def test_compression_summary_reports_active_modes_and_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from pdd.compression_reporting import record_compression_applied

    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "examples")
    clear_compression_fallback_events()
    record_compression_applied("examples/widget_example.py", "interface")
    record_compression_fallback("fallback event")
    lines = format_compression_summary_lines()
    assert any("context-compression=examples" in ln for ln in lines)
    assert any("Context compressed: examples/widget_example.py" in ln for ln in lines)


def test_pytest_output_skipped_by_compression_from_deselected(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("PDD_COMPRESS_TEST_CONTEXT", "1")
    assert _test_context_compression_active()
    assert _count_skipped_by_compression("===== 1 passed, 3 deselected in 0.12s =====") == 3


def test_test_interface_mode_includes_helper_dependencies(monkeypatch: pytest.MonkeyPatch) -> None:
    """PytestSlicer must pull helper functions required by the failing test."""
    from pdd.content_selector import ContentSelector

    source = (
        "def helper():\n"
        "    return 3\n\n"
        "def test_fails():\n"
        "    assert helper() == 3\n\n"
        "def test_passes():\n"
        "    assert True\n"
    )
    monkeypatch.setenv("PDD_FAILING_TESTS", "tests/test_sample.py::test_fails")
    result = ContentSelector.select(source, selectors=[], mode="test_interface", file_path="tests/test_sample.py")
    assert "def test_fails" in result
    assert "def helper" in result
    assert "def test_passes" not in result


def test_test_interface_mode_without_failing_tests_returns_full_content(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Test compression must not erase includes when PDD_FAILING_TESTS is unset."""
    from pdd.content_selector import ContentSelector

    source = "def test_sample():\n    assert True\n"
    monkeypatch.delenv("PDD_FAILING_TESTS", raising=False)
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "test")
    clear_compression_fallback_events()

    result = ContentSelector.select(
        source,
        selectors=[],
        mode="test_interface",
        file_path="tests/test_sample.py",
    )
    assert result == source
    assert any(
        "PDD_FAILING_TESTS unset" in event
        for event in format_compression_summary_lines()
    )


def test_preprocess_slice_failure_raises_compression_fallback_error(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Preprocess include path must propagate compression fallback errors."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_QUIET", "1")
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "test")
    monkeypatch.setenv("PDD_COMPRESSION_FALLBACK", "error")
    monkeypatch.setenv("PDD_FAILING_TESTS", "tests/test_sample.py::test_missing")
    clear_compression_fallback_events()

    (tmp_path / "tests").mkdir()
    (tmp_path / "tests" / "test_sample.py").write_text(
        "def test_foo():\n    assert True\n",
        encoding="utf-8",
    )

    with pytest.raises(CompressionFallbackError, match="pytest slice failed"):
        preprocess(
            "<include>tests/test_sample.py</include>",
            recursive=False,
            double_curly_brackets=False,
            tests_dir="tests",
        )


def test_preprocess_examples_compression_lists_target_in_summary(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_QUIET", "1")
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "examples")
    clear_compression_fallback_events()

    examples_dir = tmp_path / "examples"
    examples_dir.mkdir()
    (examples_dir / "widget_example.py").write_text(
        "def run_widget():\n    return 42\n",
        encoding="utf-8",
    )

    preprocess(
        f"<include>examples/widget_example.py</include>",
        recursive=False,
        double_curly_brackets=False,
        examples_dir="examples",
    )
    assert any(
        "Context compressed:" in line and "widget_example.py" in line
        for line in format_compression_summary_lines()
    )


def test_pytest_selector_slice_failure_honors_compression_fallback_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Explicit select=pytest:… must use the same fallback policy as test_interface."""
    from pdd.content_selector import ContentSelector

    source = "def test_foo():\n    assert True\n"
    monkeypatch.setenv("PDD_COMPRESSION_FALLBACK", "error")
    clear_compression_fallback_events()

    with pytest.raises(CompressionFallbackError, match="pytest slice failed"):
        ContentSelector.select(
            source,
            selectors=["pytest:test_missing"],
            file_path="tests/test_sample.py",
        )


def test_pytest_selector_records_compressed_target_in_summary(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from pdd.content_selector import ContentSelector

    source = (
        "def test_foo():\n"
        "    assert True\n\n"
        "def test_bar():\n"
        "    assert False\n"
    )
    clear_compression_fallback_events()
    result = ContentSelector.select(
        source,
        selectors=["pytest:test_foo"],
        file_path="tests/test_sample.py",
    )
    assert "def test_bar" not in result
    assert any(
        "Context compressed:" in line and "pytest:test_foo" in line
        for line in format_compression_summary_lines()
    )


def test_test_interface_slice_failure_honors_compression_fallback_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Pytest slicing failures must respect PDD_COMPRESSION_FALLBACK=error."""
    from pdd.content_selector import ContentSelector

    monkeypatch.setenv("PDD_FAILING_TESTS", "tests/test_sample.py::test_missing")
    monkeypatch.setenv("PDD_COMPRESSION_FALLBACK", "error")
    clear_compression_fallback_events()

    with pytest.raises(CompressionFallbackError, match="pytest slice failed"):
        ContentSelector.select(
            "def test_foo():\n    assert True\n",
            selectors=[],
            mode="test_interface",
            file_path="tests/test_sample.py",
        )

    assert any(
        "Compression fallback triggered" in line
        for line in format_compression_summary_lines()
    )


def test_test_interface_mode_matches_exact_test_not_prefix(monkeypatch: pytest.MonkeyPatch) -> None:
    """Node ids must not over-select prefix test names (test_foo vs test_foobar)."""
    import re

    from pdd.content_selector import ContentSelector

    source = (
        "def test_foo():\n"
        "    assert True\n\n"
        "def test_foobar():\n"
        "    assert False\n"
    )
    monkeypatch.setenv("PDD_FAILING_TESTS", "tests/test_sample.py::test_foobar")
    result = ContentSelector.select(source, selectors=[], mode="test_interface", file_path="tests/test_sample.py")
    assert "def test_foobar():" in result
    assert not re.search(r"def test_foo\(\):", result)


def test_contracts_mode_preserves_tagged_section_content() -> None:
    from pdd.content_selector import ContentSelector

    source = (
        "<pdd-reason>Keep this reason text.</pdd-reason>\n"
        "<contract_rules>\nR2 - Also keep\n- MUST validate\n</contract_rules>\n"
    )
    result = ContentSelector.select(source, selectors=[], mode="contracts")
    assert "Keep this reason text." in result
    assert "R2 - Also keep" in result
    assert "- MUST validate" in result


def test_contracts_mode_plain_markdown_unchanged() -> None:
    from pdd.content_selector import ContentSelector

    source = "# Title\n\nNarrative documentation without PDD tags.\n"
    result = ContentSelector.select(source, selectors=[], mode="contracts", file_path="docs/guide.md")
    assert result == source


def test_preprocess_contracts_mode_plain_markdown_unchanged(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_QUIET", "1")
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "contracts")
    (tmp_path / "guide.md").write_text("# Title\n\nPlain narrative docs.\n", encoding="utf-8")
    result = preprocess("<include>guide.md</include>", recursive=False, double_curly_brackets=False)
    assert "Plain narrative docs." in result


def test_fix_error_loop_compresses_unit_test_before_fix_call(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """--compress-test-context must slice the unit test sent to fix_errors_from_unit_tests."""
    from unittest.mock import patch

    from pdd.fix_error_loop import fix_error_loop

    code = tmp_path / "widget.py"
    test = tmp_path / "test_widget.py"
    prompt = tmp_path / "widget_python.prompt"
    error_log = tmp_path / "error.log"

    unit_test_content = (
        "from widget import add\n\n"
        "def test_passes():\n"
        "    assert add(1, 1) == 2\n\n"
        "def test_fails():\n"
        "    assert add(2, 3) == 5\n"
    )
    code.write_text("def add(a, b):\n    return a - b\n", encoding="utf-8")
    test.write_text(unit_test_content, encoding="utf-8")
    prompt.write_text("Fix the code.", encoding="utf-8")

    captured: dict[str, str] = {}
    pytest_output = f"FAILED {test.name}::test_fails - AssertionError\n"

    def _fake_fix(unit_test: str, code: str, *args, **kwargs):  # type: ignore[no-untyped-def]
        captured["unit_test"] = unit_test
        return False, True, unit_test, code, "analysis", 0.0, "mock"

    monkeypatch.chdir(tmp_path)
    with patch("pdd.fix_error_loop.run_pytest_on_file", return_value=(1, 0, 0, pytest_output)), patch(
        "pdd.fix_error_loop.fix_errors_from_unit_tests", side_effect=_fake_fix
    ):
        fix_error_loop(
            unit_test_file=str(test),
            code_file=str(code),
            prompt_file=str(prompt),
            prompt="Fix",
            verification_program="",
            strength=0.5,
            temperature=0.0,
            max_attempts=1,
            budget=5.0,
            error_log_file=str(error_log),
            agentic_fallback=False,
            compress_test_context=True,
        )

    sent = captured.get("unit_test", "")
    assert "def test_fails" in sent
    assert "def test_passes" not in sent
    assert sent != unit_test_content


def test_fix_error_loop_compression_fallback_error_aborts(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """fix --loop must stop cleanly when test slicing fails under error policy."""
    from unittest.mock import patch

    from pdd.fix_error_loop import fix_error_loop

    code = tmp_path / "widget.py"
    test = tmp_path / "test_widget.py"
    prompt = tmp_path / "widget_python.prompt"
    error_log = tmp_path / "error.log"

    test.write_text("def test_foo():\n    assert False\n", encoding="utf-8")
    code.write_text("def add(a, b):\n    return a - b\n", encoding="utf-8")
    prompt.write_text("Fix the code.", encoding="utf-8")

    pytest_output = f"FAILED {test.name}::test_missing - AssertionError\n"
    fix_called = {"count": 0}

    def _fake_fix(*args, **kwargs):  # type: ignore[no-untyped-def]
        fix_called["count"] += 1
        return False, True, "", "", "analysis", 0.0, "mock"

    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_COMPRESSION_FALLBACK", "error")
    clear_compression_fallback_events()

    with patch("pdd.fix_error_loop.run_pytest_on_file", return_value=(1, 0, 0, pytest_output)), patch(
        "pdd.fix_error_loop.fix_errors_from_unit_tests", side_effect=_fake_fix
    ):
        success, *_rest = fix_error_loop(
            unit_test_file=str(test),
            code_file=str(code),
            prompt_file=str(prompt),
            prompt="Fix",
            verification_program="",
            strength=0.5,
            temperature=0.0,
            max_attempts=1,
            budget=5.0,
            error_log_file=str(error_log),
            agentic_fallback=False,
            compress_test_context=True,
        )

    assert success is False
    assert fix_called["count"] == 0
    assert "pytest slice failed" in error_log.read_text(encoding="utf-8")
    assert any(
        "Compression fallback triggered" in line
        for line in format_compression_summary_lines()
    )
