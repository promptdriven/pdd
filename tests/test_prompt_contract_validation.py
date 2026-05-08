"""Regression tests for prompt interface/context contract validation."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import MagicMock

import click
import pytest

from pdd.code_generator_main import code_generator_main
from pdd.architecture_include_validation import validate_prompt_contract_context


def _write_issue_798_shape(
    root: Path,
    *,
    full_include: bool = False,
    prompt_dir: str = "prompts",
    include_override: str | None = None,
) -> tuple[Path, Path, Path]:
    prompts = root / prompt_dir
    prompts.mkdir(parents=True)
    source = root / "pdd" / "agentic_common.py"
    source.parent.mkdir(exist_ok=True)
    source.write_text(
        "def keep_me():\n"
        "    return True\n\n"
        "def missing_from_context():\n"
        "    return False\n",
        encoding="utf-8",
    )

    if include_override is not None:
        include = include_override
    else:
        include = (
            "<include>pdd/agentic_common.py</include>"
            if full_include
            else '<include select="def:keep_me">pdd/agentic_common.py</include>'
        )
    prompt = prompts / "agentic_common_python.prompt"
    prompt.write_text(
        '<pdd-interface>{"type":"module","module":{"functions":['
        '{"name":"keep_me","signature":"()","returns":"bool"},'
        '{"name":"missing_from_context","signature":"()","returns":"bool"}'
        "]}}</pdd-interface>\n"
        "% Goal\n"
        "Preserve the existing module and make a small change.\n"
        f"<existing_impl>{include}</existing_impl>\n",
        encoding="utf-8",
    )
    arch = [
        {
            "filename": "agentic_common_python.prompt",
            "filepath": "pdd/agentic_common.py",
            "interface": {
                "type": "module",
                "module": {
                    "functions": [
                        {"name": "keep_me", "signature": "()", "returns": "bool"},
                        {
                            "name": "missing_from_context",
                            "signature": "()",
                            "returns": "bool",
                        },
                    ]
                },
            },
        }
    ]
    (root / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")
    return prompt, source, root / "architecture.json"


def test_issue_798_partial_self_include_fails_contract_preflight(tmp_path: Path) -> None:
    prompt, source, arch = _write_issue_798_shape(tmp_path)

    errors = validate_prompt_contract_context(
        prompt_path=prompt,
        output_path=source,
        project_root=tmp_path,
        architecture_path=arch,
    )

    assert len(errors) == 1
    assert "missing_from_context" in errors[0]
    assert "declares 2 public symbols" in errors[0]
    assert "only includes source context for 1" in errors[0]


def test_full_existing_source_include_satisfies_contract(tmp_path: Path) -> None:
    prompt, source, arch = _write_issue_798_shape(tmp_path, full_include=True)

    assert (
        validate_prompt_contract_context(
            prompt_path=prompt,
            output_path=source,
            project_root=tmp_path,
            architecture_path=arch,
        )
        == []
    )


def test_self_closing_path_attribute_partial_self_include_fails_contract_preflight(
    tmp_path: Path,
) -> None:
    prompt, source, arch = _write_issue_798_shape(
        tmp_path,
        include_override='<include select="def:keep_me" path="pdd/agentic_common.py" />',
    )

    errors = validate_prompt_contract_context(
        prompt_path=prompt,
        output_path=source,
        project_root=tmp_path,
        architecture_path=arch,
    )

    assert len(errors) == 1
    assert "missing_from_context" in errors[0]
    assert "only includes source context for 1" in errors[0]


def test_body_include_path_attribute_takes_precedence_for_self_include(
    tmp_path: Path,
) -> None:
    prompt, source, arch = _write_issue_798_shape(
        tmp_path,
        include_override=(
            '<include select="def:keep_me" path="pdd/agentic_common.py">'
            "context/not_the_output.py"
            "</include>"
        ),
    )

    errors = validate_prompt_contract_context(
        prompt_path=prompt,
        output_path=source,
        project_root=tmp_path,
        architecture_path=arch,
    )

    assert len(errors) == 1
    assert "missing_from_context" in errors[0]


def test_line_range_self_include_covers_declared_existing_symbols(
    tmp_path: Path,
) -> None:
    prompt, source, arch = _write_issue_798_shape(
        tmp_path,
        include_override='<include lines="1-5">pdd/agentic_common.py</include>',
    )

    assert (
        validate_prompt_contract_context(
            prompt_path=prompt,
            output_path=source,
            project_root=tmp_path,
            architecture_path=arch,
        )
        == []
    )


def test_select_lines_selector_covers_declared_existing_symbols(
    tmp_path: Path,
) -> None:
    prompt, source, arch = _write_issue_798_shape(
        tmp_path,
        include_override='<include select="lines:1-5">pdd/agentic_common.py</include>',
    )

    assert (
        validate_prompt_contract_context(
            prompt_path=prompt,
            output_path=source,
            project_root=tmp_path,
            architecture_path=arch,
        )
        == []
    )


def test_line_range_self_include_reports_symbols_outside_range(
    tmp_path: Path,
) -> None:
    prompt, source, arch = _write_issue_798_shape(
        tmp_path,
        include_override='<include lines="1-2">pdd/agentic_common.py</include>',
    )

    errors = validate_prompt_contract_context(
        prompt_path=prompt,
        output_path=source,
        project_root=tmp_path,
        architecture_path=arch,
    )

    assert len(errors) == 1
    assert "missing_from_context" in errors[0]
    assert "only includes source context for 1" in errors[0]


def test_query_self_include_fails_with_explicit_unsupported_context_message(
    tmp_path: Path,
) -> None:
    prompt, source, arch = _write_issue_798_shape(
        tmp_path,
        include_override='<include query="implementation details">pdd/agentic_common.py</include>',
    )

    errors = validate_prompt_contract_context(
        prompt_path=prompt,
        output_path=source,
        project_root=tmp_path,
        architecture_path=arch,
    )

    assert len(errors) == 1
    assert "query= self-include cannot prove symbol coverage" in errors[0]


def test_interface_mode_self_include_is_not_full_source_context(
    tmp_path: Path,
) -> None:
    prompt, source, arch = _write_issue_798_shape(
        tmp_path,
        include_override='<include mode="interface">pdd/agentic_common.py</include>',
    )

    errors = validate_prompt_contract_context(
        prompt_path=prompt,
        output_path=source,
        project_root=tmp_path,
        architecture_path=arch,
    )

    assert len(errors) == 1
    assert (
        'mode="interface" self-include does not provide implementation context'
        in errors[0]
    )


def test_code_generator_main_aborts_before_llm_on_contract_gap(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    prompt, source, _arch = _write_issue_798_shape(tmp_path)
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_SKIP_CONFORMANCE", "1")
    monkeypatch.delenv("PDD_SKIP_PROMPT_CONTRACT_PREFLIGHT", raising=False)

    mock_generator = MagicMock(return_value=("def keep_me():\n    return True\n", 0.0, "mock"))
    monkeypatch.setattr("pdd.code_generator_main.local_code_generator_func", mock_generator)
    monkeypatch.setattr(
        "pdd.code_generator_main.construct_paths",
        MagicMock(return_value=({}, {"prompt_file": prompt.read_text()}, {"output": str(source)}, "python")),
    )
    monkeypatch.setattr("pdd.code_generator_main.CloudConfig.is_running_in_cloud", lambda: True)

    ctx = click.Context(click.Command("generate"))
    ctx.obj = {
        "local": True,
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
        "verbose": False,
        "force": True,
        "quiet": True,
        "context": None,
    }

    with pytest.raises(click.UsageError, match="Prompt contract preflight failed"):
        code_generator_main(
            ctx,
            str(prompt),
            str(source),
            original_prompt_file_path=None,
            force_incremental_flag=False,
            language="python",
        )

    mock_generator.assert_not_called()


def test_code_generator_main_finds_root_architecture_for_nested_pdd_prompts(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    prompt, source, _arch = _write_issue_798_shape(tmp_path, prompt_dir="pdd/prompts")
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_SKIP_CONFORMANCE", "1")

    mock_generator = MagicMock(return_value=("def keep_me():\n    return True\n", 0.0, "mock"))
    monkeypatch.setattr("pdd.code_generator_main.local_code_generator_func", mock_generator)
    monkeypatch.setattr(
        "pdd.code_generator_main.construct_paths",
        MagicMock(return_value=({}, {"prompt_file": prompt.read_text()}, {"output": str(source)}, "python")),
    )
    monkeypatch.setattr("pdd.code_generator_main.CloudConfig.is_running_in_cloud", lambda: True)

    ctx = click.Context(click.Command("generate"))
    ctx.obj = {
        "local": True,
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
        "verbose": False,
        "force": True,
        "quiet": True,
        "context": None,
    }

    with pytest.raises(click.UsageError, match="missing_from_context"):
        code_generator_main(
            ctx,
            str(prompt),
            str(source),
            original_prompt_file_path=None,
            force_incremental_flag=False,
            language="python",
        )

    mock_generator.assert_not_called()
