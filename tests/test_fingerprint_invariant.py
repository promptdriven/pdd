"""Post-command freshness invariant for every mutating command (#1926).

The command bodies are kept offline by replacing only their LLM-producing
work.  Their production metadata boundaries remain real: decorators,
single/repo update finalization, auto-deps, sync, and CI heal all have to
persist a fingerprint which the real drift classifier accepts as fresh.
"""
from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import click
import pytest

from pdd.auto_deps_main import auto_deps_main
from pdd.ci_drift_heal import _run_metadata_sync_safe
from pdd.operation_log import log_operation
from pdd.sync_determine_operation import (
    calculate_current_hashes,
    read_fingerprint,
    sync_determine_operation,
)
from pdd.sync_orchestration import _save_fingerprint_atomic
from pdd.update_main import _finalize_single_file_fingerprint


MUTATING_COMMANDS = (
    ("sync", "sync"),
    ("generate", "decorator"),
    ("example", "decorator"),
    ("update", "update"),
    ("update --all", "update"),
    ("auto-deps", "auto-deps"),
    ("fix", "decorator"),
    ("CI heal", "ci-heal"),
)


@pytest.fixture
def fingerprint_unit(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> tuple[Path, dict[str, Path]]:
    root = tmp_path / "project"
    paths = {
        "prompt": root / "prompts" / "sample_python.prompt",
        "code": root / "src" / "sample.py",
        "example": root / "examples" / "sample_example.py",
        "test": root / "tests" / "test_sample.py",
    }
    paths["test_files"] = [paths["test"]]
    for path in paths.values():
        if isinstance(path, list):
            continue
        path.parent.mkdir(parents=True, exist_ok=True)

    (root / ".pddrc").write_text(
        'version: "1.0"\n'
        "contexts:\n"
        "  default:\n"
        "    defaults:\n"
        '      generate_output_path: "src/"\n'
        '      example_output_path: "examples/"\n'
        '      test_output_path: "tests/"\n'
        '      default_language: "python"\n',
        encoding="utf-8",
    )
    paths["prompt"].write_text("% Goal\nCreate sample.\n", encoding="utf-8")
    paths["code"].write_text("def sample():\n    return 1\n", encoding="utf-8")
    paths["example"].write_text(
        "from sample import sample\nprint(sample())\n",
        encoding="utf-8",
    )
    paths["test"].write_text(
        "def test_sample():\n    assert True\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(root)
    return root, paths


def _run_decorated_finalizer(operation: str, paths: dict[str, Path]) -> None:
    @log_operation(
        operation=operation,
        clears_run_report=True,
        updates_fingerprint=True,
    )
    def mutation(*, prompt_file: str):
        if operation == "generate":
            return "written", False, 0.25, "invariant-model"
        if operation == "fix":
            return {}, "fixed", True, 1, 0.25, "invariant-model"
        return "written", 0.25, "invariant-model"

    with patch(
        "pdd.sync_determine_operation.get_pdd_file_paths",
        return_value=paths,
    ):
        mutation(prompt_file=str(paths["prompt"]))


def _run_update_finalizer(paths: dict[str, Path]) -> None:
    with patch(
        "pdd.operation_log.infer_module_identity",
        return_value=("sample", "python"),
    ), patch(
        "pdd.operation_log._clear_run_report_before_fingerprint",
        return_value=True,
    ):
        _finalize_single_file_fingerprint(
            prompt_path=paths["prompt"],
            code_path=paths["code"],
            sync_metadata=False,
            dry_run=False,
            quiet=True,
            cost=0.25,
            model="invariant-model",
        )


def _run_auto_deps_finalizer(root: Path, paths: dict[str, Path]) -> None:
    original = paths["prompt"].read_text(encoding="utf-8")
    csv_path = root / "project_dependencies.csv"
    ctx = click.Context(click.Command("auto-deps"))
    ctx.obj = {
        "quiet": True,
        "force": True,
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
    }
    with patch(
        "pdd.auto_deps_main.construct_paths",
        return_value=(
            {},
            {"prompt_file": original},
            {"output": str(paths["prompt"]), "csv": str(csv_path)},
            "python",
        ),
    ), patch(
        "pdd.auto_deps_main.insert_includes",
        return_value=(original, "", 0.25, "invariant-model"),
    ), patch(
        "pdd.auto_deps_main.sanitize_prompt_output",
        return_value=(original, []),
    ), patch(
        "pdd.auto_deps_main.merge_auto_deps_includes_from_cwd",
        return_value={"updated": False, "added_dependencies": []},
    ), patch(
        "pdd.auto_deps_main._clear_run_report_before_fingerprint",
        return_value=True,
    ):
        result = auto_deps_main(
            ctx=ctx,
            prompt_file=str(paths["prompt"]),
            directory_path=str(root),
            auto_deps_csv_path=str(csv_path),
            output=str(paths["prompt"]),
        )

    assert result[0] == original
    fingerprint = read_fingerprint("sample", "python", paths=paths)
    assert fingerprint is not None
    assert fingerprint.command == "auto-deps"


def _run_ci_heal_finalizer(paths: dict[str, Path]) -> None:
    with patch(
        "pdd.metadata_sync.run_metadata_sync",
        return_value=SimpleNamespace(ok=True),
    ):
        assert _run_metadata_sync_safe(
            str(paths["prompt"]),
            str(paths["code"]),
        )


def _run_command_finalizer(
    command: str,
    route: str,
    root: Path,
    paths: dict[str, Path],
) -> None:
    if route == "sync":
        _save_fingerprint_atomic(
            "sample",
            "python",
            "sync",
            paths,
            0.25,
            "invariant-model",
        )
    elif route == "decorator":
        _run_decorated_finalizer(command, paths)
    elif route == "update":
        _run_update_finalizer(paths)
    elif route == "auto-deps":
        _run_auto_deps_finalizer(root, paths)
        # Standalone auto-deps intentionally advances the workflow to
        # generate; model that required continuation before asserting the
        # terminal freshness invariant.
        _run_decorated_finalizer("generate", paths)
    elif route == "ci-heal":
        _run_ci_heal_finalizer(paths)
    else:  # pragma: no cover - registry is closed above
        raise AssertionError(f"unknown finalization route: {route}")


@pytest.mark.parametrize(
    ("command", "route"),
    MUTATING_COMMANDS,
    ids=[command for command, _route in MUTATING_COMMANDS],
)
def test_mutating_command_leaves_unit_fresh(
    command: str,
    route: str,
    fingerprint_unit: tuple[Path, dict[str, Path]],
) -> None:
    """A green mutating command must leave a durable, fresh fingerprint."""
    root, paths = fingerprint_unit

    _run_command_finalizer(command, route, root, paths)

    fingerprint_path = root / ".pdd" / "meta" / "sample_python.json"
    assert fingerprint_path.exists(), f"{command} returned without a fingerprint"
    payload = json.loads(fingerprint_path.read_text(encoding="utf-8"))
    assert payload["prompt_hash"], f"{command} wrote a null prompt hash"

    with patch(
        "pdd.sync_determine_operation.get_pdd_file_paths",
        return_value=paths,
    ):
        decision = sync_determine_operation(
            "sample",
            "python",
            target_coverage=90.0,
            log_mode=True,
            skip_tests=True,
            skip_verify=True,
        )

    assert decision.operation in {"nothing", "all_synced"}, (
        f"{command} reported success but the touched unit is still stale: "
        f"{decision.operation} ({decision.reason})"
    )


def test_example_from_parent_cwd_has_no_null_hashes_or_wrong_root(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Combined regressions for #1305 and #1211/#1290."""
    parent = tmp_path / "parent"
    subproject = parent / "extensions" / "app"
    parent.mkdir()
    (subproject / "prompts").mkdir(parents=True)
    (subproject / "src").mkdir()
    (subproject / "examples").mkdir()
    (subproject / "tests").mkdir()
    (subproject / ".pddrc").write_text(
        'version: "1.0"\ncontexts:\n  default:\n    defaults:\n'
        '      generate_output_path: "src/"\n'
        '      example_output_path: "examples/"\n'
        '      test_output_path: "tests/"\n',
        encoding="utf-8",
    )
    paths = {
        "prompt": subproject / "prompts" / "sample_python.prompt",
        "code": subproject / "src" / "sample.py",
        "example": subproject / "examples" / "sample_example.py",
        "test": subproject / "tests" / "test_sample.py",
    }
    paths["test_files"] = [paths["test"]]
    paths["prompt"].write_text("% Goal\nNested sample.\n", encoding="utf-8")
    paths["code"].write_text("VALUE = 1\n", encoding="utf-8")
    paths["example"].write_text("print(1)\n", encoding="utf-8")
    paths["test"].write_text("def test_value(): assert True\n", encoding="utf-8")
    monkeypatch.chdir(parent)

    _run_decorated_finalizer("example", paths)

    fingerprint_path = subproject / ".pdd" / "meta" / "sample_python.json"
    assert fingerprint_path.exists()
    assert not (parent / ".pdd" / "meta" / "sample_python.json").exists()
    payload = json.loads(fingerprint_path.read_text(encoding="utf-8"))
    expected = calculate_current_hashes(paths)
    assert payload["prompt_hash"] == expected["prompt_hash"]
    assert payload["code_hash"] == expected["code_hash"]
    assert payload["example_hash"] == expected["example_hash"]
    assert payload["test_hash"] == expected["test_hash"]

    fingerprint = read_fingerprint("sample", "python", paths=paths)
    assert fingerprint is not None
    with patch(
        "pdd.sync_determine_operation.get_pdd_file_paths",
        return_value=paths,
    ):
        decision = sync_determine_operation(
            "sample",
            "python",
            90.0,
            log_mode=True,
            skip_tests=True,
            skip_verify=True,
        )
    assert decision.operation in {"nothing", "all_synced"}


@pytest.mark.parametrize(
    ("relative_path", "required_text"),
    (
        (
            "pdd/commands/generate.py",
            '@log_operation(operation="generate", clears_run_report=True, updates_fingerprint=True)',
        ),
        (
            "pdd/commands/generate.py",
            '@log_operation(operation="example", clears_run_report=True, updates_fingerprint=True)',
        ),
        (
            "pdd/commands/fix.py",
            '@log_operation(operation="fix", clears_run_report=True, updates_fingerprint=True)',
        ),
        ("pdd/update_main.py", "_finalize_single_file_fingerprint("),
        ("pdd/auto_deps_main.py", "save_fingerprint("),
        ("pdd/sync_orchestration.py", "FingerprintTransaction("),
        ("pdd/ci_drift_heal.py", "save_fingerprint("),
    ),
)
def test_mutating_command_is_registered_with_shared_finalization_route(
    relative_path: str,
    required_text: str,
) -> None:
    """Keep the executable command registry aligned with the property harness."""
    repo_root = Path(__file__).parents[1]
    source = (repo_root / relative_path).read_text(encoding="utf-8")
    assert required_text in source
