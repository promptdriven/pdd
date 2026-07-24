"""CLI smoke tests for ``pdd checkup drift`` (PR #1261 manual test plan)."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.cli import cli
from pdd.commands.checkup import checkup
import pdd.drift_main as drift_main


def _write_smoke_project(project: Path) -> None:
    prompt = project / "prompts" / "refund_payment_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("<prompt>\nRefund module.\n</prompt>\n", encoding="utf-8")
    code = project / "src" / "refund_payment.py"
    code.parent.mkdir(parents=True)
    code.write_text(
        "def refund_payment(amount: int) -> int:\n    return amount\n",
        encoding="utf-8",
    )
    manifest = project / ".pdd" / "evidence" / "devunits" / "refund_payment.latest.json"
    manifest.parent.mkdir(parents=True)
    manifest.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "prompt": {"path": str(prompt.relative_to(project))},
                "outputs": [
                    {
                        "path": str(code.relative_to(project)),
                        "sha256": hashlib.sha256(code.read_bytes()).hexdigest(),
                    }
                ],
                "validation": {
                    "detect_stories": "not_available",
                    "verify": "not_available",
                    "unit_tests": "not_available",
                },
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


def _write_nested_project(
    project: Path,
    *,
    prompt_root: str = "prompts/src",
    prompt_name: str = "widget_Python.prompt",
    code_path: str = "generated/widget_impl.py",
) -> tuple[Path, Path]:
    prompt = project / prompt_root / prompt_name
    prompt.parent.mkdir(parents=True, exist_ok=True)
    prompt.write_text("<prompt>\nNested widget module.\n</prompt>\n", encoding="utf-8")
    code = project / code_path
    code.parent.mkdir(parents=True, exist_ok=True)
    code.write_text("def widget() -> str:\n    return 'ok'\n", encoding="utf-8")
    (project / ".pddrc").write_text(
        "version: '1.0'\n"
        "contexts:\n"
        "  nested:\n"
        "    paths:\n"
        f"      - '{prompt_root}/**'\n"
        f"      - '{Path(code_path).parent.as_posix()}/**'\n"
        "    defaults:\n"
        f"      prompts_dir: '{prompt_root}'\n"
        f"      generate_output_path: '{Path(code_path).parent.as_posix()}'\n"
        "      default_language: python\n",
        encoding="utf-8",
    )
    return prompt, code


@pytest.fixture
def runner() -> CliRunner:
    return CliRunner()


def test_checkup_drift_help(runner: CliRunner) -> None:
    result = runner.invoke(checkup, ["drift", "--help"])
    assert result.exit_code == 0
    assert "regeneration stability" in result.output.lower()
    assert "--dry-run" in result.output
    assert "--json" in result.output


def test_checkup_drift_dry_run_json(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    _write_smoke_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    result = runner.invoke(
        checkup,
        ["drift", "refund_payment", "--dry-run", "--json"],
        catch_exceptions=False,
    )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["status"] == "stable"
    assert payload["dry_run"] is True


def test_checkup_drift_from_evidence_json(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    _write_smoke_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    manifest = (
        tmp_path / ".pdd" / "evidence" / "devunits" / "refund_payment.latest.json"
    )
    result = runner.invoke(
        checkup,
        [
            "drift",
            "refund_payment",
            "--from-evidence",
            str(manifest),
            "--dry-run",
            "--json",
        ],
        catch_exceptions=False,
    )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["policy_check_skipped"] is True
    assert payload["policy_check_unavailable"] is False


def test_checkup_drift_runs_two_leaves_worktree_unchanged(
    runner: CliRunner,
    tmp_path: Path,
    monkeypatch,
) -> None:
    _write_smoke_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    code = tmp_path / "src" / "refund_payment.py"
    before = code.read_bytes()
    stable_source = code.read_text(encoding="utf-8")

    def _fake_regenerate(_prompt_path: Path, output_path: Path, **kwargs) -> float:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(stable_source, encoding="utf-8")
        return 0.0

    with patch("pdd.drift_main._regenerate_code", side_effect=_fake_regenerate):
        result = runner.invoke(
            checkup,
            ["drift", "refund_payment", "--runs", "2", "--json"],
            catch_exceptions=False,
        )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["runs"] == 2
    assert len(payload["snapshots"]) == 2
    assert code.read_bytes() == before


def test_no_top_level_pdd_drift_command(runner: CliRunner) -> None:
    result = runner.invoke(cli, ["--help"])
    assert result.exit_code == 0
    lines = [line.strip() for line in result.output.splitlines()]
    assert "drift" not in lines
    assert any(line.startswith("checkup") for line in lines)


def test_preview_does_not_inject_dry_run_into_drift(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    """--preview must never inject --dry-run into drift args (#1519 finding #3).

    pdd checkup drift <unit> --preview → drift must NOT receive --dry-run;
    drift --dry-run suppresses regeneration, which is unrelated to interactive apply preview.
    """
    _write_smoke_project(tmp_path)
    monkeypatch.chdir(tmp_path)

    captured = {}

    def _fake_drift_main(args, **kwargs):
        captured["args"] = list(args)
        return 0

    with patch("pdd.commands.checkup.drift_cmd.main", side_effect=_fake_drift_main):
        runner.invoke(
            checkup,
            ["drift", "refund_payment", "--preview"],
            catch_exceptions=False,
        )

    assert "--dry-run" not in captured.get("args", []), (
        "--preview must not forward --dry-run to drift"
    )


def test_explicit_dry_run_still_forwarded_to_drift(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    """User passing --dry-run directly as a drift arg must still reach drift unchanged."""
    _write_smoke_project(tmp_path)
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(
        checkup,
        ["drift", "refund_payment", "--dry-run", "--json"],
        catch_exceptions=False,
    )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["dry_run"] is True


def test_checkup_drift_accepts_explicit_nested_prompt_and_authoritative_code_file(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    prompt, code = _write_nested_project(tmp_path)
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(
        checkup,
        [
            "drift",
            prompt.relative_to(tmp_path).as_posix(),
            "--code-file",
            code.relative_to(tmp_path).as_posix(),
            "--dry-run",
            "--json",
        ],
        catch_exceptions=False,
    )

    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert Path(payload["prompt_path"]) == prompt.resolve()
    assert Path(payload["code_path"]) == code.resolve()
    assert payload["status"] == "stable"


def test_checkup_drift_resolves_nested_basename_from_active_pddrc(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    prompt, code = _write_nested_project(
        tmp_path,
        prompt_root="specs/backend",
        prompt_name="widget_Python.prompt",
    )
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(
        checkup,
        [
            "drift",
            "widget",
            "--code-file",
            code.relative_to(tmp_path).as_posix(),
            "--dry-run",
            "--json",
        ],
        catch_exceptions=False,
    )

    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert Path(payload["prompt_path"]) == prompt.resolve()
    assert Path(payload["code_path"]) == code.resolve()


def test_checkup_drift_basename_scan_has_actionable_work_bound(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    """Huge prompt trees fail closed instead of unbounded recursive scanning."""
    prompt, code = _write_nested_project(tmp_path)
    for index in range(3):
        extra = tmp_path / "prompts" / "bulk" / f"entry_{index}.txt"
        extra.parent.mkdir(parents=True, exist_ok=True)
        extra.write_text("x\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(drift_main, "_MAX_PROMPT_SCAN_ENTRIES", 2)

    result = runner.invoke(
        checkup,
        [
            "drift", "widget", "--code-file", code.relative_to(tmp_path).as_posix(),
            "--dry-run", "--json",
        ],
        catch_exceptions=False,
    )

    assert prompt.exists()
    assert result.exit_code == 1
    payload = json.loads(result.output)
    assert payload["error"]["code"] == "drift_input_resolution_limit"
    assert "explicit path" in payload["error"]["message"]


def test_checkup_drift_basename_scan_has_actionable_time_bound(
    tmp_path: Path, monkeypatch
) -> None:
    """A slow prompt tree fails closed with the same explicit-path remedy."""
    prompt, _code = _write_nested_project(tmp_path)
    ticks = iter((0.0, drift_main._MAX_PROMPT_SCAN_SECONDS + 1.0))
    monkeypatch.setattr(drift_main.time, "monotonic", lambda: next(ticks))

    with pytest.raises(drift_main.DriftInputError) as exc_info:
        drift_main._resolve_prompt_input("widget", tmp_path)

    assert prompt.exists()
    assert exc_info.value.code == "drift_input_resolution_limit"
    assert "explicit path" in str(exc_info.value)


def test_checkup_drift_explicit_nested_prompt_derives_own_sibling_context_code(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    """A prompt path must retain its context when ``--code-file`` is omitted."""
    for context in ("backend", "frontend"):
        prompt = tmp_path / "prompts" / context / "widget_Python.prompt"
        prompt.parent.mkdir(parents=True)
        prompt.write_text(f"<prompt>{context} widget</prompt>\n", encoding="utf-8")
        code = tmp_path / "src" / context / "widget.py"
        code.parent.mkdir(parents=True)
        code.write_text(
            f"def widget() -> str:\n    return '{context}'\n",
            encoding="utf-8",
        )
    (tmp_path / ".pddrc").write_text(
        "version: '1.0'\n"
        "contexts:\n"
        "  backend:\n"
        "    paths:\n"
        "      - 'backend/**'\n"
        "      - 'src/backend/**'\n"
        "      - 'prompts/backend/**'\n"
        "    defaults:\n"
        "      prompts_dir: prompts/backend\n"
        "      generate_output_path: src/backend\n"
        "      default_language: python\n"
        "  frontend:\n"
        "    paths:\n"
        "      - 'frontend/**'\n"
        "      - 'src/frontend/**'\n"
        "      - 'prompts/frontend/**'\n"
        "    defaults:\n"
        "      prompts_dir: prompts/frontend\n"
        "      generate_output_path: src/frontend\n"
        "      default_language: python\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(
        checkup,
        [
            "drift",
            "prompts/frontend/widget_Python.prompt",
            "--dry-run",
            "--json",
        ],
        catch_exceptions=False,
    )

    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert (
        Path(payload["prompt_path"])
        == (tmp_path / "prompts/frontend/widget_Python.prompt").resolve()
    )
    assert Path(payload["code_path"]) == (tmp_path / "src/frontend/widget.py").resolve()


def test_checkup_drift_nested_prompt_does_not_fall_back_to_unrelated_flat_code(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    prompt = tmp_path / "prompts/frontend/widget_Python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("<prompt>frontend widget</prompt>\n", encoding="utf-8")
    unrelated = tmp_path / "src/widget.py"
    unrelated.parent.mkdir()
    unrelated.write_text("def widget() -> str:\n    return 'root'\n", encoding="utf-8")
    (tmp_path / ".pddrc").write_text(
        "version: '1.0'\n"
        "contexts:\n"
        "  frontend:\n"
        "    paths:\n"
        "      - 'frontend/**'\n"
        "      - 'prompts/frontend/**'\n"
        "    defaults:\n"
        "      prompts_dir: prompts/frontend\n"
        "      generate_output_path: src/frontend\n"
        "      default_language: python\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(
        checkup,
        [
            "drift",
            "prompts/frontend/widget_Python.prompt",
            "--dry-run",
            "--json",
        ],
        catch_exceptions=False,
    )

    assert result.exit_code == 1
    payload = json.loads(result.output)
    assert payload["error"]["code"] == "drift_input_not_found"
    assert "pass --code-file" in payload["error"]["message"]


def test_checkup_drift_matches_language_suffix_case_insensitively(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    prompt, code = _write_nested_project(
        tmp_path,
        prompt_name="widget_PyThOn.prompt",
    )
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(
        checkup,
        [
            "drift",
            "widget",
            "--code-file",
            code.relative_to(tmp_path).as_posix(),
            "--dry-run",
            "--json",
        ],
        catch_exceptions=False,
    )

    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert Path(payload["prompt_path"]) == prompt.resolve()


def test_checkup_drift_json_resolution_failure_is_structured(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(
        checkup,
        ["drift", "missing_widget", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    assert result.exit_code == 1
    payload = json.loads(result.output)
    assert payload == {
        "status": "error",
        "error": {
            "code": "drift_input_not_found",
            "message": "Could not resolve prompt for dev unit 'missing_widget'",
        },
    }


def test_checkup_drift_rejects_explicit_paths_outside_project_root(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    project = tmp_path / "project"
    project.mkdir()
    outside_prompt = tmp_path / "outside_Python.prompt"
    outside_prompt.write_text("<prompt>outside</prompt>\n", encoding="utf-8")
    code = project / "src" / "widget.py"
    code.parent.mkdir()
    code.write_text("def widget() -> None:\n    pass\n", encoding="utf-8")
    monkeypatch.chdir(project)

    result = runner.invoke(
        checkup,
        [
            "drift",
            str(outside_prompt),
            "--code-file",
            str(code),
            "--dry-run",
            "--json",
        ],
        catch_exceptions=False,
    )

    assert result.exit_code == 1
    payload = json.loads(result.output)
    assert payload["status"] == "error"
    assert payload["error"]["code"] == "drift_input_outside_project"


def test_checkup_drift_rejects_explicit_code_outside_project_root(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    project = tmp_path / "project"
    prompt = project / "prompts" / "widget_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("<prompt>widget</prompt>\n", encoding="utf-8")
    outside_code = tmp_path / "widget.py"
    outside_code.write_text("def widget() -> None:\n    pass\n", encoding="utf-8")
    monkeypatch.chdir(project)

    result = runner.invoke(
        checkup,
        [
            "drift",
            "prompts/widget_python.prompt",
            "--code-file",
            str(outside_code),
            "--dry-run",
            "--json",
        ],
        catch_exceptions=False,
    )

    assert result.exit_code == 1
    payload = json.loads(result.output)
    assert payload["error"]["code"] == "drift_input_outside_project"


def test_checkup_drift_rejects_ambiguous_nested_basename(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    code = tmp_path / "src" / "widget.py"
    code.parent.mkdir(parents=True)
    code.write_text("def widget() -> None:\n    pass\n", encoding="utf-8")
    for prompt_dir in ("specs/backend", "specs/frontend"):
        prompt = tmp_path / prompt_dir / "widget_python.prompt"
        prompt.parent.mkdir(parents=True)
        prompt.write_text("<prompt>widget</prompt>\n", encoding="utf-8")
    (tmp_path / ".pddrc").write_text(
        "version: '1.0'\n"
        "contexts:\n"
        "  backend:\n"
        "    defaults:\n"
        "      prompts_dir: specs/backend\n"
        "      default_language: python\n"
        "  frontend:\n"
        "    defaults:\n"
        "      prompts_dir: specs/frontend\n"
        "      default_language: python\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(
        checkup,
        [
            "drift",
            "widget",
            "--code-file",
            "src/widget.py",
            "--dry-run",
            "--json",
        ],
        catch_exceptions=False,
    )

    assert result.exit_code == 1
    payload = json.loads(result.output)
    assert payload["error"]["code"] == "drift_input_ambiguous"
    assert "specs/backend/widget_python.prompt" in payload["error"]["message"]
    assert "specs/frontend/widget_python.prompt" in payload["error"]["message"]


def test_checkup_drift_flat_prompt_control_without_manifest(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    prompt = tmp_path / "prompts" / "widget_python.prompt"
    prompt.parent.mkdir()
    prompt.write_text("<prompt>widget</prompt>\n", encoding="utf-8")
    code = tmp_path / "src" / "widget.py"
    code.parent.mkdir()
    code.write_text("def widget() -> str:\n    return 'ok'\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(
        checkup,
        ["drift", "widget", "--code-file", "src/widget.py", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert Path(payload["prompt_path"]) == prompt.resolve()
    assert Path(payload["code_path"]) == code.resolve()


def test_root_cli_preserves_structured_drift_json_failure(
    runner: CliRunner, tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.chdir(tmp_path)

    result = runner.invoke(
        cli,
        ["checkup", "drift", "missing_widget", "--dry-run", "--json"],
        catch_exceptions=False,
    )

    assert result.exit_code == 1
    payload = json.loads(result.output)
    assert payload["status"] == "error"
    assert payload["error"]["code"] == "drift_input_not_found"
