"""Tests for the ``pdd resolve`` command (#1929).

``pdd resolve`` finalizes a both-changed CONFLICT unit:
* ``--accept-current`` deterministically stamps the current tree as the baseline;
* ``--prompt-wins`` / ``--code-wins`` preview the not-yet-automated LLM strategies.

The setup builds a real on-disk unit with a committed fingerprint, then co-edits
the prompt and the code so the unit classifies as CONFLICT — the exact state the
command exists to resolve.
"""
from __future__ import annotations

import json
import os
from datetime import datetime, timezone
from pathlib import Path
from typing import Tuple

from click.testing import CliRunner

from pdd.commands.resolve import resolve
from pdd.sync_determine_operation import (
    calculate_sha256,
    get_pdd_file_paths,
    read_fingerprint,
)

BASENAME = "widget"
LANGUAGE = "python"


def _write(path: Path, content: str) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return calculate_sha256(path)


def _make_conflict_unit(base: Path) -> Tuple[str, str, Path]:
    """Create a synced unit then co-edit prompt + code so it becomes CONFLICT."""
    os.chdir(base)
    (base / ".pdd" / "meta").mkdir(parents=True, exist_ok=True)
    (base / "prompts").mkdir(exist_ok=True)

    prompt_hash = _write(
        base / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt",
        "Generate a simple function.\n",
    )
    paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir="prompts")
    code_hash = _write(Path(paths["code"]), "def value():\n    return 1\n")
    example_hash = _write(Path(paths["example"]), "print(1)\n")
    test_hash = _write(Path(paths["test"]), "def test_v():\n    assert True\n")

    fp_path = base / ".pdd" / "meta" / f"{BASENAME}_{LANGUAGE}.json"
    fp_path.write_text(
        json.dumps(
            {
                "pdd_version": "test",
                "timestamp": datetime.now(timezone.utc).isoformat(),
                "command": "fix",
                "prompt_hash": prompt_hash,
                "code_hash": code_hash,
                "example_hash": example_hash,
                "test_hash": test_hash,
                "test_files": {Path(paths["test"]).name: test_hash},
                "include_deps": {},
            }
        ),
        encoding="utf-8",
    )

    # Co-edit BOTH the prompt and the code -> both-changed CONFLICT.
    _write(
        base / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt",
        "Generate a CHANGED function.\n",
    )
    _write(Path(paths["code"]), "def value():\n    return 2\n")
    return BASENAME, LANGUAGE, fp_path


def _make_code_only_drift_unit(base: Path) -> Tuple[str, str, Path]:
    """Create a synced unit then edit ONLY the code -> single-sided DRIFT (not CONFLICT)."""
    _make_conflict_unit(base)
    fp_path = base / ".pdd" / "meta" / f"{BASENAME}_{LANGUAGE}.json"
    paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir="prompts")
    # Re-sync by stamping current, then edit only the code so the prompt is unchanged.
    runner = CliRunner()
    runner.invoke(resolve, [BASENAME, "--accept-current"], obj={})
    _write(Path(paths["code"]), "def value():\n    return 99\n")
    return BASENAME, LANGUAGE, fp_path


def test_accept_current_refuses_code_only_drift(tmp_path):
    """#1969 review finding 2: --accept-current must NOT silently baseline single-sided
    drift; it directs the user to pdd update / pdd sync instead and does not stamp."""
    runner = CliRunner()
    with runner.isolated_filesystem() as tmp:
        base = Path(tmp)
        _make_code_only_drift_unit(base)
        paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir="prompts")
        before = read_fingerprint(BASENAME, LANGUAGE, paths=paths)

        result = runner.invoke(resolve, [BASENAME, "--accept-current"], obj={})

        assert result.exit_code == 2, result.output
        assert "not a CONFLICT" in result.output
        assert "pdd update" in result.output and "pdd sync" in result.output
        # Fingerprint is NOT changed by the refused resolve.
        after = read_fingerprint(BASENAME, LANGUAGE, paths=paths)
        assert after.code_hash == before.code_hash


def test_force_stamps_code_only_drift(tmp_path):
    """--force is the explicit escape hatch to accept current-as-truth on drift."""
    runner = CliRunner()
    with runner.isolated_filesystem() as tmp:
        base = Path(tmp)
        _make_code_only_drift_unit(base)
        paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir="prompts")
        current = calculate_sha256(Path(paths["code"]))

        result = runner.invoke(resolve, [BASENAME, "--accept-current", "--force"], obj={})

        assert result.exit_code == 0, result.output
        after = read_fingerprint(BASENAME, LANGUAGE, paths=paths)
        assert after.code_hash == current


def test_accept_current_noop_when_already_in_sync(tmp_path):
    runner = CliRunner()
    with runner.isolated_filesystem() as tmp:
        base = Path(tmp)
        _make_conflict_unit(base)
        runner.invoke(resolve, [BASENAME, "--accept-current"], obj={})  # -> IN_SYNC
        result = runner.invoke(resolve, [BASENAME, "--accept-current"], obj={})
        assert result.exit_code == 0, result.output
        assert "already in sync" in result.output


def test_accept_current_resolves_conflict_to_in_sync():
    runner = CliRunner()
    with runner.isolated_filesystem() as tmp:
        base = Path(tmp)
        _make_conflict_unit(base)

        result = runner.invoke(resolve, [BASENAME, "--accept-current"], obj={})

        assert result.exit_code == 0, result.output
        assert "Resolved 'widget'" in result.output
        # Idempotent: a second accept-current now sees the unit already IN_SYNC.
        again = runner.invoke(resolve, [BASENAME, "--accept-current", "--json"], obj={})
        assert json.loads(again.output)["before"] == "IN_SYNC"


def test_accept_current_stamps_the_current_tree_not_the_old_baseline():
    """The new baseline must fingerprint the CHANGED code (return 2), not the old."""
    runner = CliRunner()
    with runner.isolated_filesystem() as tmp:
        base = Path(tmp)
        _, _, fp_path = _make_conflict_unit(base)
        paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir="prompts")
        current_code_hash = calculate_sha256(Path(paths["code"]))

        result = runner.invoke(resolve, [BASENAME, "--accept-current"], obj={})

        assert result.exit_code == 0, result.output
        # Fingerprint is preserved (never deleted) and now matches the current code.
        assert fp_path.exists()
        fingerprint = read_fingerprint(BASENAME, LANGUAGE, paths=paths)
        assert fingerprint is not None
        assert fingerprint.code_hash == current_code_hash


def test_accept_current_json_reports_before_and_after():
    runner = CliRunner()
    with runner.isolated_filesystem() as tmp:
        base = Path(tmp)
        _make_conflict_unit(base)

        result = runner.invoke(
            resolve, [BASENAME, "--accept-current", "--json"], obj={}
        )

        assert result.exit_code == 0, result.output
        payload = json.loads(result.output)
        assert payload["resolved"] is True
        assert payload["before"] == "CONFLICT"
        assert payload["after"] == "IN_SYNC"
        assert payload["strategy"] == "accept-current"


def test_prompt_wins_is_a_documented_stub_that_exits_nonzero():
    runner = CliRunner()
    with runner.isolated_filesystem() as tmp:
        _make_conflict_unit(Path(tmp))

        result = runner.invoke(resolve, [BASENAME, "--prompt-wins"], obj={})

        assert result.exit_code == 2
        assert "not yet automated" in result.output
        assert "pdd sync widget" in result.output


def test_code_wins_is_a_documented_stub_that_exits_nonzero():
    runner = CliRunner()
    with runner.isolated_filesystem() as tmp:
        _make_conflict_unit(Path(tmp))

        result = runner.invoke(resolve, [BASENAME, "--code-wins"], obj={})

        assert result.exit_code == 2
        assert "not yet automated" in result.output
        # code-wins previews `pdd update <code file path>` (pdd update takes a file,
        # not a basename — #1969 review pass 2 finding 1).
        assert "pdd update " in result.output
        assert f"{BASENAME}.py" in result.output


def test_stub_previews_do_not_mutate_the_fingerprint():
    """A preview strategy must not change the on-disk baseline."""
    runner = CliRunner()
    with runner.isolated_filesystem() as tmp:
        base = Path(tmp)
        _, _, fp_path = _make_conflict_unit(base)
        before = fp_path.read_text(encoding="utf-8")

        runner.invoke(resolve, [BASENAME, "--prompt-wins"], obj={})

        assert fp_path.read_text(encoding="utf-8") == before
        # Still a conflict after a no-op preview (probed via the command itself).
        probe = runner.invoke(resolve, [BASENAME, "--accept-current", "--json"], obj={})
        assert json.loads(probe.output)["before"] == "CONFLICT"


def test_requires_exactly_one_strategy():
    runner = CliRunner()
    with runner.isolated_filesystem() as tmp:
        _make_conflict_unit(Path(tmp))

        none_chosen = runner.invoke(resolve, [BASENAME], obj={})
        assert none_chosen.exit_code == 2
        assert "exactly one" in none_chosen.output

        two_chosen = runner.invoke(
            resolve, [BASENAME, "--accept-current", "--prompt-wins"], obj={}
        )
        assert two_chosen.exit_code == 2
        assert "exactly one" in two_chosen.output


def test_unknown_unit_errors_without_stamping():
    runner = CliRunner()
    with runner.isolated_filesystem() as tmp:
        _make_conflict_unit(Path(tmp))

        result = runner.invoke(
            resolve, ["does_not_exist", "--accept-current"], obj={}
        )

        assert result.exit_code != 0
        assert "No PDD unit" in result.output
