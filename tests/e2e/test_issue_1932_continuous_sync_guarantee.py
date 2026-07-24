"""Issue #1932 deterministic continuous-sync acceptance coverage."""
from __future__ import annotations

import json
import os
import signal
import subprocess
import sys
from pathlib import Path
from typing import Callable, Dict, List
from unittest.mock import Mock, patch

import pytest

from pdd import continuous_sync
from pdd.operation_log import save_fingerprint
from pdd.sync_determine_operation import get_pdd_file_paths


REPO_ROOT = Path(__file__).resolve().parents[2]
COMMAND_TIMEOUT_SECONDS = 30.0


def _env() -> Dict[str, str]:
    env = os.environ.copy()
    env["PYTHONPATH"] = os.pathsep.join(
        [str(REPO_ROOT), env.get("PYTHONPATH", "")]
    )
    env["PDD_AUTO_UPDATE"] = "false"
    env["PDD_FORCE_LOCAL"] = "1"
    env["NO_COLOR"] = "1"
    return env


def _terminate(process: subprocess.Popen[str]) -> None:
    try:
        if os.name == "posix":
            os.killpg(process.pid, signal.SIGKILL)
        else:  # pragma: no cover - exercised on Windows
            process.kill()
    except (ProcessLookupError, PermissionError):
        process.kill()


def _run(
    cwd: Path,
    args: List[str],
    *,
    check: bool = True,
    timeout: float = COMMAND_TIMEOUT_SECONDS,
) -> subprocess.CompletedProcess[str]:
    process = subprocess.Popen(
        args,
        cwd=str(cwd),
        env=_env(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=os.name == "posix",
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        _terminate(process)
        stdout, stderr = process.communicate()
        raise AssertionError(
            f"{args} timed out after {timeout}s\nSTDOUT:\n{stdout}\nSTDERR:\n{stderr}"
        ) from exc
    except BaseException:
        # pytest-timeout interrupts the active frame. Reap this command and any
        # descendants before preserving that external exception.
        _terminate(process)
        process.communicate()
        raise

    result = subprocess.CompletedProcess(
        args=args,
        returncode=process.returncode,
        stdout=stdout,
        stderr=stderr,
    )
    if check and result.returncode != 0:
        raise AssertionError(
            f"{args} failed with {result.returncode}\nSTDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}"
        )
    return result


def _git(cwd: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return _run(cwd, ["git", *args], check=check)


@pytest.mark.skipif(os.name != "posix", reason="requires POSIX process groups")
def test_run_timeout_kills_isolated_process_group(tmp_path: Path) -> None:
    """The test CLI wrapper must not orphan descendants when a child stalls."""
    process = Mock(pid=43210, returncode=None)
    process.communicate.side_effect = [
        subprocess.TimeoutExpired(cmd=["stalled"], timeout=0.01),
        ("partial stdout", "partial stderr"),
    ]

    with (
        patch.object(subprocess, "Popen", return_value=process) as popen,
        patch.object(os, "killpg") as killpg,
        pytest.raises(AssertionError, match="timed out after 0.01s"),
    ):
        _run(tmp_path, ["stalled"], timeout=0.01)

    assert popen.call_args.kwargs["start_new_session"] is True
    killpg.assert_called_once_with(process.pid, signal.SIGKILL)
    assert process.communicate.call_count == 2


@pytest.mark.skipif(os.name != "posix", reason="requires POSIX process groups")
def test_run_external_interrupt_kills_isolated_process_group(tmp_path: Path) -> None:
    """A global pytest timeout must not bypass child cleanup."""
    process = Mock(pid=43210, returncode=None)
    process.communicate.side_effect = [KeyboardInterrupt, ("", "")]

    with (
        patch.object(subprocess, "Popen", return_value=process),
        patch.object(os, "killpg") as killpg,
        pytest.raises(KeyboardInterrupt),
    ):
        _run(tmp_path, ["interrupted"])

    killpg.assert_called_once_with(process.pid, signal.SIGKILL)
    assert process.communicate.call_count == 2


def _pdd_json(cwd: Path, *args: str, check: bool = True) -> dict:
    result = _run(cwd, [sys.executable, "-m", "pdd", *args], check=check)
    start = result.stdout.find("{")
    assert start >= 0, f"expected JSON on stdout, got: {result.stdout!r}"
    return json.loads(result.stdout[start:])


def _ci_json(cwd: Path, check: bool = True) -> dict:
    result = _run(
        cwd,
        [sys.executable, "-m", "pdd.ci_drift_heal", "--dry-run", "--json"],
        check=check,
    )
    start = result.stdout.find("{")
    assert start >= 0, f"expected JSON on stdout, got: {result.stdout!r}"
    return json.loads(result.stdout[start:])


@pytest.fixture()
def pdd_project(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "issue-1932@example.com")
    _git(repo, "config", "user.name", "Issue 1932")

    for directory in ("prompts", "src", "examples", "tests", "docs", ".pdd/meta"):
        (repo / directory).mkdir(parents=True, exist_ok=True)

    (repo / ".pddrc").write_text(
        "contexts:\n"
        "  default:\n"
        "    paths: [\"**\"]\n"
        "    defaults:\n"
        "      prompts_dir: prompts\n",
        encoding="utf-8",
    )
    (repo / "architecture.json").write_text(
        json.dumps(
            [
                {
                    "filename": "widget_python.prompt",
                    "filepath": "src/widget.py",
                    "description": "Widget module",
                }
            ],
            indent=2,
        ),
        encoding="utf-8",
    )
    (repo / "prompts/widget_python.prompt").write_text(
        "Build a deterministic widget.\n<include>docs/widget.md</include>\n",
        encoding="utf-8",
    )
    (repo / "prompts/runtime_template_LLM.prompt").write_text(
        "Summarize the runtime context.\n",
        encoding="utf-8",
    )
    (repo / "prompts/unbaselined_helper_python.prompt").write_text(
        "Build an unbaselined helper.\n",
        encoding="utf-8",
    )
    (repo / "docs/widget.md").write_text("Widget docs v1\n", encoding="utf-8")
    (repo / "src/widget.py").write_text(
        "def value():\n    return 1\n",
        encoding="utf-8",
    )
    (repo / "examples/widget_example.py").write_text(
        "from src.widget import value\nprint(value())\n",
        encoding="utf-8",
    )
    (repo / "tests/test_widget.py").write_text(
        "from src.widget import value\n\n\ndef test_value():\n    assert value() == 1\n",
        encoding="utf-8",
    )

    old_cwd = Path.cwd()
    try:
        os.chdir(repo)
        paths = get_pdd_file_paths("widget", "python", "prompts")
        save_fingerprint("widget", "python", "fix", paths, 0.0, "baseline")
    finally:
        os.chdir(old_cwd)

    _git(repo, "add", ".")
    _git(repo, "commit", "-q", "-m", "baseline")
    _run(repo, [sys.executable, "-m", "pdd", "install-hooks"])
    return repo


def _unit_classification(report: dict) -> str:
    units = [unit for unit in report["units"] if unit["basename"] == "widget"]
    assert len(units) == 1
    return units[0]["classification"]


def _assert_all_consumers_classify(repo: Path, expected: str) -> None:
    reports = {
        "reconcile": _pdd_json(repo, "reconcile", "--json", "--ledger", check=False),
        "sync": _pdd_json(repo, "sync", "--dry-run", "--json"),
        "update": _pdd_json(repo, "update", "--all", "--dry-run", "--json"),
        "change": _pdd_json(repo, "change", "--preflight", "--json"),
        "ci": _ci_json(repo, check=False),
    }
    assert {name: _unit_classification(report) for name, report in reports.items()} == {
        "reconcile": expected,
        "sync": expected,
        "update": expected,
        "change": expected,
        "ci": expected,
    }


def _last_ledger_classification(repo: Path) -> str:
    ledger = repo / ".pdd/drift-ledger.jsonl"
    assert ledger.exists()
    lines = [line for line in ledger.read_text(encoding="utf-8").splitlines() if line]
    assert lines
    widget_entries = [
        json.loads(line) for line in lines if json.loads(line)["basename"] == "widget"
    ]
    assert widget_entries
    return widget_entries[-1]["classification"]


def _fingerprint(repo: Path) -> dict:
    return json.loads((repo / ".pdd/meta/widget_python.json").read_text(encoding="utf-8"))


def _write_fingerprint(repo: Path, fingerprint: dict) -> None:
    (repo / ".pdd/meta/widget_python.json").write_text(
        json.dumps(fingerprint, indent=2),
        encoding="utf-8",
    )


def test_issue_1932_complete_inventory_blocks_unbaselined_units(pdd_project: Path) -> None:
    reconcile = _pdd_json(
        pdd_project, "reconcile", "--json", "--strict", check=False
    )
    sync = _pdd_json(pdd_project, "sync", "--dry-run", "--json")
    update = _pdd_json(pdd_project, "update", "--all", "--dry-run", "--json")

    for report in (reconcile, sync, update):
        assert report["ok"] is False
        assert report["metadata_stale"] == 0
        assert report["summary"]["conflicts"] == 0
        assert report["summary"]["unbaselined"] == 2
        assert report["summary"]["total"] == 3
        assert {unit["basename"] for unit in report["units"]} == {
            "widget",
            "runtime_template",
            "unbaselined_helper",
        }


def test_issue_1996_mixed_contexts_keep_implicit_default_prompt_inventory(
    pdd_project: Path,
) -> None:
    (pdd_project / ".pddrc").write_text(
        "contexts:\n"
        "  default:\n"
        "    paths: ['**']\n"
        "    defaults: {}\n"
        "  frontend:\n"
        "    paths: ['frontend/**']\n"
        "    defaults:\n"
        "      prompts_dir: prompts/frontend\n",
        encoding="utf-8",
    )
    frontend = pdd_project / "prompts/frontend/card_typescript.prompt"
    frontend.parent.mkdir(parents=True, exist_ok=True)
    frontend.write_text("Build a card.\n", encoding="utf-8")

    report = _pdd_json(pdd_project, "sync", "--dry-run", "--json", check=False)

    assert report["ok"] is False
    assert {unit["basename"] for unit in report["units"]} >= {
        "widget",
        "unbaselined_helper",
        "card",
    }


def test_issue_1996_discovered_context_owns_configured_report_paths(
    pdd_project: Path,
) -> None:
    """Discovery must retain the context identity used for output resolution."""
    (pdd_project / ".pddrc").write_text(
        "contexts:\n"
        "  default:\n"
        "    paths: ['**']\n"
        "    defaults: {}\n"
        "  frontend:\n"
        "    paths: ['frontend/**']\n"
        "    defaults:\n"
        "      prompts_dir: prompts/frontend\n"
        "      outputs:\n"
        "        code: {path: 'web/{category}/{name}.{ext}'}\n"
        "        example: {path: 'demo/{category}/{name}_example.{ext}'}\n"
        "        test: {path: 'checks/{category}/test_{name}.{ext}'}\n",
        encoding="utf-8",
    )
    prompt = pdd_project / "prompts/frontend/components/AssetCard_typescriptreact.prompt"
    prompt.parent.mkdir(parents=True, exist_ok=True)
    prompt.write_text("Build an asset card.\n", encoding="utf-8")

    report = continuous_sync.build_report(consumer="sync", root=pdd_project)
    unit = next(
        item for item in report["units"]
        if item["paths"]["prompt"].endswith(prompt.name)
    )

    assert unit["paths"]["code"] == "web/components/AssetCard.tsx"
    assert unit["paths"]["example"] == "demo/components/AssetCard_example.tsx"
    assert unit["paths"]["test"] == "checks/components/test_AssetCard.tsx"


def test_issue_1996_read_only_resolver_uses_full_context_template_contract(
    pdd_project: Path,
) -> None:
    (pdd_project / ".pddrc").write_text(
        "contexts:\n"
        "  default:\n"
        "    paths: ['**']\n"
        "    defaults: {}\n"
        "  frontend:\n"
        "    paths: ['frontend/**']\n"
        "    defaults:\n"
        "      prompts_dir: prompts/frontend\n"
        "      outputs:\n"
        "        code:\n"
        "          path: 'web/{category}/{name}/{name_snake}-{name_pascal}-{name_kebab}.{ext}'\n"
        "        example:\n"
        "          path: 'demo/{dir_prefix}{name}.{ext}'\n",
        encoding="utf-8",
    )
    prompt = pdd_project / "prompts/frontend/components/AssetCard_typescriptreact.prompt"
    prompt.parent.mkdir(parents=True, exist_ok=True)
    prompt.write_text("Build an asset card.\n", encoding="utf-8")
    unit = continuous_sync.SyncUnit(
        basename="frontend/components/AssetCard",
        language="typescriptreact",
        prompt_path=prompt,
        prompts_dir=pdd_project / "prompts/frontend",
    )

    paths = continuous_sync._resolve_report_paths(unit, pdd_project)

    assert paths["code"] == pdd_project / "web/components/AssetCard/asset_card-Assetcard-asset-card.tsx"
    assert paths["example"] == pdd_project / "demo/components/AssetCard.tsx"


def test_issue_1996_object_architecture_uses_context_derived_artifact_paths(
    pdd_project: Path,
) -> None:
    (pdd_project / ".pddrc").write_text(
        "contexts:\n"
        "  frontend:\n"
        "    paths: ['frontend/**']\n"
        "    defaults:\n"
        "      prompts_dir: prompts/frontend\n"
        "      generate_output_path: web/src\n"
        "      example_output_path: web/examples\n"
        "      test_output_path: web/tests\n",
        encoding="utf-8",
    )
    nested = pdd_project / "prompts/frontend/admin"
    nested.mkdir(parents=True, exist_ok=True)
    prompt = nested / "page_typescriptreact.prompt"
    prompt.write_text("Build admin page.\n", encoding="utf-8")
    (pdd_project / "prompts/frontend/architecture.json").write_text(
        json.dumps({"modules": [{"filename": "admin/page_typescriptreact.prompt", "filepath": "page.tsx"}]}),
        encoding="utf-8",
    )
    unit = continuous_sync.SyncUnit(
        basename="frontend/admin/page",
        language="typescriptreact",
        prompt_path=prompt,
        prompts_dir=pdd_project / "prompts/frontend",
    )

    paths = continuous_sync._resolve_report_paths(unit, pdd_project)

    assert paths["code"] == pdd_project / "prompts/frontend/web/src/page.tsx"
    assert paths["example"] == pdd_project / "prompts/frontend/web/examples/page_example.tsx"
    assert paths["test"] == pdd_project / "prompts/frontend/web/tests/test_page.tsx"


def test_issue_1996_nested_architecture_anchors_qualified_filepath_at_owner(
    pdd_project: Path,
) -> None:
    nested = pdd_project / "packages/store"
    prompt = nested / "prompts/pages/cart_typescriptreact.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("Build cart.\n", encoding="utf-8")
    (nested / "architecture.json").write_text(
        json.dumps([
            {
                "filename": "pages/cart_typescriptreact.prompt",
                "filepath": "src/pages/cart.tsx",
            }
        ]),
        encoding="utf-8",
    )
    unit = continuous_sync.SyncUnit(
        "pages/cart", "typescriptreact", prompt, nested / "prompts"
    )

    paths = continuous_sync._resolve_report_paths(unit, pdd_project)

    assert paths["code"] == nested / "src/pages/cart.tsx"


def test_issue_1996_qualified_prompt_rejects_wrong_directory_architecture_leaf(
    pdd_project: Path,
) -> None:
    prompt = pdd_project / "prompts/bar/page_typescriptreact.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("Build bar page.\n", encoding="utf-8")
    (pdd_project / "architecture.json").write_text(
        json.dumps([
            {
                "filename": "foo/page_typescriptreact.prompt",
                "filepath": "src/foo/page.tsx",
            }
        ]),
        encoding="utf-8",
    )
    unit = continuous_sync.SyncUnit(
        "bar/page", "typescriptreact", prompt, pdd_project / "prompts"
    )

    paths = continuous_sync._resolve_report_paths(unit, pdd_project)

    assert paths["code"] == pdd_project / "bar/page.tsx"


def test_issue_1996_report_templates_do_not_inspect_unvalidated_external_paths(
    pdd_project: Path,
) -> None:
    outside = pdd_project.parent / "outside"
    outside.mkdir()
    (pdd_project / ".pddrc").write_text(
        "contexts:\n  app:\n    paths: ['app/**']\n    defaults:\n"
        "      prompts_dir: prompts/app\n      outputs:\n"
        f"        prompt: {{path: '{outside}/{{name}}_{{language}}.prompt'}}\n"
        f"        test: {{path: '{outside}/test_{{name}}.{{ext}}'}}\n",
        encoding="utf-8",
    )
    prompt = pdd_project / "prompts/app/widget_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("Build widget.\n", encoding="utf-8")
    unit = continuous_sync.SyncUnit("app/widget", "python", prompt, prompt.parent)

    with patch(
        "pdd.sync_main._case_insensitive_prompt_lookup",
        side_effect=AssertionError("external prompt lookup occurred"),
    ) as lookup:
        with pytest.raises(ValueError, match="outside project"):
            continuous_sync._resolve_report_paths(unit, pdd_project)

    lookup.assert_not_called()


def test_issue_1996_duplicate_architecture_leaves_get_distinct_derived_stems(
    pdd_project: Path,
) -> None:
    architecture = {
        "modules": [
            {"filename": "admin/page_typescriptreact.prompt", "filepath": "app/admin/page.tsx"},
            {"filename": "settings/page_typescriptreact.prompt", "filepath": "app/settings/page.tsx"},
        ]
    }
    (pdd_project / "architecture.json").write_text(json.dumps(architecture), encoding="utf-8")
    prompt = pdd_project / "prompts/admin/page_typescriptreact.prompt"
    prompt.parent.mkdir(parents=True, exist_ok=True)
    prompt.write_text("Build admin page.\n", encoding="utf-8")
    unit = continuous_sync.SyncUnit(
        basename="admin/page",
        language="typescriptreact",
        prompt_path=prompt,
        prompts_dir=pdd_project / "prompts",
    )

    paths = continuous_sync._resolve_report_paths(unit, pdd_project)

    assert paths["example"] == pdd_project / "examples/app_admin_page_example.tsx"
    assert paths["test"] == pdd_project / "tests/test_app_admin_page.tsx"


@pytest.mark.skipif(not hasattr(os, "symlink"), reason="symlink unavailable")
def test_issue_1996_nested_pddrc_symlink_fails_before_identity_read(
    pdd_project: Path,
) -> None:
    nested = pdd_project / "prompts/sub"
    nested.mkdir()
    (nested / "thing_python.prompt").write_text("Build thing.\n", encoding="utf-8")
    outside = pdd_project.parent / "outside-pddrc"
    outside.write_text("contexts: {}\n", encoding="utf-8")
    os.symlink(outside, nested / ".pddrc")

    report = _pdd_json(pdd_project, "sync", "--dry-run", "--json", check=False)

    assert report["ok"] is False
    assert any(item["failure"] == "unsafe_config" for item in report["failures"])
    assert all(item["basename"] != "sub/thing" for item in report["units"])


def test_issue_1996_metadata_units_share_command_discovery_budget(
    pdd_project: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(continuous_sync, "MAX_PROMPT_DISCOVERY_FILES", 4)
    meta = pdd_project / ".pdd/meta"
    for index in range(8):
        (meta / f"extra_{index}_python.json").write_text("{}", encoding="utf-8")

    report = continuous_sync.build_report(consumer="sync", root=pdd_project)

    assert report["ok"] is False
    assert report["summary"]["total"] <= 5
    assert any(item["failure"] == "discovery_budget" for item in report["failures"])


def test_issue_1996_metadata_enumeration_stops_at_remaining_budget(
    pdd_project: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    meta = pdd_project / ".pdd/meta"
    enumerated = 0
    real_scandir = os.scandir

    def observing_scandir(path: Path):
        nonlocal enumerated
        if path != meta:
            return real_scandir(path)
        iterator = real_scandir(path)

        class Observed:
            def __enter__(self):
                return self

            def __exit__(self, *_args):
                iterator.close()

            def __iter__(self):
                return self

            def __next__(self):
                nonlocal enumerated
                entry = next(iterator)
                enumerated += 1
                return entry

        return Observed()

    for index in range(20):
        (meta / f"candidate_{index}_python.json").write_text("{}", encoding="utf-8")
    monkeypatch.setattr(continuous_sync.os, "scandir", observing_scandir)
    monkeypatch.setattr(continuous_sync, "MAX_PROMPT_DISCOVERY_ENTRIES", 2)

    _identities, failure = continuous_sync._metadata_identities(
        meta, pdd_project, {"entries": 0, "files": 0}
    )

    assert failure is not None and failure.failure == "discovery_budget"
    assert enumerated == 3


DRIFT_CASES = [
    (
        "doc",
        "docs/widget.md",
        lambda p: p.write_text("Widget docs v2\n", encoding="utf-8"),
        "DOC_CHANGED",
    ),
    (
        "prompt",
        "prompts/widget_python.prompt",
        lambda p: p.write_text(
            "Build a deterministic widget with a new requirement.\n"
            "<include>docs/widget.md</include>\n",
            encoding="utf-8",
        ),
        "PROMPT_CHANGED",
    ),
    (
        "code",
        "src/widget.py",
        lambda p: p.write_text("def value():\n    return 2\n", encoding="utf-8"),
        "CODE_CHANGED",
    ),
    (
        "test",
        "tests/test_widget.py",
        lambda p: p.write_text(
            "from src.widget import value\n\n\ndef test_value():\n    assert value() in {1, 2}\n",
            encoding="utf-8",
        ),
        "TEST_CHANGED",
    ),
]


@pytest.mark.parametrize(("name", "path", "edit", "classification"), DRIFT_CASES)
@pytest.mark.timeout(90)
def test_issue_1932_all_consumers_classify_without_blind_healing(
    pdd_project: Path,
    name: str,
    path: str,
    edit: Callable[[Path], None],
    classification: str,
) -> None:
    edit(pdd_project / path)
    _git(pdd_project, "add", path)
    _git(pdd_project, "commit", "-q", "-m", f"{name} drift")

    _assert_all_consumers_classify(pdd_project, classification)
    assert _last_ledger_classification(pdd_project) == classification


@pytest.mark.parametrize(
    ("path", "edit"),
    [(path, edit) for _name, path, edit, _classification in DRIFT_CASES],
)
def test_issue_1932_reconcile_heal_is_disabled_without_metadata_mutation(
    pdd_project: Path,
    path: str,
    edit: Callable[[Path], None],
) -> None:
    edit(pdd_project / path)

    fingerprint_before = (pdd_project / ".pdd/meta/widget_python.json").read_text(
        encoding="utf-8"
    )
    refused = _run(
        pdd_project,
        [sys.executable, "-m", "pdd", "reconcile", "--json", "--heal"],
        check=False,
    )
    assert refused.returncode != 0
    assert "--heal is disabled" in refused.stderr
    assert (pdd_project / ".pdd/meta/widget_python.json").read_text(
        encoding="utf-8"
    ) == fingerprint_before


def test_issue_1932_unbaselined_fingerprints_are_not_stamped(pdd_project: Path) -> None:
    fingerprint_path = pdd_project / ".pdd/meta/widget_python.json"

    original = fingerprint_path.read_text(encoding="utf-8")
    fingerprint_path.unlink()
    missing = _pdd_json(
        pdd_project,
        "reconcile",
        "--json",
        "--strict",
        "--module",
        "widget",
        check=False,
    )
    assert missing["ok"] is False
    assert missing["unbaselined"][0]["classification"] == "UNBASELINED"
    assert not fingerprint_path.exists()

    fingerprint_path.write_text("{not-json", encoding="utf-8")
    invalid = _pdd_json(
        pdd_project,
        "reconcile",
        "--json",
        "--strict",
        "--module",
        "widget",
        check=False,
    )
    assert invalid["ok"] is False
    assert invalid["unbaselined"][0]["reason"] == "fingerprint invalid"
    assert fingerprint_path.read_text(encoding="utf-8") == "{not-json"

    fingerprint_path.write_text(original, encoding="utf-8")


def test_issue_1932_prompt_code_coedit_is_conflict_without_data_loss(pdd_project: Path) -> None:
    fingerprint_before = (pdd_project / ".pdd/meta/widget_python.json").read_text(encoding="utf-8")
    prompt_path = pdd_project / "prompts/widget_python.prompt"
    prompt_text = (
        "Build a deterministic widget with a conflicting prompt change.\n"
        "<include>docs/widget.md</include>\n"
    )
    prompt_path.write_text(prompt_text, encoding="utf-8")
    (pdd_project / "src/widget.py").write_text(
        "def value():\n    return 99\n",
        encoding="utf-8",
    )

    _assert_all_consumers_classify(pdd_project, "CONFLICT")
    conflict = _pdd_json(pdd_project, "reconcile", "--json", "--strict", check=False)
    assert conflict["ok"] is False
    assert conflict["conflicts"][0]["operation"] == "conflict"
    assert (pdd_project / ".pdd/meta/widget_python.json").read_text(encoding="utf-8") == fingerprint_before
    assert prompt_path.read_text(encoding="utf-8") == prompt_text


def test_issue_1932_incomplete_metadata_reports_failure_not_success(pdd_project: Path) -> None:
    fingerprint_path = pdd_project / ".pdd/meta/widget_python.json"
    fingerprint = _fingerprint(pdd_project)
    fingerprint["code_hash"] = None
    _write_fingerprint(pdd_project, fingerprint)

    report = _pdd_json(pdd_project, "reconcile", "--json", "--strict", check=False)
    assert report["ok"] is False
    assert report["failures"][0]["classification"] == "FAILURE"
    assert report["failures"][0]["failure"] == "incomplete_metadata"


@pytest.mark.parametrize(
    ("dep_factory", "expected_reason"),
    [
        (
            lambda repo: repo.parent / "outside.md",
            "outside_project",
        ),
        (
            lambda _repo: "../outside.md",
            "outside_project",
        ),
        (
            lambda repo: repo / "docs" / "missing.md",
            "missing",
        ),
    ],
)
def test_issue_1996_legacy_include_deps_reject_unsafe_paths_before_hashing(
    pdd_project: Path,
    monkeypatch: pytest.MonkeyPatch,
    dep_factory: Callable[[Path], object],
    expected_reason: str,
) -> None:
    dep_path = dep_factory(pdd_project)
    if isinstance(dep_path, Path) and dep_path.name == "outside.md":
        dep_path.write_text("outside bytes must not be read\n", encoding="utf-8")
    if dep_path == "../outside.md":
        (pdd_project.parent / "outside.md").write_text(
            "outside bytes must not be read\n",
            encoding="utf-8",
        )

    fingerprint = _fingerprint(pdd_project)
    fingerprint["include_deps"] = {str(dep_path): "stored-hash"}
    _write_fingerprint(pdd_project, fingerprint)

    def fail_if_hashing_reached(*_args: object, **_kwargs: object) -> dict:
        raise AssertionError("unsafe include deps reached current hash calculation")

    monkeypatch.setattr(
        continuous_sync,
        "calculate_current_hashes",
        fail_if_hashing_reached,
    )

    result = continuous_sync.classify_unit(
        continuous_sync.SyncUnit(
            basename="widget",
            language="python",
            prompt_path=pdd_project / "prompts/widget_python.prompt",
            prompts_dir=pdd_project / "prompts",
        ),
        pdd_project,
    )

    assert result["classification"] == "FAILURE"
    assert result["failure"] == "unsafe_include_deps"
    assert result["unsafe_include_deps"] == [
        {"path": str(dep_path), "reason": expected_reason}
    ]


@pytest.mark.skipif(not hasattr(os, "symlink"), reason="symlink unavailable")
def test_issue_1996_legacy_include_deps_reject_symlink_before_hashing(
    pdd_project: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    target = pdd_project / "docs" / "target.md"
    target.write_text("target bytes must not be read through symlink\n", encoding="utf-8")
    link = pdd_project / "docs" / "link.md"
    os.symlink(target, link)

    fingerprint = _fingerprint(pdd_project)
    fingerprint["include_deps"] = {str(link): "stored-hash"}
    _write_fingerprint(pdd_project, fingerprint)

    monkeypatch.setattr(
        continuous_sync,
        "calculate_current_hashes",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("symlink include dep reached current hash calculation")
        ),
    )

    result = continuous_sync.classify_unit(
        continuous_sync.SyncUnit(
            basename="widget",
            language="python",
            prompt_path=pdd_project / "prompts/widget_python.prompt",
            prompts_dir=pdd_project / "prompts",
        ),
        pdd_project,
    )

    assert result["classification"] == "FAILURE"
    assert result["failure"] == "unsafe_include_deps"
    assert result["unsafe_include_deps"] == [
        {"path": str(link), "reason": "symlink"}
    ]


@pytest.mark.skipif(not hasattr(os, "mkfifo"), reason="FIFO unavailable")
def test_issue_1996_legacy_include_deps_reject_fifo_before_hashing(
    pdd_project: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fifo = pdd_project / "docs" / "dep.fifo"
    os.mkfifo(fifo)

    fingerprint = _fingerprint(pdd_project)
    fingerprint["include_deps"] = {str(fifo): "stored-hash"}
    _write_fingerprint(pdd_project, fingerprint)

    monkeypatch.setattr(
        continuous_sync,
        "calculate_current_hashes",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("FIFO include dep reached current hash calculation")
        ),
    )

    result = continuous_sync.classify_unit(
        continuous_sync.SyncUnit(
            basename="widget",
            language="python",
            prompt_path=pdd_project / "prompts/widget_python.prompt",
            prompts_dir=pdd_project / "prompts",
        ),
        pdd_project,
    )

    assert result["classification"] == "FAILURE"
    assert result["failure"] == "unsafe_include_deps"
    assert result["unsafe_include_deps"] == [
        {"path": str(fifo), "reason": "nonregular"}
    ]


@pytest.mark.parametrize("include_deps", [["docs/widget.md"], "docs/widget.md", {"docs/widget.md": 7}])
def test_issue_1996_malformed_include_deps_report_failure_json(
    pdd_project: Path,
    include_deps: object,
) -> None:
    fingerprint = _fingerprint(pdd_project)
    fingerprint["include_deps"] = include_deps
    _write_fingerprint(pdd_project, fingerprint)

    report = _pdd_json(pdd_project, "sync", "--dry-run", "--json", check=False)

    widget = next(unit for unit in report["units"] if unit["basename"] == "widget")
    assert widget["classification"] == "FAILURE"
    assert widget["failure"] == "unsafe_include_deps"
    assert widget["metadata_valid"] is False


@pytest.mark.skipif(not hasattr(os, "symlink"), reason="symlink unavailable")
def test_issue_1996_symlinked_metadata_ancestor_reports_failure_without_reading(
    pdd_project: Path,
) -> None:
    meta = pdd_project / ".pdd" / "meta"
    outside_meta = pdd_project.parent / "outside-meta"
    meta.rename(outside_meta)
    os.symlink(outside_meta, meta)

    report = _pdd_json(pdd_project, "sync", "--dry-run", "--json", check=False)

    assert report["ok"] is False
    assert any(item["failure"] == "unsafe_metadata" for item in report["failures"])
    assert all(item["basename"] != "widget" for item in report["units"])


@pytest.mark.parametrize(
    "pddrc",
    [
        "contexts: []\n",
        "contexts:\n  default:\n    defaults: []\n",
        "contexts: [\n",
    ],
)
def test_issue_1996_invalid_pddrc_reports_discovery_failure_json(
    pdd_project: Path,
    pddrc: str,
) -> None:
    (pdd_project / ".pddrc").write_text(pddrc, encoding="utf-8")

    report = _pdd_json(pdd_project, "sync", "--dry-run", "--json", check=False)

    assert report["ok"] is False
    assert any(item["failure"] == "invalid_pddrc" for item in report["failures"])
    assert all(item["basename"] != "widget" for item in report["units"])


def test_issue_1932_deleted_generated_artifact_is_failure_not_in_sync(
    pdd_project: Path,
) -> None:
    fingerprint_before = (pdd_project / ".pdd/meta/widget_python.json").read_text(encoding="utf-8")
    (pdd_project / "src/widget.py").unlink()

    report = _pdd_json(pdd_project, "reconcile", "--json", "--strict", check=False)
    assert report["ok"] is False
    assert report["summary"]["failures"] == 1
    assert report["failures"][0]["classification"] == "FAILURE"
    assert report["failures"][0]["failure"] == "missing_artifacts"
    assert report["failures"][0]["changed_files"] == ["code"]

    refused = _run(
        pdd_project,
        [sys.executable, "-m", "pdd", "reconcile", "--json", "--heal"],
        check=False,
    )
    assert refused.returncode != 0
    assert (pdd_project / ".pdd/meta/widget_python.json").read_text(encoding="utf-8") == fingerprint_before


def test_issue_1996_symlinked_generated_artifact_is_failure_not_in_sync(
    pdd_project: Path,
    tmp_path: Path,
) -> None:
    outside = tmp_path / "outside-widget.py"
    outside.write_text(
        (pdd_project / "src/widget.py").read_text(encoding="utf-8"),
        encoding="utf-8",
    )
    artifact = pdd_project / "src/widget.py"
    artifact.unlink()
    try:
        artifact.symlink_to(outside)
    except OSError as exc:  # pragma: no cover - platform permission guard
        pytest.skip(f"symlink creation unavailable: {exc}")

    report = _pdd_json(
        pdd_project,
        "reconcile",
        "--json",
        "--strict",
        "--module",
        "widget",
        check=False,
    )
    assert report["ok"] is False
    assert report["summary"]["synced"] == 0
    assert report["failures"][0]["classification"] == "FAILURE"
    assert report["failures"][0]["failure"] == "unsafe_artifacts"
    assert report["failures"][0]["changed_files"] == ["code"]
    assert "code is a symlink" in report["failures"][0]["reason"]


def test_issue_1932_deleted_canonical_artifact_is_not_masked_by_duplicate(
    pdd_project: Path,
) -> None:
    archive_path = pdd_project / "archive/widget.py"
    archive_path.parent.mkdir()
    archive_path.write_text(
        (pdd_project / "src/widget.py").read_text(encoding="utf-8"),
        encoding="utf-8",
    )
    (pdd_project / "src/widget.py").unlink()

    report = _pdd_json(
        pdd_project,
        "reconcile",
        "--json",
        "--strict",
        "--module",
        "widget",
        check=False,
    )
    assert report["ok"] is False
    assert report["failures"][0]["failure"] == "missing_artifacts"
    assert report["failures"][0]["changed_files"] == ["code"]
    assert report["failures"][0]["paths"]["code"] == "src/widget.py"


def test_issue_1932_deleted_prompt_stays_discovered_from_metadata(
    pdd_project: Path,
) -> None:
    (pdd_project / "prompts/widget_python.prompt").unlink()

    default_report = _pdd_json(
        pdd_project,
        "reconcile",
        "--json",
        "--strict",
        check=False,
    )
    assert default_report["ok"] is False
    assert default_report["summary"]["total"] == 3
    assert default_report["failures"][0]["failure"] == "missing_artifacts"
    assert default_report["failures"][0]["changed_files"] == ["prompt"]

    explicit_report = _pdd_json(
        pdd_project,
        "reconcile",
        "--json",
        "--strict",
        "--module",
        "widget",
        check=False,
    )
    assert explicit_report["ok"] is False
    assert explicit_report["summary"]["total"] == 1
    assert explicit_report["failures"][0]["failure"] == "missing_artifacts"


def test_issue_1932_path_qualified_deleted_prompt_matches_module_scope(
    pdd_project: Path,
) -> None:
    prompt_path = pdd_project / "prompts/commands/foo_python.prompt"
    prompt_path.parent.mkdir(parents=True)
    prompt_path.write_text("Build a command foo module.\n", encoding="utf-8")

    old_cwd = Path.cwd()
    try:
        os.chdir(pdd_project)
        paths = get_pdd_file_paths("commands/foo", "python", "prompts")
        paths["code"].parent.mkdir(parents=True, exist_ok=True)
        paths["example"].parent.mkdir(parents=True, exist_ok=True)
        paths["test"].parent.mkdir(parents=True, exist_ok=True)
        paths["code"].write_text("def value():\n    return 1\n", encoding="utf-8")
        paths["example"].write_text(
            "from commands.foo import value\nprint(value())\n",
            encoding="utf-8",
        )
        paths["test"].write_text(
            "from commands.foo import value\n\n\ndef test_value():\n    assert value() == 1\n",
            encoding="utf-8",
        )
        save_fingerprint("commands/foo", "python", "fix", paths, 0.0, "baseline")
    finally:
        os.chdir(old_cwd)

    prompt_path.unlink()

    reconcile = _pdd_json(
        pdd_project,
        "reconcile",
        "--json",
        "--strict",
        "--module",
        "commands/foo",
        check=False,
    )
    assert reconcile["ok"] is False
    assert reconcile["summary"]["total"] == 1
    assert reconcile["failures"][0]["basename"] == "commands/foo"
    assert reconcile["failures"][0]["changed_files"] == ["prompt"]
    assert reconcile["failures"][0]["paths"]["prompt"] == "prompts/commands/foo_python.prompt"

    sync = _pdd_json(
        pdd_project,
        "sync",
        "commands/foo",
        "--dry-run",
        "--json",
        check=False,
    )
    assert sync["ok"] is False
    assert sync["summary"]["total"] == 1
    assert sync["failures"][0]["basename"] == "commands/foo"


def test_issue_1932_install_hooks_supports_git_worktrees(pdd_project: Path) -> None:
    worktree = pdd_project.parent / "repo-worktree"
    _git(pdd_project, "worktree", "add", "-q", "-b", "hook-worktree", str(worktree))

    _run(worktree, [sys.executable, "-m", "pdd", "install-hooks", "--force"])
    hook_path_raw = _git(worktree, "rev-parse", "--git-path", "hooks/pre-commit").stdout.strip()
    hook_path = Path(hook_path_raw)
    if not hook_path.is_absolute():
        hook_path = worktree / hook_path

    assert hook_path.exists()
    assert "# pdd continuous-sync drift ledger" in hook_path.read_text(encoding="utf-8")
