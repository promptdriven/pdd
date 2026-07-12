"""Regression tests for authoritative Step 8.5 update pairs (issue #2004)."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.agentic_change_orchestrator import _preflight_drift_heal
from pdd.ci_drift_heal import DriftInfo


def _drift(*, prompt_path: str | None, code_path: str | None) -> DriftInfo:
    return DriftInfo(
        basename="hackathon_event_detail_page",
        language="typescriptreact",
        operation="update",
        reason="code hash changed",
        prompt_path=prompt_path,
        code_path=code_path,
    )


def test_preflight_passes_the_exact_authoritative_pair_to_true_update(tmp_path: Path) -> None:
    drift = _drift(
        prompt_path="prompts/hackathon_event_detail_page_TypeScriptReact.prompt",
        code_path="frontend/src/app/hackathon/[eventId]/page.tsx",
    )
    completed = subprocess.CompletedProcess(args=[], returncode=0, stdout="", stderr="")

    with patch("pdd.ci_drift_heal.detect_drift", return_value=([drift], [])), patch(
        "pdd.agentic_change_orchestrator.subprocess.run", return_value=completed
    ) as run:
        healed, failed, healed_prompts = _preflight_drift_heal(tmp_path, quiet=True)

    assert healed == ["hackathon_event_detail_page"]
    assert failed == []
    assert healed_prompts == [
        "prompts/hackathon_event_detail_page_TypeScriptReact.prompt"
    ]
    assert run.call_args.args[0] == [
        sys.executable,
        "-m",
        "pdd",
        "update",
        "--sync-metadata",
        "--git",
        "prompts/hackathon_event_detail_page_TypeScriptReact.prompt",
        "frontend/src/app/hackathon/[eventId]/page.tsx",
    ]
    assert run.call_args.kwargs["cwd"] == str(tmp_path)


def test_same_leaf_unrelated_prompt_remains_byte_identical(tmp_path: Path) -> None:
    """Model both CLI modes so the old code-only call corrupts this fixture."""
    authoritative = tmp_path / "prompts/hackathon_event_detail_page_TypeScriptReact.prompt"
    unrelated = tmp_path / "prompts/frontend/page_TypeScriptReact.prompt"
    code = tmp_path / "frontend/src/app/hackathon/[eventId]/page.tsx"
    for path in (authoritative, unrelated, code):
        path.parent.mkdir(parents=True, exist_ok=True)
    authoritative.write_text("stale event detail prompt\n", encoding="utf-8")
    unrelated.write_text("PDD public homepage prompt\n", encoding="utf-8")
    code.write_text("export default function EventPage() {}\n", encoding="utf-8")
    unrelated_before = unrelated.read_bytes()

    drift = _drift(
        prompt_path=str(authoritative.relative_to(tmp_path)),
        code_path=str(code.relative_to(tmp_path)),
    )

    def model_update_cli(argv: list[str], **kwargs: object) -> subprocess.CompletedProcess:
        # True update owns argv[-2]. The former code-only regeneration call would
        # weakly resolve page.tsx to the unrelated frontend/page prompt.
        target = Path(argv[-2]) if "--git" in argv else unrelated.relative_to(tmp_path)
        (Path(str(kwargs["cwd"])) / target).write_text(
            "event detail prompt derived from code\n", encoding="utf-8"
        )
        return subprocess.CompletedProcess(args=argv, returncode=0, stdout="", stderr="")

    with patch("pdd.ci_drift_heal.detect_drift", return_value=([drift], [])), patch(
        "pdd.agentic_change_orchestrator.subprocess.run", side_effect=model_update_cli
    ):
        healed, failed, _ = _preflight_drift_heal(tmp_path, quiet=True)

    assert healed == ["hackathon_event_detail_page"]
    assert failed == []
    assert authoritative.read_text(encoding="utf-8").startswith("event detail prompt")
    assert unrelated.read_bytes() == unrelated_before


@pytest.mark.parametrize(
    ("prompt_path", "code_path"),
    [
        (None, "frontend/src/unique.ts"),
        ("prompts/unique_TypeScript.prompt", None),
    ],
)
def test_missing_authoritative_pair_fails_without_code_only_fallback(
    tmp_path: Path, prompt_path: str | None, code_path: str | None
) -> None:
    drift = _drift(prompt_path=prompt_path, code_path=code_path)

    with patch("pdd.ci_drift_heal.detect_drift", return_value=([drift], [])), patch(
        "pdd.agentic_change_orchestrator.subprocess.run"
    ) as run:
        healed, failed, healed_prompts = _preflight_drift_heal(tmp_path, quiet=True)

    assert healed == []
    assert failed == ["hackathon_event_detail_page"]
    assert healed_prompts == []
    run.assert_not_called()


def test_unique_module_uses_the_same_compatible_true_update_contract(tmp_path: Path) -> None:
    drift = DriftInfo(
        basename="unique",
        language="typescript",
        operation="update",
        reason="code hash changed",
        prompt_path="prompts/unique_TypeScript.prompt",
        code_path="src/unique.ts",
    )

    with patch("pdd.ci_drift_heal.detect_drift", return_value=([drift], [])), patch(
        "pdd.agentic_change_orchestrator.subprocess.run",
        return_value=subprocess.CompletedProcess(args=[], returncode=0, stdout="", stderr=""),
    ) as run:
        healed, failed, _ = _preflight_drift_heal(tmp_path, quiet=True)

    assert healed == ["unique"]
    assert failed == []
    assert run.call_args.args[0][-3:] == [
        "--git",
        "prompts/unique_TypeScript.prompt",
        "src/unique.ts",
    ]
