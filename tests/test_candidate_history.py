"""Security matrix for authenticated candidate-only history skips."""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

from tests.candidate_history import skip_if_authenticated_candidate_lacks_refs


def _git(root: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=root, text=True, stderr=subprocess.DEVNULL
    ).strip()


def _candidate_repo(tmp_path: Path) -> tuple[Path, str, str]:
    root = tmp_path / "candidate"
    root.mkdir()
    subprocess.run(["git", "init", "-q"], cwd=root, check=True)
    (root / "tracked.txt").write_text("candidate\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=root, check=True)
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=PDD test",
            "-c",
            "user.email=pdd@example.test",
            "commit",
            "-qm",
            "candidate",
        ],
        cwd=root,
        check=True,
    )
    return root, _git(root, "rev-parse", "HEAD"), _git(root, "rev-parse", "HEAD^{tree}")


def _set_identity(
    monkeypatch: pytest.MonkeyPatch, candidate_sha: str, candidate_tree: str
) -> None:
    monkeypatch.setenv("PDD_CLOUD_SOURCE_IDENTITY_MODE", "candidate-tree-v1")
    monkeypatch.setenv("PDD_CANDIDATE_SHA", candidate_sha)
    monkeypatch.setenv("PDD_CANDIDATE_TREE", candidate_tree)


def test_candidate_history_skip_accepts_exact_authenticated_identity(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Absent history is expected only for the verified candidate commit and tree."""
    root, candidate_sha, candidate_tree = _candidate_repo(tmp_path)
    _set_identity(monkeypatch, candidate_sha, candidate_tree)

    with pytest.raises(pytest.skip.Exception, match="exact historical evidence"):
        skip_if_authenticated_candidate_lacks_refs(
            root, "exact historical evidence", "0" * 40
        )


@pytest.mark.parametrize(
    "mutation",
    ("marker-absent", "marker-mismatch", "sha-absent", "sha-invalid", "sha-mismatch",
     "tree-absent", "tree-invalid", "tree-mismatch"),
)
def test_candidate_history_skip_rejects_untrusted_identity(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mutation: str
) -> None:
    """Every incomplete or mismatched identity leaves the assertion fail-closed."""
    root, candidate_sha, candidate_tree = _candidate_repo(tmp_path)
    _set_identity(monkeypatch, candidate_sha, candidate_tree)
    variable, value = {
        "marker-absent": ("PDD_CLOUD_SOURCE_IDENTITY_MODE", None),
        "marker-mismatch": ("PDD_CLOUD_SOURCE_IDENTITY_MODE", "candidate-tree-v2"),
        "sha-absent": ("PDD_CANDIDATE_SHA", None),
        "sha-invalid": ("PDD_CANDIDATE_SHA", "not-a-sha"),
        "sha-mismatch": ("PDD_CANDIDATE_SHA", "0" * 40),
        "tree-absent": ("PDD_CANDIDATE_TREE", None),
        "tree-invalid": ("PDD_CANDIDATE_TREE", "not-a-tree"),
        "tree-mismatch": ("PDD_CANDIDATE_TREE", "0" * 40),
    }[mutation]
    if value is None:
        monkeypatch.delenv(variable)
    else:
        monkeypatch.setenv(variable, value)

    skip_if_authenticated_candidate_lacks_refs(root, "historical evidence", "0" * 40)


def test_candidate_history_skip_does_not_hide_available_ref(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Present refs continue into their repository-identity assertions."""
    root, candidate_sha, candidate_tree = _candidate_repo(tmp_path)
    _set_identity(monkeypatch, candidate_sha, candidate_tree)

    skip_if_authenticated_candidate_lacks_refs(
        root, "repository identity evidence", candidate_sha
    )
