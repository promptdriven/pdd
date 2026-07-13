"""Linux-only real Vitest execution through the production supervisor."""

import json
import os
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

import pytest

from pdd.sync_core import (
    AttestationIssue,
    AttestationSigner,
    EvidenceOutcome,
    RunBinding,
    RunnerConfig,
    UnitId,
    VerificationObligation,
    VerificationProfile,
    run_profile,
)
from pdd.sync_core.runner import vitest_validator_config_digest


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


@pytest.mark.skipif(
    not sys.platform.startswith("linux")
    or not shutil.which("bwrap")
    or not os.environ.get("PDD_REAL_VITEST_TOOLCHAIN_MANIFEST"),
    reason="requires Linux sandbox and provisioned real Vitest toolchain",
)
def test_real_vitest_runs_copied_entrypoint_without_candidate_result_access(
    tmp_path: Path,
) -> None:
    manifest = Path(os.environ["PDD_REAL_VITEST_TOOLCHAIN_MANIFEST"])
    roles = json.loads(manifest.read_text(encoding="utf-8"))["roles"]
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "runner@example.com")
    _git(root, "config", "user.name", "Runner Test")
    (root / "tests").mkdir()
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\n"
        "test('result channel is private', () => {\n"
        "  expect(process.env.PDD_TRUSTED_VITEST_OUTPUT).toBeUndefined();\n"
        "});\n",
        encoding="utf-8",
    )
    (root / "vitest.config.json").write_text('{"test":{}}\n', encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected real Vitest test")
    commit = _git(root, "rev-parse", "HEAD")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    obligation = VerificationObligation(
        "vitest-real",
        "test",
        "vitest",
        vitest_validator_config_digest(root, commit, paths),
        ("REQ-1",),
        paths,
    )
    profile = VerificationProfile(
        UnitId("repo", PurePosixPath("prompts/widget_ts.prompt"), "typescript"),
        (obligation,),
        ("REQ-1",),
        "profile-v1",
    )

    _envelope, executions = run_profile(
        root,
        profile,
        RunBinding("snapshot", commit, commit),
        AttestationIssue(
            AttestationSigner("trusted-ci", b"v" * 32),
            "id",
            "nonce",
            datetime(2026, 7, 13, tzinfo=timezone.utc),
        ),
        RunnerConfig(
            timeout_seconds=30,
            vitest_command=(roles["launcher"], roles["entrypoint"]),
            vitest_toolchain_manifest=manifest,
        ),
    )

    assert executions[0].outcome is EvidenceOutcome.PASS, executions[0].detail
