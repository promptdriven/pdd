from __future__ import annotations

import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SUBMIT_SCRIPT = REPO_ROOT / "ci" / "cloud-batch" / "submit.sh"


def _run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=REPO_ROOT,
        check=True,
        text=True,
        capture_output=True,
    )


def _cloud_batch_source_paths() -> list[str]:
    result = _run(
        "bash",
        "-c",
        (
            "source <(sed -n '/^SOURCE_PATHS=(/,/^)/p' "
            "'ci/cloud-batch/submit.sh'); "
            'printf "%s\\n" "${SOURCE_PATHS[@]}"'
        ),
    )
    return [line for line in result.stdout.splitlines() if line]


def _git_ls_files(*paths: str) -> set[str]:
    result = _run(
        "git",
        "-c",
        "core.quotePath=false",
        "ls-files",
        "--cached",
        "--others",
        "--exclude-standard",
        "--",
        *paths,
    )
    return set(result.stdout.splitlines())


def test_cloud_batch_source_upload_includes_checkup_interactive_demo() -> None:
    tracked_demo_files = _git_ls_files("demos/checkup_interactive")
    assert tracked_demo_files, "expected tracked checkup interactive demo fixtures"

    source_paths = _cloud_batch_source_paths()
    upload_files = _git_ls_files(*source_paths)

    missing = sorted(tracked_demo_files - upload_files)
    assert not missing, (
        "cloud-batch source upload must include tracked checkup interactive "
        f"demo fixtures; missing: {missing}"
    )
