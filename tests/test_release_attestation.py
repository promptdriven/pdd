"""Deterministic tests for the pdd_cloud release-attestation boundary."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "release_attestation.py"
LEASE_REF = "refs/pdd-cloud/release-lease"


def run(command: list[str], cwd: Path, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, cwd=cwd, text=True, capture_output=True, check=check)


def git(cwd: Path, *args: str) -> str:
    return run(["git", *args], cwd).stdout.strip()


def init_repo(tmp_path: Path) -> tuple[Path, Path, str]:
    remote = tmp_path / "remote.git"
    run(["git", "-c", "init.defaultBranch=main", "init", "--bare", str(remote)], tmp_path)
    repo = tmp_path / "repo"
    run(["git", "clone", str(remote), str(repo)], tmp_path)
    git(repo, "config", "user.email", "release@example.test")
    git(repo, "config", "user.name", "Release Test")
    (repo / "release.txt").write_text("A\n", encoding="utf-8")
    git(repo, "add", "release.txt")
    git(repo, "commit", "-m", "A")
    git(repo, "push", "-u", "origin", "main")
    return remote, repo, git(repo, "rev-parse", "HEAD")


def command(name: str, sha: str, owner: str, *extra: str) -> list[str]:
    return [
        "python",
        str(SCRIPT),
        name,
        "--version",
        "1",
        "--sha",
        sha,
        "--owner",
        owner,
        "--lease-ref",
        LEASE_REF,
        *extra,
    ]


def remote_ref(remote: Path, ref: str) -> str:
    return run(["git", "ls-remote", str(remote), ref], remote).stdout.strip()


def make_contract(*assignments: str, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            "make",
            "-C",
            str(ROOT),
            "--no-print-directory",
            "check-release-attestation-contract",
            *assignments,
        ],
        text=True,
        capture_output=True,
        check=False,
        env=env,
    )


def test_attested_contract_accepts_exact_full_sha(tmp_path: Path) -> None:
    _remote, _repo, sha = init_repo(tmp_path)

    result = run(command("validate", sha, "pdd-cloud-owner-a"), tmp_path)
    make_result = make_contract(
        "PDD_CLOUD_RELEASE_ATTESTATION_VERSION=1",
        f"PDD_CLOUD_VALIDATED_SHA={sha}",
        "PDD_CLOUD_RELEASE_LEASE_OWNER=pdd-cloud-owner-a",
        f"PDD_CLOUD_RELEASE_LEASE_REF={LEASE_REF}",
    )

    assert result.returncode == 0
    assert make_result.returncode == 0, make_result.stderr


def test_make_contract_rejects_ambient_attestation_values(tmp_path: Path) -> None:
    _remote, _repo, sha = init_repo(tmp_path)
    environment = {
        **os.environ,
        "PDD_CLOUD_RELEASE_ATTESTATION_VERSION": "1",
        "PDD_CLOUD_VALIDATED_SHA": sha,
        "PDD_CLOUD_RELEASE_LEASE_OWNER": "pdd-cloud-owner-a",
        "PDD_CLOUD_RELEASE_LEASE_REF": LEASE_REF,
    }

    result = make_contract(env=environment)

    assert result.returncode != 0
    assert "must be a GNU Make command-line assignment" in result.stdout


def test_attested_contract_rejects_missing_malformed_and_mismatched_sha(tmp_path: Path) -> None:
    _remote, repo, sha = init_repo(tmp_path)
    malformed = run(command("validate", "a" * 39, "pdd-cloud-owner-a"), repo, check=False)
    missing = run(command("validate", "", "pdd-cloud-owner-a"), repo, check=False)
    wrong = run(command("final-boundary", "b" * 40, "pdd-cloud-owner-a"), repo, check=False)

    assert malformed.returncode != 0
    assert missing.returncode != 0
    assert wrong.returncode != 0
    assert "must be one full" in malformed.stderr
    assert "must be one full" in missing.stderr
    assert "does not equal attested" in wrong.stderr


def test_final_boundary_rejects_main_advance_after_branch_preflight(tmp_path: Path) -> None:
    remote, repo, sha = init_repo(tmp_path)
    writer = tmp_path / "writer"
    run(["git", "clone", str(remote), str(writer)], tmp_path)
    git(writer, "config", "user.email", "writer@example.test")
    git(writer, "config", "user.name", "Writer")
    (writer / "release.txt").write_text("B\n", encoding="utf-8")
    git(writer, "add", "release.txt")
    git(writer, "commit", "-m", "B")
    git(writer, "push", "origin", "main")

    result = run(command("final-boundary", sha, "pdd-cloud-owner-a"), repo, check=False)

    assert result.returncode != 0
    assert "fresh origin/main" in result.stderr
    assert not remote_ref(remote, "refs/tags/*")
    assert not remote_ref(remote, LEASE_REF)


def test_remote_lease_serializes_concurrent_attempts_and_cleanup_is_owner_safe(tmp_path: Path) -> None:
    remote, repo, sha = init_repo(tmp_path)
    first = run(command("acquire", sha, "pdd-cloud-owner-a"), repo)
    first_lease_oid = first.stdout.strip()
    loser = run(command("acquire", sha, "pdd-cloud-owner-b"), repo, check=False)

    assert loser.returncode != 0
    assert "already owns" in loser.stderr
    assert remote_ref(remote, LEASE_REF).startswith(first_lease_oid)

    # Simulate an owner-A process that has finished, followed by owner B. A's
    # stale cleanup must not delete B's distinct server-visible lease object.
    git(repo, "push", "origin", f":{LEASE_REF}")
    second = run(command("acquire", sha, "pdd-cloud-owner-b"), repo)
    second_lease_oid = second.stdout.strip()
    stale_cleanup = run(
        command("cleanup", sha, "pdd-cloud-owner-a", "--lease-oid", first_lease_oid),
        repo,
        check=False,
    )

    assert stale_cleanup.returncode != 0
    assert remote_ref(remote, LEASE_REF).startswith(second_lease_oid)

    run(command("cleanup", sha, "pdd-cloud-owner-b", "--lease-oid", second_lease_oid), repo)
    assert not remote_ref(remote, LEASE_REF)


def test_final_boundary_never_publishes_a_remote_tag_without_server_cas(tmp_path: Path) -> None:
    remote, repo, sha = init_repo(tmp_path)

    result = run(command("final-boundary", sha, "pdd-cloud-owner-a"), repo, check=False)

    assert result.returncode != 0
    assert "cannot atomically compare unchanged origin/main" in result.stderr
    assert not remote_ref(remote, "refs/tags/*")
    assert not remote_ref(remote, LEASE_REF)
