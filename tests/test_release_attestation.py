"""Deterministic tests for the pdd_cloud release-attestation boundary."""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import textwrap


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "release_attestation.py"
LEASE_REF = "refs/pdd-cloud/release-lease"


def run(
    command: list[str],
    cwd: Path,
    check: bool = True,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command, cwd=cwd, text=True, capture_output=True, check=check, env=env
    )


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
        "2",
        "--sha",
        sha,
        "--owner",
        owner,
        "--lease-ref",
        LEASE_REF,
        *extra,
    ]


def recovery_command(name: str, *extra: str) -> list[str]:
    return ["python", str(SCRIPT), name, "--lease-ref", LEASE_REF, *extra]


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
        "PDD_CLOUD_RELEASE_ATTESTATION_VERSION=2",
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
        "PDD_CLOUD_RELEASE_ATTESTATION_VERSION": "2",
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


def test_manual_stale_recovery_inspects_exact_tag_metadata_then_cas_deletes(tmp_path: Path) -> None:
    remote, repo, sha = init_repo(tmp_path)
    owner = "pdd-cloud-owner-stale"
    lease_oid = run(command("acquire", sha, owner), repo).stdout.strip()

    inspected = run(recovery_command("inspect-lease"), repo)
    details = json.loads(inspected.stdout)
    assert details == {
        "created_epoch": details["created_epoch"],
        "lease_oid": lease_oid,
        "owner": owner,
        "sha": sha,
    }

    recovered = run(
        recovery_command(
            "recover-stale-lease",
            "--lease-oid",
            lease_oid,
            "--expected-owner",
            owner,
            "--expected-sha",
            sha,
            "--stale-before-epoch",
            str(details["created_epoch"]),
        ),
        repo,
    )

    assert json.loads(recovered.stdout)["recovered_lease_oid"] == lease_oid
    assert not remote_ref(remote, LEASE_REF)


def test_manual_stale_recovery_never_deletes_a_successor(tmp_path: Path) -> None:
    remote, repo, sha = init_repo(tmp_path)
    first_owner = "pdd-cloud-owner-first"
    first_oid = run(command("acquire", sha, first_owner), repo).stdout.strip()
    first_details = json.loads(run(recovery_command("inspect-lease"), repo).stdout)
    git(repo, "push", "origin", f":{LEASE_REF}")
    second_owner = "pdd-cloud-owner-second"
    second_oid = run(command("acquire", sha, second_owner), repo).stdout.strip()

    recovered = run(
        recovery_command(
            "recover-stale-lease",
            "--lease-oid",
            first_oid,
            "--expected-owner",
            first_owner,
            "--expected-sha",
            sha,
            "--stale-before-epoch",
            str(first_details["created_epoch"]),
        ),
        repo,
        check=False,
    )

    assert recovered.returncode != 0
    assert "OID changed" in recovered.stderr
    assert remote_ref(remote, LEASE_REF).startswith(second_oid)
    run(command("cleanup", sha, second_owner, "--lease-oid", second_oid), repo)


def test_final_boundary_never_publishes_a_remote_tag_without_server_cas(tmp_path: Path) -> None:
    remote, repo, sha = init_repo(tmp_path)

    result = run(command("final-boundary", sha, "pdd-cloud-owner-a"), repo, check=False)

    assert result.returncode != 0
    assert "cannot atomically compare unchanged origin/main" in result.stderr
    assert not remote_ref(remote, "refs/tags/*")
    assert not remote_ref(remote, LEASE_REF)


def _git_that_interrupts_after_lease_push(tmp_path: Path, interrupt_command: str) -> Path:
    """Interrupt either acquire readback or final-boundary's second fetch."""
    real_git = shutil.which("git")
    assert real_git is not None
    wrapper_dir = tmp_path / "interrupt-wrapper"
    wrapper_dir.mkdir()
    (wrapper_dir / "git").write_text(
        textwrap.dedent(
            f"""\
            #!/usr/bin/env bash
            set -eu
            if [ "$1" = push ] && [[ " $* " == *":{LEASE_REF}"* ]] && \\
              [[ ! " $* " =~ --force-with-lease={LEASE_REF}:[0-9a-f]{{40}} ]]; then
              touch "$INTERRUPT_ARMED"
            fi
            if [ -f "$INTERRUPT_ARMED" ] && [ ! -f "$INTERRUPT_FIRED" ] && \\
              [ "$1" = "{interrupt_command}" ]; then
              touch "$INTERRUPT_FIRED"
              kill -TERM "$PPID"
            fi
            exec "{real_git}" "$@"
            """
        ),
        encoding="utf-8",
    )
    (wrapper_dir / "git").chmod(0o755)
    return wrapper_dir


def test_sigterm_during_acquire_or_final_recheck_cleans_the_remote_lease(
    tmp_path: Path,
) -> None:
    for command_name, interrupt_command in (("acquire", "ls-remote"), ("final-boundary", "fetch")):
        case_dir = tmp_path / command_name
        case_dir.mkdir()
        remote, repo, sha = init_repo(case_dir)
        owner = f"pdd-cloud-owner-interrupt-{command_name}"
        wrapper_dir = _git_that_interrupts_after_lease_push(
            case_dir, interrupt_command
        )
        result = run(
            command(command_name, sha, owner),
            repo,
            check=False,
            env={
                **os.environ,
                "PATH": f"{wrapper_dir}:{os.environ['PATH']}",
                "INTERRUPT_ARMED": str(case_dir / "armed"),
                "INTERRUPT_FIRED": str(case_dir / "fired"),
            },
        )

        assert result.returncode == 128 + 15
        assert "SIGTERM" in result.stderr
        assert not remote_ref(remote, LEASE_REF), command_name
        assert not git(repo, "tag", "--list", owner), command_name


def _git_that_breaks_post_push_readback(tmp_path: Path, mode: str) -> Path:
    """Return a git wrapper that fails only acquire's post-push readback."""
    real_git = shutil.which("git")
    assert real_git is not None
    wrapper_dir = tmp_path / "git-wrapper"
    wrapper_dir.mkdir(parents=True)
    (wrapper_dir / "git").write_text(
        textwrap.dedent(
            f"""\
            #!/usr/bin/env bash
            set -eu
            if [ "$1" = "ls-remote" ] && [ "${{FAIL_POST_PUSH_READBACK:-}}" = "1" ]; then
              if [ "{mode}" = "failed" ]; then
                echo 'simulated ls-remote transport failure' >&2
                exit 23
              fi
              printf '%040d refs/pdd-cloud/release-lease\\n' 0
              exit 0
            fi
            if [ "$1" = "push" ] && [ "${{FAIL_LEASE_CLEANUP:-}}" = "1" ] && [[ " $* " =~ --force-with-lease=refs/pdd-cloud/release-lease:[0-9a-f]{{40}} ]]; then
              echo 'simulated owner-safe remote cleanup failure' >&2
              exit 24
            fi
            exec "{real_git}" "$@"
            """
        ),
        encoding="utf-8",
    )
    (wrapper_dir / "git").chmod(0o755)
    return wrapper_dir


def test_acquire_cleans_remote_lease_when_post_push_readback_fails_or_is_ambiguous(
    tmp_path: Path,
) -> None:
    remote, repo, sha = init_repo(tmp_path)

    for mode in ("failed", "ambiguous"):
        wrapper_dir = _git_that_breaks_post_push_readback(tmp_path / mode, mode)
        result = run(
            command("acquire", sha, f"pdd-cloud-owner-{mode}"),
            repo,
            check=False,
            env={
                **os.environ,
                "PATH": f"{wrapper_dir}:{os.environ['PATH']}",
                "FAIL_POST_PUSH_READBACK": "1",
            },
        )

        assert result.returncode != 0
        assert not remote_ref(remote, LEASE_REF), mode
        assert not git(repo, "tag", "--list", f"pdd-cloud-owner-{mode}")


def test_acquire_reports_owner_safe_cleanup_failure_after_readback_failure(
    tmp_path: Path,
) -> None:
    remote, repo, sha = init_repo(tmp_path)
    wrapper_dir = _git_that_breaks_post_push_readback(tmp_path, "failed")

    result = run(
        command("acquire", sha, "pdd-cloud-owner-cleanup-failure"),
        repo,
        check=False,
        env={
            **os.environ,
            "PATH": f"{wrapper_dir}:{os.environ['PATH']}",
            "FAIL_POST_PUSH_READBACK": "1",
            "FAIL_LEASE_CLEANUP": "1",
        },
    )

    assert result.returncode != 0
    assert "ls-remote" in result.stderr
    assert "remote lease cleanup failed" in result.stderr
    assert remote_ref(remote, LEASE_REF)


def _git_that_reports_accepted_push_failure(
    tmp_path: Path, *, fail_readback: bool = False, successor_oid: str | None = None
) -> Path:
    """Return a Git wrapper that makes a successful lease push look failed."""
    real_git = shutil.which("git")
    assert real_git is not None
    wrapper_dir = tmp_path / "accepted-push-wrapper"
    wrapper_dir.mkdir(parents=True)
    successor_update = ""
    if successor_oid is not None:
        successor_update = (
            f'  "{real_git}" --git-dir "$REMOTE_BARE" update-ref '
            f'"{LEASE_REF}" "{successor_oid}"\n'
        )
    readback_failure = ""
    if fail_readback:
        readback_failure = (
            'if [ "$1" = "ls-remote" ] && [ "${FAIL_LEASE_READBACK:-}" = "1" ]; then\n'
            "  echo 'simulated remote readback outage' >&2\n"
            "  exit 43\n"
            "fi\n"
        )
    (wrapper_dir / "git").write_text(
        "#!/usr/bin/env bash\n"
        "set -eu\n"
        f"{readback_failure}"
        f'if [ "$1" = "push" ] && [[ " $* " == *":{LEASE_REF}"* ]] && '
        f'[[ ! " $* " =~ --force-with-lease={LEASE_REF}:[0-9a-f]{{40}} ]]; then\n'
        f'  "{real_git}" "$@"\n'
        f"{successor_update}"
        "  echo 'simulated client failure after remote acceptance' >&2\n"
        "  exit 42\n"
        "fi\n"
        f'exec "{real_git}" "$@"\n',
        encoding="utf-8",
    )
    (wrapper_dir / "git").chmod(0o755)
    return wrapper_dir


def test_acquire_cleans_lease_when_server_accepts_push_but_client_returns_nonzero(
    tmp_path: Path,
) -> None:
    remote, repo, sha = init_repo(tmp_path)
    wrapper_dir = _git_that_reports_accepted_push_failure(tmp_path)

    result = run(
        command("acquire", sha, "pdd-cloud-owner-client-nonzero"),
        repo,
        check=False,
        env={**os.environ, "PATH": f"{wrapper_dir}:{os.environ['PATH']}"},
    )

    assert result.returncode != 0
    assert "after accepting this attempt" in result.stderr
    assert not remote_ref(remote, LEASE_REF)
    assert not git(repo, "tag", "--list", "pdd-cloud-owner-client-nonzero")


def test_acquire_attempts_owner_safe_cleanup_when_failed_push_readback_is_unknown(
    tmp_path: Path,
) -> None:
    remote, repo, sha = init_repo(tmp_path)
    wrapper_dir = _git_that_reports_accepted_push_failure(tmp_path, fail_readback=True)

    result = run(
        command("acquire", sha, "pdd-cloud-owner-unknown-readback"),
        repo,
        check=False,
        env={
            **os.environ,
            "PATH": f"{wrapper_dir}:{os.environ['PATH']}",
            "FAIL_LEASE_READBACK": "1",
        },
    )

    assert result.returncode != 0
    assert "push outcome is ambiguous" in result.stderr
    assert "remote readback failed" in result.stderr
    assert not remote_ref(remote, LEASE_REF)
    assert not git(repo, "tag", "--list", "pdd-cloud-owner-unknown-readback")


def test_acquire_never_deletes_successor_after_client_reports_failed_push(
    tmp_path: Path,
) -> None:
    remote, repo, sha = init_repo(tmp_path)
    wrapper_dir = _git_that_reports_accepted_push_failure(
        tmp_path, successor_oid=sha
    )

    result = run(
        command("acquire", sha, "pdd-cloud-owner-superseded"),
        repo,
        check=False,
        env={
            **os.environ,
            "PATH": f"{wrapper_dir}:{os.environ['PATH']}",
            "REMOTE_BARE": str(remote),
        },
    )

    assert result.returncode != 0
    assert "another release attempt already owns" in result.stderr
    assert remote_ref(remote, LEASE_REF).startswith(sha)
    assert not git(repo, "tag", "--list", "pdd-cloud-owner-superseded")


def test_attestation_git_calls_override_hostile_replacement_environment(
    tmp_path: Path,
) -> None:
    """Every attestation Git call uses canonical objects in a real repo."""
    remote, repo, sha = init_repo(tmp_path)
    writer = tmp_path / "writer"
    run(["git", "clone", str(remote), str(writer)], tmp_path)
    git(writer, "config", "user.email", "writer@example.test")
    git(writer, "config", "user.name", "Writer")
    (writer / "release.txt").write_text("replacement target\n", encoding="utf-8")
    git(writer, "commit", "-am", "replacement target")
    replacement_sha = git(writer, "rev-parse", "HEAD")
    git(writer, "push", "origin", "main")
    git(repo, "fetch", "origin", "main")
    git(repo, "replace", sha, replacement_sha)

    real_git = shutil.which("git")
    assert real_git is not None
    wrapper_dir = tmp_path / "replacement-env-wrapper"
    wrapper_dir.mkdir()
    call_log = tmp_path / "replacement-env.log"
    (wrapper_dir / "git").write_text(
        "#!/usr/bin/env bash\n"
        "set -eu\n"
        "printf '%s/%s\\n' \"${GIT_NO_REPLACE_OBJECTS-}\" "
        "\"${GIT_REPLACE_REF_BASE-unset}\" >> \"$GIT_ENV_LOG\"\n"
        f'exec "{real_git}" "$@"\n',
        encoding="utf-8",
    )
    (wrapper_dir / "git").chmod(0o755)
    environment = {
        **os.environ,
        "PATH": f"{wrapper_dir}:{os.environ['PATH']}",
        "GIT_ENV_LOG": str(call_log),
        "GIT_NO_REPLACE_OBJECTS": "0",
        "GIT_REPLACE_REF_BASE": "refs/replace/",
    }

    acquired = run(
        command("acquire", sha, "pdd-cloud-owner-replacement-env"),
        repo,
        env=environment,
    )
    run(
        command(
            "cleanup",
            sha,
            "pdd-cloud-owner-replacement-env",
            "--lease-oid",
            acquired.stdout.strip(),
        ),
        repo,
        env=environment,
    )

    assert call_log.read_text(encoding="utf-8").splitlines()
    assert set(call_log.read_text(encoding="utf-8").splitlines()) == {"1/unset"}
