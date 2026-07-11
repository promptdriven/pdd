"""Tests for stable repository identity and protected path handling."""

import os
from concurrent.futures import ThreadPoolExecutor
from threading import Barrier
import subprocess
from pathlib import PurePosixPath

import pytest

from pdd.sync_core import (
    PathPolicy,
    PathPolicyError,
    RepositoryIdentityError,
    initialize_repository_identity,
    read_repository_identity,
)


def test_repository_identity_is_initialized_once(tmp_path) -> None:
    expected = "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
    identity = initialize_repository_identity(tmp_path, expected)
    assert identity.value == expected
    assert identity.persistent is True
    assert read_repository_identity(tmp_path) == identity
    assert initialize_repository_identity(tmp_path, "aaaaaaaa-aaaa-4aaa-aaaa-aaaaaaaaaaaa") == identity


def test_concurrent_repository_identity_initialization_returns_single_winner(
    tmp_path, monkeypatch
) -> None:
    barrier = Barrier(2)
    real_replace = os.replace

    def racing_replace(source, destination):
        barrier.wait(timeout=5)
        real_replace(source, destination)

    monkeypatch.setattr("pdd.sync_core.identity.os.replace", racing_replace)
    requested = (
        "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0",
        "aaaaaaaa-aaaa-4aaa-aaaa-aaaaaaaaaaaa",
    )
    with ThreadPoolExecutor(max_workers=2) as pool:
        results = tuple(pool.map(lambda value: initialize_repository_identity(tmp_path, value), requested))
    persisted = read_repository_identity(tmp_path, require_persistent=True)
    assert results == (persisted, persisted)


def test_legacy_identity_is_report_only(tmp_path) -> None:
    first = read_repository_identity(tmp_path)
    second = read_repository_identity(tmp_path)
    assert first == second
    assert first.persistent is False
    with pytest.raises(RepositoryIdentityError, match="requires initialization"):
        read_repository_identity(tmp_path, require_persistent=True)


def test_malformed_repository_identity_fails_closed(tmp_path) -> None:
    identity_path = tmp_path / ".pdd/repository-id"
    identity_path.parent.mkdir()
    identity_path.write_text("candidate-controlled-name\n", encoding="ascii")
    with pytest.raises(RepositoryIdentityError, match="valid UUID"):
        read_repository_identity(tmp_path)


@pytest.fixture()
def repository(tmp_path):
    (tmp_path / "src").mkdir()
    (tmp_path / "src/widget.py").write_text("print('widget')\n", encoding="utf-8")
    return tmp_path


def test_snapshot_binds_content_and_executable_mode(repository) -> None:
    policy = PathPolicy(repository)
    relpath = PurePosixPath("src/widget.py")
    regular = policy.snapshot("code", relpath)
    os.chmod(repository / relpath, 0o755)
    executable = policy.snapshot("code", relpath)
    assert regular.digest == executable.digest
    assert regular.git_mode == "100644"
    assert executable.git_mode == "100755"


@pytest.mark.parametrize(
    "relpath",
    [PurePosixPath("../outside.py"), PurePosixPath("/tmp/outside.py")],
)
def test_path_policy_rejects_lexical_escape(repository, relpath) -> None:
    with pytest.raises(PathPolicyError, match="repository-relative"):
        PathPolicy(repository).resolve(relpath)


def test_path_policy_rejects_unapproved_symlink(repository, tmp_path) -> None:
    outside = tmp_path / "outside.py"
    outside.write_text("secret\n", encoding="utf-8")
    (repository / "src/alias.py").symlink_to(outside)
    with pytest.raises(PathPolicyError, match="unapproved managed symlink"):
        PathPolicy(repository).resolve(PurePosixPath("src/alias.py"))


def test_path_policy_accepts_unchanged_tracked_alias(repository) -> None:
    (repository / "canonical").mkdir()
    (repository / "canonical/widget.py").write_text("value = 1\n", encoding="utf-8")
    (repository / "alias").symlink_to("canonical", target_is_directory=True)
    policy = PathPolicy(
        repository,
        {PurePosixPath("alias"): PurePosixPath("canonical")},
    )
    resolved = policy.resolve(PurePosixPath("alias/widget.py"))
    assert resolved.logical_relpath == PurePosixPath("alias/widget.py")
    assert resolved.canonical_path == repository / "canonical/widget.py"
    assert resolved.alias_relpath == PurePosixPath("alias")


def test_path_policy_rejects_unapproved_symlink_below_approved_target(tmp_path) -> None:
    _git_repository(tmp_path)
    (tmp_path / "canonical").mkdir()
    (tmp_path / "canonical/widget.py").write_text("value = 1\n", encoding="utf-8")
    (tmp_path / "middle").symlink_to("canonical", target_is_directory=True)
    (tmp_path / "alias").symlink_to("middle", target_is_directory=True)
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-q", "-m", "tracked outer alias")
    commit = _git(tmp_path, "rev-parse", "HEAD")

    policy = PathPolicy(
        tmp_path,
        {PurePosixPath("alias"): PurePosixPath("middle")},
        base_ref=commit,
        head_ref=commit,
    )

    with pytest.raises(PathPolicyError, match="unapproved managed symlink: middle"):
        policy.resolve(PurePosixPath("alias/widget.py"))


def test_path_policy_rejects_unapproved_symlink_in_canonical_suffix(tmp_path) -> None:
    _git_repository(tmp_path)
    (tmp_path / "canonical").mkdir()
    (tmp_path / "terminal").mkdir()
    (tmp_path / "terminal/widget.py").write_text("value = 1\n", encoding="utf-8")
    (tmp_path / "canonical/nested").symlink_to(
        "../terminal", target_is_directory=True
    )
    (tmp_path / "alias").symlink_to("canonical", target_is_directory=True)
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-q", "-m", "tracked descendant alias")
    commit = _git(tmp_path, "rev-parse", "HEAD")

    policy = PathPolicy(
        tmp_path,
        {PurePosixPath("alias"): PurePosixPath("canonical")},
        base_ref=commit,
        head_ref=commit,
    )

    with pytest.raises(
        PathPolicyError, match="unapproved managed symlink: canonical/nested"
    ):
        policy.resolve(PurePosixPath("alias/nested/widget.py"))


@pytest.mark.parametrize("replacement_in_head", [False, True])
def test_path_policy_rejects_canonical_suffix_symlink_replaced_by_directory(
    tmp_path, replacement_in_head
) -> None:
    _git_repository(tmp_path)
    (tmp_path / "canonical").mkdir()
    (tmp_path / "terminal").mkdir()
    (tmp_path / "terminal/widget.py").write_text("terminal = True\n", encoding="utf-8")
    nested = tmp_path / "canonical/nested"
    nested.symlink_to("../terminal", target_is_directory=True)
    (tmp_path / "alias").symlink_to("canonical", target_is_directory=True)
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-q", "-m", "base descendant alias")
    base = _git(tmp_path, "rev-parse", "HEAD")

    nested.unlink()
    nested.mkdir()
    (nested / "widget.py").write_text("replacement = True\n", encoding="utf-8")
    head = base
    if replacement_in_head:
        _git(tmp_path, "add", "canonical/nested")
        _git(tmp_path, "commit", "-q", "-m", "replace descendant alias")
        head = _git(tmp_path, "rev-parse", "HEAD")

    policy = PathPolicy(
        tmp_path,
        {PurePosixPath("alias"): PurePosixPath("canonical")},
        base_ref=base,
        head_ref=head,
    )

    with pytest.raises(
        PathPolicyError, match="unapproved managed symlink: canonical/nested"
    ):
        policy.resolve(PurePosixPath("alias/nested/widget.py"))


def _git(root, *args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=root,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()


def _git_repository(root) -> None:
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "path-policy@example.com")
    _git(root, "config", "user.name", "Path Policy")


def test_path_policy_rejects_unchanged_alias_absent_from_policy(tmp_path) -> None:
    _git_repository(tmp_path)
    (tmp_path / "canonical").mkdir()
    (tmp_path / "canonical/widget.py").write_text("value = 1\n", encoding="utf-8")
    (tmp_path / "alias").symlink_to("canonical", target_is_directory=True)
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-q", "-m", "tracked alias")
    commit = _git(tmp_path, "rev-parse", "HEAD")

    policy = PathPolicy(tmp_path, base_ref=commit, head_ref=commit)
    with pytest.raises(PathPolicyError, match="unapproved managed symlink"):
        policy.resolve(PurePosixPath("alias/widget.py"))


def test_path_policy_allows_regular_file_edit_between_immutable_trees(tmp_path) -> None:
    _git_repository(tmp_path)
    (tmp_path / "src").mkdir()
    widget = tmp_path / "src/widget.py"
    widget.write_text("value = 1\n", encoding="utf-8")
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-q", "-m", "base file")
    base = _git(tmp_path, "rev-parse", "HEAD")
    widget.write_text("value = 2\n", encoding="utf-8")
    _git(tmp_path, "add", "src/widget.py")
    _git(tmp_path, "commit", "-q", "-m", "edit file")
    head = _git(tmp_path, "rev-parse", "HEAD")

    resolved = PathPolicy(tmp_path, base_ref=base, head_ref=head).resolve(
        PurePosixPath("src/widget.py")
    )

    assert resolved.canonical_path == widget
    assert resolved.alias_relpath is None


def test_path_policy_rejects_alias_retarget_between_immutable_trees(tmp_path) -> None:
    _git_repository(tmp_path)
    (tmp_path / "canonical").mkdir()
    (tmp_path / "canonical/widget.py").write_text("value = 1\n", encoding="utf-8")
    (tmp_path / "other").mkdir()
    (tmp_path / "other/widget.py").write_text("value = 2\n", encoding="utf-8")
    alias = tmp_path / "alias"
    alias.symlink_to("canonical", target_is_directory=True)
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-q", "-m", "base alias")
    base = _git(tmp_path, "rev-parse", "HEAD")
    alias.unlink()
    alias.symlink_to("other", target_is_directory=True)
    _git(tmp_path, "add", "alias")
    _git(tmp_path, "commit", "-q", "-m", "retarget alias")
    head = _git(tmp_path, "rev-parse", "HEAD")

    policy = PathPolicy(
        tmp_path,
        {PurePosixPath("alias"): PurePosixPath("canonical")},
        base_ref=base,
        head_ref=head,
    )
    with pytest.raises(PathPolicyError, match="changed in protected trees"):
        policy.resolve(PurePosixPath("alias/widget.py"))


def test_path_policy_rejects_configured_alias_absent_from_immutable_trees(
    tmp_path,
) -> None:
    _git_repository(tmp_path)
    (tmp_path / "canonical").mkdir()
    (tmp_path / "canonical/widget.py").write_text("value = 1\n", encoding="utf-8")
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-q", "-m", "protected tree without alias")
    commit = _git(tmp_path, "rev-parse", "HEAD")
    (tmp_path / "alias").symlink_to("canonical", target_is_directory=True)

    policy = PathPolicy(
        tmp_path,
        {PurePosixPath("alias"): PurePosixPath("canonical")},
        base_ref=commit,
        head_ref=commit,
    )
    with pytest.raises(PathPolicyError, match="protected trees"):
        policy.resolve(PurePosixPath("alias/widget.py"))


def test_path_policy_rejects_stale_alias_policy_over_real_directory(tmp_path) -> None:
    _git_repository(tmp_path)
    (tmp_path / "alias").mkdir()
    (tmp_path / "alias/widget.py").write_text("candidate = True\n", encoding="utf-8")
    (tmp_path / "canonical").mkdir()
    (tmp_path / "canonical/widget.py").write_text("value = 1\n", encoding="utf-8")
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-q", "-m", "real directory")
    commit = _git(tmp_path, "rev-parse", "HEAD")

    policy = PathPolicy(
        tmp_path,
        {PurePosixPath("alias"): PurePosixPath("canonical")},
        base_ref=commit,
        head_ref=commit,
    )
    with pytest.raises(PathPolicyError, match="not an unchanged symlink"):
        policy.resolve(PurePosixPath("alias/widget.py"))


def test_path_policy_rejects_alias_retarget(repository) -> None:
    (repository / "canonical").mkdir()
    (repository / "canonical/widget.py").write_text("value = 1\n", encoding="utf-8")
    (repository / "other").mkdir()
    (repository / "other/widget.py").write_text("value = 2\n", encoding="utf-8")
    alias = repository / "alias"
    alias.symlink_to("canonical", target_is_directory=True)
    policy = PathPolicy(
        repository,
        {PurePosixPath("alias"): PurePosixPath("canonical")},
    )
    policy.resolve(PurePosixPath("alias/widget.py"))
    alias.unlink()
    alias.symlink_to("other", target_is_directory=True)
    with pytest.raises(PathPolicyError, match="target changed"):
        policy.resolve(PurePosixPath("alias/widget.py"))


def test_path_policy_rejects_special_file(repository) -> None:
    fifo = repository / "src/events"
    os.mkfifo(fifo)
    with pytest.raises(PathPolicyError, match="not a regular file"):
        PathPolicy(repository).resolve(PurePosixPath("src/events"))
