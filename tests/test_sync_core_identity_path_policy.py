"""Tests for stable repository identity and protected path handling."""

import os
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
