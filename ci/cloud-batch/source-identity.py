#!/usr/bin/env python3
"""Create and verify immutable, Git-bound Cloud Batch source archives."""
# pylint: disable=invalid-name,duplicate-code

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile
import urllib.error
import urllib.parse
import urllib.request
from collections.abc import Callable
from pathlib import Path, PurePosixPath


METADATA_TOKEN_URL = (
    "http://metadata.google.internal/computeMetadata/v1/instance/"
    "service-accounts/default/token"
)
ARCHIVE_MEMBERS = ("candidate-source.tar", "candidate-objects.pack")


class SourceIdentityError(RuntimeError):
    """A sanitized, fail-closed source identity error."""


class _NoRedirectHandler(urllib.request.HTTPRedirectHandler):
    # pylint: disable=too-many-arguments,too-many-positional-arguments
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        del req, fp, code, msg, headers, newurl
        raise urllib.error.HTTPError(
            "redirects-disabled", 400, "redirects disabled", {}, None
        )


_NO_REDIRECT_OPENER = urllib.request.build_opener(_NoRedirectHandler()).open


def _command(
    command: list[str], *, input_bytes: bytes | None = None
) -> subprocess.CompletedProcess[bytes]:
    result = subprocess.run(
        command,
        input=input_bytes,
        check=False,
        capture_output=True,
    )
    if result.returncode != 0:
        raise SourceIdentityError("candidate source identity unavailable")
    return result


def _git(repo: Path, *arguments: str) -> str:
    return _command(["git", "-C", str(repo), *arguments]).stdout.decode().strip()


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _add_regular(archive: tarfile.TarFile, path: Path, name: str) -> None:
    info = tarfile.TarInfo(name)
    info.size = path.stat().st_size
    info.mode = 0o644
    info.mtime = 0
    info.uid = 0
    info.gid = 0
    info.uname = ""
    info.gname = ""
    with path.open("rb") as handle:
        archive.addfile(info, handle)


def _write_tracked_source_tar(repo: Path, candidate_sha: str, output: Path) -> None:
    """Write every raw tracked blob, ignoring archive export attributes."""
    # The streaming Git batch protocol and tar mode handling intentionally stay
    # in one fail-closed lifetime so a partial archive can never be accepted.
    # pylint: disable=too-many-locals,too-many-branches,too-many-statements
    # pylint: disable=consider-using-with
    listing = _command(
        [
            "git",
            "-C",
            str(repo),
            "ls-tree",
            "-rz",
            "--full-tree",
            "-r",
            candidate_sha,
        ]
    ).stdout
    entries: list[tuple[str, str, str]] = []
    for record in listing.split(b"\0"):
        if not record:
            continue
        try:
            metadata, raw_path = record.split(b"\t", 1)
            mode, object_type, object_id = metadata.decode("ascii").split()
            path = raw_path.decode("utf-8", errors="surrogateescape")
        except (UnicodeDecodeError, ValueError) as error:
            raise SourceIdentityError("candidate source identity unavailable") from error
        if (
            object_type != "blob"
            or mode not in {"100644", "100755", "120000"}
            or not re.fullmatch(r"[0-9a-f]{40}", object_id)
        ):
            raise SourceIdentityError("candidate source identity unavailable")
        entries.append((mode, object_id, path))
    if not entries:
        raise SourceIdentityError("candidate source identity unavailable")

    process = subprocess.Popen(
        ["git", "-C", str(repo), "cat-file", "--batch"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    if process.stdin is None or process.stdout is None:
        process.kill()
        raise SourceIdentityError("candidate source identity unavailable")
    try:
        with tarfile.open(output, mode="w", format=tarfile.PAX_FORMAT) as archive:
            for mode, object_id, path in entries:
                process.stdin.write(f"{object_id}\n".encode("ascii"))
                process.stdin.flush()
                header = process.stdout.readline().decode("ascii").strip().split()
                if (
                    len(header) != 3
                    or header[0] != object_id
                    or header[1] != "blob"
                    or not header[2].isdigit()
                ):
                    raise SourceIdentityError("candidate source identity unavailable")
                payload = process.stdout.read(int(header[2]))
                if len(payload) != int(header[2]) or process.stdout.read(1) != b"\n":
                    raise SourceIdentityError("candidate source identity unavailable")
                info = tarfile.TarInfo(path)
                info.mtime = 0
                info.uid = 0
                info.gid = 0
                info.uname = ""
                info.gname = ""
                if mode == "120000":
                    info.type = tarfile.SYMTYPE
                    info.mode = 0o777
                    info.linkname = payload.decode("utf-8", errors="surrogateescape")
                    info.size = 0
                    if not _safe_member(info):
                        raise SourceIdentityError("candidate source identity unavailable")
                    archive.addfile(info)
                else:
                    info.mode = 0o755 if mode == "100755" else 0o644
                    info.size = len(payload)
                    if not _safe_member(info):
                        raise SourceIdentityError("candidate source identity unavailable")
                    archive.addfile(info, io.BytesIO(payload))
        process.stdin.close()
        if process.wait() != 0:
            raise SourceIdentityError("candidate source identity unavailable")
    except (BrokenPipeError, OSError, UnicodeDecodeError, tarfile.TarError) as error:
        process.kill()
        process.wait()
        raise SourceIdentityError("candidate source identity unavailable") from error
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()


def create_archive(repo: Path, output: Path) -> dict[str, object]:
    """Archive every tracked byte and exact commit/tree object at clean HEAD."""
    if _git(repo, "status", "--porcelain=v1", "--untracked-files=all"):
        raise SourceIdentityError("candidate worktree is not clean")
    candidate_sha = _git(repo, "rev-parse", "HEAD^{commit}")
    candidate_tree = _git(repo, "rev-parse", "HEAD^{tree}")
    if not all(
        re.fullmatch(r"[0-9a-f]{40}", value)
        for value in (candidate_sha, candidate_tree)
    ):
        raise SourceIdentityError("candidate source identity unavailable")

    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as temporary:
        temporary_path = Path(temporary)
        source_tar = temporary_path / ARCHIVE_MEMBERS[0]
        object_pack = temporary_path / ARCHIVE_MEMBERS[1]
        _write_tracked_source_tar(repo, candidate_sha, source_tar)
        object_ids = set(
            _git(
                repo,
                "rev-list",
                "--objects",
                "--no-object-names",
                candidate_tree,
            ).splitlines()
        )
        object_ids.add(candidate_sha)
        if not object_ids or any(
            not re.fullmatch(r"[0-9a-f]{40}", object_id)
            for object_id in object_ids
        ):
            raise SourceIdentityError("candidate source identity unavailable")
        packed = _command(
            [
                "git",
                "-C",
                str(repo),
                "pack-objects",
                "--stdout",
                "--compression=9",
                "--threads=1",
            ],
            input_bytes=("\n".join(sorted(object_ids)) + "\n").encode("ascii"),
        ).stdout
        object_pack.write_bytes(packed)

        with output.open("wb") as destination:
            with gzip.GzipFile(
                fileobj=destination, mode="wb", filename="", mtime=0
            ) as zipped:
                with tarfile.open(
                    fileobj=zipped, mode="w", format=tarfile.USTAR_FORMAT
                ) as archive:
                    _add_regular(archive, source_tar, ARCHIVE_MEMBERS[0])
                    _add_regular(archive, object_pack, ARCHIVE_MEMBERS[1])

    return {
        "candidate_sha": candidate_sha,
        "candidate_tree": candidate_tree,
        "source_sha256": _sha256(output),
        "source_size": output.stat().st_size,
    }


def verify_local_source(
    archive: Path, *, expected_sha256: str, expected_size: int
) -> None:
    """Verify the mounted archive's exact bytes before extraction."""
    if (
        not re.fullmatch(r"[0-9a-f]{64}", expected_sha256)
        or expected_size < 1
        or not archive.is_file()
        or archive.stat().st_size != expected_size
        or _sha256(archive) != expected_sha256
    ):
        raise SourceIdentityError("candidate source identity mismatch")


def _safe_member(member: tarfile.TarInfo) -> bool:
    path = PurePosixPath(member.name)
    return (
        member.name
        and not path.is_absolute()
        and ".." not in path.parts
        and not member.isdev()
    )


def verify_candidate_checkout(
    work_dir: Path, *, expected_candidate_sha: str, expected_candidate_tree: str
) -> None:
    """Prove the extracted filesystem and Git material equal candidate HEAD."""
    if not all(
        re.fullmatch(r"[0-9a-f]{40}", value)
        for value in (expected_candidate_sha, expected_candidate_tree)
    ):
        raise SourceIdentityError("candidate source identity mismatch")
    try:
        actual_sha = _git(work_dir, "rev-parse", "HEAD^{commit}")
        commit_tree = _git(work_dir, "rev-parse", "HEAD^{tree}")
        _git(work_dir, "config", "core.autocrlf", "false")
        _git(work_dir, "read-tree", "--empty")
        _git(work_dir, "add", "-f", "-A", "--", ".")
        extracted_tree = _git(work_dir, "write-tree")
    except SourceIdentityError as error:
        raise SourceIdentityError("candidate source identity mismatch") from error
    if (
        actual_sha != expected_candidate_sha
        or commit_tree != expected_candidate_tree
        or extracted_tree != expected_candidate_tree
    ):
        raise SourceIdentityError("candidate source identity mismatch")


def extract_verified_candidate(
    archive: Path,
    work_dir: Path,
    *,
    expected_candidate_sha: str,
    expected_candidate_tree: str,
) -> None:
    """Extract only after Git objects prove every filesystem byte is candidate HEAD."""
    if work_dir.exists() and any(work_dir.iterdir()):
        raise SourceIdentityError("candidate source identity mismatch")
    work_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as temporary:
        payload_dir = Path(temporary)
        try:
            with tarfile.open(archive, "r:gz") as outer:
                members = outer.getmembers()
                if (
                    tuple(member.name for member in members) != ARCHIVE_MEMBERS
                    or any(not member.isfile() or not _safe_member(member) for member in members)
                ):
                    raise SourceIdentityError("candidate source identity mismatch")
                outer.extractall(payload_dir, filter="data")

            _command(["git", "init", "-q", str(work_dir)])
            object_pack = payload_dir / ARCHIVE_MEMBERS[1]
            _command(
                ["git", "-C", str(work_dir), "index-pack", "--stdin"],
                input_bytes=object_pack.read_bytes(),
            )
            _git(work_dir, "cat-file", "-e", f"{expected_candidate_sha}^{{commit}}")
            _git(work_dir, "update-ref", "HEAD", expected_candidate_sha)

            source_tar = payload_dir / ARCHIVE_MEMBERS[0]
            with tarfile.open(source_tar, "r:") as source:
                source_members = source.getmembers()
                if any(not _safe_member(member) for member in source_members):
                    raise SourceIdentityError("candidate source identity mismatch")
                source.extractall(work_dir, filter="data")
        except (OSError, tarfile.TarError, subprocess.SubprocessError) as error:
            raise SourceIdentityError("candidate source identity mismatch") from error

    verify_candidate_checkout(
        work_dir,
        expected_candidate_sha=expected_candidate_sha,
        expected_candidate_tree=expected_candidate_tree,
    )
    if _git(work_dir, "status", "--porcelain=v1", "--untracked-files=all"):
        raise SourceIdentityError("candidate source identity mismatch")


def validate_gcs_metadata(
    document: object,
    *,
    expected_bucket: str,
    expected_object: str,
    expected_generation: str,
    expected_size: int,
) -> None:
    """Validate immutable object metadata returned for the pinned generation."""
    if not isinstance(document, dict) or (
        document.get("bucket") != expected_bucket
        or document.get("name") != expected_object
        or str(document.get("generation", "")) != expected_generation
        or str(document.get("size", "")) != str(expected_size)
    ):
        raise SourceIdentityError("candidate source identity mismatch")


def _read_json(
    request: urllib.request.Request,
    *,
    expected_scheme: str,
    expected_host: str,
    opener: Callable[..., object] = _NO_REDIRECT_OPENER,
) -> object:
    parsed = urllib.parse.urlsplit(request.full_url)
    if parsed.scheme != expected_scheme or parsed.hostname != expected_host:
        raise SourceIdentityError("candidate source identity unavailable")
    try:
        with opener(request, timeout=15) as response:
            final = urllib.parse.urlsplit(response.geturl())
            if (
                getattr(response, "status", None) != 200
                or final.scheme != expected_scheme
                or final.hostname != expected_host
                or response.geturl() != request.full_url
            ):
                raise SourceIdentityError("candidate source identity unavailable")
            return json.loads(response.read())
    except (OSError, ValueError, urllib.error.URLError) as error:
        raise SourceIdentityError("candidate source identity unavailable") from error


def verify_worker_source(environment: dict[str, str], work_dir: Path) -> None:
    """Verify GCS identity and Git-bound mounted bytes before test execution."""
    archive = Path(environment["PDD_SOURCE_ARCHIVE"])
    expected_size = int(environment["PDD_SOURCE_SIZE"])
    verify_local_source(
        archive,
        expected_sha256=environment["PDD_SOURCE_SHA256"],
        expected_size=expected_size,
    )

    token_request = urllib.request.Request(
        METADATA_TOKEN_URL, headers={"Metadata-Flavor": "Google"}
    )
    token_document = _read_json(
        token_request,
        expected_scheme="http",
        expected_host="metadata.google.internal",
    )
    token = token_document.get("access_token") if isinstance(token_document, dict) else None
    if not isinstance(token, str) or not token:
        raise SourceIdentityError("candidate source identity unavailable")

    bucket = environment["PDD_SOURCE_GCS_BUCKET"]
    object_name = environment["PDD_SOURCE_GCS_OBJECT"]
    generation = environment["PDD_SOURCE_GCS_GENERATION"]
    query = urllib.parse.urlencode(
        {"generation": generation, "fields": "bucket,name,generation,size"}
    )
    metadata_url = (
        f"https://storage.googleapis.com/storage/v1/b/{urllib.parse.quote(bucket, safe='')}"
        f"/o/{urllib.parse.quote(object_name, safe='')}?{query}"
    )
    metadata_request = urllib.request.Request(
        metadata_url, headers={"Authorization": f"Bearer {token}"}
    )
    document = _read_json(
        metadata_request,
        expected_scheme="https",
        expected_host="storage.googleapis.com",
    )
    validate_gcs_metadata(
        document,
        expected_bucket=bucket,
        expected_object=object_name,
        expected_generation=generation,
        expected_size=expected_size,
    )
    extract_verified_candidate(
        archive,
        work_dir,
        expected_candidate_sha=environment["PDD_CANDIDATE_SHA"],
        expected_candidate_tree=environment["PDD_CANDIDATE_TREE"],
    )


def parse_args() -> argparse.Namespace:
    """Parse source archive creation or worker verification arguments."""
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    archive = subparsers.add_parser("archive")
    archive.add_argument("--repo", type=Path, required=True)
    archive.add_argument("--output", type=Path, required=True)
    verify = subparsers.add_parser("verify")
    verify.add_argument("--work-dir", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    """Create a source archive or verify/extract its immutable worker identity."""
    args = parse_args()
    try:
        if args.command == "archive":
            print(json.dumps(create_archive(args.repo, args.output), sort_keys=True))
        else:
            verify_worker_source(dict(os.environ), args.work_dir)
    except (KeyError, ValueError, SourceIdentityError):
        print("FATAL: candidate source identity verification failed", file=sys.stderr)
        return 78
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
