#!/usr/bin/env python3
"""Create and verify immutable Cloud Batch source archives."""
# pylint: disable=invalid-name,duplicate-code

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import urllib.error
import urllib.parse
import urllib.request
from collections.abc import Callable, Sequence
from pathlib import Path


METADATA_TOKEN_URL = (
    "http://metadata.google.internal/computeMetadata/v1/instance/"
    "service-accounts/default/token"
)


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


def _git(repo: Path, *arguments: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(repo), *arguments],
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        raise SourceIdentityError("candidate source identity unavailable")
    return result.stdout.strip()


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def create_archive(repo: Path, output: Path, paths: Sequence[str]) -> dict[str, object]:
    """Archive exact tracked HEAD bytes after rejecting any working-tree drift."""
    if _git(repo, "status", "--porcelain=v1", "--untracked-files=all"):
        raise SourceIdentityError("candidate worktree is not clean")
    candidate_sha = _git(repo, "rev-parse", "HEAD^{commit}")
    candidate_tree = _git(repo, "rev-parse", "HEAD^{tree}")
    if not paths:
        raise SourceIdentityError("candidate source paths unavailable")

    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as temporary:
        tar_path = Path(temporary) / "source.tar"
        result = subprocess.run(
            [
                "git",
                "-C",
                str(repo),
                "archive",
                "--format=tar",
                f"--output={tar_path}",
                candidate_sha,
                "--",
                *paths,
            ],
            check=False,
            capture_output=True,
        )
        if result.returncode != 0:
            raise SourceIdentityError("candidate source archive failed")
        with tar_path.open("rb") as source, output.open("wb") as destination:
            with gzip.GzipFile(fileobj=destination, mode="wb", filename="", mtime=0) as zipped:
                for chunk in iter(lambda: source.read(1024 * 1024), b""):
                    zipped.write(chunk)

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


def verify_worker_source(environment: dict[str, str]) -> None:
    """Verify mounted bytes and their exact GCS generation with workload identity."""
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


def parse_args() -> argparse.Namespace:
    """Parse source archive creation or worker verification arguments."""
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    archive = subparsers.add_parser("archive")
    archive.add_argument("--repo", type=Path, required=True)
    archive.add_argument("--output", type=Path, required=True)
    archive.add_argument("--path", action="append", default=[])
    subparsers.add_parser("verify")
    return parser.parse_args()


def main() -> int:
    """Create a source archive or verify its immutable worker identity."""
    args = parse_args()
    try:
        if args.command == "archive":
            print(json.dumps(create_archive(args.repo, args.output, args.path), sort_keys=True))
        else:
            verify_worker_source(dict(os.environ))
    except (KeyError, ValueError, SourceIdentityError):
        print("FATAL: candidate source identity verification failed", file=sys.stderr)
        return 78
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
