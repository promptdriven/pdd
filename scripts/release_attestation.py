#!/usr/bin/env python3
"""Fail-closed boundary for pdd_cloud-attested release attempts.

Git can create a tag and a lease ref atomically, but it cannot make an
unchanged ``refs/heads/main`` update participate in that transaction: Git
omits a no-op refspec.  This helper therefore records a server-visible lease,
rechecks ``origin/main``, and refuses to create a tag until a server-side
compare-and-swap policy is available.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from dataclasses import dataclass


SHA_RE = re.compile(r"^[0-9a-f]{40}$")
OWNER_RE = re.compile(r"^pdd-cloud-[a-z0-9][a-z0-9._-]{0,127}$")
LEASE_RE = re.compile(r"^refs/pdd-cloud/release-lease$")


class AttestationError(RuntimeError):
    """A release attestation condition was not met."""


def git(*args: str) -> str:
    # Attestation binds to canonical Git object IDs. Explicitly disable
    # replacement objects for every read and mutation instead of inheriting a
    # caller-controlled replacement namespace.
    environment = os.environ.copy()
    environment.pop("GIT_REPLACE_REF_BASE", None)
    environment["GIT_NO_REPLACE_OBJECTS"] = "1"
    result = subprocess.run(
        ["git", *args],
        text=True,
        capture_output=True,
        check=False,
        env=environment,
    )
    if result.returncode:
        detail = result.stderr.strip() or result.stdout.strip() or "git command failed"
        raise AttestationError(f"{' '.join(args)}: {detail}")
    return result.stdout.strip()


def require_contract(version: str, sha: str, owner: str, lease_ref: str) -> None:
    if version != "2":
        raise AttestationError("unsupported pdd_cloud release-attestation contract version")
    if not SHA_RE.fullmatch(sha):
        raise AttestationError("PDD_CLOUD_VALIDATED_SHA must be one full lowercase 40-hex SHA")
    if not OWNER_RE.fullmatch(owner):
        raise AttestationError("PDD_CLOUD_RELEASE_LEASE_OWNER is malformed")
    if not LEASE_RE.fullmatch(lease_ref):
        raise AttestationError("PDD_CLOUD_RELEASE_LEASE_REF is not the reviewed lease ref")


@dataclass(frozen=True)
class Lease:
    ref: str
    oid: str
    local_ref: str


def check_canonical_origin() -> None:
    canonical = {
        "https://github.com/promptdriven/pdd.git",
        "https://github.com/promptdriven/pdd",
        "git@github.com:promptdriven/pdd.git",
        "git@github.com:promptdriven/pdd",
        "ssh://git@github.com/promptdriven/pdd.git",
        "ssh://git@github.com/promptdriven/pdd",
    }
    for args, label in (
        (("remote", "get-url", "--all", "origin"), "fetch"),
        (("remote", "get-url", "--push", "--all", "origin"), "push"),
    ):
        urls = [url for url in git(*args).splitlines() if url]
        if len(urls) != 1 or urls[0] not in canonical:
            raise AttestationError(f"origin must have exactly one canonical {label} URL")


def check_current_main(sha: str, *, require_canonical_origin: bool) -> None:
    if require_canonical_origin:
        check_canonical_origin()
    head = git("rev-parse", "HEAD")
    if head != sha:
        raise AttestationError(f"local HEAD {head} does not equal attested SHA {sha}")
    git("fetch", "origin", "main")
    remote_main = git("rev-parse", "refs/remotes/origin/main")
    if remote_main != sha:
        raise AttestationError(
            f"fresh origin/main {remote_main} does not equal attested SHA {sha}"
        )


def acquire(sha: str, owner: str, lease_ref: str) -> Lease:
    local_ref = f"refs/tags/{owner}"
    oid = ""
    pushed = False
    git("tag", "-a", "-f", owner, "-m", f"pdd_cloud release lease owner={owner}", sha)
    try:
        oid = git("rev-parse", f"{local_ref}^{{tag}}")
        try:
            # An empty expected value makes this a create-only lease. A plain
            # custom-ref push can otherwise replace another attempt's tag
            # object when both tags peel to the same commit.
            git(
                "push",
                f"--force-with-lease={lease_ref}:",
                "origin",
                f"{local_ref}:{lease_ref}",
            )
            pushed = True
        except AttestationError as push_error:
            # A transport can report failure after the server accepted the
            # ref update. Read the remote before classifying this as ordinary
            # contention, and arrange exact owner-safe cleanup when our OID
            # may have landed.
            try:
                observed = remote_lease_oid(lease_ref)
            except AttestationError as readback_error:
                pushed = True
                raise AttestationError(
                    "remote lease push outcome is ambiguous after client failure: "
                    f"{push_error}; remote readback failed: {readback_error}"
                ) from push_error
            if observed == oid:
                pushed = True
                raise AttestationError(
                    "remote lease push reported client failure after accepting this "
                    "attempt; attempting owner-safe cleanup"
                ) from push_error
            if observed is not None:
                raise AttestationError(
                    "another release attempt already owns the remote lease "
                    f"at {observed}; push failure: {push_error}"
                ) from push_error
            raise AttestationError(
                f"remote lease push failed and no remote lease was observed: {push_error}"
            ) from push_error
        observed = remote_lease_oid(lease_ref)
        if observed != oid:
            raise AttestationError("remote lease readback is ambiguous")
        return Lease(ref=lease_ref, oid=oid, local_ref=local_ref)
    except Exception as primary_error:
        cleanup_errors: list[str] = []
        if pushed:
            try:
                # A successful push may be followed by a transport failure or
                # ambiguous readback. Delete only the exact object we pushed;
                # never leave a remote lease orphaned when that cleanup works.
                cleanup(Lease(lease_ref, oid, local_ref))
            except AttestationError as cleanup_error:
                cleanup_errors.append(str(cleanup_error))
        else:
            try:
                git("tag", "-d", owner)
            except AttestationError as cleanup_error:
                cleanup_errors.append(f"local lease cleanup failed: {cleanup_error}")
        if cleanup_errors:
            raise AttestationError(
                f"{primary_error}; {'; '.join(cleanup_errors)}"
            ) from primary_error
        raise


def remote_lease_oid(lease_ref: str) -> str | None:
    """Return the exact remote lease OID, or None when it is absent."""
    lines = [line.split() for line in git("ls-remote", "origin", lease_ref).splitlines()]
    if not lines:
        return None
    if (
        len(lines) != 1
        or len(lines[0]) != 2
        or not SHA_RE.fullmatch(lines[0][0])
        or lines[0][1] != lease_ref
    ):
        raise AttestationError("remote lease readback is ambiguous")
    return lines[0][0]


def cleanup(lease: Lease) -> None:
    cleanup_errors: list[str] = []
    try:
        # Unlike a no-op main refspec, this deletion sends an actual ref update.
        # The lease makes cleanup owner-safe if the ref changed after acquisition.
        git("push", f"--force-with-lease={lease.ref}:{lease.oid}", "origin", f":{lease.ref}")
    except AttestationError as cleanup_error:
        cleanup_errors.append(f"remote lease cleanup failed: {cleanup_error}")
    try:
        git("tag", "-d", lease.local_ref.removeprefix("refs/tags/"))
    except AttestationError as cleanup_error:
        cleanup_errors.append(f"local lease cleanup failed: {cleanup_error}")
    if cleanup_errors:
        raise AttestationError("; ".join(cleanup_errors))


def command_validate(args: argparse.Namespace) -> int:
    require_contract(args.version, args.sha, args.owner, args.lease_ref)
    return 0


def command_acquire(args: argparse.Namespace) -> int:
    require_contract(args.version, args.sha, args.owner, args.lease_ref)
    lease = acquire(args.sha, args.owner, args.lease_ref)
    print(lease.oid)
    return 0


def command_cleanup(args: argparse.Namespace) -> int:
    require_contract(args.version, args.sha, args.owner, args.lease_ref)
    if not re.fullmatch(r"[0-9a-f]{40}", args.lease_oid):
        raise AttestationError("lease object ID is malformed")
    cleanup(Lease(args.lease_ref, args.lease_oid, f"refs/tags/{args.owner}"))
    return 0


def command_final_boundary(args: argparse.Namespace) -> int:
    require_contract(args.version, args.sha, args.owner, args.lease_ref)
    check_current_main(args.sha, require_canonical_origin=args.canonical_origin)
    lease = acquire(args.sha, args.owner, args.lease_ref)
    try:
        check_current_main(args.sha, require_canonical_origin=args.canonical_origin)
        raise AttestationError(
            "pdd_cloud-attested tag creation is disabled: Git cannot atomically "
            "compare unchanged origin/main with tag creation; a no-op main refspec "
            "is omitted and is not a server compare-and-swap"
        )
    except AttestationError as primary_error:
        try:
            cleanup(lease)
        except AttestationError as cleanup_error:
            raise AttestationError(
                f"{primary_error}; lease cleanup failed: {cleanup_error}"
            ) from primary_error
        raise


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser()
    subparsers = result.add_subparsers(dest="command", required=True)
    for name, handler, needs_oid in (
        ("validate", command_validate, False),
        ("acquire", command_acquire, False),
        ("cleanup", command_cleanup, True),
        ("final-boundary", command_final_boundary, False),
    ):
        item = subparsers.add_parser(name)
        item.add_argument("--version", required=True)
        item.add_argument("--sha", required=True)
        item.add_argument("--owner", required=True)
        item.add_argument("--lease-ref", required=True)
        if name == "final-boundary":
            item.add_argument("--canonical-origin", action="store_true")
        if needs_oid:
            item.add_argument("--lease-oid", required=True)
        item.set_defaults(handler=handler)
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        return args.handler(args)
    except AttestationError as error:
        print(f"release attestation failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
