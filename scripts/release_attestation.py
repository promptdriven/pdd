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
from contextlib import contextmanager
import json
import os
import re
import signal
import subprocess
import sys
from dataclasses import dataclass


SHA_RE = re.compile(r"^[0-9a-f]{40}$")
OWNER_RE = re.compile(r"^pdd-cloud-[a-z0-9][a-z0-9._-]{0,127}$")
LEASE_RE = re.compile(r"^refs/pdd-cloud/release-lease$")
TAGGER_RE = re.compile(r"^tagger .+ <[^\n<>]+> (?P<epoch>[0-9]+) [+-][0-9]{4}$")


class AttestationError(RuntimeError):
    """A release attestation condition was not met."""


class SignalInterrupted(BaseException):
    """A catchable termination signal that still retains its exit status."""

    def __init__(self, signum: int, cleanup_detail: str = "") -> None:
        self.signum = signum
        self.cleanup_detail = cleanup_detail
        super().__init__(signal.Signals(signum).name)


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


@dataclass(frozen=True)
class LeaseDetails:
    oid: str
    owner: str
    sha: str
    created_epoch: int


def _interrupt(signum: int, _frame: object) -> None:
    raise SignalInterrupted(signum)


@contextmanager
def termination_signals_as_exceptions():
    """Turn SIGINT/SIGTERM into cleanup-triggering exceptions while in the CLI."""
    previous = {item: signal.getsignal(item) for item in (signal.SIGINT, signal.SIGTERM)}
    for item in previous:
        signal.signal(item, _interrupt)
    try:
        yield
    finally:
        for item, handler in previous.items():
            signal.signal(item, handler)


def _rethrow_after_cleanup(primary_error: BaseException, cleanup_errors: list[str]) -> None:
    """Preserve interruption semantics while retaining any cleanup failure."""
    if not cleanup_errors:
        raise primary_error
    detail = "; ".join(cleanup_errors)
    if isinstance(primary_error, AttestationError):
        raise AttestationError(f"{primary_error}; {detail}") from primary_error
    if isinstance(primary_error, SignalInterrupted):
        raise SignalInterrupted(primary_error.signum, detail) from primary_error
    if hasattr(primary_error, "add_note"):
        primary_error.add_note(f"lease cleanup failed: {detail}")
    raise primary_error


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
    except BaseException as primary_error:
        cleanup_errors: list[str] = []
        if pushed:
            try:
                # A successful push may be followed by a transport failure or
                # ambiguous readback. Delete only the exact object we pushed;
                # never leave a remote lease orphaned when that cleanup works.
                cleanup(Lease(lease_ref, oid, local_ref))
            except BaseException as cleanup_error:
                cleanup_errors.append(str(cleanup_error))
        else:
            try:
                git("tag", "-d", owner)
            except BaseException as cleanup_error:
                cleanup_errors.append(f"local lease cleanup failed: {cleanup_error}")
        _rethrow_after_cleanup(primary_error, cleanup_errors)


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


def delete_remote_lease_exact(lease_ref: str, expected_oid: str) -> None:
    """Delete only ``expected_oid`` and prove the remote outcome before returning."""
    push_error: AttestationError | None = None
    try:
        # Unlike a no-op main refspec, this deletion sends an actual ref update.
        # The expected old OID fences both ordinary and stale-owner cleanup.
        git("push", f"--force-with-lease={lease_ref}:{expected_oid}", "origin", f":{lease_ref}")
    except AttestationError as error:
        push_error = error

    try:
        observed = remote_lease_oid(lease_ref)
    except AttestationError as readback_error:
        if push_error is not None:
            raise AttestationError(
                "remote lease cleanup outcome is ambiguous after push failure: "
                f"{push_error}; remote readback failed: {readback_error}"
            ) from push_error
        raise AttestationError(
            "remote lease cleanup outcome is ambiguous after push success: "
            f"remote readback failed: {readback_error}"
        ) from readback_error

    if observed is None:
        # A client can receive a transport error after the server accepted the
        # deletion. A fresh absence readback is the only success condition.
        return
    if observed != expected_oid:
        raise AttestationError(
            "remote lease changed during cleanup; exact-OID fence preserved the "
            f"successor at {observed}"
        ) from push_error
    if push_error is not None:
        raise AttestationError(
            f"remote lease cleanup failed and still owns expected OID {expected_oid}: {push_error}"
        ) from push_error
    raise AttestationError(
        f"remote lease cleanup push reported success but still owns expected OID {expected_oid}"
    )


def cleanup(lease: Lease) -> None:
    cleanup_errors: list[str] = []
    try:
        delete_remote_lease_exact(lease.ref, lease.oid)
    except AttestationError as cleanup_error:
        cleanup_errors.append(f"remote lease cleanup failed: {cleanup_error}")
    try:
        git("tag", "-d", lease.local_ref.removeprefix("refs/tags/"))
    except AttestationError as cleanup_error:
        cleanup_errors.append(f"local lease cleanup failed: {cleanup_error}")
    if cleanup_errors:
        raise AttestationError("; ".join(cleanup_errors))


def _lease_tag_details(lease_ref: str, expected_oid: str) -> LeaseDetails:
    """Fetch and validate the exact annotated tag currently fencing a lease."""
    observed = remote_lease_oid(lease_ref)
    if observed is None:
        raise AttestationError("remote lease is absent")
    if observed != expected_oid:
        raise AttestationError(
            f"remote lease OID changed: expected {expected_oid}, observed {observed}"
        )

    local_ref = f"refs/pdd-cloud/recovery-{os.getpid()}-{expected_oid[:12]}"
    try:
        git("fetch", "--no-tags", "origin", f"{lease_ref}:{local_ref}")
        fetched_oid = git("rev-parse", local_ref)
        if fetched_oid != expected_oid:
            raise AttestationError(
                f"fetched lease OID changed: expected {expected_oid}, observed {fetched_oid}"
            )
        if git("cat-file", "-t", expected_oid) != "tag":
            raise AttestationError("remote lease must be an annotated tag object")
        raw_tag = git("cat-file", "-p", expected_oid)
    finally:
        try:
            git("update-ref", "-d", local_ref)
        except AttestationError:
            # This local diagnostic ref is never used for deletion; do not hide
            # a successful remote inspection if a concurrent local tool removed it.
            pass

    header, separator, message = raw_tag.partition("\n\n")
    if not separator:
        raise AttestationError("remote lease tag is malformed")
    fields: dict[str, str] = {}
    for line in header.splitlines():
        key, value = line.split(" ", 1) if " " in line else ("", "")
        if key in fields or key not in {"object", "type", "tag", "tagger"}:
            raise AttestationError("remote lease tag headers are malformed")
        fields[key] = value
    if set(fields) != {"object", "type", "tag", "tagger"}:
        raise AttestationError("remote lease tag headers are incomplete")
    if fields["type"] != "commit" or not SHA_RE.fullmatch(fields["object"]):
        raise AttestationError("remote lease tag target is malformed")
    if not OWNER_RE.fullmatch(fields["tag"]):
        raise AttestationError("remote lease tag owner is malformed")
    tagger = TAGGER_RE.fullmatch(f"tagger {fields['tagger']}")
    if tagger is None:
        raise AttestationError("remote lease tagger timestamp is malformed")
    owner = fields["tag"]
    if message != f"pdd_cloud release lease owner={owner}":
        raise AttestationError("remote lease tag message does not bind its owner")
    return LeaseDetails(
        oid=expected_oid,
        owner=owner,
        sha=fields["object"],
        created_epoch=int(tagger.group("epoch")),
    )


def inspect_lease(lease_ref: str) -> LeaseDetails | None:
    """Return durable metadata for the current lease without changing it."""
    oid = remote_lease_oid(lease_ref)
    if oid is None:
        return None
    return _lease_tag_details(lease_ref, oid)


def recover_stale_lease(
    lease_ref: str,
    lease_oid: str,
    owner: str,
    sha: str,
    stale_before_epoch: int,
) -> LeaseDetails:
    """Manually recover a proven-old lease with an exact-OID remote CAS delete."""
    details = _lease_tag_details(lease_ref, lease_oid)
    if details.owner != owner or details.sha != sha:
        raise AttestationError(
            "remote lease metadata differs from the manually reviewed owner/SHA"
        )
    if details.created_epoch > stale_before_epoch:
        raise AttestationError(
            "remote lease is newer than the manually supplied stale cutoff; "
            "refusing automatic expiry"
        )
    delete_remote_lease_exact(lease_ref, lease_oid)
    return details


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


def command_inspect_lease(args: argparse.Namespace) -> int:
    if not LEASE_RE.fullmatch(args.lease_ref):
        raise AttestationError("PDD_CLOUD_RELEASE_LEASE_REF is not the reviewed lease ref")
    details = inspect_lease(args.lease_ref)
    if details is None:
        print(json.dumps({"lease": None}, sort_keys=True))
    else:
        print(
            json.dumps(
                {
                    "created_epoch": details.created_epoch,
                    "lease_oid": details.oid,
                    "owner": details.owner,
                    "sha": details.sha,
                },
                sort_keys=True,
            )
        )
    return 0


def command_recover_stale_lease(args: argparse.Namespace) -> int:
    if not LEASE_RE.fullmatch(args.lease_ref):
        raise AttestationError("PDD_CLOUD_RELEASE_LEASE_REF is not the reviewed lease ref")
    if not SHA_RE.fullmatch(args.lease_oid):
        raise AttestationError("lease object ID is malformed")
    if not OWNER_RE.fullmatch(args.expected_owner):
        raise AttestationError("expected lease owner is malformed")
    if not SHA_RE.fullmatch(args.expected_sha):
        raise AttestationError("expected lease SHA is malformed")
    if args.stale_before_epoch < 0:
        raise AttestationError("stale cutoff epoch must be nonnegative")
    details = recover_stale_lease(
        args.lease_ref,
        args.lease_oid,
        args.expected_owner,
        args.expected_sha,
        args.stale_before_epoch,
    )
    print(
        json.dumps(
            {
                "recovered_lease_oid": details.oid,
                "owner": details.owner,
                "sha": details.sha,
            },
            sort_keys=True,
        )
    )
    return 0


def command_final_boundary(args: argparse.Namespace) -> int:
    require_contract(args.version, args.sha, args.owner, args.lease_ref)
    check_current_main(args.sha, require_canonical_origin=args.canonical_origin)
    lease: Lease | None = None
    try:
        lease = acquire(args.sha, args.owner, args.lease_ref)
        check_current_main(args.sha, require_canonical_origin=args.canonical_origin)
        raise AttestationError(
            "pdd_cloud-attested tag creation is disabled: Git cannot atomically "
            "compare unchanged origin/main with tag creation; a no-op main refspec "
            "is omitted and is not a server compare-and-swap"
        )
    except BaseException as primary_error:
        if lease is None:
            raise primary_error
        try:
            cleanup(lease)
        except BaseException as cleanup_error:
            _rethrow_after_cleanup(primary_error, [f"lease cleanup failed: {cleanup_error}"])
        raise primary_error


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
    inspect = subparsers.add_parser("inspect-lease")
    inspect.add_argument("--lease-ref", required=True)
    inspect.set_defaults(handler=command_inspect_lease)
    recover = subparsers.add_parser("recover-stale-lease")
    recover.add_argument("--lease-ref", required=True)
    recover.add_argument("--lease-oid", required=True)
    recover.add_argument("--expected-owner", required=True)
    recover.add_argument("--expected-sha", required=True)
    recover.add_argument("--stale-before-epoch", required=True, type=int)
    recover.set_defaults(handler=command_recover_stale_lease)
    return result


def main() -> int:
    args = parser().parse_args()
    with termination_signals_as_exceptions():
        try:
            return args.handler(args)
        except AttestationError as error:
            print(f"release attestation failed: {error}", file=sys.stderr)
            return 1
        except SignalInterrupted as error:
            detail = f"; lease cleanup failed: {error.cleanup_detail}" if error.cleanup_detail else ""
            print(
                f"release attestation interrupted by {signal.Signals(error.signum).name}{detail}",
                file=sys.stderr,
            )
            return 128 + error.signum


if __name__ == "__main__":
    raise SystemExit(main())
