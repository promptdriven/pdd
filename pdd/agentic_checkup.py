"""
Agentic checkup: LLM-driven project health check from a GitHub issue.

Entry point for ``pdd checkup <github_issue_url>``. Fetches issue content, loads
project context (architecture.json, .pddrc), then dispatches the multi-step
orchestrator that explores the project, identifies problems, and optionally
fixes them — one step per LLM call for reliability.
"""

from __future__ import annotations

import hashlib
import hmac
import json
import logging
import math
import os
import re
import secrets
import sys
import tempfile
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, IO, Iterator, List, Optional, Tuple, Union

from filelock import FileLock
from rich.console import Console

from .agentic_common import post_pr_comment, post_step_comment
from .agentic_change import (
    _check_gh_cli,
    _escape_format_braces,
    _parse_issue_url,
    _parse_pr_url,
    _run_gh_command,
)
from .agentic_checkup_orchestrator import (
    STEP5_SHELL_EVIDENCE_FILENAME,
    STEP5_SHELL_EVIDENCE_SCHEMA,
    _is_provider_failure,
    _is_step_timeout_failure,
    _load_step5_shell_evidence_from_memory,
    run_agentic_checkup_orchestrator,
)
from .checkup_review_loop import (
    FINAL_GATE_CATEGORY_FULL_SUITE,
    FINAL_GATE_CATEGORY_GITHUB_CHECKS,
    FINAL_GATE_CATEGORY_INCOMPLETE_VERIFICATION,
    FINAL_GATE_CATEGORY_LAYER1,
    FINAL_GATE_CATEGORY_PROVIDER_PARSER,
    FINAL_GATE_CATEGORY_SOURCE_OF_TRUTH,
    FINAL_GATE_REPORT_SCHEMA,
    SOURCE_OF_TRUTH_GUARD_REFUSAL_MARKERS,
    ReviewLoopConfig,
    ReviewLoopContext,
    _is_terra_sol_model,
    _scrub_secrets,
    clear_final_state,
    load_final_state,
    parse_reviewer_commands,
    parse_reviewers,
    parse_severity_list,
    parse_state_list,
    run_checkup_review_loop,
    write_terra_sol_progress,
    write_final_gate_fallback_artifact,
)
from .ci_validation import run_github_checks_gate
from .agentic_sync import _find_project_root, _load_architecture_json
from .prompt_repair import (
    PromptRepairConfig,
    discover_prompt_paths,
    format_token_delta_summary,
    run_prompt_repair_loop,
)

console = Console()
logger = logging.getLogger(__name__)


_TRUTHY_ENV_VALUES = {"1", "true", "yes", "on"}
_HOSTED_ARTIFACT_ENV_KEYS = (
    "PDD_CHECKUP_FALLBACK_MIRROR",
    "PDD_AGENTIC_CHECKUP_ARTIFACT_PATH",
)
_HOSTED_RECEIPT_KEY_ENV = "PDD_AGENTIC_CHECKUP_RECEIPT_KEY"
_HOSTED_RECEIPT_RUN_ID_ENV = "PDD_AGENTIC_CHECKUP_RECEIPT_RUN_ID"
_HOSTED_EXPECTED_HEAD_ENV = "PDD_CHECKUP_EXPECTED_HEAD_SHA"
_LOWER_HEX_64_RE = re.compile(r"[0-9a-f]{64}\Z")
_LOWER_HEX_40_RE = re.compile(r"[0-9a-f]{40}\Z")
_LOWER_HEX_32_RE = re.compile(r"[0-9a-f]{32}\Z")
# Semantic image-build capability marker. Hosted consumers must require this
# exact marker; older receipt producers reread the public pathname after
# publication and are not safe substitutes.
HOSTED_AGENTIC_ARTIFACT_CAPABILITY = "prepublication-snapshot-v2"


def _env_flag_enabled(value: Optional[str]) -> bool:
    """Return True for the small truthy vocabulary used by hosted env flags."""
    return str(value or "").strip().lower() in _TRUTHY_ENV_VALUES


@contextmanager
def _without_hosted_artifact_child_env() -> Iterator[None]:
    """Keep the outer hosted reservation out of Layer-1 child processes.

    Provider commands and test subprocesses inherit ``os.environ``.  If they
    receive the stable hosted path, a nested fixture checkup can claim that
    public slot (often as synthetic PR #1) and fence the real outer invocation
    out of its own final publication.  Temporarily remove only the transport
    variables while provider/test children run in either layer, then restore
    the caller's exact environment.
    """
    saved = {key: os.environ.get(key) for key in _HOSTED_ARTIFACT_ENV_KEYS}
    for key in _HOSTED_ARTIFACT_ENV_KEYS:
        os.environ.pop(key, None)
    try:
        yield
    finally:
        for key, value in saved.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value


def _hosted_agentic_artifact_path(project_root: Path) -> Optional[str]:
    """Resolve the pdd_cloud fallback/mirror artifact path env contract.

    ``PDD_CHECKUP_FALLBACK_MIRROR=1`` requests the additive
    ``pdd.checkup.agentic.v1`` artifact while preserving canonical checkup
    authority. ``PDD_AGENTIC_CHECKUP_ARTIFACT_PATH`` is the hosted
    caller-controlled destination; if an operator accidentally omits it, fall
    back to the same deterministic path pdd_cloud documents instead of silently
    disabling artifact emission.
    """
    if not _env_flag_enabled(os.environ.get("PDD_CHECKUP_FALLBACK_MIRROR")):
        return None
    configured = str(os.environ.get("PDD_AGENTIC_CHECKUP_ARTIFACT_PATH", ""))
    if configured:
        return configured
    return str(
        project_root / ".pdd" / "artifacts" / "agentic_checkup_fallback_mirror.json"
    )


def _hosted_agentic_reviewers(reviewers: str) -> str:
    """Resolve hosted fallback reviewer commands from the env contract.

    Issue #1884.
    ``PDD_AGENTIC_CHECKUP_REVIEWERS`` is intentionally scoped behind
    ``PDD_CHECKUP_FALLBACK_MIRROR`` so normal local checkup runs keep their CLI
    semantics. A caller-provided ``--reviewers role:/command`` value wins over
    the env knob; hosted pdd_cloud can set the env only when it wants additive
    fallback/mirror evidence such as ``codex:/review,claude:/code-review``.
    """
    if not _env_flag_enabled(os.environ.get("PDD_CHECKUP_FALLBACK_MIRROR")):
        return reviewers
    if any(command for command in parse_reviewer_commands(reviewers).values()):
        return reviewers
    configured = str(os.environ.get("PDD_AGENTIC_CHECKUP_REVIEWERS", "")).strip()
    if not configured:
        return reviewers
    if not any(command for command in parse_reviewer_commands(configured).values()):
        return reviewers
    return configured


@dataclass(frozen=True)
class _HostedAgenticArtifactReservation:
    """Invocation-private hosted artifact and its stable publication slot."""

    public_path: Path
    private_path: Path
    lock_path: Path
    invocation_id: str
    identity_digest: str
    pr_number: int
    receipt_key: Optional[bytes] = field(default=None, repr=False)
    receipt_artifact_path: str = ""
    receipt_run_id: str = ""
    receipt_expected_head_sha: str = ""
    private_dir: Optional[Path] = field(default=None, repr=False)
    private_file: Optional[IO[str]] = field(default=None, repr=False)
    private_payload: bytearray = field(default_factory=bytearray, repr=False)

    def cleanup(self) -> None:
        """Remove invocation-private state while retaining the public blocker."""
        try:
            self.private_path.unlink(missing_ok=True)
        except OSError:
            pass
        if self.private_file is not None:
            try:
                self.private_file.close()
            except OSError:
                pass
        if self.private_dir is not None:
            try:
                self.private_dir.rmdir()
            except OSError:
                pass

    def __del__(self) -> None:
        # ``run_agentic_checkup`` has many validation/network early returns.
        # CPython releases this local reservation at function exit, providing a
        # final safety net that cannot leave private/owner files behind.
        self.cleanup()

    def read_private_bytes(self) -> bytes:
        """Read the anonymous staging descriptor from offset zero."""
        if self.private_payload:
            return bytes(self.private_payload)
        if self.private_file is None:
            return self.private_path.read_bytes()
        self.private_file.flush()
        self.private_file.seek(0)
        return self.private_file.read().encode("utf-8")

    def write_private_bytes(self, payload: bytes) -> None:
        """Replace anonymous staging contents without sharing a stale offset."""
        self.private_payload[:] = payload
        return


@contextmanager
def _hosted_artifact_lock(lock_path: Path) -> Iterator[None]:
    """Serialize public-slot compare-and-swap operations across processes."""
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with FileLock(str(lock_path)):
        yield


def _atomic_publish_hosted_payload(path: Path, payload: Dict[str, Any]) -> None:
    """Atomically publish one hosted payload to ``path``."""
    tmp = tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        prefix=f".{path.name}.",
        suffix=".tmp",
        dir=str(path.parent),
        delete=False,
    )  # pylint: disable=consider-using-with -- closed before atomic replace
    try:
        tmp.write(json.dumps(payload, indent=2))
        tmp.close()
        os.replace(tmp.name, str(path))
    except OSError:
        try:
            os.unlink(tmp.name)
        except OSError:
            pass
        raise


def _atomic_publish_hosted_bytes(path: Path, payload: bytes) -> None:
    """Publish a trusted in-memory snapshot without renaming its staging fd."""
    tmp = tempfile.NamedTemporaryFile(
        mode="wb",
        prefix=f".{path.name}.",
        suffix=".publish.tmp",
        dir=str(path.parent),
        delete=False,
    )
    try:
        tmp.write(payload)
        tmp.flush()
        os.fsync(tmp.fileno())
        tmp.close()
        os.replace(tmp.name, str(path))
    except OSError:
        try:
            tmp.close()
            os.unlink(tmp.name)
        except OSError:
            pass
        raise


def _hosted_blocking_payload(
    invocation_id: str,
    *,
    pr_number: int = 0,
    head_sha: str = "",
    reason: str = "Current hosted checkup invocation has not produced a verdict.",
) -> Dict[str, Any]:
    """Return the fail-closed public record shared by invalidation/reservation."""
    return {
        "schema_version": "pdd.checkup.agentic.v1",
        "invocation_id": invocation_id,
        "owner": "",
        "repo": "",
        "pr_number": pr_number,
        "head_sha": head_sha,
        "status": "error",
        "authority": "canonical_unknown_agentic_fallback_blocking",
        "layer1": {"status": "unknown", "blockers": [reason]},
        "verdict": {"decision": "block", "reason": reason},
    }


def _invalidate_hosted_agentic_artifact(artifact_path: Optional[str]) -> bool:
    """Replace a prior public verdict before validation can return early.

    This deliberately does not reserve private storage or bind PR/issue
    identity. Identity-bound reservation remains later, after Terra/Sol has
    cleared its local final state. If an atomic blocker cannot be installed,
    remove a stale public record so an earlier PASS is never current.
    """
    if not artifact_path:
        return True
    path = Path(artifact_path)
    lock_path = path.with_name(f".{path.name}.lock")
    invocation_id = secrets.token_hex(16)
    payload = _hosted_blocking_payload(invocation_id)
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with _hosted_artifact_lock(lock_path):
            _atomic_publish_hosted_payload(path, payload)
        persisted = json.loads(path.read_text(encoding="utf-8"))
        return bool(
            isinstance(persisted, dict)
            and persisted.get("invocation_id") == invocation_id
            and persisted.get("status") != "passed"
            and isinstance(persisted.get("verdict"), dict)
            and persisted["verdict"].get("decision") == "block"
        )
    except (OSError, TypeError, ValueError, json.JSONDecodeError):
        try:
            with _hosted_artifact_lock(lock_path):
                try:
                    current = json.loads(path.read_text(encoding="utf-8"))
                except (OSError, json.JSONDecodeError):
                    current = None
                current_id = (
                    current.get("invocation_id")
                    if isinstance(current, dict)
                    else None
                )
                if current_id in (None, invocation_id):
                    path.unlink(missing_ok=True)
        except (OSError, TypeError, json.JSONDecodeError):
            pass
        return False


def _prepare_hosted_agentic_artifact(
    artifact_path: Optional[str],
    *,
    pr_owner: str = "",
    pr_repo: str = "",
    pr_number: int = 0,
    receipt_key_hex: Optional[str] = None,
    receipt_run_id: str = "",
    receipt_expected_head_sha: str = "",
) -> Optional[_HostedAgenticArtifactReservation]:
    """Reserve a private path and claim the public slot for parsed identities.

    Anonymous public invalidation runs separately before validation. This
    identity-bound reservation runs only after Terra/Sol clears local state;
    its nonce then provides locked compare-and-swap publication ownership.
    """
    if not artifact_path:
        return None
    receipt_key: Optional[bytes] = None
    if receipt_key_hex is not None:
        if (
            _LOWER_HEX_64_RE.fullmatch(receipt_key_hex) is None
            or _LOWER_HEX_32_RE.fullmatch(receipt_run_id) is None
            or _LOWER_HEX_40_RE.fullmatch(receipt_expected_head_sha) is None
        ):
            return None
        receipt_key = bytes.fromhex(receipt_key_hex)
    path = Path(artifact_path)
    safe_owner = _scrub_secrets(str(pr_owner or ""))[:2000]
    safe_repo = _scrub_secrets(str(pr_repo or ""))[:2000]
    identity_digest = hashlib.sha256(
        f"{safe_owner}\0{safe_repo}\0{pr_number}".encode("utf-8")
    ).hexdigest()
    private_path: Optional[Path] = None
    private_file: Optional[IO[str]] = None
    invocation_id = secrets.token_hex(16)
    lock_path = path.with_name(f".{path.name}.lock")
    claimed_public_slot = False
    blocking_payload = _hosted_blocking_payload(
        invocation_id,
        pr_number=pr_number,
        head_sha=receipt_expected_head_sha,
    )
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        # Claim and invalidate the public slot before reserving private storage.
        # If private reservation subsequently fails, this current blocker stays
        # visible instead of exposing a pass from an earlier invocation.
        with _hosted_artifact_lock(lock_path):
            _atomic_publish_hosted_payload(path, blocking_payload)
            claimed_public_slot = True
        public_payload = json.loads(path.read_text(encoding="utf-8"))
        if not (
            isinstance(public_payload, dict)
            and public_payload.get("invocation_id") == invocation_id
            and public_payload.get("status") != "passed"
            and isinstance(public_payload.get("verdict"), dict)
            and public_payload["verdict"].get("decision") == "block"
        ):
            raise ValueError("hosted public placeholder failed readback")
        # Anonymous parent-owned staging: the descriptor is non-inheritable and
        # has no target-workspace pathname for reviewers, tests, or detached
        # target processes to poll/replace. `/dev/fd/N` lets trusted in-process
        # writers use their existing path API while still addressing this fd.
        reserved = tempfile.TemporaryFile(mode="w+", encoding="utf-8")
        private_file = reserved
        os.set_inheritable(reserved.fileno(), False)
        private_path = Path(f"/dev/fd/{reserved.fileno()}")
        private_dir = None
        written_path = write_final_gate_fallback_artifact(
            artifact_path=str(private_path),
            pr_owner="",
            pr_repo="",
            pr_number=pr_number,
            head_sha=receipt_expected_head_sha,
            canonical_status="unknown",
            blockers=["Current hosted checkup invocation has not produced a verdict."],
            no_fix=True,
        )
        if (
            written_path is None
            or Path(written_path).resolve() != private_path.resolve()
        ):
            raise ValueError("hosted placeholder writer returned the wrong path")
        reserved.flush()
        reserved.seek(0)
        payload = json.loads(reserved.read())
        if not (
            isinstance(payload, dict)
            and payload.get("schema_version") == "pdd.checkup.agentic.v1"
            and payload.get("status") != "passed"
            and payload.get("authority")
            == "canonical_unknown_agentic_fallback_blocking"
            and isinstance(payload.get("verdict"), dict)
            and payload["verdict"].get("decision") == "block"
        ):
            raise ValueError("hosted placeholder is not a blocking v1 artifact")
        # Retain the blocking placeholder until the real review overwrites it.
        # Besides preserving fail-closed behavior when a mocked or interrupted
        # producer emits nothing, this gives finalization a valid artifact to
        # downgrade rather than an empty descriptor.
        reserved.seek(0)
        reservation = _HostedAgenticArtifactReservation(
            public_path=path,
            private_path=private_path,
            lock_path=lock_path,
            invocation_id=invocation_id,
            identity_digest=identity_digest,
            pr_number=pr_number,
            receipt_key=receipt_key,
            receipt_artifact_path=artifact_path,
            receipt_run_id=receipt_run_id,
            receipt_expected_head_sha=receipt_expected_head_sha,
            private_dir=private_dir,
            private_file=reserved,
            private_payload=bytearray(json.dumps(payload, indent=2).encode("utf-8")),
        )
        return reservation
    except (OSError, ValueError, TypeError, json.JSONDecodeError):
        if private_file is not None:
            try:
                private_file.close()
            except OSError:
                pass
        try:
            with _hosted_artifact_lock(lock_path):
                try:
                    current = json.loads(path.read_text(encoding="utf-8"))
                except (OSError, json.JSONDecodeError):
                    current = None
                current_id = (
                    current.get("invocation_id") if isinstance(current, dict) else None
                )
                # Retain our already-published blocker. If the claim itself
                # failed, replace/remove any nonce-less stale PASS. Never touch
                # a different invocation's demonstrably current placeholder.
                if current_id != invocation_id and current_id is None:
                    failure_payload = dict(blocking_payload)
                    failure_payload["layer1"] = {
                        "status": "unknown",
                        "blockers": ["Hosted artifact provenance setup failed."],
                    }
                    failure_payload["verdict"] = {
                        "decision": "block",
                        "reason": "Hosted artifact provenance setup failed.",
                    }
                    try:
                        _atomic_publish_hosted_payload(path, failure_payload)
                    except OSError:
                        path.unlink(missing_ok=True)
                elif claimed_public_slot and current_id == invocation_id:
                    # The single atomic ownership/blocking record is already
                    # the desired fail-closed result.
                    pass
        except (OSError, TypeError, json.JSONDecodeError):
            pass
        try:
            if private_path is not None:
                private_path.unlink(missing_ok=True)
        except OSError:
            pass
        return None


def _publish_hosted_agentic_artifact(
    reservation: Optional[_HostedAgenticArtifactReservation],
    *,
    canonical_passed: Optional[bool],
) -> Optional[str]:
    """Finalize and publish only if this invocation still owns the slot."""
    if reservation is None:
        return None
    try:
        if canonical_passed is not None:
            finalized_bytes = _finalize_hosted_agentic_payload(
                reservation.read_private_bytes(), canonical_passed=canonical_passed
            )
            # Canonical finalization is authoritative and terminal. It either
            # atomically downgrades/labels the private artifact IN PLACE (and
            # returns that same private path) or it fails closed. A ``None`` or
            # wrong-path result means the private payload was NOT finalized:
            # publishing it here could move a pre-finalization ``status="passed"``
            # into the public slot even though the canonical gate did not produce
            # a shippable verdict. Stop before any publication; the public path
            # retains its blocking placeholder, and the ``finally`` clause drops
            # the un-finalized private payload (issue #1788).
            if finalized_bytes is None:
                return None
            reservation.write_private_bytes(finalized_bytes)
        # Snapshot the producer-owned bytes once, before they enter the public
        # pathname.  The receipt must authenticate this exact snapshot rather
        # than bytes reopened from the target-writable public slot after
        # ``os.replace``.  A concurrent replacement after publication then
        # produces a digest mismatch at the consumer instead of turning the
        # producer into a signing oracle.
        artifact_bytes = reservation.read_private_bytes()
        payload = json.loads(artifact_bytes.decode("utf-8"))
        if (
            not isinstance(payload, dict)
            or payload.get("schema_version") != "pdd.checkup.agentic.v1"
        ):
            raise ValueError("hosted artifact is not a v1 object")
        artifact_owner = str(payload.get("owner", ""))
        artifact_repo = str(payload.get("repo", ""))
        artifact_pr_number = int(payload.get("pr_number", 0) or 0)
        artifact_digest = hashlib.sha256(
            f"{artifact_owner}\0{artifact_repo}\0{artifact_pr_number}".encode("utf-8")
        ).hexdigest()
        if artifact_pr_number != reservation.pr_number or (
            (artifact_owner or artifact_repo)
            and artifact_digest != reservation.identity_digest
        ):
            raise ValueError("hosted artifact PR identity mismatch")
        with _hosted_artifact_lock(reservation.lock_path):
            current = json.loads(reservation.public_path.read_text(encoding="utf-8"))
            if (
                not isinstance(current, dict)
                or current.get("invocation_id") != reservation.invocation_id
            ):
                return None
            _atomic_publish_hosted_bytes(reservation.public_path, artifact_bytes)
            if reservation.receipt_key is not None:
                artifact_digest = hashlib.sha256(artifact_bytes).hexdigest()
                receipt_message = json.dumps(
                    {
                        "schema_version": 1,
                        "artifact_sha256": artifact_digest,
                        "context": {
                            "artifact_path": reservation.receipt_artifact_path,
                            "expected_head_sha": reservation.receipt_expected_head_sha,
                            "run_id": reservation.receipt_run_id,
                        },
                    },
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=True,
                ).encode("utf-8")
                receipt_message = (
                    b"pdd-agentic-checkup-receipt-v1\0"
                    + len(receipt_message).to_bytes(8, "big")
                    + receipt_message
                )
                receipt = hmac.new(
                    reservation.receipt_key, receipt_message, hashlib.sha256
                ).hexdigest()
                print(
                    f"PDD_AGENTIC_CHECKUP_RECEIPT_V1={receipt}",
                    file=sys.stderr,
                    flush=True,
                )
        return str(reservation.public_path)
    except (OSError, ValueError, TypeError, json.JSONDecodeError):
        return None
    finally:
        try:
            reservation.private_path.unlink(missing_ok=True)
        except OSError:
            pass


def _require_hosted_publication(
    result: Tuple[bool, str, float, str],
    reservation: Optional[_HostedAgenticArtifactReservation],
    *,
    canonical_passed: Optional[bool],
) -> Tuple[bool, str, float, str]:
    """Make a requested hosted publication part of the terminal result."""
    if reservation is None:
        return result
    published = _publish_hosted_agentic_artifact(
        reservation, canonical_passed=canonical_passed
    )
    if published is not None:
        return result
    return (
        False,
        f"{result[1]} Hosted agentic artifact publication failed.",
        result[2],
        result[3],
    )


def _finalize_hosted_agentic_artifact(
    artifact_path: Optional[str],
    *,
    canonical_passed: bool,
) -> Optional[str]:
    """Apply the complete canonical final-gate verdict to a hosted artifact.

    The review loop emits its mirror/fallback details before the outer final
    gate has loaded ``final-state.json`` and derived the real ship verdict.
    Finalize authority only after that canonical result is known, so a Layer 2
    failure can never remain labeled ``canonical_pass_*``.
    """
    if not artifact_path:
        return None
    path = Path(artifact_path)

    def _atomic_publish(obj: Dict[str, Any]) -> None:
        """Atomically replace ``path`` with ``obj`` (temp + os.replace).

        A partial or interrupted write can never leave a truncated — or
        stale — artifact behind (issue #1788).
        """
        encoded = json.dumps(obj, indent=2).encode("utf-8")
        if path.parent == Path("/dev/fd") and path.name.isdigit():
            fd = int(path.name)
            os.ftruncate(fd, 0)
            os.lseek(fd, 0, os.SEEK_SET)
            os.write(fd, encoded)
            os.fsync(fd)
            os.lseek(fd, 0, os.SEEK_SET)
            return
        tmp = tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            prefix=f".{path.name}.",
            suffix=".tmp",
            dir=str(path.parent),
            delete=False,
        )
        try:
            tmp.write(encoded.decode("utf-8"))
            tmp.close()
            os.replace(tmp.name, str(path))
        except OSError:
            try:
                os.unlink(tmp.name)
            except OSError:
                pass
            raise

    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(payload, dict):
            raise ValueError("hosted agentic artifact must be a JSON object")
        if payload.get("schema_version") != "pdd.checkup.agentic.v1":
            raise ValueError("unexpected hosted agentic artifact schema")

        verdict = payload.get("verdict")
        if not isinstance(verdict, dict):
            verdict = {}
            payload["verdict"] = verdict
        mirror_blocking = (
            payload.get("status") != "passed" or verdict.get("decision") != "pass"
        )
        if canonical_passed:
            payload["authority"] = (
                "canonical_pass_agentic_mirror_blocking"
                if mirror_blocking
                else "canonical_pass_agentic_mirror_clean"
            )
        else:
            payload["authority"] = "canonical_fail_agentic_not_authoritative"
            if payload.get("status") == "passed":
                payload["status"] = "failed"
            verdict["decision"] = "block"
            verdict["reason"] = (
                "Canonical final gate did not produce a shippable verdict."
            )

        _atomic_publish(payload)
        return str(path)
    except (OSError, ValueError, TypeError) as exc:
        logger.warning(
            "Failed to finalize hosted agentic artifact (%s)", type(exc).__name__
        )
        # Fail closed: when the canonical final gate did NOT pass, the hosted
        # artifact must never remain consumable as a pass. If finalization
        # could not downgrade it, atomically replace it with a minimal blocking
        # tombstone, or remove it, so a stale ``status="passed"`` can never
        # survive a read/parse/write failure (issue #1788).
        if not canonical_passed:
            try:
                _atomic_publish(
                    {
                        "schema_version": "pdd.checkup.agentic.v1",
                        "status": "failed",
                        "authority": "canonical_fail_agentic_not_authoritative",
                        "layer1": {
                            "status": "fail",
                            "blockers": [
                                "Canonical final gate did not produce a "
                                "shippable verdict."
                            ],
                        },
                        "verdict": {
                            "decision": "block",
                            "reason": (
                                "Canonical final gate did not produce a "
                                "shippable verdict; hosted artifact "
                                "finalization failed."
                            ),
                        },
                    }
                )
            except OSError:
                try:
                    path.unlink(missing_ok=True)
                except OSError:
                    pass
        return None


def _finalize_hosted_agentic_payload(
    artifact_bytes: bytes, *, canonical_passed: bool
) -> Optional[bytes]:
    """Finalize trusted parent-memory bytes without exposing mutable storage."""
    try:
        payload = json.loads(artifact_bytes.decode("utf-8"))
        if not isinstance(payload, dict):
            raise ValueError("hosted agentic artifact must be a JSON object")
        if payload.get("schema_version") != "pdd.checkup.agentic.v1":
            raise ValueError("unexpected hosted agentic artifact schema")
        verdict = payload.get("verdict")
        if not isinstance(verdict, dict):
            verdict = {}
            payload["verdict"] = verdict
        mirror_blocking = (
            payload.get("status") != "passed" or verdict.get("decision") != "pass"
        )
        if canonical_passed:
            payload["authority"] = (
                "canonical_pass_agentic_mirror_blocking"
                if mirror_blocking
                else "canonical_pass_agentic_mirror_clean"
            )
        else:
            payload["authority"] = "canonical_fail_agentic_not_authoritative"
            if payload.get("status") == "passed":
                payload["status"] = "failed"
            verdict["decision"] = "block"
            verdict["reason"] = (
                "Canonical final gate did not produce a shippable verdict."
            )
        return json.dumps(payload, indent=2).encode("utf-8")
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError, TypeError):
        return None


def _extract_json_from_text(text: str) -> Optional[Dict[str, Any]]:
    """Extract the LAST top-level JSON object from agent output text.

    Matches the Step 7 prompt contract ("The JSON report MUST be the
    last output") so earlier intermediate-reasoning blocks never mask
    the final verdict. Handles fenced JSON, raw JSON, and the mixed
    case (fenced earlier blocks followed by an unfenced final verdict)
    uniformly — ``json.JSONDecoder.raw_decode`` ignores markdown fences
    and just looks for valid JSON starting at a ``{``.
    """
    if not text or not text.strip():
        return None

    decoder = json.JSONDecoder()
    last_match: Optional[Dict[str, Any]] = None
    search_from = 0
    while True:
        idx = text.find("{", search_from)
        if idx == -1:
            break
        try:
            obj, end = decoder.raw_decode(text, idx)
        except json.JSONDecodeError:
            search_from = idx + 1
            continue
        if isinstance(obj, dict):
            last_match = obj
        search_from = end if end > idx else idx + 1
    return last_match


def _load_pddrc_content(project_root: Path) -> str:
    """Load .pddrc file content from the project root."""
    pddrc_path = project_root / ".pddrc"
    if not pddrc_path.exists():
        return "No .pddrc found."
    try:
        return pddrc_path.read_text(encoding="utf-8")
    except OSError:
        return "Failed to read .pddrc."


def _post_checkup_comment(
    owner: str,
    repo: str,
    issue_number: int,
    report: Dict[str, Any],
) -> None:
    """Post checkup results as a GitHub issue comment."""
    issues = report.get("issues", [])
    changed_files = report.get("changed_files", [])
    tech_stack = report.get("tech_stack", [])
    success = report.get("success", False)
    message = report.get("message", "")

    status_emoji = "+" if success else "x"

    body_lines = [
        f"## PDD Checkup Report {status_emoji}",
        "",
        f"**Summary:** {message}",
        "",
    ]

    if tech_stack:
        body_lines.append(f"**Tech stack:** {', '.join(tech_stack)}")
        body_lines.append("")

    if issues:
        body_lines.append("### Issues Found")
        body_lines.append("")
        body_lines.append("| Severity | Category | Module | Description | Fixed |")
        body_lines.append("|----------|----------|--------|-------------|-------|")
        for issue in issues:
            sev = issue.get("severity", "?")
            cat = issue.get("category", "?")
            mod = issue.get("module", "?")
            desc = issue.get("description", "?")
            fixed = "yes" if issue.get("fixed", False) else "no"
            body_lines.append(f"| {sev} | {cat} | {mod} | {desc} | {fixed} |")
        body_lines.append("")

    if changed_files:
        body_lines.append("### Changed Files")
        body_lines.append("")
        for f in changed_files:
            body_lines.append(f"- `{f}`")
        body_lines.append("")

    body = "\n".join(body_lines)

    _run_gh_command(
        [
            "api",
            f"repos/{owner}/{repo}/issues/{issue_number}/comments",
            "-X",
            "POST",
            "-f",
            f"body={body}",
        ]
    )


def _post_error_comment(owner: str, repo: str, issue_number: int, message: str) -> None:
    """Post an error comment on the GitHub issue."""
    body = f"## PDD Checkup - Error\n\n```\n{message[:1000]}\n```\n"
    _run_gh_command(
        [
            "api",
            f"repos/{owner}/{repo}/issues/{issue_number}/comments",
            "-X",
            "POST",
            "-f",
            f"body={body}",
        ]
    )


def _fetch_pr_context(owner: str, repo: str, pr_number: int) -> str:
    """Fetch PR, comments, reviews, and changed-file context for review-loop prompts."""
    success, output = _run_gh_command(
        ["api", f"repos/{owner}/{repo}/pulls/{pr_number}"]
    )
    if not success:
        return f"Failed to fetch PR context: {output}"
    try:
        data = json.loads(output)
    except json.JSONDecodeError:
        return "Failed to parse PR context JSON."

    head = data.get("head") or {}
    base = data.get("base") or {}
    changed_files = _fetch_pr_changed_files(owner, repo, pr_number)
    conversation = _fetch_pr_conversation(owner, repo, pr_number)
    reviews = _fetch_pr_reviews(owner, repo, pr_number)
    return _truncate_context(
        f"Title: {data.get('title', '')}\n"
        f"Base: {base.get('label') or base.get('ref') or ''}\n"
        f"Head: {head.get('label') or head.get('ref') or ''}\n"
        f"State: {data.get('state', '')}\n"
        f"Mergeable state: {data.get('mergeable_state', '')}\n"
        f"Description:\n{data.get('body') or ''}\n\n"
        f"Changed files:\n{changed_files}\n\n"
        f"PR conversation comments:\n{conversation}\n\n"
        f"PR reviews:\n{reviews}",
        60000,
    )


def _fetch_pr_changed_files(owner: str, repo: str, pr_number: int) -> str:
    """Fetch a concise changed-file inventory for reviewer context."""
    success, output = _run_gh_command(
        ["api", f"repos/{owner}/{repo}/pulls/{pr_number}/files?per_page=100"]
    )
    if not success:
        return f"Failed to fetch changed files: {output}"
    try:
        files = json.loads(output)
    except json.JSONDecodeError:
        return "Failed to parse changed-file JSON."
    if not isinstance(files, list) or not files:
        return "No changed files reported."

    lines = []
    for item in files:
        if not isinstance(item, dict):
            continue
        filename = item.get("filename") or ""
        status = item.get("status") or ""
        additions = item.get("additions", 0)
        deletions = item.get("deletions", 0)
        patch = item.get("patch") or ""
        patch_hint = ""
        if patch:
            patch_hint = " | patch excerpt: " + _one_line(patch, 500)
        lines.append(f"- {filename} ({status}, +{additions}/-{deletions}){patch_hint}")
    return "\n".join(lines) if lines else "No changed files reported."


def _fetch_pr_conversation(owner: str, repo: str, pr_number: int) -> str:
    """Fetch PR issue-thread comments, which often explain direction changes."""
    success, output = _run_gh_command(
        ["api", f"repos/{owner}/{repo}/issues/{pr_number}/comments?per_page=100"]
    )
    if not success:
        return f"Failed to fetch PR comments: {output}"
    return _format_github_comment_list(output, body_key="body")


def _fetch_pr_reviews(owner: str, repo: str, pr_number: int) -> str:
    """Fetch submitted PR reviews for reviewer context."""
    success, output = _run_gh_command(
        ["api", f"repos/{owner}/{repo}/pulls/{pr_number}/reviews?per_page=100"]
    )
    if not success:
        return f"Failed to fetch PR reviews: {output}"
    return _format_github_comment_list(output, body_key="body", include_state=True)


def _format_github_comment_list(
    output: str,
    *,
    body_key: str,
    include_state: bool = False,
) -> str:
    try:
        items = json.loads(output)
    except json.JSONDecodeError:
        return "Failed to parse GitHub comment JSON."
    if not isinstance(items, list) or not items:
        return "None."

    lines = []
    for item in items:
        if not isinstance(item, dict):
            continue
        user = item.get("user") or {}
        author = user.get("login") if isinstance(user, dict) else ""
        created = item.get("submitted_at") or item.get("created_at") or ""
        state = f" [{item.get('state')}]" if include_state and item.get("state") else ""
        body = _one_line(item.get(body_key) or "", 1200)
        if not body:
            continue
        lines.append(f"- {author}{state} at {created}: {body}")
    return "\n".join(lines) if lines else "None."


def _one_line(text: str, limit: int) -> str:
    compact = re.sub(r"\s+", " ", text or "").strip()
    if len(compact) <= limit:
        return compact
    return compact[: max(0, limit - 3)].rstrip() + "..."


def _truncate_context(text: str, limit: int) -> str:
    if len(text) <= limit:
        return text
    return text[: max(0, limit - 120)].rstrip() + (
        "\n\n[PR context truncated to keep the reviewer prompt within budget.]"
    )


def _truncate_issue_context(text: str, limit: int) -> str:
    """Truncate issue context while preserving the latest issue comments.

    Issue bodies often become stale while later maintainer/user comments narrow
    or replace the contract. Review-loop prompts must retain that tail context
    when large bot logs force truncation.
    """
    if len(text) <= limit:
        return text
    marker = "\nComments:\n"
    if marker not in text:
        return _truncate_context(text, limit)

    header, comments = text.split(marker, 1)
    notice = "\n\n[Issue context truncated; latest comments preserved.]"
    available = max(0, limit - len(marker) - len(notice))
    tail_budget = min(max(limit // 3, 12000), max(0, available // 2))
    head_budget = max(0, available - tail_budget)

    if len(header) > head_budget:
        header = header[:head_budget].rstrip()
    if len(comments) > tail_budget:
        comment_notice = "[Older issue comments truncated; newest comments retained.]\n"
        retained_budget = max(0, tail_budget - len(comment_notice))
        comments = comment_notice + comments[-retained_budget:].lstrip()

    return f"{header.rstrip()}{marker}{comments.rstrip()}{notice}"


# Reviewer statuses that count as "this reviewer accepted the PR". The hard
# not-clean states (failed/degraded/missing) must never satisfy the gate even
# if a caller widens ``clean_reviewer_states``; the final gate uses the strict
# "clean" sentinel to stay conservative (a false non-ship is recoverable by a
# re-run; a false ship is not).
_SHIP_REVIEWER_STATES = ("clean",)


def _markdown_table_cell(value: str) -> str:
    """Return a one-line markdown table cell."""
    return (value or "").replace("|", "\\|").replace("\n", " ").strip()


def _classify_layer1_failure_category(message: str) -> str:
    """Map a Layer 1 failure ``message`` to a stable ``failure_category``.

    Layer 1 (the PR-mode orchestrator checkup) surfaces several distinct
    failure shapes through one free-text message. Issue #2047 needs these
    distinguished so pdd_cloud reports the right next action instead of a
    generic failure:

      - empty / unparseable Step 7 verdict  -> provider_parser_failure (retryable infra)
      - targeted-only verification, full suite not run -> incomplete_verification
      - full-suite/build/test verification failed -> full_suite_failed
      - generated-code-only / source-of-truth refusal -> source_of_truth_repair_needed
      - anything else -> layer1_failed
    """
    text = (message or "").lower()
    if (
        _layer1_failure_is_provider_or_timeout(message)
        or "verdict json could not be parsed" in text
        or "empty step 7 output" in text
        or "could not be parsed" in text
        or "empty step-7" in text
    ):
        return FINAL_GATE_CATEGORY_PROVIDER_PARSER
    if (
        any(marker in text for marker in SOURCE_OF_TRUTH_GUARD_REFUSAL_MARKERS)
        or ("source of truth" in text and "prompt" in text)
        or ("architecture" in text and "registry" in text)
    ):
        return FINAL_GATE_CATEGORY_SOURCE_OF_TRUTH
    if (
        "full suite not run" in text
        or "full-suite/ci re-run" in text
        or "full suite (" in text
        and "not run" in text
        or "verification scope: targeted" in text
    ):
        return FINAL_GATE_CATEGORY_INCOMPLETE_VERIFICATION
    if (
        "build replay still fails" in text
        or "pytest suite timed out" in text
        or "tests already failing" in text
        or "reproduced tests" in text
        or ("full suite" in text and "fail" in text)
    ):
        return FINAL_GATE_CATEGORY_FULL_SUITE
    return FINAL_GATE_CATEGORY_LAYER1


def _format_github_checks_gate_failure_report(
    *,
    pr_url: str,
    issue_url: str,
    github_checks_message: str,
) -> str:
    """Render a parseable final-gate failure report before Layer 2 starts."""
    finding = _markdown_table_cell(
        f"GitHub checks gate failed before Layer 2: {github_checks_message}"
    )
    issue_line = issue_url or "none"
    issue_aligned = "unknown" if issue_url else "n/a"
    machine_payload = {
        "schema": FINAL_GATE_REPORT_SCHEMA,
        "stage": "github-checks",
        "status": "failed",
        "failure_category": FINAL_GATE_CATEGORY_GITHUB_CHECKS,
        "reason": github_checks_message,
        "pr_url": pr_url,
        "issue_url": issue_url,
        "issue_aligned": None,
        "full_suite_source": "github-checks",
        "layer1_status": "passed",
        "layer2_status": "skipped",
        "reviewer_status": {},
        "fresh_final_status": "missing",
        "findings": [
            {
                "severity": "blocker",
                "area": "github-checks",
                "location": "",
                "finding": f"GitHub checks gate failed before Layer 2: {github_checks_message}",
                "required_fix": "Fix the failing, stale, pending, or missing GitHub checks on the current PR head.",
                "status": "open",
            }
        ],
    }
    return "\n".join(
        [
            "## Step 7/8: Final Gate Report",
            "",
            f"PR: {pr_url}",
            f"Issue: {issue_line}",
            "final-gate-status: failed",
            "final-gate-stage: github-checks",
            f"issue_aligned: {issue_aligned}",
            "",
            "### Summary",
            "",
            "Layer 1 targeted checkup passed, but GitHub checks did not pass on the current PR head. Layer 2 was skipped.",
            "",
            "### Machine Verdict",
            "",
            "```json",
            json.dumps(machine_payload, indent=2, sort_keys=True),
            "```",
            "",
            "### Issues Summary",
            "",
            "| Severity | Module | Description | Fixed |",
            "|----------|--------|-------------|-------|",
            f"| blocker | github-checks | {finding} | No |",
        ]
    )


def _format_layer1_failure_report(
    *,
    pr_url: str,
    issue_url: str,
    layer1_message: str,
    full_suite_source: str,
) -> str:
    """Render a parseable final-gate failure report for Layer 1 failures."""
    reason = (layer1_message or "Layer 1 checkup failed.").strip()
    payload_reason = reason
    if len(payload_reason) > 4000:
        payload_reason = payload_reason[:4000].rstrip() + "...[truncated]"
    finding = _markdown_table_cell(
        f"Layer 1 checkup failed before Layer 2: {payload_reason}"
    )
    issue_line = issue_url or "none"
    issue_aligned = "unknown" if issue_url else "n/a"
    machine_payload = {
        "schema": FINAL_GATE_REPORT_SCHEMA,
        "stage": "layer1",
        "status": "failed",
        "failure_category": _classify_layer1_failure_category(payload_reason),
        "reason": payload_reason,
        "pr_url": pr_url,
        "issue_url": issue_url,
        "issue_aligned": None,
        "full_suite_source": full_suite_source,
        "layer1_status": "failed",
        "layer2_status": "skipped",
        "reviewer_status": {},
        "fresh_final_status": "missing",
        "findings": [
            {
                "severity": "blocker",
                "area": "layer1",
                "location": "",
                "finding": f"Layer 1 checkup failed before Layer 2: {payload_reason}",
                "required_fix": "Resolve the Layer 1 checkup failure or push-guard refusal, then re-run the final gate.",
                "status": "open",
            }
        ],
    }
    return "\n".join(
        [
            "## Step 7/8: Final Gate Report",
            "",
            f"PR: {pr_url}",
            f"Issue: {issue_line}",
            "final-gate-status: failed",
            "final-gate-stage: layer1",
            f"issue_aligned: {issue_aligned}",
            "",
            "### Summary",
            "",
            ("Layer 1 PR checkup failed before Layer 2 review loop could run."),
            "",
            "### Machine Verdict",
            "",
            "```json",
            json.dumps(machine_payload, indent=2, sort_keys=True),
            "```",
            "",
            "### Issues Summary",
            "",
            "| Severity | Module | Description | Fixed |",
            "|----------|--------|-------------|-------|",
            f"| blocker | layer1 | {finding} | No |",
        ]
    )


def _post_final_gate_report(
    *,
    owner: str,
    repo: str,
    issue_number: int,
    pr_owner: str,
    pr_repo: str,
    pr_number: int,
    has_issue: bool,
    body: str,
    cwd: Path,
    use_github_state: bool,
) -> str:
    """Best-effort post of a final-gate report to PR and issue threads."""
    if not use_github_state or not body.strip():
        return ""

    pr_posted = post_pr_comment(pr_owner, pr_repo, pr_number, body, cwd)
    issue_posted = True
    if has_issue:
        issue_posted = post_step_comment(
            repo_owner=owner,
            repo_name=repo,
            issue_number=issue_number,
            step_num=7,
            total_steps=8,
            description="Verification & Final Report",
            output=body,
            cwd=cwd,
            body=body,
        )
    if pr_posted and issue_posted:
        return ""
    failed = []
    if not pr_posted:
        failed.append("PR")
    if not issue_posted:
        failed.append("issue")
    return f" Final report post failed for: {', '.join(failed)}."


def _review_loop_ship_verdict(
    final_state: Optional[Dict[str, Any]],
    *,
    has_issue: bool,
    require_terra_sol_model: bool = False,
) -> bool:
    """Derive a real ship/no-ship verdict from a review-loop ``final-state.json``.

    ``run_checkup_review_loop`` returns ``success=True`` whenever it produces a
    trustworthy report — even when findings remain — so the boolean alone is NOT
    a ship gate (the rendered report carries the authoritative markers). The
    canonical final gate (issue #1406) needs a true pass/fail, so this predicate
    replicates the canonical ship markers against the persisted verdict:

    - ``fresh_final_status == "clean"`` — the verifier's clean pass survived the
      stale-head re-check ``_finalize`` performs (issue #1088). A head that
      advanced after verification is downgraded to ``missing`` there, so this
      field already encodes "the clean verdict matches the current remote head".
    - the active reviewer's status is a hard ``clean`` (not failed/degraded/
      missing/findings).
    - no finding is still ``open``.
    - when an issue is in scope, the PR is reported as issue-aligned.

    Fails closed: a missing/unparsable state, or any unmet condition, returns
    ``False``. A false non-ship is recoverable by re-running; a false ship is
    not.
    """
    if not isinstance(final_state, dict):
        return False
    if final_state.get("fresh_final_status") != "clean":
        return False
    reviewer_status = final_state.get("reviewer_status")
    active = final_state.get("active_reviewer")
    # ``active_reviewer`` must be a real string key; a non-string (or empty)
    # value is a malformed verdict — fail closed instead of raising on the
    # unhashable ``dict.get`` lookup below.
    if (
        not isinstance(reviewer_status, dict)
        or not isinstance(active, str)
        or not active
    ):
        return False
    if reviewer_status.get(active) not in _SHIP_REVIEWER_STATES:
        return False
    if require_terra_sol_model:
        if final_state.get("terra_sol_mode") is not True or active != "codex":
            return False
        if not _is_terra_sol_model(final_state.get("sol_model")):
            return False
    # Canonical persisted state uses booleans for all cap flags. An explicit
    # cap hit can never ship, and a present malformed value fails closed.
    for cap_flag in (
        "max_rounds_reached",
        "max_cost_reached",
        "max_duration_reached",
    ):
        if cap_flag in final_state and final_state.get(cap_flag) is not False:
            return False
    # The canonical ``_write_final_state`` ALWAYS serializes ``findings`` as a
    # list of dicts (``ReviewFinding.to_dict()``) whose ``status`` is a non-empty
    # string ("open" while unresolved, "fixed" once resolved). The canonical
    # ship gate blocks on any ``open`` row, so we mirror that; a non-list value,
    # a non-dict entry, or a missing/non-string/empty ``status`` means the
    # verdict file is malformed or not from a real run — fail closed rather than
    # treat the absence of an ``open`` row as "no findings".
    findings = final_state.get("findings")
    if not isinstance(findings, list):
        return False
    for finding in findings:
        if not isinstance(finding, dict):
            return False
        status = finding.get("status")
        if not isinstance(status, str) or not status or status == "open":
            return False
    if has_issue and str(final_state.get("issue_aligned")).lower() != "true":
        return False
    return True


_LAYER1_STEP5_ACTIONABLE_STATUSES = {"failed", "error", "timeout_partial"}


def _layer1_failure_is_provider_or_timeout(message: str) -> bool:
    """Return True when Layer 1 failed before producing a trustworthy verdict."""
    text = message or ""
    lowered = text.lower()
    return (
        _is_provider_failure(text)
        or _is_step_timeout_failure(text)
        or "agent providers unavailable" in lowered
    )


def _load_layer1_step5_evidence(
    project_root: Path,
    pr_number: Optional[int],
) -> Optional[Dict[str, Any]]:
    """Load Layer 1 shell-first Step 5 evidence, if present."""
    if pr_number is None:
        return None
    memory_payload = _load_step5_shell_evidence_from_memory(project_root, pr_number)
    if isinstance(memory_payload, dict):
        return memory_payload
    path = (
        project_root
        / ".pdd"
        / f"checkup-pr-{pr_number}"
        / STEP5_SHELL_EVIDENCE_FILENAME
    )
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if not isinstance(payload, dict):
        return None
    if payload.get("schema") != STEP5_SHELL_EVIDENCE_SCHEMA:
        return None
    payload = dict(payload)
    payload.setdefault("artifact_file", str(path))
    return payload


def _layer1_step5_evidence_is_actionable(
    evidence: Optional[Dict[str, Any]],
    *,
    layer1_succeeded: bool = False,
    layer1_message: str = "",
) -> bool:
    """Return True when shell-first Step 5 evidence should drive Layer 2."""
    if not isinstance(evidence, dict):
        return False
    if not layer1_succeeded and _layer1_failure_is_provider_or_timeout(layer1_message):
        return False
    status = str(evidence.get("status", "")).strip().lower()
    if status not in _LAYER1_STEP5_ACTIONABLE_STATUSES:
        return False
    if layer1_succeeded and status == "timeout_partial":
        return False
    return True


def _layer1_step5_evidence_for_review(
    evidence: Optional[Dict[str, Any]],
) -> str:
    """Render bounded JSON for ReviewLoopContext."""
    if not isinstance(evidence, dict):
        return ""
    payload = dict(evidence)
    output = str(payload.get("output") or "")
    if len(output) > 12000:
        payload["output"] = (
            output[:5950].rstrip()
            + "\n...[layer1 step5 evidence output truncated]...\n"
            + output[-5950:].lstrip()
        )
        payload["output_truncated"] = True
    return json.dumps(payload, indent=2, sort_keys=True)


def run_agentic_checkup(
    issue_url: Optional[str] = None,
    *,
    verbose: bool = False,
    quiet: bool = False,
    no_fix: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True,
    reasoning_time: Optional[float] = None,
    pr_url: Optional[str] = None,
    test_scope: str = "full",
    full_suite_source: str = "local",
    review_loop: bool = False,
    final_gate: bool = False,
    review_only: bool = False,
    reviewers: str = "codex,claude",
    reviewer: Optional[str] = None,
    fixer: Optional[str] = None,
    reviewer_fallback: Optional[str] = None,
    fixer_fallback: Optional[str] = None,
    max_review_rounds: int = 5,
    max_review_cost: float = 50.0,
    max_review_minutes: float = 90.0,
    require_all_reviewers_clean: bool = True,
    continue_on_reviewer_limit: bool = False,
    require_final_fresh_review: bool = True,
    blocking_severities: Optional[str] = None,
    clean_reviewer_states: Optional[str] = None,
    fallback_reviewer_on_failure: bool = False,
    allow_same_reviewer_fixer: bool = False,
    enable_gates: bool = True,
    gate_timeout: float = 60.0,
    gate_allow: Tuple[str, ...] = (),
    start_step_override: Optional[Union[int, float]] = None,
    cwd: Optional[Path] = None,
    prompt_repair: str = "off",
    max_prompt_repair_rounds: int = 1,
    max_prompt_token_growth: int = 1000,
    max_prompt_repair_seconds: float = 120.0,
    adversarial_prompt: Optional[str] = None,
    agentic_review_loop: bool = False,
    fresh_final_review_role: Optional[str] = None,
    agentic_artifact_path: Optional[str] = None,
    terra_sol: bool = False,
) -> Tuple[bool, str, float, str]:
    """Run agentic checkup workflow from a GitHub issue URL.

    Args:
        issue_url: GitHub issue URL describing what to check. Optional in PR
            mode (``pr_url`` set): when ``None``, the PR is reviewed on its
            own merits and the issue-alignment gate is skipped (#1292).
        verbose: Enable detailed logging.
        quiet: Suppress standard output.
        no_fix: Report only, don't apply fixes.
        timeout_adder: Additional seconds to add to each step timeout.
        use_github_state: Whether to persist state to GitHub comments.
        cwd: Project working directory to use when loading local context.
        pr_url: When set, review this existing PR instead of creating a new
            branch/PR. With ``issue_url`` provided, the PR is verified against
            that issue; with ``issue_url`` omitted (#1292), the PR is reviewed
            on its own merits. Step 8 (create_pr) is skipped and the worktree
            is based on the PR's head branch.
        review_loop: When true in PR mode, run the primary-reviewer/fixer
            loop instead of the legacy single-pass checkup path.
        full_suite_source: Final-gate full-suite source. ``local`` preserves
            the historical contract: Layer 1 must run the full local suite.
            ``github-checks`` makes Layer 1 run targeted local checks and then
            gates on GitHub checks for the current PR head before Layer 2.
        final_gate: When true in PR mode, run the canonical two-layer final
            gate (issue #1406): Layer 1 is the PR-scoped checkup orchestrator
            (no new PR), Layer 2 is the primary-reviewer/fixer review loop on
            the resulting PR head. Unlike ``review_loop`` — whose success only
            means "trustworthy report produced" — the returned ``success`` is
            a real ship verdict derived from the review-loop's current-run
            ``final-state.json``. Requires both ``pr_url`` and ``issue_url``.
            A Layer 1 failure or GitHub-checks gate failure short-circuits
            before Layer 2; either layer's failure fails the gate.
        review_only: When true with ``review_loop``, run only the primary
            reviewer first pass and do not invoke the fixer or push changes.
        reviewer_fallback: Optional secondary reviewer role to try once when
            the primary reviewer cannot complete.
        fixer_fallback: Optional secondary fixer role to try once when the
            primary fixer cannot address the reviewer's findings (e.g. a
            subscription-tier credential is exhausted). Must differ from
            both the primary fixer and the active reviewer.
        allow_same_reviewer_fixer: Explicitly allow the same role to act as
            reviewer and fixer in the review loop. Off by default so the
            independent reviewer/fixer contract remains the normal mode.
        start_step_override: Optional recovery override for the legacy
            orchestrator resume point. Used to start from a later step when
            cached state already contains earlier step outputs.
        agentic_artifact_path: Invocation-private artifact destination for an
            explicit standalone agentic review loop. Ignored in other modes.
        terra_sol: Run the bounded Codex-only Terra/Sol convergence loop.
            It uses ``max_review_rounds`` (default 5) as its authoritative
            round cap while retaining no cost/duration cap. Conflicting
            review/final-gate/report-only modes are rejected before any
            environment mutation or external I/O.

    Returns:
        Tuple of (success, message, total_cost, model_used).
    """
    # Capture the receipt secret as the first operation at this library
    # boundary, before project discovery, hosted invalidation, validation, or
    # any target-repository hook can expose it to a subprocess. The key is
    # never restored to ``os.environ`` and is retained only in this process.
    hosted_receipt_key_hex = os.environ.pop(_HOSTED_RECEIPT_KEY_ENV, None)

    # Hosted consumers read one stable public verdict path. Invalidate it
    # before *any* validation return, without reserving private storage or
    # binding identities that have not yet parsed.
    project_root = _find_project_root(cwd if cwd is not None else Path.cwd())
    hosted_agentic_artifact_path = _hosted_agentic_artifact_path(project_root)
    if not _invalidate_hosted_agentic_artifact(hosted_agentic_artifact_path):
        return (
            False,
            "Failed to invalidate the prior hosted agentic artifact.",
            0.0,
            "",
        )

    # ``run_agentic_checkup`` is the library boundary used by pdd_cloud and
    # e2e callers, so enforce the same mutually-exclusive mode contract as the
    # Click command before mutating the hosted environment, reserving artifacts,
    # fetching GitHub state, or running any provider. Terra/Sol owns its
    # fix/review loop end to end.
    if terra_sol:
        incompatible = [
            name
            for enabled, name in (
                (final_gate, "--final-gate"),
                (review_loop, "--review-loop"),
                (no_fix, "--no-fix"),
                (review_only, "--review-only"),
                (agentic_review_loop, "--agentic-review-loop"),
            )
            if enabled
        ]
        if incompatible:
            return (
                False,
                "--terra-sol cannot be combined with " + ", ".join(incompatible) + ".",
                0.0,
                "",
            )
        if not str(pr_url or "").strip():
            return False, "--terra-sol requires --pr.", 0.0, ""
        if str(prompt_repair or "off").strip().lower() != "off":
            return (
                False,
                "--terra-sol requires prompt repair to be off; an explicit "
                "--prompt-repair value or project .pddrc default cannot cross "
                "the Codex-only worktree boundary.",
                0.0,
                "",
            )
        if (
            isinstance(max_review_rounds, bool)
            or not isinstance(max_review_rounds, int)
            or max_review_rounds < 1
        ):
            return (
                False,
                "--terra-sol max_review_rounds must be a positive integer.",
                0.0,
                "",
            )

    # Report-only modes are a hard write boundary.  Apply it before prompt
    # discovery/check/repair so an explicit CLI value or project default can
    # never trigger prompt edits or prompt-repair audit artifacts.
    effective_prompt_repair = "off" if (no_fix or review_only) else prompt_repair

    # Resolve artifact paths without reserving hosted provenance yet. Terra/Sol
    # owns its local verdict slot as soon as the request identities are valid,
    # so stale local state must be invalidated before this fallible reservation.
    standalone_agentic_artifact_path = (
        str(agentic_artifact_path or "").strip() or None
        if agentic_review_loop
        else None
    )

    # 1. Parse PR URL up-front (when in PR mode) so an invalid PR fails before
    #    any issue work, and so a no-issue run can alias its comment/state
    #    thread to the PR (GitHub treats PRs as issues for the comments API).
    pr_owner: Optional[str] = None
    pr_repo: Optional[str] = None
    pr_number: Optional[int] = None
    if pr_url is not None:
        pr_parsed = _parse_pr_url(pr_url)
        if not pr_parsed:
            return False, f"Invalid GitHub PR URL: {pr_url}", 0.0, ""
        pr_owner, pr_repo, pr_number = pr_parsed

    # 2. Resolve the source issue identifier. The issue is OPTIONAL in PR mode
    #    (#1292):
    #    with no issue the PR is reviewed on its own merits, the issue fetch
    #    is skipped, and the issue context stays empty (never the literal
    #    "None") so the step prompts do merit review.
    # None, "", whitespace, or null-like strings all mean merit-review mode,
    # matching the orchestrator's own has_issue derivation at line 1846.
    has_issue = bool((issue_url or "").strip()) and issue_url not in ("null", "None")
    if has_issue:
        parsed = _parse_issue_url(issue_url)
        if not parsed:
            return False, f"Invalid GitHub issue URL: {issue_url}", 0.0, ""
        owner, repo, issue_number = parsed
    else:
        # No issue: the comment/state thread is the PR itself.
        if pr_url is None or pr_owner is None or pr_repo is None or pr_number is None:
            return (
                False,
                "No issue URL and no PR URL provided; nothing to check.",
                0.0,
                "",
            )
        owner, repo, issue_number = pr_owner, pr_repo, pr_number

    # An explicit Terra/Sol invocation owns the verdict slot as soon as its PR
    # and optional issue identities are known. Invalidate a prior clean verdict
    # before gh validation, network fetches, project loading, or any repair path
    # can fail so a retry can never leave stale clean state authoritative.
    if terra_sol:
        assert pr_number is not None
        terra_sol_artifacts_dir = (
            project_root
            / ".pdd"
            / "checkup-review-loop"
            / f"issue-{issue_number}-pr-{pr_number}"
        )

        def _terra_sol_early_failure(
            message: str,
        ) -> Tuple[bool, str, float, str]:
            try:
                write_terra_sol_progress(
                    artifacts_dir=terra_sol_artifacts_dir,
                    max_rounds=max_review_rounds,
                    round_number=0,
                    phase="terminal",
                    terminal_reason=message,
                )
            except Exception as exc:  # pylint: disable=broad-exception-caught
                # Terminal publication is diagnostic and must never replace
                # the authoritative workflow failure or break this function's
                # documented tuple-return contract. Avoid echoing exception
                # text because persistence failures can contain sensitive
                # paths or environment-derived details.
                message += (
                    " Additionally, terminal Terra/Sol watchdog progress could "
                    f"not be persisted ({type(exc).__name__})."
                )
            return False, message, 0.0, ""

        if (
            not clear_final_state(project_root, issue_number, pr_number)
            or load_final_state(project_root, issue_number, pr_number) is not None
        ):
            return _terra_sol_early_failure(
                (
                    "Terra/Sol could not clear the stale review-loop verdict at "
                    ".pdd/checkup-review-loop/; refusing to trust a prior run."
                )
            )
        try:
            write_terra_sol_progress(
                artifacts_dir=terra_sol_artifacts_dir,
                max_rounds=max_review_rounds,
                round_number=0,
                phase="initializing",
            )
        except Exception:  # pylint: disable=broad-exception-caught
            # The stale verdict is already gone. Do not continue into hosted,
            # GitHub, project, or provider work without a current watchdog
            # record, and do not retry through the same failing writer.
            return (
                False,
                "Failed to publish initial Terra/Sol watchdog progress; "
                "the stale verdict was cleared and the review did not start.",
                0.0,
                "",
            )

    # Establish hosted public-placeholder provenance after Terra/Sol has
    # invalidated its prior local verdict, but before any network/project I/O.
    # A reservation failure therefore blocks the run without leaving either a
    # stale local clean verdict or a stale public PASS authoritative.
    hosted_artifact_reservation = (
        _prepare_hosted_agentic_artifact(
            hosted_agentic_artifact_path,
            pr_owner=pr_owner or "",
            pr_repo=pr_repo or "",
            pr_number=pr_number or 0,
            receipt_key_hex=hosted_receipt_key_hex,
            receipt_run_id=str(os.environ.get(_HOSTED_RECEIPT_RUN_ID_ENV, "")),
            receipt_expected_head_sha=str(os.environ.get(_HOSTED_EXPECTED_HEAD_ENV, ""))
            .strip()
            .lower(),
        )
        if hosted_agentic_artifact_path is not None
        else None
    )
    if hosted_agentic_artifact_path is not None and hosted_artifact_reservation is None:
        if terra_sol:
            return _terra_sol_early_failure(
                "Failed to establish current hosted agentic artifact provenance."
            )
        return (
            False,
            "Failed to establish current hosted agentic artifact provenance.",
            0.0,
            "",
        )
    effective_agentic_artifact_path = standalone_agentic_artifact_path or (
        str(hosted_artifact_reservation.private_path)
        if hosted_artifact_reservation is not None
        else None
    )

    # 3. Check gh only after stale Terra/Sol state has been invalidated.
    if not _check_gh_cli():
        if terra_sol:
            return _terra_sol_early_failure(
                "GitHub CLI (gh) not found. Install from https://cli.github.com/"
            )
        return (
            False,
            "GitHub CLI (gh) not found. Install from https://cli.github.com/",
            0.0,
            "",
        )

    # 4. Fetch the already-validated optional issue.
    if has_issue:

        if not quiet:
            console.print(
                f"[bold]Fetching issue #{issue_number} from {owner}/{repo}...[/bold]"
            )

        success, issue_json = _run_gh_command(
            ["api", f"repos/{owner}/{repo}/issues/{issue_number}"]
        )
        if not success:
            if terra_sol:
                return _terra_sol_early_failure(
                    f"Failed to fetch issue: {issue_json}"
                )
            return False, f"Failed to fetch issue: {issue_json}", 0.0, ""

        try:
            issue_data = json.loads(issue_json)
        except json.JSONDecodeError:
            if terra_sol:
                return _terra_sol_early_failure("Failed to parse issue JSON")
            return False, "Failed to parse issue JSON", 0.0, ""

        raw_title = issue_data.get("title", "")
        body = issue_data.get("body", "") or ""

        # Fetch comments for full context
        comments_url = issue_data.get("comments_url", "")
        comments_text = _fetch_comments(comments_url) if comments_url else ""

        raw_full_content = (
            f"Title: {raw_title}\nDescription:\n{body}\n\nComments:\n{comments_text}"
        )
        effective_issue_url = issue_url
    else:
        raw_title = ""
        raw_full_content = ""
        effective_issue_url = ""

    # Escape braces so .format() doesn't choke on user content
    title = _escape_format_braces(raw_title)
    full_content = _escape_format_braces(raw_full_content)

    # 5. Load project context
    architecture, _ = _load_architecture_json(project_root)
    raw_arch_json_str = (
        json.dumps(architecture, indent=2)
        if architecture
        else "No architecture.json available."
    )
    arch_json_str = _escape_format_braces(raw_arch_json_str)
    raw_pddrc_content = _load_pddrc_content(project_root)
    pddrc_content = _escape_format_braces(raw_pddrc_content)

    if not quiet:
        console.print("[bold]Running agentic checkup...[/bold]")

    hosted_reviewers = _hosted_agentic_reviewers(reviewers)

    full_suite_source = (full_suite_source or "local").strip().lower()
    if full_suite_source not in {"local", "github-checks"}:
        if terra_sol:
            return _terra_sol_early_failure(
                "--full-suite-source must be 'local' or 'github-checks', "
                f"got {full_suite_source!r}."
            )
        return (
            False,
            "--full-suite-source must be 'local' or 'github-checks', "
            f"got {full_suite_source!r}.",
            0.0,
            "",
        )

    # check → repair → recheck cycle for changed prompt files (Issue #1422).
    # Uses the full pdd.prompt_source_set_report.v1 structured report as the
    # repair oracle (not just lint), then re-verifies before the orchestrator runs.
    if effective_prompt_repair != "off":
        from .checkup_prompt_main import (
            build_prompt_source_set_report,
        )  # pylint: disable=import-outside-toplevel

        repair_config = PromptRepairConfig(
            mode=effective_prompt_repair,
            max_rounds=max_prompt_repair_rounds,
            max_token_growth=max_prompt_token_growth,
            max_seconds=max_prompt_repair_seconds,
        )
        # Base context from issue/PR content (oracle enrichment)
        issue_context: Dict[str, str] = {}
        if raw_full_content.strip():
            issue_context["issue"] = raw_full_content
        if pr_url and pr_owner and pr_repo and pr_number is not None:
            issue_context["pr"] = _fetch_pr_context(pr_owner, pr_repo, pr_number)

        strict_failures: List[str] = []
        work_cwd = cwd if cwd is not None else Path.cwd()
        # Forward strictness so warnings are treated as errors consistently in
        # all three phases (initial check, repair loop re-checks, post-repair
        # check).  Mirrors the commands/checkup.py path which passes strict=strict.
        is_strict = effective_prompt_repair == "strict"
        for prompt_path in discover_prompt_paths(work_cwd):
            # Step 1: run the full structured checkup to decide if repair is needed
            src_report = build_prompt_source_set_report(
                prompt_path,
                target=str(prompt_path),
                project_root=project_root,
                strict=is_strict,
            )
            if src_report.status == "pass":
                continue  # no repair needed for this prompt
            # Step 2: repair using the structured report + issue context as oracle
            repair_context = dict(issue_context)
            repair_context["source_set_report"] = json.dumps(
                src_report.as_dict(), indent=2
            )
            repair_context["recommended_actions"] = "\n".join(
                src_report.recommended_actions()
            )
            repair_result = run_prompt_repair_loop(
                prompt_path,
                repair_config,
                context=repair_context,
                cwd=project_root,
                verbose=verbose,
                quiet=quiet,
                strict=is_strict,
            )
            summary = format_token_delta_summary(repair_result)
            if summary:
                logger.info("%s: %s", prompt_path, summary.replace("\n", "; "))
                if not quiet:
                    console.print(f"[cyan]{summary}[/cyan]")
            # Step 3: re-check with the structured report after repair
            post_report = build_prompt_source_set_report(
                prompt_path,
                target=str(prompt_path),
                project_root=project_root,
                strict=is_strict,
            )
            if post_report.status != "pass" and effective_prompt_repair == "strict":
                strict_failures.append(str(prompt_path))
            elif post_report.status != "pass":
                logger.warning(
                    "Prompt repair left issues in %s: %s",
                    prompt_path,
                    ", ".join(f.code for f in post_report.findings),
                )

        if strict_failures:
            paths = ", ".join(strict_failures)
            return (
                False,
                f"Prompt repair strict mode: unresolved issues in {paths}",
                0.0,
                "",
            )

    # Layer 2 (review-loop) runner, shared by ``--review-loop`` (Layer 2 only)
    # and the canonical ``--final-gate`` (Layer 1 then Layer 2). Defined as a
    # closure so it captures the already-fetched issue/PR context instead of
    # re-threading the full config surface. ``pr_content`` is fetched lazily by
    # default, but the final gate passes a pre-Layer-1 snapshot so Layer 2 does
    # not ingest Layer 1's own freshly-posted checkup report.
    def _run_review_loop_layer(
        pr_content: Optional[str] = None,
        layer1_step5_evidence: str = "",
        final_gate_canonical_status: str = "",
    ) -> Tuple[bool, str, float, str]:
        loop_context = ReviewLoopContext(
            issue_url=issue_url,
            issue_content=_truncate_issue_context(raw_full_content, 60000),
            repo_owner=owner,
            repo_name=repo,
            issue_number=issue_number,
            issue_title=raw_title,
            architecture_json=_truncate_context(raw_arch_json_str, 40000),
            pddrc_content=raw_pddrc_content,
            pr_url=pr_url,
            pr_owner=pr_owner,
            pr_repo=pr_repo,
            pr_number=pr_number,
            project_root=project_root,
            pr_content=(
                pr_content
                if pr_content is not None
                else _fetch_pr_context(pr_owner, pr_repo, pr_number)
            ),
            has_issue=has_issue,
            full_suite_source=full_suite_source,
            test_scope=test_scope,
            layer1_step5_evidence=layer1_step5_evidence,
            final_gate_canonical_status=final_gate_canonical_status,
        )
        hosted_agentic_mode = hosted_artifact_reservation is not None
        # In terra_sol mode both roles run on the GPT-5.6 Codex provider so
        # that fixer (Terra) and reviewer (Sol) share the same model family
        # while keeping their execution contexts and audit evidence distinct.
        effective_reviewers = "codex" if terra_sol else reviewers
        effective_reviewer = "codex" if terra_sol else reviewer
        effective_fixer = "codex" if terra_sol else fixer
        # There is no distinct GPT-5.6 Codex fallback role. Ignore caller
        # fallbacks in Terra/Sol mode so Claude/Gemini can never take over
        # either authoritative role after a Codex failure.
        effective_reviewer_fallback = None if terra_sol else reviewer_fallback
        effective_fixer_fallback = None if terra_sol else fixer_fallback
        effective_allow_same = allow_same_reviewer_fixer or terra_sol
        loop_config = ReviewLoopConfig(
            # Hosted fallback/mirror settings are additive evidence only: they
            # must not change the canonical review-loop provider set or prompt.
            # Per-role hosted commands are still serialized below for the
            # artifact, but canonical execution uses the caller's reviewers.
            reviewers=parse_reviewers(effective_reviewers),
            reviewer=effective_reviewer,
            fixer=effective_fixer,
            reviewer_fallback=effective_reviewer_fallback,
            fixer_fallback=effective_fixer_fallback,
            review_only=review_only or no_fix,
            no_fix=no_fix,
            max_rounds=max_review_rounds,
            max_cost=max_review_cost,
            max_minutes=max_review_minutes,
            require_all_reviewers_clean=require_all_reviewers_clean,
            continue_on_reviewer_limit=continue_on_reviewer_limit,
            require_final_fresh_review=require_final_fresh_review,
            timeout_adder=timeout_adder,
            reasoning_time=reasoning_time,
            blocking_severities=parse_severity_list(blocking_severities),
            clean_reviewer_states=parse_state_list(clean_reviewer_states),
            fallback_reviewer_on_failure=fallback_reviewer_on_failure,
            allow_same_reviewer_fixer=effective_allow_same,
            enable_gates=enable_gates,
            gate_timeout=gate_timeout,
            gate_allow=tuple(gate_allow),
            # Issue #1788 / #1881 — ``agentic_mode`` drives the bounded
            # ``pdd.checkup.agentic.v1`` artifact write. Explicit
            # ``--agentic-review-loop`` keeps its manual artifact behavior; the
            # hosted pdd_cloud env contract turns this on for canonical
            # final-gate/review-loop execution and writes to the env-provided
            # path without changing checkup authority.
            adversarial_prompt=(adversarial_prompt if agentic_review_loop else None),
            agentic_mode=(agentic_review_loop or hosted_agentic_mode),
            fresh_final_review_role=(
                fresh_final_review_role if agentic_review_loop else None
            ),
            agentic_artifact_path=effective_agentic_artifact_path,
            # Canonical prompts may only consume commands supplied by the
            # caller. Hosted fallback/mirror commands are artifact metadata;
            # keeping them in a separate field prevents the non-authoritative
            # env contract from steering ``_reviewer_command_block``.
            reviewer_commands=parse_reviewer_commands(effective_reviewers),
            artifact_reviewer_commands=parse_reviewer_commands(hosted_reviewers),
            agentic_artifact_sink=(
                hosted_artifact_reservation.write_private_bytes
                if hosted_artifact_reservation is not None
                else None
            ),
            terra_sol=terra_sol,
        )
        # Reviewers/fixers may run repository tests too. Keep the outer stable
        # transport slot out of every provider/test child while the private
        # artifact path remains explicitly threaded through ``loop_config``.
        with _without_hosted_artifact_child_env():
            return run_checkup_review_loop(
                context=loop_context,
                config=loop_config,
                cwd=project_root,
                verbose=verbose,
                quiet=quiet,
                use_github_state=use_github_state,
            )

    pr_context_ready = (
        pr_url is not None
        and pr_owner is not None
        and pr_repo is not None
        and pr_number is not None
    )

    if final_gate and (not pr_context_ready or not has_issue):
        # The final gate is the two-layer PR-readiness path; it is PR-scoped,
        # issue-resolution gate, so it never runs in plain issue mode or
        # PR-only merit-review mode.
        return False, "--final-gate requires --pr and --issue.", 0.0, ""

    if final_gate:
        # The CLI rejects these combinations, but ``run_agentic_checkup`` is the
        # real contract boundary (the e2e/pdd-issue path and pdd_cloud call it
        # directly). Enforce the same gate-owned-knobs rule here so a direct
        # caller cannot run a non-canonical "final gate" — e.g. Layer 1
        # inheriting ``no_fix`` or a resume override, Layer 2 running with the
        # deterministic gates disabled, or Layer 1 using a test/full-suite
        # pairing that is weaker than the selected source — and silently get a
        # weaker verdict than the canonical gate promises.
        conflicts = [
            name
            for name, set_ in (
                ("no_fix", no_fix),
                ("review_only", review_only),
                ("review_loop", review_loop),
                ("start_step_override", start_step_override is not None),
                ("enable_gates=False (--no-gates)", not enable_gates),
                (
                    "test_scope!=full (--test-scope targeted)",
                    full_suite_source == "local" and test_scope != "full",
                ),
                (
                    "test_scope!=targeted (--test-scope full)",
                    full_suite_source == "github-checks" and test_scope != "targeted",
                ),
            )
            if set_
        ]
        if conflicts:
            return (
                False,
                (
                    "--final-gate cannot be combined with: "
                    f"{', '.join(conflicts)}; the gate owns the fix/review steps, "
                    "requires deterministic gates plus a valid full-suite source, "
                    "and runs the review-loop as Layer 2."
                ),
                0.0,
                "",
            )
        # The gate runs the review loop as Layer 2, so its budget knobs must be
        # valid BEFORE Layer 1 spends cost / mutates the PR — otherwise a direct
        # caller could push Layer-1 fixes and then have Layer 2 die via a runtime
        # cap (e.g. "Max review rounds reached: 0"). Mirror the CLI's checks.
        budget_errors = []
        # ``max_review_rounds`` is typed ``int`` but a direct library caller is
        # not bound by the hint: ``1.5``/``nan``/``inf`` all slip past a bare
        # ``< 1`` (and a float ``max_rounds`` later breaks ``range(1, n + 1)`` in
        # the loop). Require an actual positive integer — and reject ``bool``,
        # which is an ``int`` subclass — BEFORE Layer 1 spends cost / mutates.
        if (
            isinstance(max_review_rounds, bool)
            or not isinstance(max_review_rounds, int)
            or max_review_rounds < 1
        ):
            budget_errors.append("max_review_rounds must be a positive integer")
        if not math.isfinite(max_review_cost) or max_review_cost <= 0:
            budget_errors.append("max_review_cost must be a finite value > 0")
        if not math.isfinite(max_review_minutes) or max_review_minutes <= 0:
            budget_errors.append("max_review_minutes must be a finite value > 0")
        if budget_errors:
            return (
                False,
                f"--final-gate review budget invalid: {'; '.join(budget_errors)}.",
                0.0,
                "",
            )

    if agentic_review_loop and not final_gate and not pr_context_ready:
        # Issue #1788: standalone adversarial PR checkup still requires PR
        # context.  Its canonical Layer 1 is run below before any reviewer or
        # fixer spend; do not short-circuit directly into Layer 2 here.
        if not pr_context_ready:
            return False, "--agentic-review-loop requires --pr.", 0.0, ""

    if review_loop and not agentic_review_loop and not final_gate:
        if not pr_context_ready:
            # Review-loop is issue-coupled; review-loop-without-issue is a
            # deferred follow-up (#1292).
            return False, "--review-loop requires --pr and --issue.", 0.0, ""
        result = _run_review_loop_layer()
        return _require_hosted_publication(
            result, hosted_artifact_reservation, canonical_passed=None
        )

    # Terra/Sol bounded convergence mode: Sol can finish early when clean, but
    # a non-clean run stops at the caller-selected round cap (default five).
    # Cost and duration remain intentionally uncapped so each allowed round can
    # get a decisive Sol result.
    if terra_sol:
        if not pr_context_ready:
            return _terra_sol_early_failure("--terra-sol requires --pr.")
        assert pr_number is not None
        # The returned loop boolean means "trustworthy report produced", not
        # "Sol is clean". The prior verdict was cleared immediately after URL
        # parsing above; derive the CLI result only from this run's state.
        _loop_success, loop_message, loop_cost, loop_model = _run_review_loop_layer()
        ship = _review_loop_ship_verdict(
            load_final_state(project_root, issue_number, pr_number),
            has_issue=has_issue,
            require_terra_sol_model=True,
        )
        return _require_hosted_publication(
            (ship, loop_message, loop_cost, loop_model),
            hosted_artifact_reservation,
            canonical_passed=ship,
        )

    # For the final gate, snapshot PR context BEFORE Layer 1 so Layer 2 reviews
    # the PR's human context without ingesting Layer 1's own posted report.
    final_gate_pr_content: Optional[str] = None
    if final_gate:
        final_gate_pr_content = _fetch_pr_context(pr_owner, pr_repo, pr_number)

    # 5. Invoke orchestrator (Layer 1 of the final gate; the only layer for a
    #    plain checkup run).
    try:
        with _without_hosted_artifact_child_env():
            orch_success, orch_message, orch_cost, orch_model = (
                run_agentic_checkup_orchestrator(
                    issue_url=effective_issue_url,
                    issue_content=full_content,
                    repo_owner=owner,
                    repo_name=repo,
                    issue_number=issue_number,
                    issue_title=title,
                    architecture_json=arch_json_str,
                    pddrc_content=pddrc_content,
                    cwd=project_root,
                    verbose=verbose,
                    quiet=quiet,
                    no_fix=no_fix,
                    timeout_adder=timeout_adder,
                    use_github_state=use_github_state,
                    reasoning_time=reasoning_time,
                    pr_url=pr_url,
                    pr_owner=pr_owner,
                    pr_repo=pr_repo,
                    pr_number=pr_number,
                    test_scope=test_scope,
                    defer_step5_to_github_checks=(
                        final_gate and full_suite_source == "github-checks"
                    ),
                    start_step_override=start_step_override,
                )
            )
    except Exception as exc:
        msg = f"Orchestrator failed: {exc}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        _post_error_comment(owner, repo, issue_number, msg)
        return False, msg, 0.0, ""

    layer1_step5_evidence = (
        _load_layer1_step5_evidence(project_root, pr_number) if final_gate else None
    )
    layer1_step5_evidence_for_review = (
        _layer1_step5_evidence_for_review(layer1_step5_evidence)
        if _layer1_step5_evidence_is_actionable(
            layer1_step5_evidence,
            layer1_succeeded=orch_success,
            layer1_message=orch_message,
        )
        else ""
    )

    if not orch_success:
        if agentic_review_loop and not final_gate:
            layer1_failure_category = _classify_layer1_failure_category(orch_message)
            canonical_status = (
                "unknown"
                if layer1_failure_category == FINAL_GATE_CATEGORY_PROVIDER_PARSER
                else "fail"
            )
            if canonical_status == "unknown":
                # Provider/parser/timeout ambiguity is exactly the standalone
                # fallback case. Run independent reviewers instead of
                # synthesizing an empty blocking artifact; canonical authority
                # remains unknown and the agentic result supplies the verdict.
                loop_success, loop_message, loop_cost, loop_model = (
                    _run_review_loop_layer(final_gate_canonical_status="unknown")
                )
                ship = _review_loop_ship_verdict(
                    load_final_state(project_root, issue_number, pr_number),
                    has_issue=has_issue,
                )
                return _require_hosted_publication(
                    (
                        ship,
                        "Agentic checkup canonical Layer 1 unknown; "
                        f"independent fallback review: {loop_message}",
                        orch_cost + loop_cost,
                        loop_model or orch_model,
                    ),
                    hosted_artifact_reservation,
                    canonical_passed=None,
                )
            write_final_gate_fallback_artifact(
                artifact_path=effective_agentic_artifact_path,
                pr_owner=pr_owner or "",
                pr_repo=pr_repo or "",
                pr_number=pr_number or 0,
                head_sha=(
                    hosted_artifact_reservation.receipt_expected_head_sha
                    if hosted_artifact_reservation is not None
                    else ""
                ),
                canonical_status=canonical_status,
                blockers=[f"Canonical Layer 1 failed: {orch_message}"],
                no_fix=no_fix,
                artifact_sink=(
                    hosted_artifact_reservation.write_private_bytes
                    if hosted_artifact_reservation is not None
                    else None
                ),
            )
            return _require_hosted_publication(
                (
                    False,
                    f"Agentic checkup canonical Layer 1 failed: {orch_message}",
                    orch_cost,
                    orch_model,
                ),
                hosted_artifact_reservation,
                canonical_passed=(False if canonical_status == "fail" else None),
            )
        if final_gate:
            assert (
                pr_owner is not None and pr_repo is not None and pr_number is not None
            )
            if layer1_step5_evidence_for_review:
                if (
                    not clear_final_state(project_root, issue_number, pr_number)
                    or load_final_state(project_root, issue_number, pr_number)
                    is not None
                ):
                    return (
                        False,
                        (
                            "Final gate could not clear the stale review-loop verdict at "
                            ".pdd/checkup-review-loop/; refusing to run Layer 2 to avoid "
                            "trusting a prior run's verdict. Remove the artifact and re-run."
                        ),
                        orch_cost,
                        orch_model,
                    )
                if not quiet:
                    console.print(
                        "[bold]Final gate Layer 1 found Step 5 shell test failures; "
                        "running Layer 2 fixer with that evidence...[/bold]"
                    )
                loop_success, loop_message, loop_cost, loop_model = (
                    _run_review_loop_layer(
                        pr_content=final_gate_pr_content,
                        layer1_step5_evidence=layer1_step5_evidence_for_review,
                    )
                )
                ship = _review_loop_ship_verdict(
                    load_final_state(project_root, issue_number, pr_number),
                    has_issue=has_issue,
                )
                total_cost = orch_cost + loop_cost
                message = (
                    "Final gate: Layer 1 Step 5 shell-first tests failed; "
                    f"Layer 2 (review-loop): {loop_message}"
                )
                if not ship and loop_success:
                    message += " — verdict: not shippable (findings remain or "
                    message += "verification is unverified)."
                return _require_hosted_publication(
                    (ship, message, total_cost, (loop_model or orch_model)),
                    hosted_artifact_reservation,
                    canonical_passed=ship,
                )

            # Non-actionable Layer 1 failures still short-circuit before Layer 2.
            report = _format_layer1_failure_report(
                pr_url=pr_url or "",
                issue_url=issue_url or "",
                layer1_message=orch_message,
                full_suite_source=full_suite_source,
            )
            post_suffix = _post_final_gate_report(
                owner=owner,
                repo=repo,
                issue_number=issue_number,
                pr_owner=pr_owner,
                pr_repo=pr_repo,
                pr_number=pr_number,
                has_issue=has_issue,
                body=report,
                cwd=project_root,
                use_github_state=use_github_state,
            )
            # Issue #1788: this canonical Layer 1 failure short-circuits before
            # Layer 2, so the review-loop artifact writer never runs. Emit the
            # bounded canonical-failure mirror artifact for hosted consumers.
            write_final_gate_fallback_artifact(
                artifact_path=effective_agentic_artifact_path,
                pr_owner=pr_owner or "",
                pr_repo=pr_repo or "",
                pr_number=pr_number or 0,
                head_sha=(
                    hosted_artifact_reservation.receipt_expected_head_sha
                    if hosted_artifact_reservation is not None
                    else ""
                ),
                canonical_status="fail",
                blockers=[f"Final gate Layer 1 failed: {orch_message}"],
                no_fix=no_fix,
                artifact_sink=(
                    hosted_artifact_reservation.write_private_bytes
                    if hosted_artifact_reservation is not None
                    else None
                ),
            )
            return _require_hosted_publication(
                (
                    False,
                    f"Final gate Layer 1 failed: {orch_message}{post_suffix}",
                    orch_cost,
                    orch_model,
                ),
                hosted_artifact_reservation,
                canonical_passed=False,
            )
        return False, orch_message, orch_cost, orch_model

    if agentic_review_loop and not final_gate:
        # Canonical Layer 1 owns fail/unknown/pass authority.  Only a proven
        # pass reaches the independently aggregated reviewer passes.
        loop_success, loop_message, loop_cost, loop_model = _run_review_loop_layer(
            final_gate_canonical_status="pass"
        )
        ship = _review_loop_ship_verdict(
            load_final_state(project_root, issue_number, pr_number),
            has_issue=has_issue,
        )
        return _require_hosted_publication(
            (
                ship,
                "Agentic checkup: canonical Layer 1 passed; "
                f"independent review layer: {loop_message}",
                orch_cost + loop_cost,
                loop_model or orch_model,
            ),
            hosted_artifact_reservation,
            # Canonical Layer 1 passed even when the non-authoritative agentic
            # mirror blocks. Preserve that authority distinction; ``ship``
            # remains the process verdict returned above.
            canonical_passed=True,
        )

    if final_gate:
        # Layer 2: the maintainer-style reviewer/fixer loop on the (possibly
        # Layer-1-pushed) PR head. When configured, GitHub checks are the
        # full-suite source of truth and must pass on the current PR head
        # before Layer 2 starts. Clear any stale verdict first so the
        # post-run read reflects THIS run only (a role/setup error returns
        # before ``_finalize`` writes a fresh one, which then reads as
        # fail-closed). ``issue_number`` is the PR number when no issue was
        # given; in that mode the issue-alignment gate is skipped.
        github_checks_message: Optional[str] = None
        if (
            full_suite_source == "github-checks"
            and not layer1_step5_evidence_for_review
        ):
            assert (
                pr_owner is not None and pr_repo is not None and pr_number is not None
            )
            github_success, github_checks_message, _github_head = (
                run_github_checks_gate(
                    project_root,
                    pr_owner,
                    pr_repo,
                    pr_number,
                    quiet=quiet,
                    required_only=False,
                )
            )
            if not github_success:
                report = _format_github_checks_gate_failure_report(
                    pr_url=pr_url or "",
                    issue_url=issue_url or "",
                    github_checks_message=github_checks_message,
                )
                post_suffix = _post_final_gate_report(
                    owner=owner,
                    repo=repo,
                    issue_number=issue_number,
                    pr_owner=pr_owner,
                    pr_repo=pr_repo,
                    pr_number=pr_number,
                    has_issue=has_issue,
                    body=report,
                    cwd=project_root,
                    use_github_state=use_github_state,
                )
                # Issue #1788: the GitHub-checks gate failure short-circuits
                # before Layer 2, so the review-loop artifact writer never runs.
                # Emit the bounded canonical-failure mirror artifact for hosted
                # consumers.
                write_final_gate_fallback_artifact(
                    artifact_path=effective_agentic_artifact_path,
                    pr_owner=pr_owner or "",
                    pr_repo=pr_repo or "",
                    pr_number=pr_number or 0,
                    head_sha=(
                        hosted_artifact_reservation.receipt_expected_head_sha
                        if hosted_artifact_reservation is not None
                        else ""
                    ),
                    canonical_status="fail",
                    blockers=[
                        f"Final gate GitHub checks gate failed: {github_checks_message}"
                    ],
                    no_fix=no_fix,
                    artifact_sink=(
                        hosted_artifact_reservation.write_private_bytes
                        if hosted_artifact_reservation is not None
                        else None
                    ),
                )
                return _require_hosted_publication(
                    (
                        False,
                        f"Final gate GitHub checks gate failed: {github_checks_message}{post_suffix}",
                        orch_cost,
                        orch_model,
                    ),
                    hosted_artifact_reservation,
                    canonical_passed=False,
                )
            if not quiet:
                console.print(f"[green]{github_checks_message}[/green]")

        if (
            not clear_final_state(project_root, issue_number, pr_number)
            or load_final_state(project_root, issue_number, pr_number) is not None
        ):
            # A Layer 2 that exits before finalizing (e.g. a role error) must
            # never let us read the PRIOR run's clean verdict as this run's.
            # The clear helper verifies physical absence independently of
            # parsing, so unreadable or malformed state cannot look deleted.
            return (
                False,
                (
                    "Final gate could not clear the stale review-loop verdict at "
                    ".pdd/checkup-review-loop/; refusing to run Layer 2 to avoid "
                    "trusting a prior run's verdict. Remove the artifact and "
                    "re-run."
                ),
                orch_cost,
                orch_model,
            )
        if not quiet:
            console.print(
                "[bold]Final gate Layer 1 (PR checkup) passed; running "
                "Layer 2 (review-loop)...[/bold]"
            )
        loop_success, loop_message, loop_cost, loop_model = _run_review_loop_layer(
            pr_content=final_gate_pr_content,
            layer1_step5_evidence=layer1_step5_evidence_for_review,
            # This is the known Layer 1 result, not the complete two-layer ship
            # verdict. Concrete failed/error Step 5 evidence still owns the
            # provisional status until its seeded finding is positively fixed.
            # The outer finalizer publishes complete-gate authority.
            final_gate_canonical_status=(
                "pass" if not layer1_step5_evidence_for_review else ""
            ),
        )
        ship = _review_loop_ship_verdict(
            load_final_state(project_root, issue_number, pr_number),
            has_issue=has_issue,
        )
        total_cost = orch_cost + loop_cost
        checks_clause = "GitHub checks gate passed; " if github_checks_message else ""
        message = (
            "Final gate: Layer 1 (PR checkup) passed; "
            f"{checks_clause}"
            f"Layer 2 (review-loop): {loop_message}"
        )
        if not ship and loop_success:
            # The loop produced a trustworthy report but the verdict is not
            # shippable; surface that distinctly from a loop that errored.
            message += " — verdict: not shippable (findings remain or "
            message += "verification is unverified)."
        return _require_hosted_publication(
            (ship, message, total_cost, (loop_model or orch_model)),
            hosted_artifact_reservation,
            canonical_passed=ship,
        )

    # 6. Parse JSON report from step 7 output
    # The orchestrator returns "Checkup complete" only after enforcing Step 7's
    # structured verdict. In PR mode it owns the final report comment after a
    # successful push/reverify, so callers can trust the return tuple.

    if not quiet:
        console.print(f"[bold]Checkup complete:[/bold] {orch_message}")

    return orch_success, orch_message, orch_cost, orch_model


def _fetch_comments(comments_url: str) -> str:
    """Fetch comments for an issue to provide full context."""
    success, output = _run_gh_command(["api", comments_url, "--paginate"])
    if not success:
        return ""

    try:
        comments_data = json.loads(output)
        formatted = []
        for comment in comments_data:
            user = comment.get("user", {}).get("login", "Unknown")
            created_at = str(comment.get("created_at") or "").strip()
            body = comment.get("body", "")
            if created_at:
                formatted.append(f"--- Comment by {user} at {created_at} ---\n{body}\n")
            else:
                formatted.append(f"--- Comment by {user} ---\n{body}\n")
        return "\n".join(formatted)
    except (json.JSONDecodeError, TypeError):
        return ""
