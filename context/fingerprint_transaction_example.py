"""Examples of the shared fingerprint finalization boundary."""
from __future__ import annotations

from pathlib import Path
from typing import Any

from pdd.fingerprint_transaction import FingerprintTransaction


def finalize_generated_unit(
    prompt_path: Path,
    code_path: Path,
    *,
    dry_run: bool = False,
) -> Path:
    """Persist a complete fingerprint, or explicitly skip a dry run."""
    transaction = FingerprintTransaction(
        "sample",
        "python",
        "generate",
        paths={"prompt": prompt_path, "code": code_path},
        cost=0.01,
        model="example-model",
    )
    with transaction:
        if dry_run:
            transaction.skip("dry-run")
    return transaction.fingerprint_path


class FingerprintBuffer:
    """Minimal duck-typed buffer used by an outer atomic-state context."""

    def __init__(self) -> None:
        self.pending: tuple[dict[str, Any], Path, str | None] | None = None

    def set_fingerprint(
        self,
        payload: dict[str, Any],
        path: Path,
        *,
        operation: str | None = None,
    ) -> None:
        self.pending = (payload, path, operation)


def buffer_sync_fingerprint(
    paths: dict[str, Path],
    buffer: FingerprintBuffer,
) -> None:
    """Build the canonical payload while deferring persistence to sync."""
    with FingerprintTransaction(
        "sample",
        "python",
        "sync",
        paths=paths,
        atomic_state=buffer,
    ):
        pass
