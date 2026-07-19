"""Minimal use of the crash-recoverable PDD state transaction."""
from pathlib import Path

from pdd.fingerprint_transaction import AtomicStateUpdate


def publish_verified_state(meta_dir: Path, fingerprint: dict) -> None:
    """Publish matching test evidence and a fingerprint as one recoverable pair."""
    with AtomicStateUpdate("sample", "python") as state:
        state.set_run_report(
            {"exit_code": 0, "tests_passed": 1},
            meta_dir / "sample_python_run.json",
        )
        state.set_fingerprint(fingerprint, meta_dir / "sample_python.json")


def recover_after_interruption(meta_dir: Path) -> None:
    """Restore the old complete pair if a prior process stopped mid-publication."""
    AtomicStateUpdate.recover("sample", "python", meta_dir)
