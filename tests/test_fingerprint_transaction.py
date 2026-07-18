"""PDD-named contract coverage for the fingerprint transaction module."""
from pdd.fingerprint_transaction import AtomicStateUpdate, finalize_fingerprint


def test_fingerprint_transaction_public_contract() -> None:
    """The prompt-declared finalizer and recovery API remain importable."""
    assert callable(finalize_fingerprint)
    assert callable(AtomicStateUpdate.recover)
