"""Demo tests for `pdd coverage --contracts`.

The coverage command only scans explicit rule IDs in test names, comments, and
docstrings. These tests are intentionally lightweight fixtures.
"""


def test_R1_rejects_zero_refund():
    """R1: zero-amount refund is rejected."""
    assert True


def test_R3_no_provider_call_invalid():  # R3: provider is not called for invalid refunds
    assert True


def test_non_contract_helper_behavior():
    assert True

