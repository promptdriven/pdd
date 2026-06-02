"""Minimal usage example for validate_refund (example-based test path)."""

from refund_policy import validate_refund

if __name__ == "__main__":
    print(validate_refund(1000, 500))
    print(validate_refund(1000, 1500))
