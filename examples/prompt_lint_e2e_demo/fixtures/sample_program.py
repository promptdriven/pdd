"""Fixture program for verifier smoke test."""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from sample_code import validate_refund  # noqa: E402


def main() -> None:
    for amount, original in ((50, 100), (0, 100), (150, 100)):
        print(validate_refund(amount, original))


if __name__ == "__main__":
    main()
