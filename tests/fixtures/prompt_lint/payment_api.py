"""
Stub Python module that implements the payment_api_python.prompt contract.
Used as a companion file in lint tests to verify the prompt→code relationship.
Not meant to run — it exists to make the test fixture directory realistic.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional


@dataclass
class ChargeRequest:
    idempotency_key: str
    merchant_id: str
    amount: int       # smallest currency unit (e.g. cents)
    currency: str     # ISO 4217 (e.g. "USD")


@dataclass
class ChargeReceipt:
    id: str
    status: str       # "succeeded" | "pending" | "failed"
    amount: int
    currency: str


class PaymentAPI:
    """Stub implementation of the charge endpoint contract."""

    def charge(
        self,
        request: ChargeRequest,
        bearer_token: Optional[str],
    ) -> tuple[int, dict]:
        """
        POST /charge — returns (http_status_code, response_body).

        Contract obligations:
          R1  — reject invalid amounts (amount <= 0 or > 99_999_999)
          R2  — return 403 for unauthorized principals
          R3  — return existing record for duplicate idempotency_key
          R4  — return 200 with successful charge receipt on success
          R5  — return 502 gracefully on provider failure
        """
        raise NotImplementedError("Stub — implement against the prompt contract")
