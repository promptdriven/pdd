# Well-Specified PRD: Payment Processing Module

## Overview

Add a payment processing module at `pdd/payments.py` that exposes a `process_payment()`
function. The module integrates with the Stripe API for card charging and emits audit
records to `.pdd/evidence/payments/`.

## Requirements

### R-1: process_payment function signature

`pdd/payments.py` MUST export `process_payment(user_id: str, amount_cents: int, currency: str) -> PaymentResult`.

**Acceptance criteria:**
- `PaymentResult` is a Pydantic v2 `BaseModel` with fields `payment_id: str`, `status: str`, `error_message: str | None`.
- When Stripe returns HTTP 200, `status` is `"succeeded"`.
- When Stripe returns HTTP 402, `status` is `"declined"` and `error_message` contains the decline reason.
- Test: `tests/test_payments.py::TestProcessPayment::test_successful_charge` covers HTTP 200 path.
- Test: `tests/test_payments.py::TestProcessPayment::test_declined_charge` covers HTTP 402 path.

### R-2: Route registration

`pdd/server/routes/payments.py` MUST register `POST /api/v1/payments` and return HTTP 201 on success.

**Acceptance criteria:**
- Route decorator: `@router.post("/api/v1/payments", status_code=201)`.
- Router registered in `pdd/server/main.py` via `app.include_router(payments_router)`.
- Test: `tests/server/test_payment_routes.py::TestPaymentRoutes::test_create_payment_returns_201`.

### R-3: Config entry

`config/settings.yaml` MUST declare `stripe.api_key` with type `str` and no default value.

**Acceptance criteria:**
- Key present in `config/settings.yaml` under `stripe:`.
- Validation in `pdd/config.py` raises `ConfigError` if key is missing.
- Test: `tests/test_config.py::test_missing_stripe_key_raises`.

## Required Variant List (exhaustive)

The following payment statuses are the ONLY supported values: `succeeded`, `declined`, `pending`, `refunded`.

## Interface References

- `PaymentResult` fields: `payment_id: str`, `status: Literal["succeeded", "declined", "pending", "refunded"]`, `error_message: str | None`.
- `StripeClient.__init__(api_key: str)`, `StripeClient.charge(amount: int, currency: str, source: str) -> dict`.
