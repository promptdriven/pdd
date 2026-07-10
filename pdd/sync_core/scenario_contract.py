"""Stable required scenario identities shared by checker and launcher."""

REQUIRED_SCENARIOS = frozenset(
    {
        "source-edit-matrix",
        "missing-corrupt-delete-mode",
        "transaction-crash-race-recovery",
        "forged-stale-replayed-revoked-evidence",
        "complete-base-head-inventory",
        "trusted-runner-outcomes",
        "transactional-canonical-report",
        "merge-group-base-movement-and-stale-repair",
        "built-wheel-clean-environment",
        "pdd-cloud-real-consumer-canary",
        "released-checker-owned-scenario-harness",
    }
)
