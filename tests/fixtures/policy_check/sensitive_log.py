"""Audit helper that logs a sensitive variable name."""

import logging

logger = logging.getLogger(__name__)


def audit_refund(bearer_token: str) -> None:
    """Log refund activity (forbidden: sensitive name in log call)."""
    logger.info("refund processed: %s", bearer_token)
