"""Shared waiver status classification helpers."""
from __future__ import annotations

import re
from datetime import date
from typing import Any, Optional

from .contract_ir import Waiver

_EXPIRES_FIELD_RE = re.compile(r"^\s*expires\s*:\s*(.+)$", re.IGNORECASE | re.MULTILINE)


def _has_expires_field(waiver: Waiver) -> bool:
    return bool(_EXPIRES_FIELD_RE.search(waiver.raw_block or ""))


def classify_waiver_status(
    waiver: Waiver,
    known_rule_ids: set[str],
    *,
    today: Optional[date] = None,
) -> str:
    """Return one of: active, expired, unknown-rule, malformed."""
    current_day = today or date.today()

    required = {
        "rule": bool(waiver.rule_id),
        "reason": bool(waiver.reason),
        "approved_by": bool(waiver.approved_by),
        "expires": bool(waiver.expires is not None or _has_expires_field(waiver)),
    }
    if not all(required.values()):
        return "malformed"
    if waiver.rule_id.upper() not in known_rule_ids:
        return "unknown-rule"
    if waiver.expires is not None and waiver.expires < current_day:
        return "expired"
    return "active"


def summarize_waivers(
    waivers: list[Waiver],
    known_rule_ids: set[str],
    *,
    today: Optional[date] = None,
) -> list[dict[str, Any]]:
    """Return machine-readable waiver summary rows."""
    rows: list[dict[str, Any]] = []
    for waiver in waivers:
        status = classify_waiver_status(waiver, known_rule_ids, today=today)
        rows.append(
            {
                "id": waiver.raw_id,
                "rule_id": waiver.rule_id,
                "reason": waiver.reason,
                "approved_by": waiver.approved_by,
                "status": status,
                "expires": waiver.expires.isoformat() if waiver.expires else None,
            }
        )
    return rows
