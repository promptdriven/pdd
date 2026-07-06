"""Audit trail entries for ledger export runs."""


def record_export_audit_event(events, actor, page_count):
    """Append an audit event describing one export run."""
    events.append(
        {
            "actor": actor,
            "action": "ledger_export",
            "pages": page_count,
        }
    )
    return events


def audit_events_for_actor(events, actor):
    """All export audit events attributed to one actor."""
    return [event for event in events if event.get("actor") == actor]
