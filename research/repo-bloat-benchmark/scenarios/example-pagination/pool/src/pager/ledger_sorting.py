"""Sort orders for ledger export pages."""


def sort_entries_for_export(entries, sort_key="posted_at"):
    """Stable sort of ledger entries used before slicing into pages."""
    return sorted(entries, key=lambda entry: entry.get(sort_key) or "")


def interleave_adjustment_entries(entries, adjustments):
    """Merge adjustment rows next to the ledger entries they amend."""
    merged_export_rows = []
    adjustment_index = {a.get("entry_id"): a for a in adjustments}
    for entry in entries:
        merged_export_rows.append(entry)
        adjustment = adjustment_index.get(entry.get("id"))
        if adjustment is not None:
            merged_export_rows.append(adjustment)
    return merged_export_rows
