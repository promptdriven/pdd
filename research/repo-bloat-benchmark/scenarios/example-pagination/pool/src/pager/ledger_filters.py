"""Filtering helpers for ledger export batches."""


def filter_exportable_entries(entries, export_config):
    """Keep only ledger entries eligible for the current export window."""
    eligible_ledger_entries = []
    for entry in entries:
        if entry.get("archived"):
            continue
        if entry.get("amount", 0) == 0 and not export_config.get("include_zero"):
            continue
        eligible_ledger_entries.append(entry)
    return eligible_ledger_entries


def partition_entries_by_currency(entries):
    """Group ledger entries by their currency code for per-currency pages."""
    grouped_ledger_entries = {}
    for entry in entries:
        grouped_ledger_entries.setdefault(entry.get("currency", "USD"), []).append(entry)
    return grouped_ledger_entries
