"""Summary lines for completed ledger exports."""


def summarize_export_batch(pages, export_config):
    """One-line summary of an export batch for the reporting feed."""
    total_entries = sum(len(page) for page in pages)
    return {
        "pages": len(pages),
        "entries": total_entries,
        "batch_label": export_config.get("label", "ledger-export"),
    }


def format_summary_line(summary):
    """Render a summary dict for the export activity log."""
    return (
        f"{summary['batch_label']}: {summary['entries']} entries "
        f"across {summary['pages']} pages"
    )
