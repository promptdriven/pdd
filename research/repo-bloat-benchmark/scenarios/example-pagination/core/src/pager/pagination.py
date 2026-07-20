"""Pagination for ledger export batches."""


def slice_page(items, page, page_size):
    """Return one page of ledger items (0-indexed page)."""
    start = page * page_size
    return items[start:start + page_size]


def count_pages(items, page_size):
    """Number of pages needed to export all ledger items."""
    if page_size <= 0:
        raise ValueError("page_size must be positive")
    return (len(items) + page_size) // page_size
