"""Visible tests — deliberately under-determine the page-count contract:
they never exercise an exact-multiple length or the empty list."""

from pager.pagination import count_pages, slice_page


def test_slice_page_returns_requested_window():
    assert slice_page([1, 2, 3, 4], 1, 2) == [3, 4]


def test_slice_page_partial_last_page():
    assert slice_page([1, 2, 3], 1, 2) == [3]


def test_count_pages_partial_last_page():
    assert count_pages([1, 2, 3], 2) == 2


def test_count_pages_rejects_bad_page_size():
    import pytest

    with pytest.raises(ValueError):
        count_pages([1], 0)
