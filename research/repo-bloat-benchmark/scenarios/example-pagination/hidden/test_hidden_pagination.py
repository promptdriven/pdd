"""Hidden verifier — the sole arbiter of success (design §4.4).

Checks exactly what the visible tests under-determine: exact-multiple
lengths and the empty list. Never mounted into the agent's sandbox.
"""

from pager.pagination import count_pages, slice_page


def test_count_pages_exact_multiple():
    assert count_pages([1, 2, 3, 4], 2) == 2


def test_count_pages_empty():
    assert count_pages([], 5) == 0


def test_count_matches_slicing_for_many_shapes():
    for length in range(0, 12):
        items = list(range(length))
        for page_size in range(1, 6):
            pages = count_pages(items, page_size)
            sliced = [
                slice_page(items, page, page_size) for page in range(pages)
            ]
            flattened = [x for chunk in sliced for x in chunk]
            assert flattened == items
            if pages:
                assert sliced[-1] != []
