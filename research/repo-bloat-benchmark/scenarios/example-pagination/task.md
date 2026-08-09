# Bug report: page count wrong for exports that fill pages exactly

When exporting a ledger whose row count is an exact multiple of the page
size, the export footer shows one page too many. For example, exporting 4
rows with `page_size=2` reports **3 pages**; the export itself only has 2.

Empty exports also report 1 page instead of 0.

## Reproduction

```python
from pager.pagination import count_pages
count_pages([1, 2, 3, 4], 2)   # expected 2
count_pages([], 5)             # expected 0
```

## Acceptance

Page counts must equal the number of pages `slice_page` actually yields, for
every list length and page size. Existing behavior for partial last pages
must not change.
