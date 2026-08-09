# Bug report: unclosed fenced code block reports an out-of-range end index

`find_section` scans markdown-style text for ``` fenced code blocks and
returns `(language, start, end)` line-index tuples.

When a fenced block is opened but **never closed** before the end of the
input, the function reports an end index **equal to the number of input
lines** — one past the last valid line index. Downstream consumers that
slice `lines[start:end + 1]` or index `lines[end]` on the result either
drop content or raise `IndexError` for unclosed blocks.

Expected behavior: a block that is still open at end of input ends at the
**last line index** of the input.

Closed-block behavior is correct and must not change.

## Constraints

- Fix the defect in the library code under `src/pdd/`.
- Do not modify anything under `tests/`.
- The visible suite (`pytest tests/visible -q`) must keep passing.
