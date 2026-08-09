# Hidden verifier for scenario pdd-find-section (design §4.4).
#
# Pins the unclosed-fence contract the visible suite deliberately leaves
# open: a block that is never closed ends at the LAST line index
# (len(lines) - 1), never one past it. This tree is physically separate
# from the core and must never enter the agent sandbox.

from pdd.find_section import find_section


def test_unclosed_block_ends_at_last_line_index():
    lines = [
        "Some text",
        "```python",
        "def unclosed():",
        "    print('This block is not closed')"
    ]
    assert find_section(lines) == [("python", 1, 3)]


def test_unclosed_block_opened_on_final_line():
    lines = [
        "prose",
        "```toml"
    ]
    assert find_section(lines) == [("toml", 1, 1)]


def test_unclosed_outer_with_closed_inner_block():
    lines = [
        "```python",
        "def outer():",
        "    ```sql",
        "    SELECT 1",
        "    ```",
        "    return None"
    ]
    assert find_section(lines) == [("python", 0, 5)]


def test_unclosed_block_respects_start_index():
    lines = [
        "```python",
        "print('closed')",
        "```",
        "```yaml",
        "key: value"
    ]
    assert find_section(lines, start_index=3) == [("yaml", 3, 4)]


def test_closed_blocks_unaffected_by_the_fix():
    lines = [
        "```python",
        "x = 1",
        "```"
    ]
    assert find_section(lines) == [("python", 0, 2)]
