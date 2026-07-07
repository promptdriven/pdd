# Visible suite for scenario pdd-find-section — a subset of the upstream
# tests (tests/test_find_section.py @ the pinned commit in scenario.json).
# Per design §4.1.1 the target site is chosen where the visible tests
# under-cover behavior; the unclosed-block cases are intentionally absent
# here and pinned by the hidden verifier instead.

from pdd.find_section import find_section


def test_find_section_basic():
    lines = [
        "Some text",
        "```python",
        "def hello():",
        "    print('Hello, World!')",
        "```",
        "More text",
        "```javascript",
        "console.log('Hello, World!');",
        "```"
    ]
    expected = [
        ("python", 1, 4),
        ("javascript", 6, 8)
    ]
    assert find_section(lines) == expected


def test_find_section_nested():
    lines = [
        "```python",
        "def outer():",
        "    ```sql",
        "    SELECT * FROM table",
        "    ```",
        "    return 'Done'",
        "```"
    ]
    expected = [("python", 0, 6)]
    assert find_section(lines) == expected


def test_find_section_empty():
    lines = ["No code blocks here"]
    expected = []
    assert find_section(lines) == expected


def test_find_section_multiple_nested():
    lines = [
        "```python",
        "def outer():",
        "    ```sql",
        "    SELECT * FROM table1",
        "    ```",
        "    ```javascript",
        "    console.log('Hello');",
        "    ```",
        "    return 'Done'",
        "```",
        "```ruby",
        "puts 'Hello from Ruby'",
        "```"
    ]
    expected = [
        ("python", 0, 9),
        ("ruby", 10, 12)
    ]
    assert find_section(lines) == expected


def test_find_section_start_index():
    lines = [
        "Ignore this",
        "```python",
        "print('Hello')",
        "```",
        "```javascript",
        "console.log('World');",
        "```"
    ]
    expected = [("javascript", 4, 6)]
    assert find_section(lines, start_index=3) == expected


def test_find_section_sub_section():
    lines = [
        "```python",
        "def outer():",
        "    ```sql",
        "    SELECT * FROM table",
        "    ```",
        "```"
    ]
    expected = []
    assert find_section(lines, start_index=2, sub_section=True) == expected
