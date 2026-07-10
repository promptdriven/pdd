"""Locate fenced code blocks in markdown-style text.

Dependency-sliced from ``pdd/find_section.py`` (upstream pinned commit in
``scenario.json``); identifiers and structure were normalized during slicing
— see ``seed.patch`` for the recorded transform.
"""


def find_section(lines, start_index=0, sub_section=False):
    """Return ``(language, start, end)`` for each top-level ``` fenced block.

    Only blocks whose opening fence is at or after ``start_index`` are
    reported. With ``sub_section=True`` the first qualifying closed block is
    returned on its own. Blocks left unclosed at end of input are reported
    as running to the end of the input.
    """
    found = []
    open_blocks = []

    for index, raw in enumerate(lines):
        fence = raw.strip()
        if not fence.startswith('```'):
            continue
        if len(fence) > 3:
            # Opening fence: remember where it started and its language tag.
            open_blocks.append((index, fence[3:].strip()))
        elif open_blocks:
            # Closing fence for the most recent open block.
            start, language = open_blocks.pop()
            if open_blocks or start < start_index:
                continue
            if sub_section:
                return [(language, start, index)]
            found.append((language, start, index))

    # Unclosed blocks run to the end of the input.
    while open_blocks:
        start, language = open_blocks.pop()
        if not open_blocks and start >= start_index:
            found.append((language, start, len(lines)))

    return found
