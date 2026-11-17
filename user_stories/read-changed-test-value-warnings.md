# Read a changed test value

As a developer reviewing a changed saved test value, I want to read its path and link in the terminal and in the pull request, so that I can see exactly what changed.

## Acceptance criteria

1. When a saved value in `tests/add.json` changes from `3` to `https://example.test/new?a=1&b=2`, the terminal warning shows the path and link as plain text.
2. The pull request warning preserves the same path and link as literal text, escaped in the description so Markdown does not interpret it as a link.
