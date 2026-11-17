# Render a changed saved test-value warning

Own src/saved-value-warning.mjs. Export the pure module function
`formatSavedValueWarning({vector, reason?, path?, before?, after?, format?})`, returning one string.
`vector` is the exact repository-relative scenario path. For a nonempty `reason` string, show
`warning: Saved test values changed: VECTOR REASON`. Otherwise `path` is the JSON Pointer
(the empty string denotes the root), and `before` and `after` are pre-serialized JSON values
with exact numeric spelling, or `(missing)`. Show `warning: Saved test values changed: VECTOR PATH BEFORE -> AFTER`.

## Domain decisions

- `format` is `plain` for command output and `markdown` (the default) for a PR description.
  In plain text, show printable characters as given, including slashes in paths, pointers and URLs.
- In both formats, keep vector paths, reasons and pointers distinguishable by quoting their contents
  as JSON string text without the outer quotes. Write code units outside printable ASCII as lowercase
  four-digit JSON Unicode escapes, so controls, invisible characters and bidi characters cannot alter the display.
  Preserve the exact supplied JSON spelling of values apart from that display escaping.
- In Markdown only, keep Markdown punctuation and HTML inert, including backslash, backtick, asterisk,
  underscore, square brackets, parentheses, pipe, ampersand, angle brackets and slashes. Encode slashes
  as `&#47;` so the PR description's path cleaner cannot collapse paths or damage URLs. Keep the
  `pdd-workflow:` and `pdd-product:` markers inert by escaping their colons as in other replay metadata.
- Do not truncate, redact or decode warning contents. Budgeting and storage belong to the replay report.
