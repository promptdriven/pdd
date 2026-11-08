# Markdown examples do not add upload dependencies

As a person previewing the files for a Story, I can include documentation with code examples and escaped Markdown without pdd requiring example paths as upload dependencies.

## Acceptance criteria

1. A documentation file containing `# Example`, a blank line, and `    ![a](miss5.svg)` does not require `miss5.svg`.
2. A documentation file containing `# Example`, a blank line, and `\![a](x)` does not require `x`: the remaining link is navigation outside Dependencies.
3. A documentation file containing `# Example`, a blank line, `## Dependencies`, another blank line, and `!\[a](x)` does not require `x`.
4. Genuine images and declared dependencies are included; missing or unsafe genuine dependencies still refuse.

## Rules to check

- The indented example must not make `miss5.svg` an upload dependency or cause a missing-file refusal.
- Escaping `!` in `\![a](x)` leaves a navigation link outside Dependencies; it must not make `x` an upload dependency or cause a missing-file refusal.
- Escaping `[` in `!\[a](x)` leaves neither a link nor an image; it must not make `x` an upload dependency or cause a missing-file refusal, even inside Dependencies.
- An indented code block continues across indented and blank lines, ends at prose, and cannot interrupt a paragraph; a genuine dependency after it remains a dependency.
- Consecutive backslashes escape punctuation in odd runs and leave it active in even runs. An escaped image marker leaves a link that counts inside Dependencies; an escaped opening bracket leaves neither link nor image.
- Actual images and links declared in Dependencies remain upload dependencies. Missing or unsafe actual dependencies must still refuse.
