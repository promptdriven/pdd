# Markdown examples do not add upload dependencies

As a person previewing the files for a Story, I can include documentation with code examples and escaped Markdown without pdd requiring example paths as upload dependencies.

## Acceptance criteria

1. A documentation file containing `# Example`, a blank line, and `    ![a](miss5.svg)` does not require `miss5.svg`.
2. A documentation file containing `# Example`, a blank line, and `\![a](x)` does not require `x`: the remaining link is navigation outside Dependencies.
3. A documentation file containing `# Example`, a blank line, `## Dependencies`, another blank line, and `!\[a](x)` does not require `x`.
4. Genuine images and declared dependencies are included; missing or unsafe genuine dependencies still refuse.
