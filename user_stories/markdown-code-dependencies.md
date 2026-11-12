As a prompt author, I want code examples and escaped Markdown to stay documentation, so I can preview a Story upload without false missing-file errors.

## Acceptance criteria

1. Indented code after a blank line contributes no destinations, including four-space, tab and quote/list examples; following prose and indented paragraph continuations remain active, with offsets and line endings preserved.
2. An escaped opening bracket creates neither a link nor an image; escaping only the image marker leaves an ordinary link and no image. Odd and even backslash runs apply to inline and reference uses.
3. Real destinations retain their spelling, duplicates and order, including angle destinations, balanced parentheses and escaped destination punctuation; reference labels normalize as before and the first definition wins.
4. Existing code spans, backtick/tilde fences and HTML comments still exclude their example links and definitions while preserving prose offsets and line endings.

## Rules to check

The reported documents are `# Example\n\n    ![a](miss5.svg)\n`,
`# Example\n\n\![a](x)\n`, and
`# Example\n\n## Dependencies\n\n!\[a](x)\n`.
The first contributes no destination. The second contributes no image but keeps
the ordinary link `x`. The third contributes neither a link nor an image.
A paragraph continuation must not be hidden merely because it has four spaces.

## What must not change

Ordinary links outside Dependencies remain navigation-only. Real images and
Dependency links remain included; missing or unsafe real dependencies still
refuse. Discovery preserves all authored file bytes and existing public APIs.

## Verification boundary

The prompt test checks Markdown masking and destination recognition. Native CLI
replays must separately check the unchanged Harbor fixture with `docs/example.md`
in `pdd-source.json`, upload membership, missing/unsafe refusals and archive bytes.
A parser result alone does not prove those caller-owned effects.

```pdd-boundary
prompts/cli/runtime-markdown.prompt.md
```
