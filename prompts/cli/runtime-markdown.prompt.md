# Runtime Markdown links

Own `src/runtime-markdown.mjs`. Share the existing runtime source discovery
parser with Story boundary parsing. Preserve destination ordering and spelling,
inline angle destinations, escaped characters and balanced parentheses, and
inline optional titles. Link labels are not paths.

Export `markdownDefinitions(text)`: return a Map of reference labels to raw
destinations from Markdown reference definitions. Normalize labels by trimming,
collapsing whitespace and lowercasing. The first definition wins. Accept angle
destinations and ordinary non-whitespace destinations.

Export `markdownLinks(text,definitions,imagesOnly=false)`: return destination
strings for inline links followed by full, collapsed and shortcut reference
links resolved from the supplied Map. With imagesOnly, return only image uses.
Do not treat definitions as uses. Unresolved references return no destination;
strict declaration callers must refuse them rather than accept partial scope.
Export `markdownSectionText(text)`: return a prose view with offsets and newlines
preserved. Mask code spans, backtick/tilde fences and HTML comments. A code span
closes with a backtick run of exactly its opening length in the same leaf block;
an unmatched opener retains prose. Escaped openers do not start spans; backslashes
inside spans do not prevent closing. Paragraphs, headings, HTML block starts and
container changes bound inline spans and comments. Retain ordinary tags and
angle destinations, consuming valid tags and autolinks before looking for
backticks within them. An inline comment masks through its matching close within
the leaf block. A comment starting a block masks through its close or the rest.

A fence opens with at least three identical backticks or tildes and closes only
with the same character and at least its opening length. Backtick fence info
cannot contain a backtick. Shorter and different closing markers stay inside the
example. Preserve quote/list container continuation, indentation and paragraph
boundaries when finding fences; an unclosed fence masks the rest of its
container. Tabs count to four-column stops for indentation only. These masks
also exclude reference definitions inside examples and comments. Callers own
section selection, syntax admission and path safety. Do no I/O and do not rewrite
captured source bytes.

## Dependencies

None.

<details><summary>Runtime interface</summary>

```json
{"status":"draft","prose_sha256":"","entries":[],"calls":[],"resources":[],"limits":{"max_steps":12,"max_model_calls":6},"conventions":[]}
```
</details>
