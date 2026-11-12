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
An opening `[` creates a link use only when unescaped. A punctuation character
is escaped exactly when immediately preceded by an odd run of backslashes. An
image additionally needs an adjacent unescaped `!` before its unescaped `[`.
An escaped `!` can leave an ordinary link. Apply these opening-marker rules to
inline, full, collapsed and shortcut reference uses.
Do not treat definitions as uses. Unresolved references return no destination;
strict declaration callers must refuse them rather than accept partial scope.
Export `markdownSectionText(text)`: return a prose view with offsets and newlines
preserved. Replace masked characters with spaces, keeping CR and LF unchanged.
Mask code spans, backtick/tilde fences and HTML comments. A code span
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
also exclude reference definitions inside examples and comments.

Mask indented code at a leaf block boundary when content has at least four
columns of indentation relative to its quote/list container. Tabs advance to
four-column stops. An indented code block cannot interrupt a paragraph: an
indented paragraph continuation remains prose. Blank lines can continue a code
block; a nonblank line below the required indentation ends it. Container exits
end its scope; code lines cannot use lazy container continuation.

Callers own section selection, syntax admission and path safety. Do no I/O and
do not rewrite captured source bytes.

## Runtime transport

Keep the native exported signatures and return types above. The Runtime uses
JSON object envelopes for these same three operations; no native wrapper is added:

| Operation | Input | Result |
|---|---|---|
| `markdownSectionText` | required string `text` | required string `text`, the returned prose view |
| `markdownDefinitions` | required string `text` | required `definitions`, the returned Map as ordered rows |
| `markdownLinks` | required string `text` and `definitions`; optional Boolean `imagesOnly`, default false | required `destinations`, the returned ordered string array |

Every envelope has exactly the listed fields. Each definitions row has exactly
string `label` and `destination`; labels are unique. Rows preserve Map insertion
order and exact keys and values. Decode input rows as the supplied Map, without
normalizing its keys. The transport performs no implicit masking or section
selection: callers can pass the prose view to either scanner. These operations
have no resources, child calls or persistent state.

## Dependencies

None.

<details><summary>Runtime interface</summary>

```json
{"status":"approved","prose_sha256":"fa297c8d3b7525ddec73a1d4898d61b892e2825415ae702b4bb258339c75fe4d","entries":[{"operation":"markdownSectionText","input_schema":{"type":"object","properties":{"text":{"type":"string"}},"required":["text"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"text":{"type":"string"}},"required":["text"],"additionalProperties":false},"errors":[]},{"operation":"markdownDefinitions","input_schema":{"type":"object","properties":{"text":{"type":"string"}},"required":["text"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"definitions":{"type":"array","items":{"type":"object","properties":{"label":{"type":"string"},"destination":{"type":"string"}},"required":["label","destination"],"additionalProperties":false}}},"required":["definitions"],"additionalProperties":false},"errors":[]},{"operation":"markdownLinks","input_schema":{"type":"object","properties":{"text":{"type":"string"},"definitions":{"type":"array","items":{"type":"object","properties":{"label":{"type":"string"},"destination":{"type":"string"}},"required":["label","destination"],"additionalProperties":false}},"imagesOnly":{"type":"boolean","default":false}},"required":["text","definitions"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"destinations":{"type":"array","items":{"type":"string"}}},"required":["destinations"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":12,"max_model_calls":6},"conventions":[]}
```
</details>
