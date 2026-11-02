# Runtime split

Own `src/runtime-split.mjs`: the one place in pdd that knows how much one server
request can take, and how a selection of tests is cut into parts that each fit.
A lint or check of many Stories can be larger than one upload or than one lint
can judge before its deadline. Then pdd sends the selection in parts, never a
silent cut and never a refusal of the whole run. Pure planning: no IO, clock or
module state; captures are measured by an injected function.

## Limits

Export `UPLOAD = {bytes: 10485760, files: 10000}`: the server's upload limit for
one source archive (prompt-runtime `server/uploads.py` and the request body limit
in `server/http_server.py`). This is the only copy in pdd; [preflight](runtime-preflight.prompt.md)
uses it for its own capture guard. A caller may pass other limits (the client's
`uploadLimits` port, for tests and for a value the server publishes later).

The server also stops a lint's per-test admission at a deadline (90 s, shared with
the prompt lint) and lists at most 200 tests (`server/lint_driver.py` `MAX_TESTS`).
pdd does not guess a test count from that deadline: a test that a lint did not
reach is linted again in a new part (see the [client](runtime-client.prompt.md#parts)).

## Plan parts

Module function `planParts(stories, {measure, limits = UPLOAD})` returns
`{parts: [{stories, tests}], refused: [{story, tests, bytes, files}]}`.

- `stories` is the selection in table order: `[{story, tests}]`, each with its
  selected test paths. A Story is never split across parts.
- `measure(tests)` returns the capture of exactly those tests:
  `{bytes: <archive size>, files: <file count>}`. A part fits when
  `bytes <= limits.bytes` and `files <= limits.files`. Shared files count once,
  because the part is measured as one capture.
- Pack greedily in order: add the next Story to the current part when the part
  with it still fits, otherwise start a new part with it.
- A Story that does not fit even alone is refused, with its measured `bytes`
  and `files`. It is never sent, and it never stops the other Stories.
- An empty selection gives no parts. One part that fits everything is the
  normal case and changes nothing in the output.

Module function `partsText(counts, sizes, verb = 'Sent')` takes each part's test
count and its size text (the caller formats sizes) and returns the stderr line for
two or more parts, for example `Sent in 3 parts: 12, 12 and 9 tests (9.8 MB,
9.6 MB, 4.1 MB).` (`Linted in …` for `pdd lint`), and null for one part.

## Dependencies

None. [Preflight](runtime-preflight.prompt.md) and the [client](runtime-client.prompt.md)
import `UPLOAD` and the planner from here.
