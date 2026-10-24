# Story: ticket status labels

Synthetic teaching example; it describes no real customer or ticket system.

## Request and scope

As a reader of ticket data, I want a stable label for each recognized status and an honest unknown result for unrecognized data, so the display does not silently mislabel tickets. Preserve the public `statusLabel(status)` function and the [owning prompt](../prompts/status-label.prompt.md). Rendering, fetching tickets, localization and changing ticket state are outside this example.

## Observable acceptance criteria

- **AC1:** `open`, `blocked` and `done` return `Open`, `Blocked` and `Done` respectively.
- **AC2:** Any other string, including empty text, and `null` return `Unknown` without throwing.
- **AC3:** Any non-string other than `null`, including omitted input, throws `TypeError` rather than being coerced. No specific error message is required.
- **AC4:** Matching is exact and case-sensitive. Whitespace and different case do not become recognized statuses; input conversion hooks are never used.

The independently authored [expected cases](../vectors/status-labels.json) map inputs to these criteria. The ordinary [native tests](../test/status.test.mjs) also cover JavaScript values that JSON cannot represent. Expected values come from this contract, never from calling the implementation. Passing these cases is finite evidence, not a proof over all JavaScript inputs.
