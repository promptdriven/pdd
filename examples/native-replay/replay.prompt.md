# Native case replay recipe

`replay.mjs` is a Node command for the accompanying synthetic native cases. It
accepts a case JSON path and a JavaScript module path as its two arguments. The
module exports `countWords`; each case supplies its input and exactly one expected
return value or expected error name and message. Call that real export for every
case. A return passes only when it deeply equals the expected return; a thrown
error passes only when both its name and message match the expected error.
A missing expected error, an unexpected error, a wrong error or wrong return
fails the case. Print one `PASS <id>` or `FAIL <id>` line per case, followed by
`<passed>/<total> passed`, and exit 0 only when all cases pass. Invalid cases,
missing exports and setup errors exit nonzero and must not count as detections.
The cases are independently authored expectations, not values copied from a run.

This verification command owns neither the target module nor its Runtime
interface. It demonstrates native execution; it is not a Runtime entry and has
no declared Runtime interface. Native results do not approve prompts or gates.

## Dependencies

The command reads its case file and imports the target module supplied by the
caller. Node.js supplies file and module loading and deep equality.
