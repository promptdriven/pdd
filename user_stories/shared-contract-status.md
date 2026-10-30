# I see which shared records and Stories changed

## Acceptance criteria

1. The contract list names records, their owner files and their current prompt and test users.
2. Changing a used shared record marks every Story using it stale since its last actual check.
3. A different record in the same file leaves an unrelated Story in the same batch current.
4. No actual check baseline is shown as not checked, and a legacy baseline is shown as unavailable.
5. Lint and Try do not replace an actual check baseline.
6. Listing contracts makes no runtime call and changes no source or history.
7. Checking one test, all tests of the same Story or a larger batch leaves an unchanged Story current.
8. Listing many records from one JSON file reads and parses that file once and leaves independent uses unchanged.

## Rules to check

Compare each Story with its latest evaluated Check and its own effective source footprint. Refused/pending/unknown work supplies no new baseline. Failed checks stay failed; source freshness is not a pass. Transitive references count as uses. A Story footprint includes all discovered tests for that Story and their closures regardless of selection; other Stories stay outside it.

A missing entry prompt, missing seed or other unresolved source in an unselected sibling records that sibling's footprint as unavailable and lets the selected good test continue, with or without contracts. The affected Story cannot claim a complete footprint or current freshness from a partial closure. Selecting the same broken source still refuses before upload/authentication; valid siblings keep their complete selection-independent footprint.

Within one catalog operation parse a JSON contract file once, reuse immutable parsed data and clone before differing annotations or overrides. No timing threshold is a gate.

Runtime check: native effects unbound: file/history/write cases specified separately; expansion cases do not establish these effects.
