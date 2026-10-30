# I see which shared records and Stories changed

## Acceptance criteria

1. The contract list names records, their owner files and their current prompt and test users.
2. Changing a used shared record marks every Story using it stale since its last actual check.
3. A different record in the same file leaves an unrelated Story in the same batch current.
4. No actual check baseline is shown as not checked, and a legacy baseline is shown as unavailable.
5. Lint and Try do not replace an actual check baseline.
6. Listing contracts makes no runtime call and changes no source or history.

## Rules to check

Compare each Story with its latest evaluated Check and its own effective source footprint. Refused/pending/unknown work supplies no new baseline. Failed checks stay failed; source freshness is not a pass. Transitive references count as uses.

Runtime check: native effects unbound: file/history/write cases specified separately; expansion cases do not establish these effects.
