# Keep passes when another check has not started

I can see my earlier passing checks in product progress when a later check stops before sending them.

## Acceptance criteria

1. After four current server Story passes, a later check on the same files that sends none of its checks keeps server 4 of 4 and slice 1 4 of 13; this holds after a lint hold or a stop before sending, including for saved Check batches without an intent label.
2. A saved check that was never sent supplies no passing, failing, unknown or stale Story result, even if its saved label says passed or its lint finished; a Story with only unsent checks supplies no result.
3. When one Story has two selected tests and only one was sent and passed, the incomplete later check neither establishes a whole-Story pass nor erases an earlier pass. An unsent duplicate of an already sent passing test does not make that Story incomplete or failing, and an unsent check for a different Story does not hide a completed Story.
4. A later sent check that fails, is unknown or lacks a valid matching receipt still cannot pass and can replace an earlier pass, including when another selected test for that Story was never sent.
5. Source matching uses every originally selected test, including unsent tests; reading this progress makes no Runtime request, authenticates no Runtime user, changes no saved check and starts no workflow.

## Rules to check

Only a saved row's Check request IDs establish a sent attempt; a lint request
does not. A well-formed row with an empty Check request-ID list supplies no
evidence. Nonempty lists retain the existing latest-attempt and matching-receipt
rules, even when the receipt is absent, invalid or for a different request.

Whole-Story success requires a sent pass for every unique test originally
selected for that Story. Missing sent coverage omits an otherwise all-passing
summary, while a sent nonpassing result retains its negative evidence. Unsent
duplicates cannot add missing coverage, failures or result times. The complete
original selection still defines source identity. Existing legacy batch
validation, capture sharing, currentness and warning rules remain in force.
