# Read test evidence for the current PR head

I can read a PR and tell what was checked for its current contents, with honest warnings when the test did not check its promised output.

## Acceptance criteria

1. After checked files change or disappear, or their current source cannot be verified, the PR shows no current successful check or count for that saved result.
2. Unchanged checked content can retain its current result across commits; newer compatible evidence updates the same Story without restoring an older overall total.
3. Without current machine evidence, a PR does not present "Full npm test: 665/665 passed" typed in a verification note or summary as checked evidence; ordinary proof prose and not-checked warnings remain visible.
4. A missing machine proof remains "not run" and an unreadable proof remains "unavailable"; neither prevents publication.
5. When "the release prints only the release version" has only an exit-code assertion, pdd warns that the output is unchecked and still accepts the test.
6. Adding an output assertion for that criterion removes the exit-only warning; a criterion promising only a successful exit needs no output warning.

## What must not change

Missing or unsuccessful proof stays publishable. Source freshness does not run tests, spend model calls or approve prompts. Keep safe formatting, report links, body budgets, PR stacking and approval gates. Before changed source is pushed, an existing PR must lose its old current-success claims; a failed final description update leaves honest pending evidence.

## Rules to check

A current successful check requires compatible current selected content; changed, deleted, unavailable or unbound source must never count as a current pass. Only current-head CI or a current machine proof's actual new-code output can supply test counts. An output-criterion warning must never become a refusal or claim that output was checked.

## Coverage boundary

The runtime cases exercise the existing source-aware Story count helper, evidence preparation and local preflight through fixed outside replies. They do not publish or refresh a PR. Native code verification must replay these cases and also prove removal of stale claims from headers, step summaries, Verify and PR contents descriptions; pending edits before push; final-edit failures; exact-head CI/proof count provenance; and CLI warning propagation. No runtime pass by itself proves those effects.
