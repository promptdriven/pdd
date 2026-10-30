# Recover retried check results

I can retry checks held by a busy runtime and later read the batch without losing the results or paying for duplicate work.

## Acceptance criteria

1. A retried check that finishes with 17/17 checks, four passed criteria and four AI calls shows those facts in both the retry summary and the later batch read.
2. Reading an older saved batch recovers every accepted check by its original ID, even if it was saved as locally held or already passed, and reuses a verified terminal receipt.
3. Reading one check ID refreshes only its raw receipt in matching saved batches belonging to my account, repository and runtime; batch and summary files stay byte-identical until the next batch read lazily updates the result. The hidden --request path is excluded.
4. Retrying a batch with only accepted jobs reads those jobs without submitting any new checks. Pending, unavailable or incomplete usage stays unknown, while summaries retain known calls plus the unknown part.
5. Recovery keeps source, ownership, capacity and interruption safeguards, existing exit codes (except that a saved passed label without terminal evidence becomes unknown with exit 3), summary formatting and the "no verdict" distinction.

## Rules to check

An accepted request is never posted again. A saved "passed" label without a verified terminal receipt cannot replace the receipt. A stale local label cannot make a known dispatched request appear unsent. Final POST refusals and nonbusy not-run outcomes keep their verdict and exit code without GETs, including older saved batches with no receipt. A request ID alone is not acceptance. Zero-eligible retries keep polling accepted IDs until terminal or the wait limit; stale busy flags without unstarted proof cannot authorize a POST. Only positively unsent checks have zero calls by default. Changed source never authorizes recovery execution.

Verification: `node --test test/runtime-batch-receipts.test.mjs test/runtime-batch-receipts-verify.test.mjs test/runtime-batch-receipts-formal.test.mjs test/runtime-batch-receipts-review.test.mjs` uses the existing local fake runtime and native state files with zero AI calls. The module has no bound Runtime interface for these filesystem and network lifecycle effects; no synthetic check-only interface is introduced.
