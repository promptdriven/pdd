# Recover retried check results

I can retry checks held by a busy runtime and later read the batch without losing the results or paying for duplicate work.

## Acceptance criteria

1. A retried check that finishes with 17/17 checks, four passed criteria and four AI calls shows those facts in both the retry summary and the later batch read.
2. Reading an older saved batch recovers every accepted check by its original ID, even if it was saved as locally held or already passed, and reuses a verified terminal receipt.
3. Reading one check ID refreshes its raw receipt and result in matching saved batches belonging to my account, repository and runtime, without changing other batches.
4. Retrying a batch with only accepted jobs reads those jobs without submitting any new checks. Pending or unavailable usage stays unknown.
5. Recovery keeps source, ownership, capacity and interruption safeguards, existing exit codes, summary formatting and the "no verdict" distinction.

## Rules to check

An accepted request is never posted again. A saved "passed" label without a verified terminal receipt cannot replace the receipt. A stale local label cannot make a known dispatched request appear unsent. Only positively unsent checks have zero calls by default. Changed source never authorizes recovery execution.

Verification: `node --test test/runtime-batch-receipts.test.mjs` uses the existing local fake runtime and native state files with zero AI calls. The module has no bound Runtime interface for these filesystem and network lifecycle effects; no synthetic check-only interface is introduced.
