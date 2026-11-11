As a person reviewing a PDD code PR, I want green public checks to reveal stale
generated-source prompt digests, so that I can verify the source-to-code
relationship before the PR is reported ready.

## Acceptance criteria

1. I can run a local check against a base revision and see every affected stale header's source path, prompt path and expected/current digests, with a failing exit status.
2. A changed owning prompt makes its unchanged generated source subject to the check, including when the prompt arrives through an alpha integration.
3. Correct digests pass; approval metadata changes do not stale behavior digests, and unrelated stale headers do not block this PR.
4. Missing prompts and unavailable comparisons cannot produce a green check; the check changes no source or prompt files.
5. Public checks run the same verification on the proposed integration before the offline tests; after integrating alpha I can rerun it locally before reporting the PR ready.

## Rules to check

For each affected surviving file, every header that claims a digest must match
the shared owner lookup's current digest rules. Green Runtime approval or code
full-file hash checks cannot substitute for this verification. Hashless ownership
headers make no digest claim and remain outside this check.
