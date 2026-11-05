# Move projection state without repeating old work

I can preview and apply an exact mapping from my old projection to authored source. I keep original evidence, pending cases and simulator state without rerunning uncertain work. The draft exposes a native operation to my coding agent; new CLI syntax is outside this draft.

Draft for review. These choices and expected results are not approved.

## Acceptance criteria

1. A preview shows exact original-to-authored file mappings, complete selected tests, source and reference meaning, owned records and unresolved items, and writes nothing.
2. Apply consumes the shared workflow evidence association owner, keeps original receipt bytes and request or session provenance, and does not turn historical PR 1 proof into current code-head proof.
3. Pending, conflicting, applied and interrupted saved cases keep their full payload and exact original destination mapping, with applied-once recovery or a clear unresolved result.
4. Known running, paused, pending, ended and unknown simulator or job state keeps its original identity and recovery command; migration never dispatches, recreates, reopens or replays a job.
5. Repeated or interrupted apply preserves original state and receipts, resumes without duplication or reports conflict, and retains the old projection while unresolved items remain.

## Rules to check

Use the association and eligibility rule owned by workflow-runner for issue 2899. Source equality alone cannot grant authority. Forbidden: changing receipt repository identity, shortening selected tests, changing reference meaning through prefix mapping, deleting uncertain work, or spending a model call to migrate. Migration does not expand source permission.
