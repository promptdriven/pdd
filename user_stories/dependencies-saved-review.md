# Reuse and recover dependency reviews

I can keep a dependency review on GitHub and reuse it after a restart.

## Acceptance criteria

1. A fresh machine reuses a saved completed empty review. A newer question or pending review suppresses that older completion.
2. Competing current reviews, edited records and revoked or unknown review authority remain unresolved; an outsider marker gives no authority.
3. A confirmed continuation can finish only its own pending intent. An absent confirmed edge stays absent and requires an override review.
4. After one edge of a two-edge intent is present, a changed requirement keeps that edge, leaves the second absent, and leaves recovery pending with no new edge write.
5. A lost edge-write reply is reconciled from the present native edge without adding it twice. Checked-empty save appends one durable review.
6. A completed current new-issue impact check reuses unaffected review heads. Unfinished or stale impact coverage does not.

7. A cross-repository blocker with issue number 42 and a different REST ID is added to the dependent with its REST ID. A GraphQL node ID never supplies the write identity.

## Rules to check

No older complete record may hide a current question, pending result, edit, trust loss or conflict. A stale or replaced intent must never add an absent edge. A later human removal must never be restored from a confirmed review. Unfinished impact coverage cannot establish freshness.

Native replay must also call applyDependencyChanges with its default snapshot
reader and injected raw GitHub/context ports. Supply blocker number 42, REST id
834217 and node_id I_distinct_graphql_schema42. Assert dependent repository
example/crm, issue 42 and blockerId "834217" on the real addBlocker callback.
The native transport test must inspect REST body issue_id 834217. A normalized
snapshot fixture alone does not prove this raw read-to-write wiring.
