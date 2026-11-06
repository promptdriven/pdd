# Durable prompt-only scope

I can limit named work to its prompt PR and inspect that limit later, so PDD waits for my explicit permission before starting code.

## Acceptance criteria

1. I can set a prompt-only limit for a named run or a named batch with explicit members, including work that has not started and an existing saved run.
2. I can inspect the limit and identify the repository, the selected work and the batch members it covers.
3. The limit remains effective through process, chat, account and PDD restarts or updates. If its applicable state cannot be read or trusted, PDD stops and tells me how to inspect or recover it.
4. For limited work, PDD can proceed through the prompt PR but stops before allocating a code area, branch or chat, building or publishing code, merging or deploying.
5. Repeated starts, ticks, opens, approvals and resumes, including reuse of a current saved run, do not bypass the limit or assign the same issue twice.
6. A routine gate approval, checker pass or release detection does not grant code permission or widen the limit, whether the repository is new or already released.
7. I can explicitly permit code for selected limited work later, and PDD records the actual permission and its scope. A question, a change request or earlier unrelated approval is not permission.
8. I can explicitly revoke or extend a limit. Revoking a limit alone does not silently permit code, and an unauthorized request changes neither the limit nor code permission.
9. Work with no applicable limit retains its existing authorized flow.

## Rules to check

- A batch has a fixed, explicit set of distinct issue members; members cannot be added later. Run selections also contain distinct stable run IDs. Reject duplicates and attempts to overwrite an existing selection.
- All applicable batch and run limits apply together; the most restrictive one wins. Genuinely absent applicable scope preserves the existing authorized flow, while unavailable, malformed or inconsistent applicable state stops work for inspection or recovery.
- Revocation keeps a prompt-only hold and never grants code permission. A later extension is a separate explicit permission for its selected work. Strict policy requires a person at the terminal; easy policy also permits the established said route. Record the actual actor, time, route and exact supplied words, with null words for terminal permission.
- Refuse a change affecting already-running code without changing state or terminating that code. The limit is durable within the local repository and its common Git identity; it promises no transfer between machines.
