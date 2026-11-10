# Approval policy and durable prompt evidence ports

I can read repository approval policy, resolve `--said` words from arguments or stdin, identify the invoking actor, and read and record durable prompt approvals under lock custody and commit guards.

```pdd-boundary
prompts/cli/approval-policy.prompt.md
```

## Acceptance criteria

1. `readApprovalPolicy` reads `pdd.json` in `root`, returning `{strictApprovals: true}` when `strict_approvals` is `true`, `{strictApprovals: false}` when the file or key is absent, and raising `invalid-approval-policy` when `pdd.json` is malformed or has a non-boolean `strict_approvals`.
2. `readSaidWords` reads once from `stdin.read` when `said` is `-`, preserves verbatim text including newlines and quotes, and raises `invalid-said-words` when the payload is blank-only.
3. `approvalActor` receives the environment object directly, prefers `CODEX_THREAD_ID` over `CLAUDECODE` and `PDD_AGENT_SESSION`, falls back to terminal `USER` or `LOGNAME`, and preserves selected values including NUL.
4. `readPromptApprovals` returns retained journal records from `pdd/approvals.json` under `commonDir` and raises `invalid-approval-journal` when the existing file is malformed.
5. `recordPromptApproval` acquires lock custody, invokes `guards.afterApprovalLock` and `guards.beforeApprovalCommit`, uses the caller-supplied event ID for a new record, writes the updated `{v: 1, approvals}` journal, returns undefined, releases the lock, and propagates a guard rejection without writing.
