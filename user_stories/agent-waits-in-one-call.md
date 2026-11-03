# Wait for Story results in one call

As an author using a person or agent shell, I can run a check once and receive its
final Story results without asking my agent to poll every minute.

## Acceptance criteria

1. With no timeout, `pdd test` waits until every Story ends in either kind of shell, including checks finishing after 90 seconds.
2. `pdd test --read BATCH` waits until every saved Story ends, including results after 90 seconds, using the original request IDs for accepted running checks without resubmitting them or creating replacement request IDs. A saved Check held for queued or running lint waits for lint to finish, then starts each original held check at most once.
3. Before the first check is sent, pdd saves the batch and prints its recovery command. While waiting, it prints progress on stderr every 30 seconds, keeping stdout for the final results.
4. `--timeout 1` stops either a new check or a saved read at 60 seconds with exit 3 and the recovery command, retaining running receipts and their request IDs.
5. If the shell tool stops pdd, one recovery read waits for completion without resending the checks. Final results retain one Prompt tests line per Story, the existing table, reports, coverage and failure details; JSON remains one document.
6. Check help describes the same unlimited default in every shell, the explicit timeout option and 30-second progress.

## Rules to check

- No caller deadline is inferred from whether a shell is interactive. A run still pending at 90 seconds must not return merely because it is an agent shell.
- A saved read with an accepted running receipt repeatedly reads that same ID until terminal, interrupted or explicitly timed out. Returning its first pending snapshot is forbidden.
- With an explicit 60-second budget, remote admission and receipt waiting share that budget. Waiting beyond it or silently resubmitting a running request is forbidden.
- Unlimited start/read persist `timeout_min: null`; explicit limits persist their supplied minutes. A previous invocation's limit cannot become the next read's default.
- Recovery text and saved state precede the first check POST. Progress stays on stderr at 30-second intervals; repeated progress or successful-check payloads in final stdout are forbidden.
- The 90-second POST transport timeout, Try lint policy, finite explicit-retry default and existing outcome/output contracts remain separate.

Existing guarded dispatch of lint-held checks and confirmed restart recovery retain their own authorization rules; they do not resubmit an accepted running check.
