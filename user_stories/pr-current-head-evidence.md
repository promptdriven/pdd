# Read test evidence for the current PR head

I can read a PR and tell what was checked for its current contents, and see when a criterion was checked by exit code only.

## Acceptance criteria

1. After checked files change or disappear, or their current source cannot be verified, the PR shows no current successful check or count for that saved result.
2. Unchanged checked content can retain its current result across commits; newer compatible evidence updates the same Story without restoring an older overall total.
3. Agent prose, including "Full npm test: 665/665 passed", ordinary proof, warnings and failures, stays under "Agent note — not checked by pdd"; only structured current-head CI or the old-code proof run supplies checked native-suite counts, otherwise they are unknown.
4. A missing machine proof remains "not run" and an unreadable proof remains "unavailable"; neither prevents publication.
5. A criterion with one or more checks, all checking exit code across every step, says "checked by exit code only", regardless of its wording or result; checks assigned to other criteria do not affect this fact.
6. A criterion with mixed checks or zero checks has no exit-code-only annotation; unavailable authored checks remain unknown. No new warning, refusal or verdict change is added.

## What must not change

Missing or unsuccessful proof stays publishable. Source freshness does not run tests, spend model calls or approve prompts. Keep safe formatting, report links, body budgets, PR stacking and approval gates. Before changed source is pushed, an existing PR must lose its old current-success claims; a failed final description update leaves honest pending evidence.

## Rules to check

A current successful check requires compatible current selected content; changed, deleted, unavailable or unbound source must never count as a current pass. Only current-head CI or a current machine proof's actual new-code output can supply test counts. Never infer pass, tests or counts from agent words. Exit-code-only requires at least one assigned check and every assigned check across all steps to check result exit_code or exitCode; never infer output intent from criterion words.

## Coverage boundary

The runtime cases exercise the existing source-aware Story count helper, evidence preparation through fixed outside replies, and the existing JSON renderer with authored check facts. They do not publish or refresh a PR. Native code verification must replay these cases and also prove removal of stale claims from headers, step summaries, Verify and PR contents descriptions; pending edits before push; final-edit failures; exact-head CI/proof count provenance; and text/JSON saved-read coverage propagation. The runtime renderer cases do not prove those text or read effects. No runtime pass by itself proves those effects.

```pdd-boundary
prompts/cli/workflow-runner.prompt.md
prompts/cli/workflow-pr-evidence.prompt.md
prompts/cli/runtime-output.prompt.md
```
