# Keep my local lint result

As a person who runs local lint during a run, I want the run to show that result, so that I can see what was checked and what remains unproved.

## Acceptance criteria

1. After `pdd lint --local` completes in a repository with valid Runtime interfaces and no warnings, the run shows its saved lint result as partial and local-only, with 0 warnings, 0 AI calls and no checks sent, instead of "no pdd lint result".
2. With a selected Story or no Story selector, saved evidence and JSON retain the actual inspected scope; text and JSON retain warnings, interface findings and the existing lint exit. Saving local evidence and reading it with `pdd test --read BATCH` need no sign-in, network or model calls.
3. A local result remains partial and local-only when it has no test rows. It never appears as a full pass or satisfies a full lint/check gate, pass cache or recent passing lint receipt.
4. The run reads only eligible results at or after its start and keeps the newest lint result, including a newer local partial result after an older hosted pass. Reading changes no files and starts no work.
5. If the state folder is inside the repository, or the local result cannot be saved, local lint exits 2 with a clear state error, does not claim a saved result and leaves previous results intact.

## Rules to check

Local evidence records completed local inspection, not prompt behavior. Zero rows must not become "0 of 0 tests pass". Exit 0 for completed advisory lint must not become evidence of a full pass. A newer local result must not reveal an older hosted pass in its place. Existing source/root/time admission, named/default selection, warnings and refusals stay in force. Native Story assessment keeps its separate route.

Criterion 2 preserves the existing immediate text output; scope is recorded in saved evidence and JSON, and the workflow result line can show it. The new local batch is readable offline in text and JSON even with empty rows. Its saved read preserves the original local exit; retry reads the same evidence and starts no work. This is limited to the new local-layout record and does not change legacy native-only reads.

A prepared newer local batch whose summary save did not complete stays visibly incomplete and unusable; it cannot reveal an older hosted pass as the latest result. Criterion 5 proposes the new persistence-failure policy for person review. The existing external-state boundary is retained. This Story does not broaden local preflight or interface admission (#3235).

## Cases and Runtime boundary

[Native draft cases](../test/runtime/local-lint-result-cases.json) contain the issue-derived expectations and preservation controls. They are a review inventory, not executable Runtime scenarios or completed native tests.

The owners are [Runtime client](../prompts/cli/runtime-client.prompt.md#named-check-results) and [workflow results](../prompts/cli/workflow-results.prompt.md#named-result-evidence). Runtime check: BLOCKED (#2548). The real public command boundary has no Runtime interface; the reader's partial interface exposes only native evidence assessment. Git lookup, source discovery and private state reads/writes are native and unbound. Existing injected transport, authentication and clock ports cannot bind those effects. No check-only API or unrelated assessment check can prove persistence and consumption.

Native replay must call the real command boundary, then its offline CLI saved read and the production workflow saved-result reader, formatter and eligibility function against actual temporary state. Fake saved results alone cannot prove the repair. No interpreter check, report, prompt-versus-code verdict or native replay pass is claimed.
