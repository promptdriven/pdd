# Synthetic ticket-status example

A complete, deliberately small prompt-first change: a behavior contract, observable Story, independently authored cases, JavaScript implementation and real native tests. It has no external dependencies, services or model calls.

## Use it in your existing agent conversation

Before asking an agent to draft any Story, have it read the **entire** [Prompting guide](../../docs/prompting-guide.md) in that conversation, even if the chat already exists. Ask it to summarize the relevant method and then apply it. A link or filename alone does not load the guide. You can ask the agent to read that local file; if it cannot, provide the full contents.

A useful request, after that reading:

> Follow the feature recipe for this synthetic ticket-label module. Preserve `statusLabel(status)`: known values `open`, `blocked`, `done` get their title-case labels; unknown strings and null stay Unknown; other types throw TypeError. Keep exact case and whitespace behavior. Review the prompt, Story and independent cases first, then use the ordinary Node tests to check the implementation. Show the diff and actual results; prepare a PR only if I ask.

Read the [feature recipe](../../.pdd/workflows/feature/WORKFLOW.md), or use the [bug recipe](../../.pdd/workflows/bug/WORKFLOW.md) to correct a deliberately broken implementation in a disposable copy. These are manual agent instructions, not an automated workflow engine.

## Files and their roles

| File | Role |
| --- | --- |
| [prompts/status-label.prompt.md](prompts/status-label.prompt.md) | Canonical module behavior, input domain and errors |
| [story/STATUS-LABELS.md](story/STATUS-LABELS.md) | User outcome and observable acceptance criteria |
| [vectors/status-labels.json](vectors/status-labels.json) | Literal independent inputs and expected outputs/errors, mapped to criteria |
| [src/status.mjs](src/status.mjs) | Ordinary JavaScript implementation |
| [test/status.test.mjs](test/status.test.mjs) | Native tests through the public function, plus non-JSON input cases |

The JSON format belongs only to this example and its test. It is not a PDD execution schema. Keep expected results independent: inspect them against the accepted contract before running the implementation, and never regenerate them from its outputs.

## Run the native tests

Use Node.js 22 or later. From the repository root, no install is needed:

```sh
node --test examples/ticket-status/test/status.test.mjs
```

An ordinary call, also from the repository root:

```sh
node --input-type=module -e "import { statusLabel } from './examples/ticket-status/src/status.mjs'; console.log(statusLabel('blocked'));"
```

Expected output is `Blocked`. The test command must exit zero. Review its individual cases rather than treating a process exit alone as acceptance of untested behavior.

## Prove a test can detect wrong behavior

In a **disposable copy** of this example, keep the null/type guards intact but normalize valid strings with `trim().toLowerCase()` before label selection, leaving the prompt, Story and expected cases untouched. Run that copy's native test file. The `case-sensitive` (`Open`) and `no-trimming` (` open `) cases must fail because the wrong implementation returns `Open` instead of `Unknown`; the process must exit nonzero. Discard the copy afterward. This detects a meaningful mislabeling defect without changing the accepted source or expected results.

Tests cover only their concrete inputs. They do not execute a prompt, verify every possible implementation, prove formal correctness or start a managed PDD session. Continue review and revisions in your existing coding-agent conversation using your normal project tools.
