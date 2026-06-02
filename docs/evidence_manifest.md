# Evidence Manifests

Evidence manifests are optional JSON audit receipts for completed PDD runs. They
do not replace core dumps: core dumps diagnose exceptional failures, while an
evidence manifest records routine provenance for a successful command.

## Commands

Pass `--evidence` to supported command invocations:

```bash
pdd generate prompts/refund_python.prompt --output src/refund.py --evidence
pdd sync refund --evidence
pdd test --manual prompts/refund_python.prompt src/refund.py --evidence
pdd verify prompts/refund_python.prompt src/refund.py verify.py --evidence
pdd detect --stories --evidence
pdd change --manual change.prompt src/refund.py prompts/refund_python.prompt --evidence
```

Manifests are written under:

```text
.pdd/evidence/runs/<run_id>.json
.pdd/evidence/devunits/<basename>.latest.json
```

The versioned run path preserves audit history. The latest path provides a
stable lookup for downstream automation.

Snapshot-enabled runs also write replay artifacts:

```bash
pdd preprocess prompts/refund_python.prompt --snapshot
pdd generate prompts/refund_python.prompt --output src/refund.py --snapshot-context
pdd sync refund --snapshot-context
pdd replay .pdd/evidence/runs/<run_id>.json
```

The run manifest remains `.pdd/evidence/runs/<run_id>.json`. Replayable
expanded-prompt and dynamic-context artifacts live in the sibling directory
`.pdd/evidence/runs/<run_id>/`.

## Contents

Schema version 1 records:

- command, timestamp, PDD version, model, temperature, and reported cost
- prompt and generated-output SHA-256 hashes when their paths are available
- deterministic local include hashes found directly in the prompt
- contract coverage status when the prompt has contract rules
- available validation outcomes and references to existing logs

`expanded_sha256` is the SHA-256 of the prompt after `pdd.preprocess` with
`recursive=True` and `double_curly_brackets=False` (the same deterministic
include expansion used before generation). `context.includes` uses the shared
include grammar (`path=` attributes, self-closing tags, backtick includes, and
`include-many`) and skips include-looking text inside fenced or inline code.
If a prompt uses shell, web, variable, query-based, or otherwise effectful
expansion, `expanded_sha256` is `null` rather than a guessed value.

When snapshotting is enabled, the run manifest records the expanded prompt hash, whether nondeterministic tags were present, and the artifact paths and SHA-256 hashes for captured shell output, web content, and semantic include-query output. Static prompts with only deterministic includes record that no nondeterministic context was captured. Shell/web snapshots are redacted before hashing and storage for known authorization headers, bearer/basic tokens, URL credentials, provider keys, and secret-like assignments; metadata records whether redaction changed content. Raw environment dumps and unredacted bearer/API tokens must not be persisted.

`pdd replay` reads a run artifact and reconstructs the expanded prompt context from the recorded snapshots. A successful replay means the prompt/context hash matches the original run; it does not assert that a later LLM generation will produce identical code.

Missing stories or contracts are reported as `not_applicable`; they do not make
an otherwise successful command fail. The schema is packaged at
`pdd/schemas/evidence_manifest.schema.json`.

## Verification

For this feature, use the focused pytest gate (not full `pytest -q` collection
on every environment):

```bash
pytest -q tests/commands/test_evidence.py tests/test_evidence_manifest.py tests/test_context_snapshot_replay.py tests/test_context_snapshot_policy.py
```

`pdd sync --evidence` records `unit_tests` / `verify` as `passed` or `failed`
only when those operations appear in `sync_main` results; otherwise the receipt
uses `not_available` or `not_applicable`.
