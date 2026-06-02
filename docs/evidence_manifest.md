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

Missing stories or contracts are reported as `not_applicable`; they do not make
an otherwise successful command fail. The schema is packaged at
`pdd/schemas/evidence_manifest.schema.json`.

## Verification

For this feature, use the focused pytest gate (not full `pytest -q` collection
on every environment):

```bash
pytest -q tests/commands/test_evidence.py tests/test_evidence_manifest.py
```

`pdd sync --evidence` records `unit_tests`, `verify`, and `policy` as `passed` or `failed`
only when those operations appear in `sync_main` results; otherwise the receipt
uses `not_available` or `not_applicable`. `policy` status is derived from
`pdd policy check` (deterministic side-effect analysis).
