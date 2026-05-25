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

For a simple prompt with no expansion tags, `expanded_sha256` equals the prompt
hash. Plain local file includes are expanded deterministically for hashing. If
a prompt uses shell, web, variable, query-based, or otherwise effectful
expansion, the command boundary cannot reproduce the exact expanded input
without repeating effects; `expanded_sha256` is therefore `null` rather than a
guessed value. Dynamic provenance can be filled in when generation exposes its
original context snapshot.

Missing stories or contracts are reported as `not_applicable`; they do not make
an otherwise successful command fail. The schema is packaged at
`pdd/schemas/evidence_manifest.schema.json`.
