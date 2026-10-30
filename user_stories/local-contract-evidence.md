# I see complete local contract evidence

## Acceptance criteria

1. I see multiple writers rejected even when they share one table cell, while repeated claims by one writer agree.
2. I see invalid schema members checked beside metadata, while business annotations and fake resources stay data.
3. I can check a seed against one record named or linked by its world row and see which declarations have no schema.
4. I see an advisory when declared records disagree without losing real drift or adding a refusal.
5. I can declare nested world namespaces with Key or Path and keep exact escaped names and independent ownership.
6. I get the same warnings and check facts in text and JSON with no service call or source change.
7. I can compare parsed schemas with the established schema comparison semantics without mutating their values.

## Rules to check

Writer cells use the [writer rules](../prompts/cli/contracts.prompt.md#world-keys-and-their-seed-values),
including initial-only declarations, comma qualifiers and exact-path actor deduplication.
Uncovered seed branches warn; advisory value coverage gives no inherited writer. Recognized JSON members validate independently; annotation-only payloads,
resources, simulation and seeds remain data unless a schema target is explicit.
An explicit Schema wins; otherwise exactly one canonical declared identity designated
by a schema link, exact inline-code identifier in a non-actor cell, or whole
plain Key/What it holds cell selects its schema. Ordinary prose, path components
and Writer/Readers actor labels do not designate records. Unknown or ambiguous
inference leaves a warning, never an invented mismatch. Missing-schema counts use unique declared
keys/paths, including absent and symbolic declarations. Declared same-field-set
shape disagreements warn once per pair, including small records. Warnings alone
exit 0 and never hide genuine problems. Leading slash means JSON Pointer under
either header; bare Key is top-level. Namespace coverage gives no parent writer.
Schema equality uses the existing schema differences semantics independently of
copy eligibility. All checks are read-only; no Runtime behavior is claimed.

Runtime check: Not run: native CLI/Git/filesystem and module equality cases;
no Runtime entry or live service is part of these observations.
