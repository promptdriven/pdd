# Export formal test cases and ITF traces to Short JSON companion vectors

As a developer maintaining formal boundary tests or Quint ITF traces, I want `pdd vector export` to emit `pdd lint`-clean Short JSON companion vectors, so that counterexamples and boundary cells replay directly through `pdd test` and native suites.

## Acceptance criteria

1. Running `pdd vector export` on a `pdd.formal-vectors.v1` input with 2 boundary cases (one normal case with `shares: 10, strike_cents: 4200` and one error case `pool_exhausted`) prints a valid Short JSON scenario preserving both cases and checks, writes zero files without `--write`, and exits with code 0.
2. Running `pdd vector export` on a Quint ITF trace (`#meta` and `states`) with `--entry prompts/ledger.prompt.md` and `--op withdraw` unwraps `#bigint` values, sets `initial_world` from state 0, and emits exact checks for each transition step with exit code 0.
3. Running `pdd vector export` on 20 cases with default `--max-steps 15` refuses with code `max-steps-exceeded` and exit code 1, whereas adding `--split --out tests/ledger.formal.json --write` writes `tests/ledger.formal-01.json` (15 steps) and `tests/ledger.formal-02.json` (5 steps) and exits with code 0.
4. Running `pdd vector export` on a case with zero checks or a malformed JSON Pointer refuses fail-closed with exit code 1 and writes zero files.

## Rules to check

- Invocations without `--write` never create or modify files on disk. Forbidden: writing output files unless `--write` is explicitly supplied.
- Every exported Short JSON file must compile with zero refusals and stay within `max-steps`. Forbidden: writing an uncompilable or oversized scenario file.
- Integers outside IEEE-754 safe precision (`9007199254740993`) stay exact in exported JSON. Forbidden: rounding large integers to floating-point approximations.

## Verification boundary

The prompt scenario verifies pure `pdd.formal-vectors.v1` and Quint ITF conversion, splitting, exact-check validation, and fail-closed refusals over supplied documents. Native tests separately verify real `pdd vector export` subprocess execution, stdin reading, `--write` path/symlink safety, `BigInt` JSON round-trip, and `pdd lint` cleanliness on exported files.
