# Prompt/code drift found while splitting `code_generator_main`

Date: 2026-08-06
Baseline: `main` @ `c443f2f91`
Related: `2026-08-06-code-generator-main-shared-layer-design.md`

## Why this file exists

`pdd/prompts/code_generator_main_python.prompt` and `pdd/code_generator_main.py`
disagree in several places. This is the predictable consequence of the module
being the only one of 114 whose `.pdd/meta` fingerprint records
`"command": "manual"` — commit `16a48378c` on `feat/language-validity-gate`
states the prompt and code "were hand-authored together… never went through
`pdd generate`", so nothing ever reconciled them.

**Decision:** the new `pdd/prompts/conformance/*.prompt` files describe **what
the code actually does**, so regeneration preserves behavior. Each divergence is
logged below so the prompt's version can be adopted deliberately later if it was
the intended contract.

Nothing here is fixed by the split. This is a record, not a change.

## D1 — `PublicSurfaceRegressionError.repair_directive`

**Prompt** (§5b, "exposes a `repair_directive: str` property of the form"):

```
Public-surface regression detected for {prompt_name}.
The following previously-exported public symbols are missing from the regenerated code:
- <symbol>
...
Restore these exact symbols (same names, compatible signatures) OR, if the change is intentional, add a scoped line such as `BREAKING-CHANGE: remove <symbol>` or `BREAKING-CHANGE: change signature <symbol>` to the prompt body.
Do not modify the prompt to delete unrelated content. Do not remove other existing valid exports.
```

**Code** (`PublicSurfaceRegressionError.repair_directive`):

```
Public surface regression repair required.
Restore these public symbols from the existing module:
- <symbol>
…
Preserve backward-compatible public helpers unless the prompt lists the intended removals with BREAKING-CHANGE: remove <symbol>.
```

The string `Public surface regression detected` appears nowhere in the module.

The code additionally carries #1900/#1968 behavior the prompt's template does not
describe: a `declared_details` branch that emits the declared `<pdd-interface>`
signature as a VERBATIM constraint, and declaration-aware advice steering the
caller to edit the declaration rather than add a `BREAKING-CHANGE` marker.

**Assessment:** the prompt's wording is arguably better — it names the
`BREAKING-CHANGE: change signature` escape hatch, which the code's version omits.
But the code's version carries the newer declared-interface logic. Adopting the
prompt's text wholesale would lose that.

**Taken:** the code's version.

## D2 — `TestChurnError.repair_directive`

**Prompt** (§5c):

```
Test churn for {prompt_name} exceeds threshold (ratio={churn_ratio:.2f}, threshold={threshold:.2f}).
Regenerate by extending the existing test file rather than rewriting it. Preserve existing test function names and coverage for unrelated behavior. Add new tests for the prompt change without deleting accumulated regression tests.
If a wholesale rewrite is intentional, add a line beginning with `BREAKING-CHANGE:` that explicitly mentions rewriting/replacing tests.
```

**Code**:

```
Test churn repair required.
- Keep the existing broad test coverage in {output_path}.
- Reduce unrelated rewrites below the configured churn threshold ({threshold:.2f}); current churn is {churn_ratio:.2f}.
- Add or update only tests needed for the prompt change.
```

**Assessment:** same shape of divergence as D1 — the prompt's version names the
`BREAKING-CHANGE:` opt-out and the code's does not. A model receiving the code's
directive is never told the escape hatch exists.

**Taken:** the code's version.

## D3 — `TestChurnError` constructor signature

`adopted_human: bool = False` (issue #1903 §B.4) exists in the code but is
**absent from both** the prompt's `<pdd-interface>` block and the
`architecture.json` entry for `code_generator_main_python.prompt`.

| Source | Has `adopted_human`? |
|---|---|
| `pdd/code_generator_main.py` | yes |
| prompt `<pdd-interface>` | no |
| `architecture.json` | no |

The message body does serialize it (`adopted: <true\|false>`), and `_verify_test_churn`
accepts and forwards a matching parameter — so the code is self-consistent; only
the two declarations are stale.

This one is a live risk rather than cosmetic: the `<pdd-interface>` signature
check compares declared against actual parameters, so a future regeneration
governed by the stale declaration could legitimately drop `adopted_human`.

**Taken:** the code's version. `conformance/errors_python.prompt` and its
`architecture.json` entry both declare `adopted_human: bool = False`.

## D4 — the `architecture_sync` self-include selector

Not a prompt/code disagreement, but the same class of staleness. On
`feat/language-validity-gate` the selector at prompt line 172 carried
`class:LanguageMismatchError` while the class did not yet exist in the source,
and preprocessing emitted:

```
<!-- Invalid selector for pdd/code_generator_main.py: Class 'LanguageMismatchError' not found in source -->
```

The selector silently degrades to a comment rather than failing, so a stale entry
is invisible. `scripts/validate_conformance_prompts.py` now checks every symbol in
the self-include selector against the module and fails loudly instead.

## Not drifted

Verified as matching between prompt and code:

- `ArchitectureConformanceError.repair_directive` — `Required missing exports:` and
  `Do not modify architecture.json. Do not remove existing valid exports.`
- `ProseOutputError.repair_directive` — the `PROSE_OUTPUT_REPAIR_DIRECTIVE` text.
- All four cross-process message prefixes, which are the parsed contract:
  `Architecture conformance error for `, `Public surface regression for `,
  `Test churn threshold exceeded for `, `Generation output extraction failure for `.
- The `ArchitectureConformanceError`, `PublicSurfaceRegressionError` and
  `ProseOutputError` constructor signatures.

## Follow-up worth considering

D1 and D2 both lose the `BREAKING-CHANGE` escape hatch in the text the model
actually receives. If the prompt's wording was the intent, adopting it is a
behavior change worth making deliberately — as its own change with its own
review, not smuggled in under a refactor.
