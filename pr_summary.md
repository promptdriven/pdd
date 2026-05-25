# PR #1108 — Clarify `pdd sync` no-op output and clean up Model labeling

Closes #1103.

## Scope

This PR is scoped to the user-visible output of `pdd sync` and related commands. It does **not** introduce the selective-include / `<include select=...>` / `pdd extracts prune` features (those are tracked separately).

## Issue #1103: improved sync output and Model labeling

### Runtime changes

- `pdd/sync_orchestration.py` — Adds a truthful `summary` field via the new `_compose_sync_summary` helper so a successful no-op no longer produces a `None` Details cell. The composed summary is scoped to the selected target/language and surfaces accepted-as-complete reasons when applicable.
- `pdd/sync_main.py` — Final summary table now picks `summary` first and guards against `None` / "No details." / empty strings, falling back to a status-scoped phrase so a row never carries a placeholder.
- `pdd/sync_main.py` (one-session path) — When the pre-generate phase ran inside one-session mode, `generate` is surfaced in `operations_completed` and the success `summary`, so the Details column does not under-report completed work.
- `pdd/one_session_sync.py` — Always sets a non-empty `summary` on both success and failure so downstream rendering never collapses to a placeholder.
- `pdd/commands/checkup.py`, `pdd/commands/maintenance.py`, `pdd/commands/modify.py`, `pdd/core/utils.py` — All five `Model: {model}` echo sites now go through the shared `echo_model_line(model)` helper, which suppresses the line when the model is empty, `"unknown"`, or `"N/A"` (case-insensitive).

### Prompt changes (kept in sync with the runtime above)

- `pdd/prompts/sync_orchestration_python.prompt`, `pdd/prompts/one_session_sync_python.prompt`, `pdd/prompts/sync_main_python.prompt` — Standardized no-op success and failure summary contracts; documented the `summary` field and the placeholder-rejection rule.
- `pdd/prompts/commands/checkup_python.prompt`, `pdd/prompts/commands/maintenance_python.prompt`, `pdd/prompts/commands/modify_python.prompt` — Standardized Model-suppression contract (kept in sync with the `echo_model_line` runtime helper added in this PR). Prompt-only suppression edits previously made to `bug_main`, `code_generator_main`, and `update_main` were reverted because this PR does not modify those modules' runtime — declaring a contract the runtime does not honor would let the next `pdd sync` rewrite stable, out-of-scope command behavior.
- Several prompts that previously carried `<pdd-interface>` blocks declaring signatures that did not match the runtime have been corrected so conformance repair does not try to reshape stable signatures.

### Tests

- `tests/test_sync_main.py` — New regression `test_sync_no_op_success_details_never_renders_none` covering the historical no-op shape (`summary` absent, `error: None`) and asserting the final table never contains the literal `"None"`. Additional `TestSyncMainEarlyOutSummaryKeys` cases cover the one-session early-out summary contract.
- `tests/test_one_session_sync.py`, `tests/test_sync_orchestration.py` — Updated to cover the new `summary` contract and the `_compose_sync_summary` outputs.
- `tests/core/test_cli.py` — Coverage for the shared `echo_model_line` helper (suppression cases for empty / `unknown` / `N/A`).

### Architecture metadata

- `architecture.json` — Updated to reflect the prompt-side dependency edges that were tightened in this PR, including restoring `preprocess_python.prompt` as a dependency of `include_query_extractor_python.prompt` (matches both the prompt body and the runtime imports).

## Out of scope

Anything outside the `pdd sync` no-op / Model-labeling surface (e.g., selective-include syntax, `pdd extracts prune`, `auto-deps` selector emission, README / `docs/prompting_guide.md` rewrites) is intentionally **not** part of this PR.
