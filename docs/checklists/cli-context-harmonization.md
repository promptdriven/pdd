# CLI Context Harmonization and Listing — Summary and Checklist

This document summarizes the end‑to‑end work completed to harmonize `.pddrc` context handling across prompts, CLI, and implementations, plus what remains to finish and harden the change.

## Summary

We aligned the CLI and internal modules around a single source of truth for listing and validating `.pddrc` contexts and ensured every CLI wrapper passes a context override consistently into `construct_paths`. We also added a regression test step to validate the global flags `--list-contexts` and `--context`, and fixed test suites to reflect the new `construct_paths` call signature.

## Changes Implemented

- CLI options and early handling
  - Added global `--context CONTEXT_NAME` and `--list-contexts` flags in `pdd/cli.py`.
  - Set `@click.group(invoke_without_command=True)` so global actions work without a subcommand.
  - Implemented early handling in `cli()`:
    - `--list-contexts` prints contexts and `ctx.exit(0)` before any auto‑update or subcommands.
    - Early validation for unknown `--context` via `click.UsageError` (prevents double reporting).
  - Persisted `ctx.obj['context']` for subcommands.

- Single source of truth for listing
  - Implemented `list_available_contexts(start_path: Optional[Path] = None) -> list[str]` in `pdd/construct_paths.py`.
  - `cli` reuses `list_available_contexts()` for both printing and early validation.

- Threaded `context_override` everywhere
  - All `*_main` wrappers now pass `context_override=ctx.obj.get('context')` to `construct_paths`:
    - `pdd/code_generator_main.py`, `pdd/cmd_test_main.py`, `pdd/fix_main.py`, `pdd/change_main.py`, `pdd/update_main.py`, `pdd/preprocess_main.py`, `pdd/split_main.py`, `pdd/bug_main.py`, `pdd/trace_main.py`, `pdd/conflicts_main.py`, `pdd/auto_deps_main.py`, `pdd/fix_verification_main.py`, `pdd/detect_change_main.py`, `pdd/crash_main.py`, `pdd/context_generator_main.py`.
  - Sync internals updated to propagate the override:
    - `pdd/sync_determine_operation.py`: added `context_override` to `sync_determine_operation`, `_perform_sync_analysis`, and `get_pdd_file_paths`; passed override to all internal `construct_paths` calls.
    - `pdd/sync_determine_operation.py`: fixed `analyze_conflict_with_llm` to accept `context_override` and pass it to `get_pdd_file_paths` (resolved NameError and ensures context-aware conflict analysis).
    - `pdd/sync_orchestration.py`: added `context_override` parameter; passed to `get_pdd_file_paths` and `sync_determine_operation`.
    - `pdd/sync_main.py`: read `ctx.obj['context']` and forwarded to `sync_orchestration` in both `--log` and normal flows.

- Prompt templates harmonized
  - `prompts/cli_python.prompt`: instructs importing and reusing `list_available_contexts()`; mandates `ctx.exit(0)` after listing; clarifies early validation to avoid double reporting.
  - `prompts/construct_paths_python.prompt`: documents `list_available_contexts()` as the single source of truth and preserves validation in `construct_paths` as a safeguard.
  - “Main” prompts updated to instruct passing `context_override=ctx.obj.get('context')` when calling `construct_paths`.
  - `prompts/sync_determine_operation_python.prompt`: notes to accept/propagate `context_override` and to pass it to internal `construct_paths` calls.

- Tests and regression updates
  - `tests/regression.sh`:
    - Added Test 0 “CLI globals”: validates `--list-contexts` and `--context` (unknown and known cases) using a local `.pddrc` with `default` and `alt` contexts.
    - Fixed env‑var precedence check for `generate` by commenting out any `generate_output_path` in the local `.pddrc` before setting `PDD_GENERATE_OUTPUT_PATH`.
  - Unit tests adjusted for the new `construct_paths` kwarg:
    - `tests/test_conflicts_main.py`: added `context_override=None` to `mock_construct_paths.assert_called_once_with(...)` expectations.
    - `tests/test_detect_change_main.py`: added `context_override=None` to the corresponding expectation.
  - Additional unit tests and updates (new):
    - CLI globals and context handling in `tests/test_cli.py`:
      - `--list-contexts` early exit without `auto_update`.
      - Known `--context` threads into subcommands; unknown context raises `UsageError` (with and without `.pddrc`).
      - Malformed `.pddrc` surfaces a helpful `UsageError` during `--list-contexts`.
    - Listing helper in `tests/test_construct_paths.py`:
      - Added tests for `list_available_contexts` (no `.pddrc`, valid `.pddrc`, malformed `.pddrc`).
    - Sync pathing in `tests/test_sync_determine_operation.py`:
      - `get_pdd_file_paths` respects `context_override` for test/example/code directories.
      - LLM conflict analysis tests fixed to reflect context-aware changes.
    - Trace and preprocess/fix wrappers:
      - Updated `tests/test_trace_main.py`, `tests/test_preprocess_main.py`, and `tests/test_fix_main.py` to include `context_override=None` in `construct_paths` expectations.
    - Sync normal flow propagation:
      - Added `tests/test_sync_main.py::test_sync_normal_flow_threads_context_override` to assert `context_override` is passed to both `construct_paths` and `sync_orchestration`.

## Validation Results

- `--list-contexts` prints contexts and exits 0 without running auto‑update or subcommands.
- Unknown `--context` fails early with a `click.UsageError` (exit code 2), as designed.
- Known `--context` (e.g., `alt`) threads through to subcommands; `preprocess` produced output under the expected configuration.
- Regression suite proceeds to later tests after Test 0.
 - Conflict analysis via LLM succeeds with valid JSON and falls back cleanly on invalid/low-confidence responses (now context-aware).
 - Unit tests for `fix_main`, `preprocess_main`, `trace_main`, `sync_determine_operation`, and `sync_main` pass with the new `context_override` threading.

## Remaining Work

- Update any remaining tests that assert `construct_paths` without `context_override`:
  - Grep for direct assertions similar to `assert_called_once_with(..., command=..., command_options=...)` and add `context_override=None`.
  - Targets likely include wrappers for: `generate`, `update`, `change`, `split`, `bug`, `auto-deps`, `verify`, `crash`, `context_generator` (several already updated: `fix`, `preprocess`, `trace`).

- Optional: make `context_override` kwarg conditional in code
  - If backward compatibility with tests is preferred, conditionally add the kwarg only when not `None`. We chose explicit passing for clarity and consistency.

- Reduce startup noise on `--list-contexts`
  - Some modules log at import time. For a quieter UX, consider lazy imports in `pdd/cli.py` or guard logs behind `quiet`.

- Documentation
  - README: add a short section on global flags `--context` and `--list-contexts` and note that `--list-contexts` exits early.
  - Developer docs: clarify the precedence order (CLI > .pddrc > env > defaults), and codify the requirement to pass `context_override` when calling `construct_paths`.

- Broader sync test coverage
  - We changed signatures for `sync_determine_operation`/`get_pdd_file_paths`. Ensure any direct test references are updated to include the new parameter (or updated to use kwargs where appropriate).

## Risk and Compatibility Notes

- Function signature changes in sync internals may require test updates wherever they are imported directly.
- Passing `context_override=None` changes `assert_called_once_with` expectations; tests must be updated accordingly (done for conflicts and detect_change_main; scan for others).

## Checklist

- [x] Add `--context` and `--list-contexts` CLI options.
- [x] Early handle `--list-contexts` with `ctx.exit(0)`.
- [x] Early validate unknown `--context` with `click.UsageError`.
- [x] Implement `list_available_contexts()` in `pdd/construct_paths.py`.
- [x] Reuse `list_available_contexts()` in CLI for listing and validation.
- [x] Pass `context_override=ctx.obj.get('context')` in all CLI wrappers.
- [x] Update sync internals to accept and propagate `context_override`.
- [x] Harmonize related prompt templates.
- [x] Add regression test step for `--list-contexts` and `--context`.
- [x] Fix env var precedence step in regression by updating the local `.pddrc`.
- [x] Update `tests/test_conflicts_main.py` expectations.
- [x] Update `tests/test_detect_change_main.py` expectation.
- [x] Update tests for `fix_main`, `preprocess_main`, `trace_main`, `sync_determine_operation`, and `sync_main` to include or respect `context_override`.
- [ ] Update any remaining tests asserting `construct_paths` calls to include `context_override=None`.
- [ ] Optional: make logging quieter for `--list-contexts` by deferring imports.
- [ ] Optional: add README and developer doc notes for the new flags and requirements.
