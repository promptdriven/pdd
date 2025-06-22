# PDD CLI `--time` Option Update Status

This document tracks which Python files in the PDD CLI have been updated to support the global `--time` option and which ones may still need review or modification.

The `--time` option is a global CLI option intended to control the reasoning allocation for LLM models. It is defined in `pdd/cli.py` and its value is passed via the `click` context object (`ctx.obj['time']`).

## Key Files and Modules:

*   **`pdd/cli.py`**:
    *   **Status**: Updated
    *   **Notes**: Defines the global `--time` option and correctly passes it into the `ctx.obj`.

*   **`pdd/llm_invoke.py`**:
    *   **Status**: Updated
    *   **Notes**: The core `llm_invoke` function accepts a `time` parameter (defaulting to 0.25) and is expected to use this to influence LLM calls.

*   **`pdd/*_main.py` (Individual Command Main Functions)**:
    *   **Status**: Needs Review (Per File)
    *   **Notes**: Each `*_main.py` file that orchestrates a command involving an LLM call should:
        1.  Retrieve the `time` value from `ctx.obj` (e.g., `time_budget = ctx.obj.get('time', DEFAULT_TIME)`).
        2.  Pass this `time_budget` to any calls to `llm_invoke.py` or to other functions/classes that will ultimately call `llm_invoke.py`.

## Files Potentially Requiring Updates:

The following is a list of `*_main.py` files and other relevant Python files that likely interact with `llm_invoke.py` and should be verified to ensure they correctly handle and propagate the `time` parameter.

*   `pdd/auto_deps_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` and passes it to `insert_includes`.
*   `pdd/bug_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` and passes it to `bug_to_unit_test`.
*   `pdd/change_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` and passes it to `process_csv_change` and `change` (imported as `change_func`).
*   `pdd/cmd_test_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` and passes it to `generate_test` and `increase_tests`.
*   `pdd/code_generator_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` and passes it to `code_generator` and `incremental_code_generator`.
*   `pdd/conflicts_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` and passes it to `conflicts_in_prompts`.
*   `pdd/context_generator_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` and passes it to `context_generator`.
*   `pdd/crash_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` and passes it to `fix_code_loop` and `fix_code_module_errors`.
*   `pdd/detect_change_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` and passes it to `detect_change`.
*   `pdd/fix_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` and passes it to `fix_error_loop` and `fix_errors_from_unit_tests`.
*   `pdd/fix_verification_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` (defaulting to 0.25) and passes it to `fix_verification_errors_loop` and `fix_verification_errors`.
*   `pdd/preprocess_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` (defaulting to 0.25) and passes it to `xml_tagger` if `--xml` is used. (`xml_tagger.py` also updated to accept and use `time`).
*   `pdd/split_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` and passes it to the `split` function.
*   `pdd/trace_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` (defaulting to 0.25) and passes it to the `trace` function. (`trace.py` also updated to accept and use `time`).
*   `pdd/update_main.py`
    *   **Status**: Updated
    *   **Notes**: Retrieves `time` from `ctx.obj` (defaulting to 0.25) and passes it to `git_update` or `update_prompt`. (`git_update.py` and `update_prompt.py` also updated to accept and use `time`).
*   `pdd/verify_main.py`
    *   **Status**: N/A
    *   **Notes**: File does not exist. Logic is assumed to be covered by `pdd/fix_verification_main.py` (which has been updated).

**Other potentially relevant files (deeper in the call stack or helpers):**

*   `pdd/code_generator.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` in signature and passes it to `llm_invoke`, `unfinished_prompt`, `continue_generation`, and `postprocess`.
*   `pdd/incremental_code_generator.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` in signature and passes it to `llm_invoke` calls.
*   `pdd/insert_includes.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` and passes to `auto_include` and `llm_invoke`.
*   `pdd/auto_include.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` and passes to `summarize_directory` and `llm_invoke`.
*   `pdd/summarize_directory.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` and passes to `llm_invoke`.
*   `pdd/bug_to_unit_test.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` and passes to `llm_invoke`, `unfinished_prompt`, `continue_generation`, and `postprocess`.
*   `pdd/unfinished_prompt.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` and passes to `llm_invoke`.
*   `pdd/continue_generation.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` and passes to `llm_invoke` and `unfinished_prompt`.
*   `pdd/postprocess.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` and passes to `llm_invoke`.
*   `pdd/change.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` (and `budget`, `quiet`) in signature and passes `time` to `llm_invoke` calls.
*   `pdd/process_csv_change.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` in signature and passes it to `change` function calls for each CSV row.
*   `pdd/generate_test.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` in signature and passes it to `llm_invoke`, `unfinished_prompt`, `continue_generation`, and `postprocess`.
*   `pdd/increase_tests.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` in signature and passes it to `llm_invoke` and `postprocess`.
*   `pdd/conflicts_in_prompts.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` in signature and passes it to `llm_invoke` calls.
*   `pdd/context_generator.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` in signature and passes it to `llm_invoke`, `unfinished_prompt`, `continue_generation`, and `postprocess`.
*   `pdd/fix_code_loop.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` in signature and passes it to `fix_code_module_errors`.
*   `pdd/fix_code_module_errors.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` in signature and passes it to `llm_invoke` calls.
*   `pdd/detect_change.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` in signature and passes it to `llm_invoke` calls.
*   `pdd/fix_errors_from_unit_tests.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` (defaulting to `DEFAULT_TIME`) in signature and passes it to `llm_invoke` calls.
*   `pdd/fix_error_loop.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` (defaulting to `DEFAULT_TIME`) in signature and passes it to `fix_errors_from_unit_tests`.
*   `pdd/fix_verification_errors.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` (defaulting to `DEFAULT_TIME`) and `strength` (defaulting to `DEFAULT_STRENGTH`) in signature and passes `time` to `llm_invoke` calls.
*   `pdd/fix_verification_errors_loop.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` (defaulting to `DEFAULT_TIME`) in signature and passes it to `fix_verification_errors` calls.
*   `pdd/trace.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` (defaulting to `DEFAULT_TIME`) and `strength` (defaulting to `DEFAULT_STRENGTH`) in signature and passes `time` to `llm_invoke` calls.
*   `pdd/update_prompt.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` (defaulting to `DEFAULT_TIME`) in signature and passes it to `llm_invoke` calls.
*   `pdd/split.py`
    *   **Status**: Updated
    *   **Notes**: Accepts `time` (defaulting to `DEFAULT_TIME`) in signature and passes it to `llm_invoke` calls.

## Action Items:

1.  **Review each `