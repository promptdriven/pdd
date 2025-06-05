# Pylint Progress Checklist

This document tracks the progress of applying `pylint` fixes to the codebase.

## Process

The following steps are used to systematically improve code quality:

1.  **Select Module and Test File**: Choose a Python file from the "To Do" list (e.g., `pdd/some_module.py`) and its corresponding test file (e.g., `tests/test_some_module.py`).
2.  **Run Pylint on Both**: Execute `pylint` on both the module and its test file to identify linting errors.
    ```bash
    conda run -n pdd pylint path/to/module.py path/to/test_file.py
    ```
3.  **Fix Errors**: Address the issues reported by `pylint` in both files.
4.  **Verify Fixes**: Run `pylint` again on both files to ensure the score has improved and major issues are resolved.
5.  **Run Unit Tests**: Execute `pytest` on the test file to confirm that the changes have not introduced any regressions.
    ```bash
    conda run -n pdd pytest path/to/test_file.py
    ```
6.  **Update Checklist**: Once both the module and its test file are linted and tested, mark them as complete in this document.

## Completed

- [x] `pdd/get_extension.py`
- [x] `tests/test_get_extension.py`
- [x] `pdd/auto_deps_main.py`
- [x] `tests/test_auto_deps_main.py`
- [x] `pdd/__init__.py` (Note: `C0305: Trailing newlines` persists)
- [x] `tests/__init__.py`
- [x] `pdd/auto_include.py` (Note: `C0304: Final newline missing`, `W0703: Catching too general exception Exception`, `R0913: Too many arguments`, `R0914: Too many local variables` persist)
- [x] `tests/test_auto_include.py` (Note: `C0304: Final newline missing` persists)
- [x] `pdd/auto_update.py` (Note: `C0303: Trailing whitespace`, `C0304: Final newline missing`, `E0401: Unable to import 'semver'` persist)
- [x] `tests/test_auto_update.py` (Note: `C0303: Trailing whitespace`, `C0304: Final newline missing` persist)

## To Do

### pdd/
- [ ] `pdd/bug_main.py`
- [ ] `pdd/bug_to_unit_test.py`
- [ ] `pdd/change.py`
- [ ] `pdd/change_main.py`
- [ ] `pdd/cli.py`
- [ ] `pdd/cmd_test_main.py`
- [ ] `pdd/code_generator.py`
- [ ] `pdd/code_generator_main.py`
- [ ] `pdd/comment_line.py`
- [ ] `pdd/conflicts_in_prompts.py`
- [ ] `pdd/conflicts_main.py`
- [ ] `pdd/construct_paths.py`
- [ ] `pdd/context_generator.py`
- [ ] `pdd/context_generator_main.py`
- [ ] `pdd/continue_generation.py`
- [ ] `pdd/crash_main.py`
- [ ] `pdd/detect_change.py`
- [ ] `pdd/detect_change_main.py`
- [ ] `pdd/edit_file.py`
- [ ] `pdd/find_section.py`
- [ ] `pdd/fix_code_loop.py`
- [ ] `pdd/fix_code_module_errors.py`
- [ ] `pdd/fix_error_loop.py`
- [ ] `pdd/fix_errors_from_unit_tests.py`
- [ ] `pdd/fix_main.py`
- [ ] `pdd/fix_verification_errors.py`
- [ ] `pdd/fix_verification_errors_loop.py`
- [ ] `pdd/fix_verification_main.py`
- [ ] `pdd/generate_output_paths.py`
- [ ] `pdd/generate_test.py`
- [ ] `pdd/get_comment.py`
- [ ] `pdd/get_jwt_token.py`
- [ ] `pdd/get_language.py`
- [ ] `pdd/git_update.py`
- [ ] `pdd/increase_tests.py`
- [ ] `pdd/incremental_code_generator.py`
- [ ] `pdd/insert_includes.py`
- [ ] `pdd/install_completion.py`
- [ ] `pdd/llm_invoke.py`
- [ ] `pdd/load_prompt_template.py`
- [ ] `pdd/postprocess.py`
- [ ] `pdd/postprocess_0.py`
- [ ] `pdd/preprocess.py`
- [ ] `pdd/preprocess_main.py`
- [ ] `pdd/process_csv_change.py`
- [ ] `pdd/pytest_output.py`
- [ ] `pdd/split.py`
- [ ] `pdd/split_main.py`
- [ ] `pdd/summarize_directory.py`
- [ ] `pdd/trace.py`
- [ ] `pdd/trace_main.py`
- [ ] `pdd/track_cost.py`
- [ ] `pdd/unfinished_prompt.py`
- [ ] `pdd/update_main.py`
- [ ] `pdd/update_model_costs.py`
- [ ] `pdd/update_prompt.py`
- [ ] `pdd/xml_tagger.py`

### tests/
- [ ] `tests/isolated_verify.py`
- [ ] `tests/prompt_tester.py`
- [ ] `tests/test_bug_main.py`
- [ ] `tests/test_bug_to_unit_test.py`
- [ ] `tests/test_change.py`
- [ ] `tests/test_change_main.py`
- [ ] `tests/test_cli.py`
- [ ] `tests/test_cmd_test_main.py`
- [ ] `tests/test_code_generator.py`
- [ ] `tests/test_code_generator_main.py`
- [ ] `tests/test_comment_line.py`
- [ ] `tests/test_conflicts_in_prompts.py`
- [ ] `tests/test_conflicts_main.py`
- [ ] `tests/test_construct_paths.py`
- [ ] `tests/test_context_generator.py`
- [ ] `tests/test_context_generator_main.py`
- [ ] `tests/test_continue_generation.py`
- [ ] `tests/test_crash_main.py`
- [ ] `tests/test_detect_change.py`
- [ ] `tests/test_detect_change_main.py`
- [ ] `tests/test_find_section.py`
- [ ] `tests/test_fix_code_loop.py`
- [ ] `tests/test_fix_code_module_errors.py`
- [ ] `tests/test_fix_error_loop.py`
- [ ] `tests/test_fix_errors_from_unit_tests.py`
- [ ] `tests/test_fix_main.py`
- [ ] `tests/test_fix_verification_errors.py`
- [ ] `tests/test_fix_verification_errors_loop.py`
- [ ] `tests/test_fix_verification_main.py`
- [ ] `tests/test_generate_output_paths.py`
- [ ] `tests/test_generate_test.py`
- [ ] `tests/test_get_comment.py`
- [ ] `tests/test_get_jwt_token.py`
- [ ] `tests/test_get_language.py`
- [ ] `tests/test_git_update.py`
- [ ] `tests/test_increase_tests.py`
- [ ] `tests/test_incremental_code_generator.py`
- [ ] `tests/test_insert_includes.py`
- [ ] `tests/test_install_completion.py`
- [ ] `tests/test_llm_invoke.py`
- [ ] `tests/test_load_prompt_template.py`
- [ ] `tests/test_postprocess.py`
- [ ] `tests/test_postprocess_0.py`
- [ ] `tests/test_preprocess.py`
- [ ] `tests/test_preprocess_main.py`
- [ ] `tests/test_process_csv_change.py`
- [ ] `tests/test_pytest_output.py`
- [ ] `tests/test_split.py`
- [ ] `tests/test_split_main.py`
- [ ] `tests/test_summarize_directory.py`
- [ ] `tests/test_trace.py`
- [ ] `tests/test_trace_main.py`
- [ ] `tests/test_track_cost.py`
- [ ] `tests/test_unfinished_prompt.py`
- [ ] `tests/test_update_main.py`
- [ ] `tests/test_update_model_costs.py`
- [ ] `tests/test_update_prompt.py`
- [ ] `tests/test_xml_tagger.py` 