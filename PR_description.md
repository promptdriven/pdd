# Feat: Enhance test file handling in `pdd bug`, `pdd test`, and `pdd fix`

## Summary

This pull request introduces two key enhancements to improve the handling of test files in the PDD CLI:

1.  **Numbered File Creation:** The `pdd bug` and `pdd test` commands now automatically create new test files with a numbered suffix (e.g., `test_code_1.py`, `test_code_2.py`) if a file with the same name already exists. This prevents accidental overwrites and preserves existing test files.

2.  **Multiple Test File Support:** The `pdd fix` and `pdd test` commands have been updated to accept multiple unit test files. For both commands, the content of all provided test files is concatenated and passed to the AI model as a single context. For `pdd fix --loop`, this ensures the LLM has the full test suite for iterative fixing, while the actual execution of tests is handled by the `--verification-program` you provide.

## Motivation

The motivation for these changes is to provide a more flexible and robust testing workflow. The numbered file creation prevents data loss and allows for the generation of multiple test variations. The ability to use multiple test files in the `fix` and `test` commands enables more thorough and accurate bug fixing and test generation, especially in complex scenarios where tests are split across multiple files.

## Testing

The following steps were taken to test the changes:
*   Unit tests were added to `tests/test_cli.py` and `tests/test_fix_main.py` to verify that the `fix` and `test` commands correctly handle multiple test files.
*   The `README.md` has been updated to reflect the new functionality.
*   All existing tests were run to ensure that the changes did not introduce any regressions.
