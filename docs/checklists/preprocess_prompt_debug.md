Prompt Format Failure Investigation Checklist
=============================================

Current Actions Completed
-------------------------
- Added unit tests that reproduce the missing-key failure case (`{x}`) and broaden coverage for JavaScript destructuring, JSX, and template literals so `double_curly` behavior is verified across typical patterns.
- Hardened `pdd/preprocess.py` to restore unfenced JavaScript template literals `${IDENT}` as `${{IDENT}}`, preventing LangChain’s `PromptTemplate` from interpreting `{IDENT}` as a substitution key.
- Integrated an end-to-end test (`tests/test_llm_invoke.py::test_e2e_include_preprocess_llm_no_missing_key`) that exercises `include → preprocess → llm_invoke`, confirming no missing-key errors once braces are doubled.
- Instrumented `pdd/preprocess.py` with opt-in debugging via `PDD_PREPROCESS_DEBUG` and `PDD_PREPROCESS_DEBUG_FILE`, including scans for risky single-brace placeholders and unfenced template literals.
- Fixed `tests/sync_regression.sh` to remove a macOS-incompatible bash substitution so regression runs succeed on local machines.

Likely Root Cause of the Remaining Error
---------------------------------------
- The final prompt still contains a literal `{count}` (or similar) outside fenced code blocks after preprocessing, meaning it is a genuine placeholder intended for prompt variables rather than an accidental JS literal.
- No value is being supplied for `count` via CLI flags (`-e count=…`), environment variables, or prompt front matter (`variables:` block). Consequently, `PromptTemplate` raises `Missing key 'count'` when formatting the prompt.
- The user’s environment may be including additional files (e.g., `renderer.js`, `main.js`) that developers without those files do not see, leaving placeholders in the processed prompt.

Recommended Next Steps
----------------------
1. **Capture Detailed Preprocess Output**
   - Run the failing prompt with instrumentation enabled:
     ```bash
     PDD_PREPROCESS_DEBUG=1 \
     PDD_PREPROCESS_DEBUG_FILE=/tmp/pdd_pre.log \
     pdd preprocess --output preprocessed/ automations_javascript.prompt
     ```
   - The console will now confirm whether the debug log was written successfully or show any errors
   - Review `/tmp/pdd_pre.log` (or console output) for warnings such as `line N: {count}` or `${count}` outside code fences.

   **Troubleshooting debug log issues:**
   - If `/tmp` gets cleared on reboot, use a persistent location like `~/pdd_debug.log` or `./pdd_pre.log` (current working directory)
   - Ensure the directory exists and is writable
   - Check that environment variables are exported: `export PDD_PREPROCESS_DEBUG=1 PDD_PREPROCESS_DEBUG_FILE=./pdd_pre.log`
   - The tool will now print success/failure messages so you know if the log was written

2. **Confirm Intent of the Placeholder**
   - If `{count}` is literal content, update the source prompt or included file to use `{{count}}` or wrap it in fenced code (```javascript … ```), which preprocess already escapes.
   - If it is an intentional input parameter, ensure front matter (`variables:`) or CLI flags supply a value.

3. **Supply Required Variables**
   - Example: `pdd generate automations_javascript.prompt -e count=3`
   - Or add front matter defaults:
     ```yaml
     ---
     variables:
       count: { required: true, default: 3 }
     ---
     ```

4. **Re-run the failing command** after escaping literals or providing `count`, confirming the missing-key error disappears.

5. **Optional strict mode**: If accidental single-brace placeholders are never expected, consider adding a stricter failure mode (e.g., `PDD_PREPROCESS_STRICT=1`) that raises when `_scan_risky_placeholders` finds unmatched `{…}` outside code fences.

6. **Verify coverage**
   - Run targeted tests: `pytest -q tests/test_preprocess.py::test_unfenced_template_literal_should_be_doubled_but_is_not tests/test_llm_invoke.py::test_e2e_include_preprocess_llm_no_missing_key`
   - Re-run `make sync-regression` to ensure no additional bash compatibility issues remain.

Following this checklist should identify any placeholders still lacking values and confirm whether the failure stems from missing input variables or unescaped literals. Once the responsible `{count}` is provided or escaped, `PromptTemplate` should no longer raise missing-key errors on the user’s machine.
