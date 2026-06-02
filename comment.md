## Step 11: Issue Identification (Iteration 5/5)

**Status:** Issues Found

### Issues to Fix

1. **[FILE]** `pdd/prompts/evidence_manifest_python.prompt`
   - **Type:** Prompt Syntax Issues
   - **Issue:** Missing standard `% Goal` and `% Role & Scope` sections.
   - **Fix:** Add `% Goal` and `% Role & Scope` sections to explicitly define the prompt's purpose and persona.

2. **[FILE]** `pdd/prompts/commands/checkup_python.prompt`
   - **Type:** Prompt Syntax Issues
   - **Issue:** Missing standard `% Goal`, `% Role & Scope`, and `% Deliverables` sections.
   - **Fix:** Add the missing required sections to comply with PDD prompt structure conventions.

3. **[FILE]** `pdd/prompts/checkup_gates_python.prompt`
   - **Type:** Prompt Syntax Issues
   - **Issue:** Missing the standard `% Role & Scope` section. Additionally, the requirements are presented under custom headers (`% Public API`, `% Conservative v1 discovery set`, etc.) rather than a standard `% Requirements` section.
   - **Fix:** Add `% Role & Scope` and rename/restructure the custom headers so they fall under a standard `% Requirements` block.

4. **[FILE]** `pdd/prompts/commands/__init___python.prompt`
   - **Type:** Prompt Syntax Issues
   - **Issue:** The `% Goal` section header is missing (the instruction exists but not under a dedicated header).
   - **Fix:** Format the goal instruction under a proper `% Goal` header.

5. **[FILE]** `README.md`
   - **Type:** Documentation
   - **Issue:** The new `pdd policy check` command is referenced at the top of the README, but it is missing from the detailed `## Commands` list section.
   - **Fix:** Add a section documenting the `policy check` command (e.g., `### 23. policy check`) in the Commands section.

6. **[FILE]** `architecture.json`
   - **Type:** Logic / Convention
   - **Issue:** `ORCHESTRATOR_POSTCHECK_WARNINGS` reported several non-existent filepaths on disk for entries like `resurface_check_Python.prompt`, `agentic_bug_step4_reproduce_LLM.prompt`, `run_generated_python.prompt`, etc. It also flagged unparsable signatures for `getPromptTemplate`, `Job`, and `write_evidence_manifest`.
   - **Fix:** Remove obsolete entries from `architecture.json` for files that no longer exist, correct mismatched filepaths, or explicitly justify them as already-consistent. Also, fix the unparsable signatures in `architecture.json` or their corresponding prompt `<pdd-interface>` tags.

### Summary
Found 6 issues requiring fixes.

---
*Proceeding to Step 12: Fix Issues*