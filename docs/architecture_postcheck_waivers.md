# Architecture Postcheck Waivers

This file records architecture filepath warnings that are known outside the
scope of issue #33. They should not block the snapshot/replay prompt and
documentation change, but they remain visible for a future cleanup pass.

## Pre-existing Missing Filepaths

- `extensions/recruiting/resurface_check.py`
- `prompts/agentic_bug_step4_reproduce_LLM.prompt`
- `prompts/agentic_bug_step10_pr_LLM.prompt`
- `prompts/extract_auto_include_LLM.prompt`
- `pdd_theme.json`
- `regression_analysis.log`
- `regression.sh`
- `pdd/run_generated.py`
- `pdd/prompt_tester.py`
- `prompts/agentic_bug_step5_5_prompt_classification_LLM.prompt`
- `prompts/agentic_bug_step9_e2e_test_LLM.prompt`

These entries were present in Step 10 postcheck output before the current
snapshot/replay additions. Issue #33 only changes prompt-context snapshot and
replay contracts; resolving unrelated legacy architecture targets would require
separate ownership decisions.
