<!-- pdd-story-prompts: prompts/ci_validation_python.prompt, prompts/agentic_e2e_fix_orchestrator_python.prompt, prompts/agentic_e2e_fix_step10_ci_validation_LLM.prompt, prompts/agentic_e2e_fix_step11_code_cleanup_LLM.prompt, prompts/commands/fix_python.prompt -->
<!-- pdd-story-dev-units: ci_validation_python.prompt, agentic_e2e_fix_orchestrator_python.prompt, agentic_e2e_fix_step10_ci_validation_LLM.prompt, agentic_e2e_fix_step11_code_cleanup_LLM.prompt, fix_python.prompt -->

# User Story: CI failures keep the fix loop honest

## Story

As a maintainer relying on external CI, I want PDD fix workflows to treat post-push check failures as repair constraints or explicit blockers, so that a locally passing fix is not presented as complete when CI disagrees.
