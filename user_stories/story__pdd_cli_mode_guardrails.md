<!-- pdd-story-prompts: prompts/core/cli_python.prompt, prompts/commands/generate_python.prompt, prompts/commands/modify_python.prompt, prompts/commands/maintenance_python.prompt -->
<!-- pdd-story-dev-units: cli_python.prompt, generate_python.prompt, modify_python.prompt, maintenance_python.prompt -->

# User Story: CLI mode guardrails reject ambiguous requests

## Story

As a developer running PDD commands, I want invalid option combinations to fail before any workflow starts, so that a typo cannot trigger the wrong generation, sync, change, or update path.
