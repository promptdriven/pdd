<!-- pdd-story-prompts: agentic_checkup_orchestrator_python.prompt -->

# User Story: feat(checkup): persist per-step telemetry (status + cost + model + stable id) in workflow state for pdd_cloud durable runs

## Story
As a platform operator running automated checkup workflows, I can see how much each step of a checkup cost, which model it used, and whether it succeeded or was skipped, so that I can track spending per phase and resume long-running checks without losing visibility into what already happened.
