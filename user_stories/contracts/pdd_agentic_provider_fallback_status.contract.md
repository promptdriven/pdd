<!-- pdd-story-contract derived-from-story="../story__pdd_agentic_provider_fallback_status.md" story-hash="07b2566fa58f9bfc" issue-ref="https://github.com/promptdriven/pdd/issues/1698" -->

# Contract: Provider fallback keeps workflow status honest

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_agentic_provider_fallback_status.md`), not this contract.

## Covers

- R1: Agentic runs record which provider or CLI was attempted.
- R2: Recoverable provider failures can fall back to an available provider without losing step context.
- R3: Degraded-but-continuing steps are reported differently from terminal workflow failures.
- R4: Provider failure details are summarized without leaking secrets.
- R5: Routing policy remains explicit about which agentic surface owns the task.

## Context

Provider selection and fallback are shared infrastructure for agentic workflows.
The user-visible status should be as testable as a unit assertion: degraded
continuation, provider fallback, and terminal failure are distinct outcomes.

## Acceptance Criteria

1. Given the preferred provider fails recoverably, when a fallback provider is available, then the workflow records the fallback and continues.
2. Given a step continues after fallback, when a GitHub or console status is posted, then the status is degraded rather than failed.
3. Given all providers fail or a nonrecoverable error occurs, when status is posted, then the workflow is marked failed and aborting.
4. Given provider diagnostics include environment or credential details, when status is rendered, then secrets are not exposed.
5. Given routing policy selects an agentic workflow, when providers are invoked, then provider fallback does not change the selected task owner.

## Oracle

These details matter for pass/fail:
- provider attempts and fallback are visible
- degraded status means continuing
- failed status means aborting
- secrets are redacted from provider diagnostics
- routing ownership remains stable across fallback

## Non-Oracle

These details should not matter:
- exact provider priority order when configuration changes
- exact spinner or progress formatting
- model names beyond visible provider attribution
- internal retry helper names

## Negative Cases

- A continuing fallback path must not post a terminal failure status.
- A terminal provider failure must not be reported as success.
- Provider diagnostics must not leak API keys or OAuth tokens.
- Fallback must not reroute a bug task into a feature workflow.

## Non-Goals

- This story does not require live provider credentials.
- This story does not guarantee provider availability.
- This story does not prescribe exact retry counts.

## Candidate Prompts

- `prompts/agentic_common_python.prompt` - owns shared agentic command execution and status reporting.
- `prompts/provider_manager_python.prompt` - owns provider selection and availability.
- `prompts/routing_policy_python.prompt` - owns task routing constraints.

## Notes

This story protects provider fallback as observable workflow behavior rather
than hidden infrastructure.
