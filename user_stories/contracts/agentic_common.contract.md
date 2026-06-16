<!-- pdd-story-contract derived-from-story="../story__agentic_common.md" story-hash="3dc4ffef663c330e" issue-ref="https://github.com/promptdriven/pdd/issues/1589" -->

# Contract: Agentic CLI routing: harness selection and feasibility

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__agentic_common.md`), not this contract.

## Covers
- AC1: Inventory available `pdd/agentic_*` harnesses and their routing-relevant capabilities.
- AC2: Define a stable `harness_id` for benchmark and policy rows.
- AC3: Record feasibility constraints per harness: installed CLI, auth, sandbox support, available flags, rate limits, and hidden-verifier compatibility.
- AC4: Define coarse task classes where harness choice is expected to matter, especially multi-file fixes and repo-scale changes.
- AC5: Keep current orchestrator defaults as fallback when no route applies.

## Context
The system has multiple external AI tool harnesses (e.g., for Claude, Gemini/Antigravity, Codex, OpenCode) available via `pdd/agentic_*` modules. A developer submits a complex task (e.g., a multi-file fix or large-scale change) via the agentic CLI. The system must decide which external harness is most suitable to execute the task.

## Acceptance Criteria
1. Given a complex task submitted via the agentic CLI, when the system evaluates routing, then it considers the available `pdd/agentic_*` harnesses and their documented capabilities.
2. Given the evaluation in (1), when a harness is selected, then a stable identifier (`harness_id`) is associated with the task for benchmarking and policy tracking.
3. Given the evaluation in (1), when checking a harness's feasibility, then the system accounts for constraints like CLI installation, authentication, sandbox support, available flags, rate limits, and hidden-verifier compatibility.
4. Given a task class like "multi-file fix" or "repo-scale change", when routing, then the harness selection logic prioritizes harnesses expected to perform better for that class.
5. Given a task where no specific route applies, when routing, then the system falls back to the current default orchestrator.

## Oracle
These details matter for pass/fail:
- The routing logic accesses an inventory of harness capabilities.
- A `harness_id` is produced for the selected route.
- Feasibility checks for a harness include at least one of: CLI installation status, authentication, sandbox support, available flags, rate limits, or hidden-verifier compatibility.
- The task class (e.g., multi-file, repo-scale) influences the harness selection priority.
- A fallback to a default orchestrator occurs when no specific route is applicable.

## Non-Oracle
These details should not matter:
- The specific internal naming or file structure of the `pdd/agentic_*` modules.
- The exact wording of capability descriptions.
- The specific values of `harness_id` strings.
- The order in which feasibility constraints are checked.
- The specific algorithm or weights used for prioritization.

## Negative Cases
- A task is routed without any consideration of harness capabilities or feasibility constraints.
- A `harness_id` is not generated or is inconsistent for the same harness across runs.
- A harness is selected for a task class it is documented as being unsuitable for (e.g., a single-file harness for a repo-scale change).
- The system fails to provide a fallback route when no specific harness is suitable.

## Non-Goals
- Direct routing for `llm_invoke` calls (see related issue #1584).
- Learned or adaptive harness selection based on runtime performance.

## Candidate Prompts
- `agentic_common_python.prompt` — Provides shared agentic CLI execution across multiple harnesses, making routing decisions. (primary)
- `agentic_architecture_orchestrator_python.prompt` — Orchestrates multi-step workflows and likely involves harness selection. (related)
- `agentic_bug_orchestrator_python.prompt` — Orchestrates a bug workflow that may require harness selection for execution. (possible)
- `agentic_change_orchestrator_python.prompt` — Orchestrates a change workflow for implementing GitHub issues, a potential complex task. (possible)
- `agentic_e2e_fix_orchestrator_python.prompt` — Orchestrates an E2E fix workflow, a candidate for multi-file/repo-scale routing. (possible)

## Notes
- The story is about the *routing* and *selection* dimension, not the execution details of any single harness.
- "Complex tasks" from the Story map to "coarse task classes" like multi-file fixes and repo-scale changes from the issue.
- The fallback behavior ensures backward compatibility and graceful degradation.
- Harness feasibility is a prerequisite for selection; a harness that fails feasibility checks should not be chosen.
