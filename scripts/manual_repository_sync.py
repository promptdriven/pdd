#!/usr/bin/env python3
"""Deterministic, repository-specific authoring helper for the manual sync audit.

This is deliberately separate from PDD's sync implementation.  It performs only
the two mechanical transformations reviewed in issue #2079: add missing prompt
metadata for existing local artifacts and derive architecture.json from those
prompt-owned assertions plus the explicit repository classifications.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
from typing import Any, Iterable

try:
    from .repository_sync_audit import (
        ARCHITECTURE_PATH,
        CLASSIFICATIONS_PATH,
        EXPECTED_MANAGED_PATH,
        PROMPTS_ROOT,
        ROOT,
        _direct_artifact,
        parse_prompt_metadata,
    )
except ImportError:  # Direct ``python scripts/manual_repository_sync.py`` execution.
    from repository_sync_audit import (
        ARCHITECTURE_PATH,
        CLASSIFICATIONS_PATH,
        EXPECTED_MANAGED_PATH,
        PROMPTS_ROOT,
        ROOT,
        _direct_artifact,
        parse_prompt_metadata,
    )

VERIFICATION_PROFILES_PATH = ROOT / ".pdd" / "verification-profiles.json"
VERIFICATION_PROFILE_ROTATIONS_PATH = ROOT / ".pdd" / "verification-profile-rotations.json"
REQUIREMENT_ID = re.compile(r"\bREQ-[A-Za-z0-9_.:-]+\b")


# These are deliberate architecture-facing summaries for prompts whose legacy
# opening is only a role assignment or an imperative deliverable.  Keeping the
# overrides explicit makes the judgment reviewable instead of hiding it in a
# heuristic.
REASON_OVERRIDES = {
    "pdd/prompts/agentic_bug_python.prompt": "Runs the GitHub issue-driven, eleven-step agentic bug investigation workflow.",
    "pdd/prompts/architecture_include_validation_python.prompt": "Validates architecture dependencies against prompt includes to expose graph drift.",
    "pdd/prompts/auto_deps_architecture_python.prompt": "Updates architecture dependencies after automatic prompt-include discovery.",
    "pdd/prompts/change_main_python.prompt": "Applies requested changes to prompts using their generated-code context.",
    "pdd/prompts/ci_detect_changed_modules_python.prompt": "Detects PDD modules affected by a Git diff for targeted CI verification.",
    "pdd/prompts/cli_python.prompt": "Provides the primary PDD command-line entry point and command dispatcher.",
    "pdd/prompts/codex_subscription_python.prompt": "Connects Codex subscription credentials to the shared LLM invocation path.",
    "pdd/prompts/commands/connect_python.prompt": "Launches the PDD Connect web interface from the command line.",
    "pdd/prompts/commands/firecrawl_python.prompt": "Inspects and clears the Firecrawl response cache through PDD CLI commands.",
    "pdd/prompts/commands/report_python.prompt": "Files GitHub issues from PDD core dumps through browser or API workflows.",
    "pdd/prompts/commands/which_python.prompt": "Explains resolved PDD configuration and candidate artifact search paths.",
    "pdd/prompts/conflicts_main_python.prompt": "Detects conflicting requirements across prompt files from the PDD CLI.",
    "pdd/prompts/crash_main_python.prompt": "Diagnoses a crashing program and generates a corrected implementation.",
    "pdd/prompts/durable_sync_runner_python.prompt": "Runs issue-driven sync modules in isolated worktrees with durable checkpoints.",
    "pdd/prompts/postprocess_0_python.prompt": "Extracts runnable source code from raw language-model output for downstream execution.",
    "pdd/prompts/ci_validation_python.prompt": "Polls CI runs, retrieves logs, and coordinates bounded repair iterations after a push.",
    "pdd/prompts/prompt_tester_python.prompt": "Evaluates a prompt file against generated output and reports contract failures.",
    "pdd/prompts/core/remote_session_python.prompt": "Detects remote or headless execution and decides when browser launches must be skipped.",
    "pdd/prompts/commands/checkup_simplify_python.prompt": "Exposes candidate simplify runs through the Click command group.",
    "pdd/prompts/frontend/components/ArchitectureView_typescriptreact.prompt": "Coordinates architecture loading, graph editing, prompt generation, and synchronization in the main workspace.",
    "pdd/prompts/frontend/hooks/useArchitectureHistory_typescript.prompt": "Maintains immutable architecture edits with bounded undo, redo, reset, and unsaved-change tracking.",
    "pdd/prompts/checkup_simplify_python.prompt": "Selects and applies conservative simplifications through supported engines while preserving unrelated edits and verifying accepted changes.",
    "pdd/prompts/gate_python.prompt": "Enforces deterministic evidence policy across validation, freshness, contract coverage, waivers, and cost limits before merge.",
    "pdd/prompts/story_regression_gate_python.prompt": "Rejects user stories whose linked executable regression evidence is missing or stale without running tests or requiring cloud credentials.",
    "pdd/prompts/edit_file_python.prompt": "Edits files from natural-language instructions through the agentic editing workflow.",
    "pdd/prompts/find_section_python.prompt": "Locates named sections in prompt text for deterministic prompt transformations.",
    "pdd/prompts/fix_code_module_errors_python.prompt": "Repairs code-module errors reported by static analysis and verification tools.",
    "pdd/prompts/generation_completion_python.prompt": "Detects structurally incomplete LLM generations before accepting their output.",
    "pdd/prompts/get_extension_python.prompt": "Resolves the configured source-file extension for a programming language.",
    "pdd/prompts/get_run_command_python.prompt": "Resolves configured execution commands for generated source languages.",
    "pdd/prompts/git_update_python.prompt": "Records generated-file changes in Git while preserving repository state.",
    "pdd/prompts/install_completion_python.prompt": "Installs shell completion scripts for supported PDD command-line shells.",
    "pdd/prompts/logo_animation_python.prompt": "Renders the animated PDD terminal logo used during interactive workflows.",
    "pdd/prompts/pin_example_hack_python.prompt": "Coordinates the full single-module PDD sync workflow and its user feedback.",
    "pdd/prompts/process_csv_change_python.prompt": "Applies a batch of prompt changes described by a structured CSV file.",
    "pdd/prompts/python_env_detector_python.prompt": "Detects and validates Python environments for generated-code execution.",
    "pdd/prompts/reasoning_python.prompt": "Maps reasoning-time settings to provider-specific reasoning effort levels.",
    "pdd/prompts/render_mermaid_python.prompt": "Renders architecture graphs as interactive, standalone Mermaid HTML pages.",
    "pdd/prompts/run_generated_python.prompt": "Executes generated programs with the language-specific configured command.",
    "pdd/prompts/server/__init___python.prompt": "Defines the public package boundary for the PDD Connect server.",
    "pdd/prompts/server/click_executor_python.prompt": "Executes PDD Click commands with captured or streaming server output.",
    "pdd/prompts/server/routes/prompts_python.prompt": "Exposes prompt analysis, synchronization, comparison, and editing server APIs.",
    "pdd/prompts/trace_main_python.prompt": "Traces prompt execution and dependency context from the PDD CLI.",
    "pdd/prompts/update_model_costs_python.prompt": "Refreshes model pricing data used by PDD cost estimation and selection.",
    "pdd/prompts/validate_prompt_includes_python.prompt": "Validates and cleans include directives in generated prompt content.",
    "pdd/prompts/frontend/App_typescriptreact.prompt": "Provides the root application shell for the PDD Connect web client.",
    "pdd/prompts/frontend/index_typescriptreact.prompt": "Bootstraps and mounts the PDD Connect React application.",
    "pdd/prompts/frontend/components/AddModuleModal_typescriptreact.prompt": "Creates architecture modules through a validated modal form.",
    "pdd/prompts/frontend/components/ChangeModal_typescriptreact.prompt": "Collects, analyzes, and confirms user-proposed prompt changes.",
    "pdd/prompts/frontend/components/CommandForm_typescriptreact.prompt": "Renders command-specific input forms from declarative option metadata.",
    "pdd/prompts/frontend/components/DeviceIndicator_typescriptreact.prompt": "Displays the active responsive breakpoint during frontend development.",
    "pdd/prompts/frontend/components/ErrorBoundary_typescriptreact.prompt": "Contains React rendering failures and provides a recoverable error screen.",
    "pdd/prompts/frontend/components/FilePickerInput_typescriptreact.prompt": "Combines manual path entry with browser-based file and directory selection.",
    "pdd/prompts/frontend/components/GeneratedCommand_typescriptreact.prompt": "Displays generated CLI commands with copy and optional execution controls.",
    "pdd/prompts/frontend/components/GenerationProgressModal_typescriptreact.prompt": "Tracks multi-prompt generation progress and summarizes completed results.",
    "pdd/prompts/frontend/components/GraphToolbar_typescriptreact.prompt": "Controls architecture graph editing, history, layout, and persistence actions.",
    "pdd/prompts/frontend/components/Header_typescriptreact.prompt": "Provides PDD Connect branding and navigation between primary application views.",
    "pdd/prompts/frontend/components/Icon_typescriptreact.prompt": "Provides the shared SVG icon set used throughout the PDD Connect interface.",
    "pdd/prompts/frontend/components/JobCard_typescriptreact.prompt": "Summarizes a background job and exposes its lifecycle actions.",
    "pdd/prompts/frontend/components/JobDashboard_typescriptreact.prompt": "Displays active and completed background jobs in a floating dashboard.",
    "pdd/prompts/frontend/components/ModelSelector_typescriptreact.prompt": "Selects an available LLM from a compact searchable dropdown.",
    "pdd/prompts/frontend/components/ModelSliders_typescriptreact.prompt": "Adjusts model selection, reasoning time, and temperature in a compact popover.",
    "pdd/prompts/frontend/components/ModuleEditModal_typescriptreact.prompt": "Edits or deletes architecture modules through a validated modal form.",
    "pdd/prompts/frontend/components/PromptCodeDiffModal_typescriptreact.prompt": "Compares prompt requirements with code and displays prompt version history.",
    "pdd/prompts/frontend/components/PromptOrderModal_typescriptreact.prompt": "Selects, orders, and configures architecture prompts for batch generation.",
    "pdd/prompts/frontend/components/PromptSpace_typescriptreact.prompt": "Provides the integrated prompt, code, test, and example editing workspace.",
    "pdd/prompts/frontend/components/RemoteSessionSelector_typescriptreact.prompt": "Selects remote development sessions and surfaces their connection health.",
    "pdd/prompts/frontend/components/SyncFromPromptModal_typescriptreact.prompt": "Runs prompt-to-architecture metadata sync and explains the resulting changes.",
    "pdd/prompts/frontend/components/SyncOptionsModal_typescriptreact.prompt": "Configures and submits PDD sync execution options from the web interface.",
    "pdd/prompts/frontend/components/SyncStatusBadge_typescriptreact.prompt": "Shows the synchronization state between a prompt and its generated code.",
    "pdd/prompts/frontend/components/Tabs_typescriptreact.prompt": "Switches between command workspaces in the PDD Connect interface.",
    "pdd/prompts/frontend/components/TaskQueueControls_typescriptreact.prompt": "Controls task-queue execution mode, progress, and bulk lifecycle actions.",
    "pdd/prompts/frontend/components/TaskQueueItem_typescriptreact.prompt": "Displays queued-task status, timing, ordering, and lifecycle controls.",
    "pdd/prompts/frontend/components/TaskQueuePanel_typescriptreact.prompt": "Provides a movable panel for task ordering and queue execution control.",
    "pdd/prompts/frontend/components/Toast_typescriptreact.prompt": "Provides application-wide toast messages and optional browser notifications.",
    "pdd/prompts/frontend/components/Tooltip_typescriptreact.prompt": "Provides accessible contextual labels for controls throughout the web UI.",
    "pdd/prompts/frontend/hooks/useAudioNotification_typescript.prompt": "Plays user-configurable audio notifications for completed background work.",
    "pdd/prompts/frontend/hooks/useJobs_typescript.prompt": "Tracks server job state, output streams, selection, and lifecycle actions.",
    "pdd/prompts/agentic_arch_step7b_review_LLM.prompt": "Reviews architecture structure, dependencies, and naming before prompt generation.",
    "pdd/prompts/agentic_arch_step8_5_context_docs_LLM.prompt": "Generates shared data, API, and integration context for consistent module prompts.",
    "pdd/prompts/agentic_architecture_python.prompt": "Builds project architecture and prompts from GitHub issues and codebase context.",
    "pdd/prompts/agentic_multishot_python.prompt": "Repeats agentic workflows under bounded budgets with durable run telemetry.",
    "pdd/prompts/agentic_split_python.prompt": "Splits large modules through validated orchestration or independent strangler passes.",
    "pdd/prompts/agentic_split_step0_intent_LLM.prompt": "Classifies split intent so later agents can apply the appropriate evaluation rubric.",
    "pdd/prompts/agentic_split_step6a_phase_extract_LLM.prompt": "Decides whether a split child contains distinct phases that merit extraction.",
    "pdd/prompts/agentic_split_step9_refine_check_LLM.prompt": "Decides whether completed split children require another bounded refinement pass.",
    "pdd/prompts/agentic_sync_runner_python.prompt": "Runs dependency-aware sync workers with module-local context and compression settings.",
    "pdd/prompts/arrange_graph_layout_LLM.prompt": "Arranges architecture modules into readable dependency-oriented graph swimlanes.",
    "pdd/prompts/bug_main_python.prompt": "Generates regression tests from GitHub issues or explicit manual bug inputs.",
    "pdd/prompts/checkup_prompt_main_python.prompt": "Normalizes prompt-source reports and routes findings to interactive or automated repair.",
    "pdd/prompts/cli_status_python.prompt": "Provides consistent, skimmable lifecycle status messages across PDD commands.",
    "pdd/prompts/cli_theme_python.prompt": "Provides the shared brand-derived color palette for all PDD command output.",
    "pdd/prompts/code_generator_main_python.prompt": "Orchestrates prompt-to-code generation with path, conformance, and safety gates.",
    "pdd/prompts/commands/context_python.prompt": "Reports per-source token usage for hydrated prompts before generation.",
    "pdd/prompts/context_audit_python.prompt": "Provides one deterministic context-attribution core for CLI and server consumers.",
    "pdd/prompts/core/dump_python.prompt": "Captures diagnostic state for reproducible PDD failure reports.",
    "pdd/prompts/coverage_contracts_python.prompt": "Maps prompt contract rules to stories and executable regression evidence.",
    "pdd/prompts/failure_classification_python.prompt": "Classifies verification failures for targeted repair and retry policy.",
    "pdd/prompts/fix_focus_python.prompt": "Runs Phase 1 when fast-path targets do not match product-code slices before focused repair.",
    "pdd/prompts/fix_main_python.prompt": "Runs bounded unit-test repair across local, cloud, and compressed-context modes.",
    "pdd/prompts/generate_model_catalog_python.prompt": "Regenerates the model catalog with reviewed rankings, metadata, and pricing.",
    "pdd/prompts/grounding_policy_python.prompt": "Enforces grounding review and pin requirements for critical generated modules.",
    "pdd/prompts/llm_model_csv.prompt": "Defines the model catalog schema used for pricing, ranking, and provider selection.",
    "pdd/prompts/metadata_sync_python.prompt": "Finalizes prompt, architecture, report, and fingerprint metadata in a fixed order.",
    "pdd/prompts/one_session_sync_python.prompt": "Runs the complete generation, verification, testing, and repair loop in one session.",
    "pdd/prompts/post_gen_verify_LLM.prompt": "Checks generated code against declared architecture symbols and conventions.",
    "pdd/prompts/postprocess_python.prompt": "Extracts clean source code from raw language-model responses.",
    "pdd/prompts/story_coverage_python.prompt": "Measures executable story-regression coverage and emits machine-readable evidence.",
    "pdd/prompts/sync_orchestration_python.prompt": "Coordinates deterministic sync operations, state transitions, and recovery metadata.",
    "pdd/prompts/test_context_packer_python.prompt": "Selects and packs relevant tests under a deterministic context budget.",
    "pdd/prompts/update_main_python.prompt": "Back-propagates code changes into prompts and finalizes synchronization metadata.",
    "pdd/prompts/user_story_tests_python.prompt": "Validates and generates user stories while maintaining shared story identity.",
    "pdd/prompts/xml_tagger_python.prompt": "Adds deterministic XML structure to prompt content for downstream processing.",
}

# The prompting guide recommends a concrete 60-120 character purpose statement.
# These reviewed overrides cover legacy role-preamble summaries and generated
# summaries that fell outside that range.  They are explicit so a future run
# cannot silently replace judgment with text heuristics.
REASON_OVERRIDES.update(
    {
        "pdd/prompts/agentic_architecture_orchestrator_python.prompt": "Coordinates the gated agentic architecture workflow, persistent state, and accumulated design context.",
        "pdd/prompts/agentic_bug_orchestrator_python.prompt": "Coordinates the issue-driven bug workflow, regression gates, durable state, and GitHub progress updates.",
        "pdd/prompts/agentic_checkup_orchestrator_python.prompt": "Coordinates project checkups, pushes back to the same PR, and preserves the pull request's original intent.",
        "pdd/prompts/agentic_common_python.prompt": "Provides shared agent execution, provider selection, mid-run steering, and durable state for agentic workflows.",
        "pdd/prompts/agentic_crash_python.prompt": "Investigates runtime crashes autonomously and applies verified corrective changes.",
        "pdd/prompts/agentic_e2e_fix_python.prompt": "Starts the issue-driven end-to-end repair workflow and resolves its repository worktree context.",
        "pdd/prompts/agentic_fix_python.prompt": "Explores failing tests, identifies their causes, and applies verified autonomous fixes.",
        "pdd/prompts/agentic_langtest_python.prompt": "Generates language-specific tests and verifies that their execution satisfies the requested contract.",
        "pdd/prompts/agentic_verify_python.prompt": "Verifies generated code against its prompt contract through an autonomous evidence-gathering workflow.",
        "pdd/prompts/architecture_registry_python.prompt": "Tracks architecture entries and issue provenance while resolving the repository root deterministically.",
        "pdd/prompts/auto_include_python.prompt": "Discovers relevant prompt dependencies and emits selective include directives from repository context.",
        "pdd/prompts/auto_update_python.prompt": "Coordinates automatic prompt updates across affected modules while preserving unrelated content.",
        "pdd/prompts/bug_to_unit_test_python.prompt": "Converts reproducible bug reports into focused failing unit tests that capture the reported behavior.",
        "pdd/prompts/change_python.prompt": "Applies requested behavioral changes to prompt contracts while preserving unaffected requirements.",
        "pdd/prompts/checkup_simplify_python.prompt": "Applies conservative simplifications through supported engines and verifies every accepted change.",
        "pdd/prompts/code_generator_python.prompt": "Generates code from hydrated prompts and handles incomplete output, continuation, and post-processing.",
        "pdd/prompts/commands/utility_python.prompt": "Provides CLI utilities for shell-completion installation and generated-code verification.",
        "pdd/prompts/comment_line_python.prompt": "Formats or removes source lines according to the target language's comment syntax.",
        "pdd/prompts/conflicts_in_prompts_python.prompt": "Detects contradictory requirements within prompts and reports actionable conflict evidence.",
        "pdd/prompts/context_generator_main_python.prompt": "Exposes context-example generation through the command-line entry point and output handling.",
        "pdd/prompts/context_generator_python.prompt": "Generates executable example code that demonstrates the public interface of a module.",
        "pdd/prompts/core/errors_python.prompt": "Records centralized CLI diagnostics and renders safe, command-specific error messages.",
        "pdd/prompts/core/cloud_python.prompt": "Centralizes cloud endpoint routing, timeout policy, environment selection, and authenticated access.",
        "pdd/prompts/core/utils_python.prompt": "Provides reusable configuration, environment, and formatting utilities for PDD core workflows.",
        "pdd/prompts/detect_change_main_python.prompt": "Exposes prompt-to-code change detection through the command-line interface.",
        "pdd/prompts/fix_code_loop_python.prompt": "Runs bounded crash-repair iterations until verification passes or the configured budget is exhausted.",
        "pdd/prompts/fix_errors_from_unit_tests_python.prompt": "Repairs generated code from failing unit-test evidence while preserving the prompt contract.",
        "pdd/prompts/frontend/components/AddToQueueModal_typescriptreact.prompt": "Collects validated command options and adds the resulting PDD task to the execution queue.",
        "pdd/prompts/frontend/components/CommandOutput_typescriptreact.prompt": "Streams command output into a terminal view and exposes the associated background-job state.",
        "pdd/prompts/frontend/components/CreatePromptModal_typescriptreact.prompt": "Collects validated module details and creates a new prompt from the modal workflow.",
        "pdd/prompts/frontend/components/ExecutionModeToggle_typescriptreact.prompt": "Switches queued task execution between supported local and remote modes.",
        "pdd/prompts/frontend/components/JobOutputPanel_typescriptreact.prompt": "Displays detailed live output, status, and controls for a selected background job.",
        "pdd/prompts/frontend/index_typescriptreact.prompt": "Bootstraps the React client and mounts the PDD Connect application into the document.",
        "pdd/prompts/gate_python.prompt": "Enforces deterministic evidence, freshness, coverage, waiver, and cost policies before integration.",
        "pdd/prompts/generate_output_paths_python.prompt": "Resolves deterministic code, example, test, and metadata paths for generated prompt artifacts.",
        "pdd/prompts/generate_test_python.prompt": "Generates unit tests for prompt-backed modules and returns their verification metadata.",
        "pdd/prompts/get_comment_python.prompt": "Returns the configured line-comment syntax for a supported programming language.",
        "pdd/prompts/get_jwt_token_python.prompt": "Obtains and refreshes authentication tokens used by PDD Cloud service requests.",
        "pdd/prompts/get_language_python.prompt": "Infers a supported programming language from a prompt name or artifact filename.",
        "pdd/prompts/increase_tests_python.prompt": "Expands existing test suites to improve behavioral coverage without weakening current assertions.",
        "pdd/prompts/incremental_prd_architecture_python.prompt": "Propagates PRD changes into architecture modules and affected prompt requirements through validated patches.",
        "pdd/prompts/server/executor_python.prompt": "Executes PDD Click commands programmatically with isolated context and captured output.",
        "pdd/prompts/server/models_python.prompt": "Defines validated request, response, job, and architecture models for the server API.",
        "pdd/prompts/server/routes/__init___python.prompt": "Exports the FastAPI route modules that compose the PDD Connect server API.",
        "pdd/prompts/server/routes/auth_python.prompt": "Exposes server endpoints for authentication status, login, refresh, and logout workflows.",
        "pdd/prompts/server/routes/commands_python.prompt": "Exposes server endpoints that discover, execute, and monitor PDD commands.",
        "pdd/prompts/server/routes/files_python.prompt": "Exposes validated server endpoints for repository file and directory operations.",
        "pdd/prompts/server/routes/websocket_python.prompt": "Streams command and background-job updates through authenticated WebSocket endpoints.",
        "pdd/prompts/server/security_python.prompt": "Enforces path, CORS, and optional token-authentication safeguards for the PDD server.",
        "pdd/prompts/split_python.prompt": "Extracts selected behavior into a new prompt while preserving the parent prompt's remaining contract.",
        "pdd/prompts/split_validation_python.prompt": "Validates split results for Git safety, completeness, metadata, test seams, and parent integration.",
        "pdd/prompts/src/clients/github_client_Python.prompt": "Provides asynchronous GitHub App access for issues, pull requests, webhooks, and shippability evidence.",
        "pdd/prompts/story_regression_gate_python.prompt": "Rejects stories whose linked executable regression evidence is missing, invalid, or stale.",
        "pdd/prompts/sync_animation_python.prompt": "Displays real-time synchronization progress and final status in interactive terminal workflows.",
        "pdd/prompts/sync_tui_python.prompt": "Provides interactive confirmation, steering, input, and progress controls for synchronization workflows.",
        "pdd/prompts/template_registry_python.prompt": "Discovers, resolves, and loads registered PDD prompt templates from supported locations.",
        "pdd/prompts/trace_python.prompt": "Maps generated artifact lines back to their originating prompt requirements and source spans.",
        "pdd/prompts/agentic_bug_step4_api_research_LLM.prompt": "Researches external APIs relevant to a bug and returns evidence that can guide a verified repair.",
        "pdd/prompts/agentic_checkup_step1_discover_LLM.prompt": "Discovers project structure, languages, frameworks, build tools, and operational entry points.",
        "pdd/prompts/agentic_checkup_step2_deps_LLM.prompt": "Audits project dependencies for correctness, freshness, security risk, and unused packages.",
        "pdd/prompts/agentic_checkup_step3_build_LLM.prompt": "Runs project build and compilation checks and reports reproducible failures with evidence.",
        "pdd/prompts/agentic_checkup_step4_interfaces_LLM.prompt": "Checks cross-module interfaces for incompatible contracts, imports, schemas, and call patterns.",
        "pdd/prompts/agentic_checkup_step5_test_LLM.prompt": "Runs the relevant test suites and records reproducible failures for later repair steps.",
        "pdd/prompts/agentic_checkup_step6_1_fix_LLM.prompt": "Repairs every confirmed checkup finding while preserving unrelated behavior and repository state.",
        "pdd/prompts/agentic_checkup_step6_2_regression_tests_LLM.prompt": "Adds focused regression tests that fail before and pass after each accepted checkup repair.",
        "pdd/prompts/agentic_checkup_step6_3_e2e_tests_LLM.prompt": "Adds end-to-end coverage for repaired user workflows when lower-level tests are insufficient.",
        "pdd/prompts/agentic_checkup_step7_verify_LLM.prompt": "Re-runs deterministic validation after repairs and produces the final evidence-backed checkup report.",
        "pdd/prompts/agentic_checkup_step8_create_pr_LLM.prompt": "Creates a pull request containing verified checkup repairs and links it to the originating issue.",
        "pdd/prompts/agentic_sync_fix_dry_run_LLM.prompt": "Diagnoses a failed synchronization dry run and proposes a bounded repair for the affected module.",
        "pdd/prompts/frontend/components/BatchFilterDropdown_typescriptreact.prompt": "Filters architecture modules by connected generation batch through an accessible dropdown.",
        "pdd/prompts/frontend/components/ReauthModal_typescriptreact.prompt": "Guides users through reauthentication when an authenticated PDD Connect session expires.",
        "pdd/prompts/generate_story_contract_LLM.prompt": "Transforms a reviewed user story into a stable, machine-checkable behavioral contract.",
        "pdd/prompts/generate_user_story_LLM.prompt": "Derives a concise user story and acceptance criteria from product and implementation context.",
        "pdd/prompts/include_query_extractor_LLM.prompt": "Extracts only document evidence relevant to a semantic include query without inventing context.",
        "pdd/prompts/one_session_agent_LLM.prompt": "Executes a bounded prompt-driven task while treating the supplied prompt as the governing contract.",
        "pdd/prompts/prompt_lint_LLM.prompt": "Reviews prompt clarity, completeness, consistency, and testability against PDD doctrine.",
        "pdd/prompts/xml/change_LLM.prompt": "Applies requested changes to a structured prompt without losing unrelated requirements.",
        "pdd/prompts/xml/split_LLM.prompt": "Splits a structured prompt into parent and child contracts without losing behavior.",
        "pdd/prompts/resurface_check_Python.prompt": "Checks whether a previously deferred GitHub issue is ready to return to active processing.",
        "pdd/prompts/Makefile_makefile.prompt": "Defines reproducible developer commands for installing, testing, building, and publishing PDD.",
        "pdd/prompts/conflict_LLM.prompt": "Compares prompt requirements and reports concrete contradictions with their source evidence.",
        "pdd/prompts/language_format_csv.prompt": "Defines canonical language identifiers, extensions, comment syntax, and execution commands.",
        "pdd/prompts/pdd_theme_json.prompt": "Defines the shared terminal presentation theme and semantic styles used by PDD commands.",
        "pdd/prompts/pypi_description_restructuredtext.prompt": "Provides the package-index description and usage overview rendered for published PDD releases.",
        "pdd/prompts/pyproject_toml.prompt": "Defines Python packaging metadata, dependencies, entry points, and build-system configuration.",
        "pdd/prompts/main_gen_prompt.prompt": "Generates a complete implementation prompt from a requested module goal and repository context.",
        "pdd/prompts/continue_generation_python.prompt": "Continues truncated model output and joins the recovered source without duplicated overlap.",
        "pdd/prompts/update_prompt_python.prompt": "Back-propagates observable code changes into the governing prompt contract.",
        "pdd/prompts/detect_change_python.prompt": "Determines which prompt contracts are affected by a requested behavioral change.",
        "pdd/prompts/agentic_crash_explore_LLM.prompt": "Explores a stubborn runtime crash after bounded repair attempts and proposes an evidence-based fix.",
        "pdd/prompts/agentic_fix_explore_LLM.prompt": "Explores a stubborn test failure after bounded repair attempts and proposes an evidence-based fix.",
        "pdd/prompts/agentic_update_LLM.prompt": "Updates a prompt contract to reflect reviewed code changes while keeping the specification concise.",
        "pdd/prompts/agentic_verify_explore_LLM.prompt": "Explores persistent verification failures and proposes a contract-preserving corrective change.",
        "pdd/prompts/sync_analysis_LLM.prompt": "Classifies prompt, code, example, and test diffs and recommends a conflict-safe sync operation.",
        "pdd/prompts/split_LLM.prompt": "Splits a prompt into parent and child contracts without losing requirements or public behavior.",
        "pdd/prompts/agentic_bug_step2_docs_LLM.prompt": "Checks whether reported behavior contradicts the project's documented and intended contract.",
        "pdd/prompts/agentic_fix_primary_LLM.prompt": "Diagnoses a failing test after normal repair attempts and produces a focused corrective patch.",
        "pdd/prompts/bug_to_unit_test_LLM.prompt": "Generates a focused failing test that reproduces a bug report's expected behavior.",
        "pdd/prompts/change_LLM.prompt": "Applies requested changes to a prompt while preserving every unrelated requirement.",
        "pdd/prompts/code_patcher_LLM.prompt": "Updates existing code from reviewed prompt differences without regenerating unrelated sections.",
        "pdd/prompts/continue_generation_LLM.prompt": "Continues a truncated code generation from its exact stopping point without commentary.",
        "pdd/prompts/detect_change_LLM.prompt": "Identifies prompt contracts affected by a change and provides precise update instructions.",
        "pdd/prompts/diff_analyzer_LLM.prompt": "Determines whether prompt differences require full regeneration or a bounded code patch.",
        "pdd/prompts/example_generator_LLM.prompt": "Generates a concise executable example that uses a module's documented public interface.",
        "pdd/prompts/extract_code_LLM.prompt": "Extracts the intended source-code block from model output into a structured response.",
        "pdd/prompts/extract_conflict_LLM.prompt": "Extracts structured prompt-conflict findings and required resolutions from model output.",
        "pdd/prompts/extract_detect_change_LLM.prompt": "Extracts the structured list of affected prompts and change instructions from model output.",
        "pdd/prompts/extract_prompt_change_LLM.prompt": "Extracts the complete modified prompt from a model's change analysis output.",
        "pdd/prompts/extract_prompt_split_LLM.prompt": "Extracts parent and child prompt contracts from a model's structured split result.",
        "pdd/prompts/extract_prompt_update_LLM.prompt": "Extracts the complete updated prompt from a model's code-alignment response.",
        "pdd/prompts/extract_promptline_LLM.prompt": "Extracts the exact prompt source line or minimal span linked to generated code.",
        "pdd/prompts/extract_unit_code_fix_LLM.prompt": "Extracts corrected code and test artifacts from a unit-test repair analysis.",
        "pdd/prompts/extract_xml_LLM.prompt": "Extracts a structurally tagged prompt from the model's XML conversion analysis.",
        "pdd/prompts/fix_code_module_errors_LLM.prompt": "Repairs code or its driver program from reproducible runtime-crash evidence.",
        "pdd/prompts/fix_verification_errors_LLM.prompt": "Repairs generated code from concrete functional-verification findings and execution output.",
        "pdd/prompts/increase_tests_LLM.prompt": "Adds focused tests for uncovered behavior while preserving the existing test suite.",
        "pdd/prompts/regression_analysis_log.prompt": "Analyzes regression logs for failures attributable to PDD rather than generated example programs.",
        "pdd/prompts/trace_LLM.prompt": "Locates the smallest prompt span responsible for a selected generated-code line.",
        "pdd/prompts/trim_results_LLM.prompt": "Removes duplicated overlap between partial generation output and its continuation.",
        "pdd/prompts/trim_results_start_LLM.prompt": "Extracts the unfinished leading code block and explains the safe continuation boundary.",
        "pdd/prompts/update_prompt_LLM.prompt": "Revises the original prompt so it specifies the reviewed behavior present in modified code.",
        "pdd/prompts/xml_convertor_LLM.prompt": "Adds useful XML structure to a prompt while preserving all original requirements and content.",
        "pdd/prompts/fix_errors_from_unit_tests_LLM.prompt": "Diagnoses failing unit-test evidence and repairs the code, the test, or both as required.",
        "pdd/prompts/agentic_arch_step1_analyze_prd_LLM.prompt": "Extracts features, constraints, technology choices, and gaps from a product requirements document.",
        "pdd/prompts/agentic_change_step12_fix_issues_LLM.prompt": "Fixes review findings from the change workflow and verifies each corrective edit.",
        "pdd/prompts/agentic_change_step6_devunits_LLM.prompt": "Identifies prompt-backed development units affected by a requested product change.",
        "pdd/prompts/agentic_change_step8_analyze_LLM.prompt": "Determines how affected prompt contracts must change to implement the requested behavior.",
        "pdd/prompts/agentic_change_step9_implement_LLM.prompt": "Applies reviewed prompt and associated-document changes together as one coherent update.",
        "pdd/prompts/agentic_test_step4_detect_frontend_LLM.prompt": "Classifies the requested test type and selects the repository's appropriate test framework.",
        "pdd/prompts/agentic_test_step5_test_plan_LLM.prompt": "Builds a comprehensive, achievable test plan from the request and repository constraints.",
        "pdd/prompts/agentic_test_step8_fix_iterate_LLM.prompt": "Repairs generated tests iteratively and reruns them until they pass or a blocker is proven.",
        "pdd/prompts/prompt_diff_LLM.prompt": "Compares two prompt versions and reports their meaningful semantic and linguistic differences.",
        "pdd/prompts/agentic_e2e_fix_step10_ci_validation_LLM.prompt": "Interprets required CI failures and applies targeted fixes that preserve the repair contract.",
        "pdd/prompts/agentic_e2e_fix_step11_code_cleanup_LLM.prompt": "Reviews the completed repair diff and corrects bounded code-quality issues before handoff.",
        "pdd/prompts/agentic_arch_step4_data_model_LLM.prompt": "Designs data entities, relationships, storage choices, and schema guidance from researched constraints.",
        "pdd/prompts/agentic_arch_step8_pddrc_LLM.prompt": "Generates and validates repository-specific PDD configuration from the reviewed architecture.",
        "pdd/prompts/agentic_arch_step9_prompts_LLM.prompt": "Generates module prompts at paths defined by the reviewed architecture and PDD configuration.",
        "pdd/prompts/agentic_arch_step9b_cross_audit_LLM.prompt": "Audits generated prompts for cross-file naming, interface, and dependency inconsistencies.",
        "pdd/prompts/api_key_scanner_python.prompt": "Discovers required model credentials across shell, environment, and PDD configuration sources.",
        "pdd/prompts/cross_issue_reconcile_LLM.prompt": "Reconciles shared types, API contracts, and enums across related implementation issues.",
        "pdd/prompts/pddrc_initializer_python.prompt": "Creates repository-specific PDD configuration with deterministic defaults and monorepo context mappings.",
        "pdd/prompts/provider_manager_python.prompt": "Manages model providers and credentials through validated catalog, add, and removal workflows.",
    }
)


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def _annotation(node: ast.AST | None) -> str:
    return ast.unparse(node) if node is not None else "Any"


def _default(value: ast.AST | None) -> str:
    return f" = {ast.unparse(value)}" if value is not None else ""


def _python_signature(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
    fallback_returns: str | None = None,
) -> tuple[str, str]:
    args = node.args
    pieces: list[str] = []
    positional = list(args.posonlyargs) + list(args.args)
    defaults: list[ast.AST | None] = [None] * (len(positional) - len(args.defaults)) + list(
        args.defaults
    )
    for index, (argument, default) in enumerate(zip(positional, defaults)):
        if argument.arg in {"self", "cls"}:
            continue
        annotation = (
            ""
            if argument.annotation is None
            else f": {_annotation(argument.annotation)}"
        )
        pieces.append(f"{argument.arg}{annotation}{_default(default)}")
        if args.posonlyargs and index + 1 == len(args.posonlyargs):
            pieces.append("/")
    if args.vararg:
        annotation = "" if args.vararg.annotation is None else f": {_annotation(args.vararg.annotation)}"
        pieces.append(f"*{args.vararg.arg}{annotation}")
    elif args.kwonlyargs:
        pieces.append("*")
    for argument, default in zip(args.kwonlyargs, args.kw_defaults):
        if argument.arg in {"self", "cls"}:
            continue
        annotation = (
            ""
            if argument.annotation is None
            else f": {_annotation(argument.annotation)}"
        )
        pieces.append(f"{argument.arg}{annotation}{_default(default)}")
    if args.kwarg:
        annotation = "" if args.kwarg.annotation is None else f": {_annotation(args.kwarg.annotation)}"
        pieces.append(f"**{args.kwarg.arg}{annotation}")
    returns = (
        _annotation(node.returns)
        if node.returns is not None
        else fallback_returns
        if fallback_returns and fallback_returns != "unspecified"
        else "Any"
    )
    return_clause = f" -> {returns}"
    prefix = "async " if isinstance(node, ast.AsyncFunctionDef) else ""
    return f"{prefix}({', '.join(pieces)}){return_clause}", returns


def _dunder_all(tree: ast.Module) -> set[str] | None:
    for node in tree.body:
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        if not any(isinstance(target, ast.Name) and target.id == "__all__" for target in targets):
            continue
        value = node.value
        if not isinstance(value, (ast.List, ast.Tuple, ast.Set)):
            return None
        names = {
            item.value
            for item in value.elts
            if isinstance(item, ast.Constant) and isinstance(item.value, str)
        }
        return names if len(names) == len(value.elts) else None
    return None


def _class_kind(node: ast.ClassDef) -> str:
    decorators = {ast.unparse(item).split("(", 1)[0].rsplit(".", 1)[-1] for item in node.decorator_list}
    bases = {ast.unparse(item).rsplit(".", 1)[-1] for item in node.bases}
    if "dataclass" in decorators:
        return "dataclass"
    if bases & {"Enum", "IntEnum", "StrEnum"}:
        return "enum"
    if "Protocol" in bases:
        return "protocol"
    return "class"


def _python_interface(path: Path) -> dict[str, Any]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    if path.name == "__init__.py":
        return {"type": "entrypoint", "entrypoint": {}}
    exports = _dunder_all(tree)
    def public(name: str) -> bool:
        return name in exports if exports is not None else not name.startswith("_")
    classes: list[dict[str, str]] = []
    functions: list[dict[str, str]] = []
    constants: list[dict[str, str]] = []
    for node in tree.body:
        if isinstance(node, ast.ClassDef) and public(node.name):
            classes.append({"name": node.name, "kind": _class_kind(node)})
            for child in node.body:
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)) and (
                    child.name == "__init__" or not child.name.startswith("_")
                ):
                    signature, returns = _python_signature(child)
                    functions.append(
                        {"name": f"{node.name}.{child.name}", "signature": signature, "returns": returns}
                    )
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and public(node.name):
            signature, returns = _python_signature(node)
            functions.append({"name": node.name, "signature": signature, "returns": returns})
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            for target in targets:
                if isinstance(target, ast.Name) and target.id.isupper() and public(target.id):
                    constants.append({"name": target.id, "kind": "constant"})
    module: dict[str, Any] = {"functions": functions}
    if classes:
        module["classes"] = classes
    if constants:
        module["constants"] = constants
    return {"type": "module", "module": module}


def _prompt_body_text(prompt: Path) -> str:
    text = prompt.read_text(encoding="utf-8")
    for tag in ("pdd-reason", "pdd-interface", "pdd-dependency"):
        text = re.sub(
            rf"<{tag}(?:\s[^>]*)?>.*?</{tag}>",
            "",
            text,
            flags=re.S | re.I,
        )
    return text


def _python_curated_interface(path: Path, prompt: Path) -> dict[str, Any]:
    """Keep only APIs the prompt names; convention-public helpers stay internal."""

    interface = _python_interface(path)
    if interface.get("type") != "module":
        return interface
    body = _prompt_body_text(prompt)
    module = interface["module"]
    functions = [
        item
        for item in module.get("functions", [])
        if re.search(rf"\b{re.escape(item['name'].split('.')[-1])}\b", body)
    ]
    classes = [
        item
        for item in module.get("classes", [])
        if re.search(rf"\b{re.escape(item['name'])}\b", body)
    ]
    constants = [
        item
        for item in module.get("constants", [])
        if re.search(rf"\b{re.escape(item['name'])}\b", body)
    ]
    curated: dict[str, Any] = {"functions": functions}
    if classes:
        curated["classes"] = classes
    if constants:
        curated["constants"] = constants
    if not functions and not classes and not constants:
        return {"type": "entrypoint", "entrypoint": {}}
    return {"type": "module", "module": curated}


def _literal_string(node: ast.AST | None) -> str | None:
    return node.value if isinstance(node, ast.Constant) and isinstance(node.value, str) else None


def _python_api_interface(path: Path) -> dict[str, Any]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    prefixes: dict[str, str] = {}
    for node in tree.body:
        if not isinstance(node, ast.Assign) or not isinstance(node.value, ast.Call):
            continue
        if ast.unparse(node.value.func).rsplit(".", 1)[-1] != "APIRouter":
            continue
        prefix = next(
            (
                value
                for keyword in node.value.keywords
                if keyword.arg == "prefix" and (value := _literal_string(keyword.value)) is not None
            ),
            "",
        )
        for target in node.targets:
            if isinstance(target, ast.Name):
                prefixes[target.id] = prefix
    endpoints: list[dict[str, str]] = []
    supported = {"get", "post", "put", "patch", "delete", "options", "head", "websocket"}
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for decorator in node.decorator_list:
            if not isinstance(decorator, ast.Call) or not isinstance(decorator.func, ast.Attribute):
                continue
            method = decorator.func.attr.lower()
            if method not in supported or not isinstance(decorator.func.value, ast.Name):
                continue
            router = decorator.func.value.id
            if router not in prefixes or not decorator.args:
                continue
            route = _literal_string(decorator.args[0])
            if route is None:
                continue
            endpoint_path = prefixes[router].rstrip("/") + "/" + route.lstrip("/")
            endpoints.append(
                {
                    "method": method.upper(),
                    "path": endpoint_path.rstrip("/") or "/",
                    "handler": node.name,
                }
            )
    return {"type": "api", "api": {"endpoints": endpoints}}


def _python_cli_interface(path: Path) -> dict[str, Any]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    commands: list[dict[str, str]] = []
    for node in tree.body:
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for decorator in node.decorator_list:
            target = decorator.func if isinstance(decorator, ast.Call) else decorator
            decorator_name = ast.unparse(target)
            if decorator_name.rsplit(".", 1)[-1] not in {"command", "group"}:
                continue
            explicit: str | None = None
            if isinstance(decorator, ast.Call):
                explicit = _literal_string(decorator.args[0]) if decorator.args else None
                explicit = explicit or next(
                    (
                        value
                        for keyword in decorator.keywords
                        if keyword.arg == "name" and (value := _literal_string(keyword.value)) is not None
                    ),
                    None,
                )
            name = explicit or re.sub(r"_(?:cmd|group)$", "", node.name).replace("_", "-")
            description = (ast.get_docstring(node, clean=True) or "").split("\n", 1)[0]
            commands.append({"name": name, "description": description})
            break
    return {"type": "cli", "cli": {"commands": commands}}


def _balanced_object(text: str, marker: re.Pattern[str]) -> tuple[str, str] | None:
    match = marker.search(text)
    if not match:
        return None
    start = text.find("{", match.end())
    if start < 0:
        return None
    depth = 0
    quote: str | None = None
    escaped = False
    for index in range(start, len(text)):
        char = text[index]
        if quote:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == quote:
                quote = None
            continue
        if char in {'"', "'", "`"}:
            quote = char
        elif char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return match.group(1), text[start + 1 : index]
    return None


def _typescript_props(text: str) -> list[dict[str, Any]]:
    markers = (
        re.compile(r"(?:export\s+)?interface\s+(\w*Props)\s*"),
        re.compile(r"(?:export\s+)?type\s+(\w*Props)\s*=\s*"),
    )
    block = next((result for marker in markers if (result := _balanced_object(text, marker))), None)
    if not block:
        return []
    _name, body = block
    props: list[dict[str, Any]] = []
    for line in body.splitlines():
        match = re.match(r"^\s*(\w+)(\?)?\s*:\s*(.*?)\s*;\s*(?://.*)?$", line)
        if not match:
            continue
        prop_type = re.sub(r"\s+", " ", match.group(3)).strip()
        props.append(
            {"name": match.group(1), "type": prop_type, "required": match.group(2) is None}
        )
    return props


def _typescript_interface(path: Path, *, react: bool) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8")
    if react:
        return {
            "type": "component",
            "component": {"name": path.stem, "props": _typescript_props(text), "emits": []},
        }
    functions: list[dict[str, str]] = []
    for match in re.finditer(
        r"export\s+(?:async\s+)?(?:function|const)\s+(\w+)", text
    ):
        functions.append({"name": match.group(1), "signature": "exported", "returns": "inferred"})
    types = sorted(
        set(
            re.findall(
                r"export\s+(?:interface|type|class|enum)\s+(\w+)",
                text,
            )
        )
    )
    module: dict[str, Any] = {"functions": functions}
    if types:
        module["types"] = types
    return {"type": "module", "module": module}


def _interface_for_artifact(path: Path, language: str, prompt: Path | None = None) -> dict[str, Any]:
    if language == "python":
        prompt_relative = str(prompt.relative_to(PROMPTS_ROOT)) if prompt is not None else ""
        if prompt_relative.startswith("server/routes/"):
            return _python_api_interface(path)
        if prompt_relative.startswith("commands/"):
            return _python_cli_interface(path)
        return _python_curated_interface(path, prompt) if prompt is not None else _python_interface(path)
    return _typescript_interface(path, react=language == "typescriptreact")


def _clean_reason(value: str) -> str:
    # Underscores are meaningful in identifiers such as PDD_CLOUD_URL.  They
    # are not Markdown emphasis when embedded in an architecture reason.
    value = re.sub(r"[`*#]", "", value)
    value = re.sub(r"\s+", " ", value).strip(" -:.")
    value = re.sub(r"^(This|The) (module|component|hook)\s+", "", value, flags=re.IGNORECASE)
    if not value:
        return value
    value = value[0].upper() + value[1:]
    if len(value) > 180:
        sentence = re.split(r"(?<=[.!?])\s", value, maxsplit=1)[0]
        value = sentence if len(sentence) <= 180 else value[:177].rstrip() + "..."
    return value.rstrip(".") + "."


def _prompt_purpose_text(text: str) -> str | None:
    # Metadata generated by this helper is not evidence for its own purpose.
    # Removing it also prevents JSON property names from being mistaken for prose.
    text = re.sub(
        r"<pdd-(?:reason|interface)(?:\s[^>]*)?>.*?</pdd-(?:reason|interface)>",
        "",
        text,
        flags=re.S | re.I,
    )
    responsibility = re.search(r"<responsibility>\s*(.*?)\s*</responsibility>", text, re.S | re.I)
    if responsibility:
        return _clean_reason(responsibility.group(1))

    lines = text.splitlines()
    for section in ("Role\\s*&\\s*Scope", "Purpose", "Functionality", "Goal"):
        section_pattern = re.compile(
            rf"^\s*(?:%+|#+)\s*(?:{section})\s*:?.*$",
            re.I,
        )
        for index, line in enumerate(lines):
            if not section_pattern.match(line):
                continue
            candidates: list[str] = []
            for candidate in lines[index + 1 : index + 10]:
                if re.match(r"^\s*(?:%+|#+)\s*[A-Za-z]", candidate):
                    break
                value = candidate.strip().lstrip("-%# ")
                if not value or value.startswith("<"):
                    continue
                candidates.append(value)
                if re.search(r"[.!?]$", value):
                    break
            cleaned = _clean_reason(" ".join(candidates))
            if cleaned and not re.match(
                r"^(?:Write|Create|Build|Implement)\b.*(?:module|component|file|hook)\b",
                cleaned,
                re.I,
            ):
                return cleaned

    for line in lines:
        value = line.strip()
        if not value or value.startswith(("<", "#", "---")):
            continue
        value = value.lstrip("% ")
        # Common prompt opening: "You are ... Build `path`, a ...".  Its useful
        # purpose begins after the concrete output path, not at the role preamble.
        opening = re.search(
            r"(?:Build|Create|Implement|Write)\s+`[^`]+`\s*,?\s*(?:an?\s+)?(.+)$",
            value,
            re.I,
        )
        if opening:
            value = opening.group(1)
        if len(value) < 25:
            continue
        cleaned = _clean_reason(value)
        cleaned = re.sub(
            r"^(?:Create|Build|Implement)\s+(?:a\s+)?(?:React\s+)?(?:component\s+)?(?:named\s+)?`?\w+`?\s+(?:that|which)\s+",
            "",
            cleaned,
            flags=re.I,
        )
        if cleaned:
            return cleaned[0].upper() + cleaned[1:]
    return None


def _prompt_purpose(prompt: Path) -> str | None:
    return _prompt_purpose_text(prompt.read_text(encoding="utf-8"))


def _architecture_reason(prompt_path: str) -> str | None:
    filename = prompt_path.removeprefix("pdd/prompts/")
    for entry in _read_json(ARCHITECTURE_PATH):
        if entry.get("filename") == filename:
            reason = entry.get("reason")
            if isinstance(reason, str) and reason.strip():
                return _clean_reason(reason)
    return None


def _reason_from_prompt_or_code(
    prompt: Path,
    artifact: Path,
    *,
    use_existing_metadata: bool = True,
    source_text: str | None = None,
) -> str:
    relative = str(prompt.relative_to(ROOT))
    if relative in REASON_OVERRIDES:
        return REASON_OVERRIDES[relative]
    metadata = parse_prompt_metadata(prompt)
    if use_existing_metadata and metadata.reason:
        return metadata.reason
    if purpose := _prompt_purpose_text(source_text) if source_text is not None else _prompt_purpose(prompt):
        return purpose
    if artifact.suffix == ".py":
        try:
            docstring = ast.get_docstring(
                ast.parse(artifact.read_text(encoding="utf-8"), filename=str(artifact)),
                clean=True,
            )
        except SyntaxError:
            docstring = None
        if docstring:
            first = re.split(r"\n\s*\n|(?<=[.!?])\s", docstring, maxsplit=1)[0]
            if cleaned := _clean_reason(first):
                return cleaned
    return f"Defines the verified behavior and public contract for {artifact.stem}."


def _render_interface_block(prompt: Path, interface: dict[str, Any]) -> str:
    """Render metadata without breaking runtime ``str.format`` templates.

    PDD's LLM templates are formatted directly.  Their literal JSON braces must
    therefore be doubled, while architecture parsers deliberately decode that
    representation back to the same interface object.
    """

    rendered = json.dumps(interface, indent=2, ensure_ascii=False)
    if prompt.name.endswith("_LLM.prompt"):
        rendered = rendered.replace("{", "{{").replace("}", "}}")
    return "<pdd-interface>\n" + rendered + "\n</pdd-interface>"


def _prepend_missing_metadata(
    prompt: Path,
    artifact: Path,
    language: str,
) -> bool:
    metadata = parse_prompt_metadata(prompt)
    additions: list[str] = []
    if metadata.reason is None:
        additions.append(f"<pdd-reason>{_reason_from_prompt_or_code(prompt, artifact)}</pdd-reason>")
    if metadata.interface is None and metadata.interface_error is None:
        interface = _interface_for_artifact(artifact, language, prompt)
        additions.append(_render_interface_block(prompt, interface))
    if not additions:
        return False
    original = prompt.read_text(encoding="utf-8")
    prompt.write_text("\n\n".join(additions) + "\n\n" + original, encoding="utf-8")
    return True


def write_prompt_metadata() -> list[str]:
    expected = _read_json(EXPECTED_MANAGED_PATH)["units"]
    classifications = _read_json(CLASSIFICATIONS_PATH)
    special = classifications["special_prompt_outputs"]
    changed: list[str] = []
    for row in expected:
        prompt_path = str(row["prompt_path"])
        prompt_relative = prompt_path.removeprefix("pdd/prompts/")
        direct = _direct_artifact(prompt_relative)
        if direct:
            language, artifact_relative = direct
        elif prompt_path in special:
            artifact_relative = special[prompt_path]
            language = "python" if artifact_relative.endswith(".py") else str(row["language_id"])
        else:
            continue
        prompt = ROOT / prompt_path
        artifact = ROOT / artifact_relative
        if _prepend_missing_metadata(prompt, artifact, language):
            changed.append(prompt_path)
    return changed


def _head_text(relative: str) -> str:
    completed = subprocess.run(
        ["git", "show", f"HEAD:{relative}"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout


def _replace_tag(text: str, tag: str, replacement: str) -> str:
    pattern = re.compile(
        rf"<{re.escape(tag)}(?:\s[^>]*)?>\s*.*?\s*</{re.escape(tag)}>",
        re.S | re.I,
    )
    updated, count = pattern.subn(replacement, text, count=1)
    if count != 1:
        raise ValueError(f"expected one generated <{tag}> block")
    return updated


def refresh_added_prompt_metadata() -> list[str]:
    """Refresh only metadata absent at HEAD, preserving hand-authored tags."""

    expected = _read_json(EXPECTED_MANAGED_PATH)["units"]
    classifications = _read_json(CLASSIFICATIONS_PATH)
    special = classifications["special_prompt_outputs"]
    changed: list[str] = []
    for row in expected:
        prompt_path = str(row["prompt_path"])
        prompt_relative = prompt_path.removeprefix("pdd/prompts/")
        direct = _direct_artifact(prompt_relative)
        if direct:
            language, artifact_relative = direct
        elif prompt_path in special:
            artifact_relative = special[prompt_path]
            language = "python" if artifact_relative.endswith(".py") else str(row["language_id"])
        else:
            continue
        head = _head_text(prompt_path)
        current_path = ROOT / prompt_path
        current = current_path.read_text(encoding="utf-8")
        artifact = ROOT / artifact_relative
        updated = current
        if "<pdd-reason>" not in head:
            reason = REASON_OVERRIDES.get(prompt_path) or _architecture_reason(prompt_path) or _reason_from_prompt_or_code(
                current_path,
                artifact,
                use_existing_metadata=False,
                source_text=head,
            )
            updated = _replace_tag(updated, "pdd-reason", f"<pdd-reason>{reason}</pdd-reason>")
        if "<pdd-interface>" not in head:
            interface = _interface_for_artifact(artifact, language, current_path)
            replacement = _render_interface_block(current_path, interface)
            updated = _replace_tag(updated, "pdd-interface", replacement)
        if updated != current:
            current_path.write_text(updated, encoding="utf-8")
            changed.append(prompt_path)
    return changed


def refresh_declared_python_interfaces() -> list[str]:
    """Align curated Python interface declarations without exposing helpers."""

    expected = _read_json(EXPECTED_MANAGED_PATH)["units"]
    changed: list[str] = []
    for row in expected:
        prompt_path = str(row["prompt_path"])
        direct = _direct_artifact(prompt_path.removeprefix("pdd/prompts/"))
        if not direct or direct[0] != "python":
            continue
        prompt = ROOT / prompt_path
        artifact = ROOT / direct[1]
        metadata = parse_prompt_metadata(prompt)
        if not metadata.interface or metadata.interface.get("type") != "module":
            continue
        derived = _python_interface(artifact)
        if derived.get("type") != "module":
            continue
        tree = ast.parse(artifact.read_text(encoding="utf-8"), filename=str(artifact))
        callable_nodes: dict[str, ast.FunctionDef | ast.AsyncFunctionDef] = {}
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                callable_nodes[node.name] = node
            elif isinstance(node, ast.ClassDef):
                callable_nodes.update(
                    {
                        f"{node.name}.{child.name}": child
                        for child in node.body
                        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
                    }
                )
        refreshed = json.loads(json.dumps(metadata.interface))
        for item in refreshed.get("module", {}).get("functions", []):
            if not isinstance(item, dict) or item.get("name") not in callable_nodes:
                continue
            previous_returns = item.get("returns")
            signature, returns = _python_signature(
                callable_nodes[item["name"]],
                previous_returns if isinstance(previous_returns, str) else None,
            )
            item["signature"] = signature
            item["returns"] = returns
        if refreshed == metadata.interface:
            continue
        current = prompt.read_text(encoding="utf-8")
        replacement = _render_interface_block(prompt, refreshed)
        prompt.write_text(_replace_tag(current, "pdd-interface", replacement), encoding="utf-8")
        changed.append(prompt_path)
    return changed


def normalize_prompt_reasons() -> list[str]:
    """Apply the reviewed concise architecture reasons in REASON_OVERRIDES."""

    changed: list[str] = []
    for prompt_path, reason in sorted(REASON_OVERRIDES.items()):
        prompt = ROOT / prompt_path
        if not prompt.is_file() or parse_prompt_metadata(prompt).reason is None:
            continue
        current = prompt.read_text(encoding="utf-8")
        updated = _replace_tag(current, "pdd-reason", f"<pdd-reason>{reason}</pdd-reason>")
        if updated != current:
            prompt.write_text(updated, encoding="utf-8")
            changed.append(prompt_path)
    return changed


def complete_registered_prompt_metadata() -> list[str]:
    """Add explicit architecture metadata to every registered prompt.

    Existing declarations remain authoritative.  Missing declarations are
    copied from the reviewed architecture entry, except that a reviewed reason
    override takes precedence over a legacy generated summary.
    """

    changed: list[str] = []
    for entry in _read_json(ARCHITECTURE_PATH):
        filename = str(entry["filename"])
        prompt_path = f"pdd/prompts/{filename}"
        prompt = ROOT / prompt_path
        metadata = parse_prompt_metadata(prompt)
        additions: list[str] = []
        if metadata.reason is None:
            reason = REASON_OVERRIDES.get(prompt_path) or str(entry.get("reason") or "").strip()
            additions.append(f"<pdd-reason>{reason}</pdd-reason>")
        if metadata.interface is None and metadata.interface_error is None:
            additions.append(
                _render_interface_block(
                    prompt, entry.get("interface") or _prompt_only_interface(filename)
                )
            )
        if metadata.dependencies is None and entry.get("dependencies"):
            additions.extend(
                f"<pdd-dependency>{dependency}</pdd-dependency>"
                for dependency in entry["dependencies"]
            )
        if additions:
            original = prompt.read_text(encoding="utf-8")
            prompt.write_text("\n\n".join(additions) + "\n\n" + original, encoding="utf-8")
            changed.append(prompt_path)
    return changed


def normalize_llm_interface_metadata() -> list[str]:
    """Escape interface JSON in runtime-formatted LLM prompt templates."""

    changed: list[str] = []
    for prompt in sorted((ROOT / "pdd/prompts").rglob("*_LLM.prompt")):
        metadata = parse_prompt_metadata(prompt)
        if metadata.interface is None:
            continue
        current = prompt.read_text(encoding="utf-8")
        updated = _replace_tag(
            current,
            "pdd-interface",
            _render_interface_block(prompt, metadata.interface),
        )
        if updated != current:
            prompt.write_text(updated, encoding="utf-8")
            changed.append(str(prompt.relative_to(ROOT)))
    return changed


def _prompt_only_interface(filename: str) -> dict[str, Any]:
    if filename.endswith("_LLM.prompt"):
        return {"type": "job", "job": {}}
    return {"type": "config", "config": {}}


def _tags_for(filename: str, filepath: str, language: str) -> list[str]:
    tags = ["module", language]
    if filename.endswith("_LLM.prompt"):
        tags = ["llm", "prompt"]
    if filepath.startswith("pdd/frontend/"):
        tags.append("frontend")
    if "/components/" in filepath:
        tags.append("component")
    if filepath.startswith("pdd/server/"):
        tags.append("server")
    return sorted(set(tags))


def _normalize_architecture_priorities(entries: list[dict[str, Any]]) -> list[str]:
    """Assign stable dependency-first priorities to an acyclic architecture."""

    by_name = {str(entry["filename"]): entry for entry in entries}
    original_order = {str(entry["filename"]): index for index, entry in enumerate(entries)}
    dependents: dict[str, set[str]] = {name: set() for name in by_name}
    remaining: dict[str, set[str]] = {}
    for name, entry in by_name.items():
        dependencies = {
            str(dependency)
            for dependency in entry.get("dependencies", [])
            if str(dependency) in by_name
        }
        remaining[name] = dependencies
        for dependency in dependencies:
            dependents[dependency].add(name)

    ready = sorted(
        (name for name, dependencies in remaining.items() if not dependencies),
        key=lambda name: (int(by_name[name].get("priority") or 0), original_order[name], name),
    )
    ordered: list[str] = []
    while ready:
        name = ready.pop(0)
        ordered.append(name)
        for dependent in sorted(dependents[name], key=original_order.get):
            remaining[dependent].discard(name)
            if not remaining[dependent] and dependent not in ordered and dependent not in ready:
                ready.append(dependent)
        ready.sort(
            key=lambda candidate: (
                int(by_name[candidate].get("priority") or 0),
                original_order[candidate],
                candidate,
            )
        )
    if len(ordered) != len(entries):
        cyclic = sorted(set(by_name) - set(ordered))
        raise ValueError(f"cannot assign priorities while dependency cycles remain: {cyclic}")

    changed: list[str] = []
    for priority, name in enumerate(ordered, start=1):
        if by_name[name].get("priority") != priority:
            by_name[name]["priority"] = priority
            changed.append(f"set priority {priority} for {name}")
    return changed


def write_architecture() -> list[str]:
    entries: list[dict[str, Any]] = _read_json(ARCHITECTURE_PATH)
    expected_rows = _read_json(EXPECTED_MANAGED_PATH)["units"]
    classifications = _read_json(CLASSIFICATIONS_PATH)
    prompt_only = set(classifications["prompt_without_local_artifact"])
    special = classifications["special_prompt_outputs"]

    changed: list[str] = []
    for entry in entries:
        if entry.get("filename") == "pdd/evidence_manifest_python.prompt":
            entry["filename"] = "evidence_manifest_python.prompt"
            changed.append("normalize evidence_manifest prompt path")
        filename = str(entry.get("filename") or "")
        prompt_path = f"pdd/prompts/{filename}"
        if prompt_path in special and entry.get("filepath") != special[prompt_path]:
            entry["filepath"] = special[prompt_path]
            changed.append(f"map {filename} to {special[prompt_path]}")

    by_filename = {str(entry["filename"]): entry for entry in entries}
    priority = max(int(entry.get("priority") or 0) for entry in entries)
    for row in expected_rows:
        prompt_path = str(row["prompt_path"])
        if prompt_path in prompt_only:
            continue
        filename = prompt_path.removeprefix("pdd/prompts/")
        direct = _direct_artifact(filename)
        if direct:
            language, filepath = direct
        elif prompt_path in special:
            language, filepath = str(row["language_id"]), special[prompt_path]
        else:
            language, filepath = str(row["language_id"]), prompt_path
        if filename not in by_filename:
            prompt = ROOT / prompt_path
            artifact = ROOT / filepath
            metadata = parse_prompt_metadata(prompt)
            priority += 1
            reason = metadata.reason or _reason_from_prompt_or_code(prompt, artifact)
            interface = metadata.interface or _prompt_only_interface(filename)
            entry = {
                "reason": reason,
                "description": reason,
                "dependencies": list(metadata.dependencies or ()),
                "priority": priority,
                "filename": filename,
                "filepath": filepath,
                "tags": _tags_for(filename, filepath, language),
                "interface": interface,
            }
            entries.append(entry)
            by_filename[filename] = entry
            changed.append(f"register {filename}")

    for entry in entries:
        filename = str(entry["filename"])
        prompt = PROMPTS_ROOT / filename
        metadata = parse_prompt_metadata(prompt)
        reviewed_reason = REASON_OVERRIDES.get(f"pdd/prompts/{filename}")
        if reviewed_reason is not None and metadata.reason == reviewed_reason and entry.get("reason") != reviewed_reason:
            entry["reason"] = reviewed_reason
            changed.append(f"sync reviewed reason {filename}")
        if metadata.reason is not None and entry.get("reason") != metadata.reason:
            entry["reason"] = metadata.reason
            changed.append(f"sync reason {filename}")
        if metadata.interface is not None and entry.get("interface") != metadata.interface:
            entry["interface"] = metadata.interface
            changed.append(f"sync interface {filename}")
        if metadata.dependencies is not None and entry.get("dependencies") != list(metadata.dependencies):
            entry["dependencies"] = list(metadata.dependencies)
            changed.append(f"sync dependencies {filename}")
        if not entry.get("description"):
            entry["description"] = str(entry.get("reason") or "")
            changed.append(f"add description {filename}")

    changed.extend(_normalize_architecture_priorities(entries))
    _write_json(ARCHITECTURE_PATH, entries)
    return changed


def write_verification_profiles() -> list[str]:
    """Restamp profile requirement identities from the reviewed prompt bytes."""

    payload = _read_json(VERIFICATION_PROFILES_PATH)
    changed: list[str] = []
    for profile in payload["profiles"]:
        prompt_path = str(profile["prompt_path"])
        raw = (ROOT / prompt_path).read_bytes()
        explicit = sorted(set(REQUIREMENT_ID.findall(raw.decode("utf-8"))))
        requirements = explicit or [f"CONTRACT-SHA256:{hashlib.sha256(raw).hexdigest()}"]
        if profile.get("required_requirement_ids") != requirements:
            profile["required_requirement_ids"] = requirements
            changed.append(prompt_path)
        for obligation in profile["obligations"]:
            obligation["requirement_ids"] = requirements
    _write_json(VERIFICATION_PROFILES_PATH, payload)
    return changed


def write_requirement_rotations() -> list[str]:
    """Prepare exact dormant transition rows from protected HEAD to this tree.

    These rows are transition data, not self-authorizing trust. They must be
    installed on the protected base before the corresponding prompt/profile
    changes can be consumed; see docs/manual_repository_sync.md.
    """

    base_ref = subprocess.run(
        ["git", "merge-base", "HEAD", "origin/main"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    base_bytes = subprocess.run(
        ["git", "show", f"{base_ref}:.pdd/verification-profiles.json"],
        cwd=ROOT,
        check=True,
        capture_output=True,
    ).stdout
    head_bytes = VERIFICATION_PROFILES_PATH.read_bytes()
    base_payload = json.loads(base_bytes)
    head_payload = json.loads(head_bytes)
    base_rows = {
        (str(row["prompt_path"]), str(row["language_id"])): row
        for row in base_payload["profiles"]
    }
    head_rows = {
        (str(row["prompt_path"]), str(row["language_id"])): row
        for row in head_payload["profiles"]
    }
    base_policy_sha = hashlib.sha256(base_bytes).hexdigest()
    head_policy_sha = hashlib.sha256(head_bytes).hexdigest()
    rotations: list[dict[str, str]] = []
    for identity in sorted(base_rows):
        before = base_rows[identity]["required_requirement_ids"]
        after = head_rows[identity]["required_requirement_ids"]
        if before == after:
            continue
        if not (
            len(before) == len(after) == 1
            and str(before[0]).startswith("CONTRACT-SHA256:")
            and str(after[0]).startswith("CONTRACT-SHA256:")
        ):
            raise ValueError(f"non-opaque requirement transition needs manual review: {identity}")
        prompt_path, language_id = identity
        base_prompt = subprocess.run(
            ["git", "show", f"{base_ref}:{prompt_path}"],
            cwd=ROOT,
            check=True,
            capture_output=True,
        ).stdout
        head_prompt = (ROOT / prompt_path).read_bytes()
        base_prompt_sha = hashlib.sha256(base_prompt).hexdigest()
        head_prompt_sha = hashlib.sha256(head_prompt).hexdigest()
        if before != [f"CONTRACT-SHA256:{base_prompt_sha}"] or after != [
            f"CONTRACT-SHA256:{head_prompt_sha}"
        ]:
            raise ValueError(f"profile requirement does not match prompt bytes: {identity}")
        rotations.append(
            {
                "prompt_path": prompt_path,
                "language_id": language_id,
                "from_requirement_id": before[0],
                "to_requirement_id": after[0],
                "policy_path": ".pdd/verification-profiles.json",
                "base_policy_sha256": base_policy_sha,
                "head_policy_sha256": head_policy_sha,
                "base_prompt_sha256": base_prompt_sha,
                "head_prompt_sha256": head_prompt_sha,
            }
        )
    generated_identities = {
        (row["prompt_path"], row["language_id"]) for row in rotations
    }
    try:
        protected_policy = json.loads(
            subprocess.run(
                [
                    "git",
                    "show",
                    f"{base_ref}:.pdd/verification-profile-rotations.json",
                ],
                cwd=ROOT,
                check=True,
                capture_output=True,
            ).stdout
        )
    except (subprocess.CalledProcessError, json.JSONDecodeError):
        protected_policy = {}
    protected_rows = (
        protected_policy.get("requirement_rotations", [])
        if isinstance(protected_policy, dict)
        else []
    )
    for row in protected_rows:
        if not isinstance(row, dict):
            continue
        identity = (str(row.get("prompt_path")), str(row.get("language_id")))
        if identity in generated_identities:
            continue
        prompt_path, _language_id = identity
        try:
            prompt_bytes = subprocess.run(
                ["git", "show", f"{base_ref}:{prompt_path}"],
                cwd=ROOT,
                check=True,
                capture_output=True,
            ).stdout
        except subprocess.CalledProcessError:
            continue
        # Retain only still-dormant protected authority. Consumed or stale rows
        # must not survive merely because they were already checked in.
        if (
            row.get("base_policy_sha256") == base_policy_sha
            and row.get("base_prompt_sha256")
            == hashlib.sha256(prompt_bytes).hexdigest()
            and base_rows.get(identity, {}).get("required_requirement_ids")
            == [row.get("from_requirement_id")]
        ):
            rotations.append(row)
    rotations.sort(key=lambda row: (row["prompt_path"], row["language_id"]))

    payload = _read_json(VERIFICATION_PROFILE_ROTATIONS_PATH)
    payload["requirement_rotations"] = rotations
    _write_json(VERIFICATION_PROFILE_ROTATIONS_PATH, payload)
    return [f"{row['prompt_path']}:{row['language_id']}" for row in rotations]


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-prompt-metadata", action="store_true")
    parser.add_argument("--refresh-added-prompt-metadata", action="store_true")
    parser.add_argument("--refresh-declared-python-interfaces", action="store_true")
    parser.add_argument("--normalize-prompt-reasons", action="store_true")
    parser.add_argument("--complete-registered-prompt-metadata", action="store_true")
    parser.add_argument("--normalize-llm-interface-metadata", action="store_true")
    parser.add_argument("--write-architecture", action="store_true")
    parser.add_argument("--write-verification-profiles", action="store_true")
    parser.add_argument("--write-requirement-rotations", action="store_true")
    args = parser.parse_args(list(argv) if argv is not None else None)
    if not args.write_prompt_metadata and not args.refresh_added_prompt_metadata and not args.refresh_declared_python_interfaces and not args.normalize_prompt_reasons and not args.complete_registered_prompt_metadata and not args.normalize_llm_interface_metadata and not args.write_architecture and not args.write_verification_profiles and not args.write_requirement_rotations:
        parser.error("select at least one explicit write operation")
    if args.write_prompt_metadata:
        changed = write_prompt_metadata()
        print(f"updated prompt metadata: {len(changed)}")
        for path in changed:
            print(path)
    if args.refresh_added_prompt_metadata:
        changed = refresh_added_prompt_metadata()
        print(f"refreshed added prompt metadata: {len(changed)}")
        for path in changed:
            print(path)
    if args.refresh_declared_python_interfaces:
        changed = refresh_declared_python_interfaces()
        print(f"refreshed declared Python interfaces: {len(changed)}")
        for path in changed:
            print(path)
    if args.normalize_prompt_reasons:
        changed = normalize_prompt_reasons()
        print(f"normalized prompt reasons: {len(changed)}")
        for path in changed:
            print(path)
    if args.complete_registered_prompt_metadata:
        changed = complete_registered_prompt_metadata()
        print(f"completed registered prompt metadata: {len(changed)}")
        for path in changed:
            print(path)
    if args.normalize_llm_interface_metadata:
        changed = normalize_llm_interface_metadata()
        print(f"escaped LLM interface metadata: {len(changed)}")
        for path in changed:
            print(path)
    if args.write_architecture:
        changed = write_architecture()
        print(f"updated architecture operations: {len(changed)}")
        for operation in changed:
            print(operation)
    if args.write_verification_profiles:
        changed = write_verification_profiles()
        print(f"restamped verification profiles: {len(changed)}")
        for prompt_path in changed:
            print(prompt_path)
    if args.write_requirement_rotations:
        changed = write_requirement_rotations()
        print(f"prepared requirement rotations: {len(changed)}")
        for identity in changed:
            print(identity)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
