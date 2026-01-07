## v0.0.104 (2026-01-06)

### Feat

- **Cloud Execution for `llm_invoke` (PR #249):** Added cloud-first execution with automatic local fallback. Key changes:
  - Add three new exception classes: `CloudFallbackError` (recoverable), `CloudInvocationError` (non-recoverable), `InsufficientCreditsError` (no fallback)
  - Add `use_cloud` parameter to `llm_invoke()`: None (auto-detect), True (force cloud), False (force local)
  - Implement `_llm_invoke_cloud()` to route LLM calls through `/llmInvoke` endpoint
  - Add `_pydantic_to_json_schema()` and `_validate_with_pydantic()` for cloud transport
  - Propagate `--local` CLI flag via `PDD_FORCE_LOCAL` environment variable
  - Graceful fallback to local execution on cloud errors (except insufficient credits)

### Fix

- **Prevent Duplicate Sync PRs:** Use fixed branch name (`pdd/sync-from-public`) instead of unique run_id-based names. Force-push to update existing branch and skip PR creation if one already exists. Prevents accumulation of duplicate sync PRs (was 8+ open).

- **Align ExtractedCode Schema with Prompt:** Added `focus` and `explanation` fields to `ExtractedCode` Pydantic model with default values. The `extract_code_LLM.prompt` asks for 3 JSON fields but the model only had 1, causing Gemini Flash to embed extra fields inside `extracted_code` string, resulting in invalid Python syntax and JSON markers leaking into code files.

- **Lower EXTRACTION_STRENGTH from 0.75 to 0.5:** At strength=0.75, target ELO was ~1458.5, causing Claude Opus (ELO 1465) to be selected for extraction/postprocessing. Lowering to 0.5 selects gemini-3-flash-preview (ELO 1430) instead, reducing costs from $5/$25 to $0.50/$3 per M tokens.

- **Narrow Console Boundary Bug (Issue #220, PR #227):** Fixed IndexError in `sync_animation.py` when console width is narrow (<=44 columns). The bug was an off-by-one boundary error in `_draw_connecting_lines_and_arrows()` where `max_x` could equal `console_width`, causing out-of-bounds array access.

### Tests

- Added 355+ lines of cloud execution tests in `test_llm_invoke.py` covering exception classes, Pydantic schema conversion, cloud execution paths (force local, force cloud, fallback), insufficient credits handling, and cloud detection.
- Added 185 lines of narrow console boundary tests in `test_narrow_console_boundary.py` (6 failing tests at widths 20-44, 2 passing at widths 45+).
- Added 91 lines of ExtractedCode schema tests in `test_postprocess.py` covering focus/explanation fields, JSON leakage prevention, and optional field validation.
- Added 44 lines of retry logic for flakey tests in `test_cmd_test_main.py` and `test_fix_main.py`.
- Added 433 lines of step 7 prompt tests in `test_agentic_bug_step7_prompt.py` for caller-mocking guidance (Issue #247).

### Docs

- Updated `postprocess_python.prompt` to reflect ExtractedCode schema changes.
- Updated `cli_python.prompt` with PDD_FORCE_LOCAL documentation.
- Updated `cloud_python.prompt` with llmInvoke endpoint.
- Updated `llm_invoke_python.prompt` with use_cloud parameter and cloud execution specifications.
- Rewrote `cli_example.py` with comprehensive CLI usage examples (430 lines).
- Rewrote `llm_invoke_example.py` with cleaner examples showing structured output, batch processing, and reasoning features (271 lines).
- Updated `agentic_bug_step7_generate_LLM.prompt` with caller-mocking guidance (20 lines added).
- Updated `agentic_bug_step9_pr_LLM.prompt` with PR description improvements.

## v0.0.103 (2026-01-05)

### Feat

- **Cloud Execution for `pdd bug` Command (PR #243):** Added cloud-first execution with automatic local fallback. Uses JWT authentication and posts to the `generateBugTest` endpoint. Non-recoverable errors (401/402/403/400) raise `UsageError`; recoverable errors (5xx, timeouts) fall back to local. Cloud request timeout set to 400s. Set `PDD_CLOUD_ONLY=1` or `PDD_NO_LOCAL_FALLBACK=1` to disable fallback.

- **Centralized Path Resolution Module (Issue #240, PR #241):** Added new `path_resolution.py` module with `PathResolver` dataclass for standardized file path resolution across the codebase. Supports four resolution profiles:
  - `resolve_include()`: cwd → package → repo fallback chain
  - `resolve_prompt_template()`: PDD_PATH → repo → cwd for prompts
  - `resolve_data_file()`: PDD_PATH only for data files
  - `resolve_project_root()`: PDD_PATH → marker → cwd for project detection

### Fix

- **Repo Root Fallback (Issue #240):** Fixed `get_file_path` to properly fall back to repo root when resolving include paths in installed-package scenarios.

### Tests

- Added 643+ lines of tests in `test_bug_main.py` covering cloud success paths, fallback scenarios, non-recoverable HTTP errors, and cloud-only mode.
- Added failing test for issue #240 repo root fallback behavior.

## v0.0.102 (2026-01-04)

### Feat

- **Git Worktree Isolation for Agentic Bug Workflow (PR #231):** Refactored `agentic_bug_orchestrator.py` to run bug investigations in isolated git worktrees. Each issue gets its own worktree at `.pdd/worktrees/fix-issue-{N}` with a dedicated branch `fix/issue-{N}`. Adds cleanup of stale worktrees/branches before starting. Prevents polluting the main branch during investigation.

- **Configurable Timeouts for Agentic Bug Steps (Issue #256):** Added `STEP_TIMEOUTS` dictionary with per-step timeout configuration. Complex steps (reproduce, root cause, generate) get 600s timeouts; simpler steps use 240s default. Added `timeout` parameter to `run_agentic_task()` and `_run_with_provider()`.

### Fix

- **Backward Compatibility with v0.0.99 Projects (Issue #251):** Fixed path resolution for projects lacking `outputs` templates in `.pddrc`. v0.0.99 projects now sync correctly with v0.0.100+ binaries.

- **CLI Results None Guard (Issue #253):** Added `results is not None` guard in `process_commands()` to prevent `TypeError: 'NoneType' object is not iterable` when results are None.

### Tests

- Added 636 lines of backward compatibility tests (`test_sync_backward_compat.py`) covering v0.0.99 projects, legacy `.pddrc`, mixed-version meta files, and bare projects.
- Added 168 lines of timeout configuration tests in `test_agentic_common.py`.
- Added regression tests for CLI None guard in `test_core_dump.py`.
- Updated `test_agentic_bug_orchestrator.py` to mock worktree setup.

## v0.0.101 (2026-01-03)

### Feat

- **Agentic Bug Investigation Workflow (Issue #153):** New 9-step automated workflow for investigating GitHub issues. Parses issue URL via `gh` CLI, fetches issue content/comments, and runs steps: duplicate detection, documentation check, triage, reproduction, root cause analysis, test plan design, test generation, verification, and PR creation. Includes hard-stop conditions (duplicate, feature request, user error, needs info) and context accumulation between steps.

- **Bidirectional Repository Sync:** Added `.sync-config.yml` for syncing files between `pdd` and `pdd_cap` repositories, including prompts, context files, and documentation.

- **Analysis Command Enhancements:** Added function namespaces to analysis prompts, improved output handling in examples, and better error handling.

### Fix

- **Firecrawl API 4.0+ Compatibility:** Updated API calls for newer Firecrawl versions.
- **Preprocess Tag Escaping:** Escape tag examples in `preprocess_python.prompt` (from pdd_cap PR #11).
- **ONBOARDING.md Sync Path:** Use `docs/*.md` pattern instead of root file.
- **Git Auth for CAP_REPO_TOKEN:** Use git config for token authentication in sync workflow.

### Tests

- Added 700+ lines of tests for agentic bug workflow (`test_agentic_bug.py`, `test_agentic_bug_orchestrator.py`).
- Added 250+ lines of analysis command tests (`tests/commands/test_analysis.py`).
- Added sync tests for construct paths, template discovery, and orchestration.

## v0.0.100 (2026-01-02)

### Feat

- **Cloud Execution for `pdd crash` and `pdd verify` Commands (PR #218):** Added cloud-first execution with automatic local fallback for both commands. Uses JWT authentication via `CloudConfig.get_jwt_token()` and posts to the `crashCode` and `verifyCode` endpoints. Supports hybrid mode for loop iterations—local program execution with cloud LLM calls. Set `PDD_CLOUD_ONLY=1` or `PDD_NO_LOCAL_FALLBACK=1` to disable fallback. Non-recoverable errors (401/402/403/400) raise `UsageError`; recoverable errors (5xx, timeouts) fall back to local.

### Docs

- Updated `crash_main_python.prompt` and `fix_verification_main_python.prompt` with cloud execution strategy documentation.

### Tests

- Added 374+ lines of tests in `test_crash_main.py` covering cloud success paths, fallback scenarios, and hybrid loop mode.
- Added 221+ lines of tests in `test_fix_main.py` for cloud execution coverage.

### Fix

- Fixed patch target in test mocking and removed outdated comment.

## v0.0.99 (2026-01-01)

### Feat

- **Cloud Hybrid Mode for `pdd fix` Command (PR #214, #217):** Added cloud execution support for fix command with hybrid mode—LLM calls go to the cloud while test execution stays local. Includes single-pass cloud fix mode with automatic fallback and iterative cloud hybrid mode with cumulative cost tracking. Added `fixCode` to CLOUD_ENDPOINTS.

- **Extensible Output Path Templates (Issue #237):** Fixed construct_paths to use prompt file path for context detection, resolving bugs where example paths were generated incorrectly (e.g., `context/credit_helpers_example.py` instead of `context/backend/credit_helpers_example.py`).

- **Strict JSON Schema Mode for LLM Responses:** Changed `llm_invoke.py` from loose `json_object` mode to strict `json_schema` mode, preventing CodeFix validation errors when LLM omits required fields.

### Fix

- **Keychain Write Failure Handling:** Handle `-25299` keychain error when storing rotated refresh tokens.
- **Code Spans Directive Fix (PR #212):** Ignore directives inside code spans during preprocessing.
- **Construct Paths Fixes:** Multiple fixes for `examples_dir` determination and outputs config usage in path generation.

## v0.0.98 (2025-12-31)

### Feat

- **Cloud Execution for `pdd test` Command (PR #206):** Added cloud-first execution with automatic local fallback. Uses JWT authentication via `CloudConfig.get_jwt_token()` and posts to the `generateTest` endpoint. Supports both generate and increase (coverage augmentation) modes. Non-recoverable errors (402 insufficient credits, 401/403 auth errors, 400 validation) raise `UsageError`; recoverable errors (5xx, timeouts, network issues) fall back to local. Set `PDD_CLOUD_ONLY=1` or `PDD_NO_LOCAL_FALLBACK=1` to disable fallback.

- **Suspicious Files Check in Release:** Added check for single-letter files (C, E, T) during the release process to catch LLM artifacts before publishing.

### Docs

- Updated `cmd_test_main_python.prompt` with cloud vs local execution strategy documentation and added context examples for JWT token retrieval and cloud function calls.

### Tests

- Added 575+ lines of tests in `tests/test_cmd_test_main.py` covering cloud success paths, fallback scenarios, non-recoverable HTTP errors, cloud-only mode, and local mode bypass.

## v0.0.97 (2025-12-30)

### Feat

- **CLI Examples Display:** After each command step, the CLI now displays examples used for grounding (slug and title), helping users know what to use in `<pin>` or `<exclude>` tags.

- **Suspicious Files Diagnostic Logging (Issue #186):** Added `_detect_suspicious_files()` in `agentic_fix.py` to detect and log when single-character files (C, E, T) are created during agentic operations. Logs include timestamp, context, directory, file sizes, and stack trace. Persistent log saved to `~/.pdd/suspicious_files.log`.

- **Cloud Example Generation:** Added cloud execution support to `context_generator_main` via async `_run_cloud_generation()` function. Uses JWT authentication with automatic local fallback on cloud failure.

- **Improved Syntax Repair:** Rewrote `_validate_and_fix_python_syntax()` with a binary search algorithm to find the longest valid Python prefix when LLM output contains trailing JSON garbage (e.g., `"explanation":` metadata).

### Fix

- **Nested asyncio.run() Bug (PR #204):** Fixed `pdd example` command failing to make cloud calls due to nested asyncio.run() error. The issue occurred because `CloudConfig.get_jwt_token()` uses asyncio.run() internally, causing conflicts when called from within an async context. Fixed by acquiring JWT token before entering the async context. (Thanks Jiamin Cai!)

- **HTTPStatusError Response Text:** Fixed error handling to check for empty `.text` instead of checking if response exists (response is always present on HTTPStatusError).

- **Test Overwrite Bug:** Fixed sync bug that would overwrite existing tests. Now uses append mode when merging with existing tests via the `--merge` flag.

- **CLI Test Fixture:** Fixed test fixture checking for "install_completion" instead of "install-completion" (Click converts underscores to hyphens in command names).

### Refactor

- **Existing Tests as Lists:** Changed `existing_tests` parameter from string path to list of paths in prompts, enabling multiple test files to be concatenated for context.

- **Test File Organization:** Moved `tests/test_core_cli.py` to `tests/core/test_cli.py` for better module organization.

### Docs

- Clarified `existing_tests` parameter behavior in `cmd_test_main_python.prompt`, documenting that it accepts a list of test file paths.

### Tests

- Added regression tests for nested asyncio.run() bug in `test_context_generator_main.py`.
- Updated `test_cmd_test_main.py` with coverage for test file append mode and existing_tests list handling.

## v0.0.96 (2025-12-29)

### Feat

- **Cloud Example Generation:** Added cloud execution support to `context_generator_main` via new async `_run_cloud_generation()` function. Uses `CloudConfig.get_jwt_token()` for authentication and automatically falls back to local execution on cloud failure. Supports `--local` flag to bypass cloud.

- **Improved Syntax Repair:** Rewrote `_validate_and_fix_python_syntax()` with a binary search algorithm to find the longest valid Python prefix when LLM output contains trailing JSON garbage (e.g., `"explanation":`, `"filename":` metadata). Provides user feedback on repair success/failure.

### Refactor

- **Prompt Include Tag Updates:** Standardized `<include>` tags in `context_generator_main_python.prompt` and `preprocess_python.prompt` to use consistent naming conventions (e.g., `<context.module_name>` wrappers).

### Tests

- Updated `tests/test_context_generator_main.py` with coverage for cloud execution, local fallback, and syntax repair scenarios.

## v0.0.95 (2025-12-28)

### Feat

- **`--directory` Option for Update Command:** Added `--directory` flag to the `update` command, allowing users to specify a subdirectory to scan in repository-wide mode instead of scanning from the repo root.

### Fix

- **Reject Suspicious LLM-Generated Paths (Issue #187):** Added `_is_suspicious_path()` function to `agentic_fix.py` that rejects single/double-character filenames (e.g., 'C', 'E', 'T'), template variables (e.g., '{path}', '{code_abs}'), and dot-only paths. This prevents LLM artifacts from being written to disk when agents produce malformed output markers.

- **Sync Only Files from Triggering Commit:** Fixed the `sync-from-public.yml` workflow to sync only files changed in the specific triggering commit, not all differences from `public/main`. This prevents inadvertently reverting private-only changes. Added conflict detection and warnings for files with local modifications.

- **Fix `get_language()` Call in Update:** Corrected `find_and_resolve_all_pairs()` to pass file extension to `get_language()` instead of the full path.

### Refactor

- **Remove langchain_core Dependency:** Removed `langchain_core` from dependencies. Replaced `PromptTemplate.from_template()` with native Python `str.format()` in `llm_invoke.py`, updating error messages from 'prompt template' to 'prompt string'.

- **LLM Invocation Prompt Reorganization:** Streamlined `prompts/llm_invoke_python.prompt` documentation for clarity.

### Docs

- **PDD Doctrine - Context Window Advantage:** Expanded `docs/prompt-driven-development-doctrine.md` with ~100 lines explaining how PDD's batch architecture eliminates agentic overhead, allowing 100% of the context window to be used for generation vs. competing with tool definitions and chat history.

### Tests

- Added 230+ lines of tests in `tests/test_agentic_fix.py` covering suspicious path detection, template variable rejection, and integration tests verifying files like 'C', 'E', 'T' are not written to disk.

## v0.0.94 (2025-12-27)

### Feat

- **Custom prompts_dir Support in Update Command (Issue #86):** Fixed `resolve_prompt_code_pair()` to use context-aware `prompts_dir` from `.pddrc` instead of hardcoding `prompts/` at repo root. Added shared `_match_path_to_contexts()` helper function in `construct_paths.py` that provides core pattern matching logic for both `_detect_context()` and `detect_context_for_file()`.

- **Enhanced Test File Discovery:** Added `tests_dir` parameter support from `.pddrc` configuration in `_discover_test_files()`. Now searches in this priority order: configured tests_dir → tests/ relative to code → same directory → sibling tests/ (../tests/) → project root tests/.

- **Target Coverage Defaults:** Changed default `--target-coverage` from 0.0 to 90.0 in `sync_main` and `sync_orchestration`. Improved CLI option handling in maintenance commands to correctly pass `None` when no coverage target specified.

- **Anthropic Result Parsing Update:** Updated `_parse_anthropic_result()` to prioritize `result` key for Claude Code output format while maintaining `response` for backward compatibility.

- **Agent Output Markdown Rendering:** Updated `run_agentic_update()` to display agent output with Markdown formatting when updates succeed, improving readability of agent responses.

- **Prose Field Detection in LLM Invoke:** Added `_PROSE_FIELD_NAMES` constant and `_is_prose_field_name()` helper to skip Python syntax validation on known prose fields (reasoning, explanation, analysis, etc.) that may mention code patterns but aren't actual code.

- **Prompting Guide in Agentic Update:** Added `<include>docs/prompting_guide.md</include>` to `agentic_update_LLM.prompt` so agents follow PDD best practices when updating prompts. Also improved test file discovery instructions to search sibling directories.

### Fix

- **Wheel Packaging for Agentic Update Prompt:** Added special curly brace escaping in `preprocess_wheel.py` for `agentic_update_LLM.prompt` to handle code examples in the included prompting guide that would otherwise break Python's `str.format()`.

- Remove Python syntax warnings across codebase.

### Data

- Added 'global' tag to Google models in `data/llm_model.csv` for fixing the missing model by location issues.

### Tests

- Added regression test for Issue #86 (prompts_dir configuration).
- Added tests for custom tests_dir discovery in `test_agentic_update.py`.
- Added tests for target coverage CLI handling in `test_commands_maintenance.py`.
- Added tests for Anthropic result parsing with 'result' key in `test_agentic_common.py`.
- Added tests for Markdown rendering of agent output.

## v0.0.93 (2025-12-27)

### Feat

- **Non-Python Agentic Fallback (Issue #189):** For non-Python languages that lack verification commands (Java without Maven/Gradle, etc.), fix loops now directly trigger agentic fallback instead of raising an error. `sync_orchestration` sets `max_attempts=0` for non-Python languages to skip iterative loops and go straight to agentic fallback. Affects `fix_code_loop`, `fix_error_loop`, and `fix_verification_errors_loop`.

- **Language Parameter Propagation:** Added `language` parameter to `llm_invoke()`, `code_generator()`, and related functions for improved language-specific handling and output schema support.

- **Makefile Update Command:** Added `make update [MODULE=name]` target for updating prompts based on code changes using git diff.

- **.env File Key Management (Issue #183):** Improved `_save_key_to_env_file()` to replace existing keys in-place (no comment + append accumulation), remove old commented versions of the same key, and use CWD-based project root when `PDD_PATH` points to a package directory.

### Fix

- **Vertex AI Credentials in Retry (Issue #185):** Fixed retry calls in `llm_invoke()` to include `vertex_credentials`, `vertex_project`, and `vertex_location` parameters. Previously retries would fail because LiteLLM defaulted to `us-central1` when these were missing.

- Remove temporary 'NEW PARAMETER' comment.

### Tests

- Added 286 lines of tests in `tests/test_llm_invoke_vertex_retry.py` covering Vertex AI credential propagation in retry code paths (None content, malformed JSON, invalid Python).
- Added 440 lines of tests in `tests/test_sync_orchestration.py` for non-Python agentic fallback behavior, verifying `max_attempts=0` is passed for crash, verify, and fix operations.

## v0.0.92 (2025-12-25)

### Feat

- **Centralized Cloud Configuration:** Added `pdd/core/cloud.py` module providing `CloudConfig` class for consistent cloud URL configuration and JWT token handling across all cloud-enabled commands. Supports `PDD_CLOUD_URL` for testing against different environments (local emulator, staging, production) and `PDD_JWT_TOKEN` for pre-injected tokens in CI/CD pipelines.

- **Subdirectory Basename Support:** Updated `generate_output_paths`, `sync_main`, and `sync_orchestration` to handle module basenames with subdirectory paths (e.g., `core/cloud`). Directory structure is preserved in output filenames: `core/cloud` with pattern `test_{basename}.py` produces `core/test_cloud.py`.

- **Enhanced Cloud Error Handling:** Cloud code generation now distinguishes between recoverable errors (5xx, timeouts → local fallback) and non-recoverable errors (401 auth, 402 insufficient credits, 403 access denied, 400 validation → immediate failure with clear error message). Added `PDD_CLOUD_ONLY` and `PDD_NO_LOCAL_FALLBACK` env vars to disable local fallback.

- **CI/Headless Mode Detection:** Added automatic TTY detection for CI/non-interactive environments. When `--force` is set and running in headless mode (non-TTY), API key prompts are skipped and cloud authentication failures fail gracefully instead of blocking on user input.

### Fix

- **Path Resolution Mismatch (Issue #177):** Fixed `sync_orchestration` to use absolute paths when calling `code_generator_main` and `context_generator_main`, preventing path resolution mode conflicts between sync (`cwd`) and generate (`config_base`). Also ensures output directories exist before writing.

- **Package Include Resolution (Issue #175):** `preprocess.py` now falls back to package directory when resolving `<include>` directives, allowing bundled docs like `docs/prompting_guide.md` to be found after pip/wheel installation.

- **Sync Log Subdirectory Handling:** All sync log and fingerprint file operations now use `_safe_basename()` to properly handle subdirectory basenames in filenames.

- **Prompt Tag Typo:** Corrected `<proompt_content>` to `<prompt_content>` in agentic fix prompt.

- **Agentic Test Fixtures:** Renamed `code.py` to `buggy.py` in agentic test fixtures to avoid confusion with module names.

### CI

- **Package Install Test Workflow:** Added `.github/workflows/package-test.yml` to validate that packaged PDD correctly resolves `<include>` directives for bundled docs when installed via pip/wheel (not editable install).

### Tests

- Added 266 lines of tests in `tests/core/test_cloud.py` covering `CloudConfig` URL resolution, JWT token handling, and environment variable precedence.
- Added subdirectory basename tests in `test_generate_output_paths.py` and `test_sync_orchestration.py`.
- Added headless mode and force flag tests across sync and code generator modules.

## v0.0.91 (2025-12-24)

### Feat

- **Backup Directory Organization (Issue #174):** Moved all fix loop backup files from polluting source/test directories to `.pdd/backups/{module}/{timestamp}/` directory. Previously, backups like `module_1.py`, `module_2.py` would clutter the source directory; now they're stored as `.pdd/backups/module/20251224_143052/code_1.py` etc. Affects `fix_code_loop`, `fix_error_loop`, and `fix_verification_errors_loop`.

- **Schema Validation Fallback (Issue #168):** Added `SchemaValidationError` exception to `llm_invoke.py`. When Pydantic/JSON schema validation fails, the error now triggers model fallback to try the next candidate model instead of just logging and skipping to the next batch item. This fixes cases where a model consistently returns malformed structured output.

### Docs

- **PDD Doctrine - The Mold Paradigm:** Expanded `docs/prompt-driven-development-doctrine.md` with ~300 lines covering the manufacturing analogy (wood carving → injection molding), the three capitals (test, prompt, grounding), tests as specification vs verification, compound returns of mold refinement, skill evolution for developers, and the complete analogy mapping table.

### Data

- **LLM Model Catalog Update:** Updated `data/llm_model.csv`:
  - Updated GLM model from 4p6 to 4p7 with revised pricing ($0.60/$2.20)
  - Enabled structured output (`True`) for DeepSeek v3.2-maas on Vertex AI

### Deps

- Updated `litellm[caching]` to version 1.80

### Tests

- Added ~700 lines of tests across `test_llm_invoke.py` and new `test_llm_invoke_integration.py` covering schema validation fallback behavior and model fallback on validation errors.
- Added backup location verification tests in `test_fix_code_loop.py`, `test_fix_error_loop.py`, and `test_fix_verification_errors_loop.py` ensuring backups are created in `.pdd/backups/` directory.

## v0.0.90 (2025-12-23)

### Feat

- **Path Resolution Mode Parameter:** Added `path_resolution_mode` parameter to `construct_paths` and `generate_output_paths` with two modes: `"cwd"` (resolve relative to current working directory) and `"config_base"` (resolve relative to `.pddrc` location). Sync uses `"cwd"` by default while other commands use `"config_base"`, enabling proper path handling when running from subdirectories.

- **Multi-File Test Support:** Enhanced `sync_orchestration` to support multiple test files matching `test_{basename}*.py` pattern. Calculates hashes for all matching test files and runs pytest on all of them, with `test_files` field added to `RunReport` for staleness tracking.

- **Allow Zero Max Attempts:** The `--max-attempts 0` option is now valid, allowing users to skip fix attempts entirely and proceed directly to agentic fallback.

### Fix

- **Path Resolution Regression (Issue #169):** Fixed sync path resolution when running from a subdirectory. Previously, relative paths in `.pddrc` could resolve incorrectly when `pdd sync` was invoked from a project subdirectory rather than the project root.

- **Atomic State Updates (Issue #159):** Added `AtomicStateUpdate` context manager to ensure `run_report` and fingerprint files are written atomically using temp file + rename pattern. Prevents state desynchronization when operations are interrupted mid-write.

- **Infinite Crash Loop Prevention (Bug #157):** Added `MAX_CONSECUTIVE_CRASHES = 3` limit to break infinite crash retry loops. Sync now detects when the same crash operation repeats without progress and exits with an error.

- **Fix Validation (Issue #158):** The `fix_main` function now validates LLM-suggested fixes by running tests after applying changes, instead of trusting the LLM's `update_code`/`update_unit_test` flags. Fixes are only reported as successful if tests actually pass.

### Tests

- Added 535 lines of tests in `tests/test_generate_output_paths.py` covering path resolution modes for all commands.
- Added 180+ lines of path resolution mode tests in `tests/test_construct_paths.py`.
- Added atomic state update tests in `tests/test_sync_orchestration.py`.
- Added PDD_PATH fixture for test isolation in `tests/conftest.py`.

## v0.0.89 (2025-12-22)

### Feat

- **Agentic Module Suite:** Added `agentic_common.py` with shared utilities for multi-provider CLI tool invocation (Claude, Gemini, Codex), including token pricing, cost tracking, and logging. New `agentic_crash.py`, `agentic_update.py`, and `agentic_verify.py` modules enable agentic workflows for crash handling, prompt updates, and verification.

- **`--simple` Flag for Update Command:** Added `--simple` flag to bypass agentic routing and use legacy `update_prompt()` path directly.

- **Self-Referential Dependency Filtering:** `auto_include` and `insert_includes` now filter out dependencies that reference the module's own prompt file, preventing circular includes.

- **Sync Auto-Deps Regeneration:** Sync now always regenerates code after `auto-deps` completes, even if code files exist (previously stale code could persist).

- **Prompt Change Priority:** Sync decision logic now prioritizes prompt changes over runtime signals, ensuring modified prompts trigger regeneration.

### Fix

- **4 Critical P0 Sync Bugs:** Fixed `skip_verify` flag not skipping crash operation; fixed stale run report processing when fingerprint is missing; fixed `skip:` prefix detection in workflow completion checks; fixed orphaned run report handling.

- **Infinite Loop Prevention:** Fixed sync orchestration infinite loop when auto-deps completed but code existed.

- **Pytest Path Resolution:** Fixed pytest invocation path issues in test execution.

- **Test File Preservation:** Ensured test files are preserved during sync operations.

### Tests

- Added ~3,300 lines of new tests across 18 test files covering agentic modules, sync operations, and edge cases. Key additions: `test_agentic_common.py` (465 lines), `test_agentic_crash.py` (432 lines), `test_agentic_update.py` (404 lines), `test_agentic_verify.py` (294 lines), expanded `test_sync_determine_operation.py` (+495 lines).

## v0.0.88 (2025-12-19)

### Feat

- **Multi-Test File Support for Fix Command:** The `pdd fix` command now accepts multiple unit test files as arguments. Each test file is processed separately by the LLM, enabling targeted fixes per test file rather than concatenating all tests into a single blob. Results are aggregated with overall success requiring all individual fixes to succeed.

- **Numbered Test Output Files:** The `test` and `bug` commands now automatically create numbered output files (e.g., `test_module_1.py`, `test_module_2.py`) when the output file already exists and `--force` is not specified, preventing accidental overwrites while maintaining workflow continuity.

- **Multi-File Existing Tests for Test Command:** The `--existing-tests` option in `cmd_test_main` now accepts multiple test file paths. All test file contents are concatenated and provided to the LLM for context-aware test generation.

Many thanks to Jiamin Cai for your contributions!

### Fix

- **Setup Tool Shell Escaping:** Fixed a security and correctness issue where API keys containing special shell characters (`$`, `"`, `'`, `\`) would generate malformed shell scripts. Now uses `shlex.quote()` for proper POSIX shell escaping across bash, zsh, fish, and csh variants. Thank you to Dhruv Garg for your contributions!

- **Makefile Commit Order:** Adjusted commit order for public repository updates to ensure proper synchronization.

### Tests

- Added 574 lines of comprehensive tests for `setup_tool.py` in `tests/test_setup_tool.py` covering shell script generation with special characters for bash, zsh, fish, and csh.

- Added regression test #21 for multi-test file fix workflow, verifying end-to-end LLM-based fixes across multiple test files.

- Added tests for numbered test file output in `tests/test_construct_paths.py` verifying automatic file numbering behavior.

- Added tests for multi-file existing tests handling in `tests/test_cmd_test_main.py`.

## v0.0.87 (2025-12-18)

### Feat

- **Centralized Config Resolution:** Added `pdd/config_resolution.py` module providing a single source of truth for resolving `strength`, `temperature`, and `time` values. Ensures consistent priority ordering across all commands: CLI global options (highest) → `.pddrc` context defaults → hardcoded defaults (lowest). Updated `crash_main`, `cmd_test_main`, and `change_main` to use `resolve_effective_config()`.

- **Groq Structured Output Workaround:** Added special handling in `llm_invoke.py` for Groq models, which have issues with tool-based structured output. When using Groq, the system now uses JSON object mode with the schema injected into the system prompt, avoiding tool_use failures.

- **Workflow Completion Test Validation:** Fixed `_is_workflow_complete()` in `sync_determine_operation.py` to verify that tests have actually been run (not just verify). Prevents false positive workflow completion when `skip_verify=True` but tests are still required. Thanks Jiamin Cai for your contributions!

- **Run Report Test Hash Tracking:** Enhanced `sync_orchestration.py` to include `test_hash` in `RunReport` when saving run reports after example execution, enabling proper staleness detection.

### Fix

- **CLI Strength/Temperature Defaults:** Changed CLI `--strength` and `--temperature` options to `default=None` instead of hardcoded values. This allows `.pddrc` defaults to take effect when CLI options aren't explicitly provided.

### Data

- **LLM Model Catalog Update:** Updated `data/llm_model.csv` with latest models and configurations:
  - Added Gemini 3 Flash Preview and updated Gemini 3 Pro Preview ELO scores
  - Added GPT-5.2 (replacing GPT-5.1-2025-11-13)
  - Added GPT-5.1-codex-max
  - Updated DeepSeek to v3.2-maas with global region
  - Updated GLM to 4p6 with revised pricing
  - Updated Claude max_reasoning_tokens to 128000
  - Revised ELO scores across multiple models

### Docs

- **Gemini Setup Guide:** Expanded `SETUP_WITH_GEMINI.md` with improved configuration guidance and examples.

### Tests

- Added 240+ lines of TRUE end-to-end tests in `tests/test_pddrc_true_e2e.py` verifying:
  - Real `.pddrc` strength/temperature values reach final functions
  - CLI options properly override `.pddrc` defaults
  - Priority ordering works correctly through actual data flow

- Added 170+ lines of workflow completion tests in `tests/test_sync_determine_operation.py` covering:
  - Test requirement validation in `_is_workflow_complete()`
  - Fingerprint command checking for test completion

- Added 100+ lines of config resolution tests in `tests/test_cmd_test_main.py` and `tests/test_core_cli.py` verifying proper strength/temperature handling.

## v0.0.86 (2025-12-17)

### Feat

- **`--dry-run` Flag for Sync Command:** Renamed the `--log` flag to `--dry-run` for clearer semantics. The `--dry-run` flag analyzes sync state without executing operations, showing what sync would do. The old `--log` flag is deprecated with a warning directing users to use `--dry-run` instead.

- **Mock vs Production Code Guidance in LLM Prompts:** Added comprehensive guidance to `fix_verification_errors_LLM.prompt` and `find_verification_errors_LLM.prompt` for distinguishing mock configuration errors from production code errors. Prompts now instruct the LLM to:
  - Identify test files using mocks (MagicMock, unittest.mock, patch)
  - Check mock setup FIRST when errors occur (wrong `return_value` structure, missing `__getitem__` configuration)
  - Preserve production code API usage patterns unless documentation proves otherwise
  - Follow a diagnosis priority: mock configuration → mock chaining → production code

- **Unit Test Auto-Discovery Regression Test:** Added regression test #20 to `tests/regression.sh` that validates the `generate` command's unit test auto-discovery feature. Tests both `--exclude-tests` mode (no context, expects failure) and default auto-discovery mode (expects success).

- **Encode Message Prompt:** Added `prompts/encode_message_python.prompt` as a simple prompt for testing unit test auto-discovery and regression test scenarios.

### Fix

- **Verification Success Tracking Bug:** Fixed a critical bug in `fix_verification_errors_loop` where the function incorrectly reported "No improvement found" when secondary verification passed but the issue count didn't decrease. Added `any_verification_passed` flag that tracks when code was actually changed AND secondary verification passed. The function now correctly returns `success=True` when verification passes, even if the LLM's issue count assessment is unchanged. This ensures code that compiles and runs correctly is recognized as successful. Key changes:
  - Track `any_verification_passed` separately from best iteration tracking
  - Only set flag when `code_updated=True` AND verification passes
  - Return `success=True` with `final_issues=0` when verification passed

### Refactor

- **Remove Unused Warnings Import:** Cleaned up unused `warnings` import from `pdd/commands/maintenance.py`.

- **Error Fixing Loop Prompt Simplification:** Streamlined `prompts/fix_verification_errors_loop_python.prompt` from 123 lines to 63 lines by:
  - Condensing implementation details into "behavior defined by test suite" directive
  - Listing key behaviors to implement without step-by-step instructions
  - Focusing on inputs/outputs and test compliance

### Docs

- **Prompting Guide Major Update:** Significantly expanded `docs/prompting_guide.md` with ~200 lines of new content:
  - **Automated Grounding (PDD Cloud):** Explains how vector embedding and similarity search automatically provides few-shot examples during generation
  - **Grounding Overrides:** Documents `<pin>module_name</pin>` and `<exclude>module_name</exclude>` tags for controlling automatic example retrieval
  - **Three Pillars of PDD Generation:** New section explaining how Prompt (WHAT), Grounding (HOW), and Tests (CORRECTNESS) work together
  - **Prompt Abstraction Guidance:** Added 10-30% prompt-to-code ratio target with clear guidelines on what NOT to include in prompts
  - **Non-Deterministic Tag Warnings:** Added explicit warnings about `<shell>` and `<web>` tags introducing environment-dependent behavior
  - **Requirements Writing Guide:** Expanded with before/after examples and testability criteria

### Tests

- Added 320+ lines of verification loop tests in `tests/test_fix_verification_errors_loop.py` covering:
  - Verification passes but issue count unchanged (regression test for the bug)
  - Best iteration restored with verification passed
  - Proper `any_verification_passed` flag behavior
  - Success determination based on verification outcome vs issue count

- Added 130+ lines of maintenance command tests in `tests/test_commands_maintenance.py` covering:
  - `@track_cost` decorator verification for sync and auto-deps commands
  - Deprecated `--log` flag warning emission and `dry_run=True` propagation
  - `click.Abort` re-raising (not caught by generic error handlers)
  - Error handling with correct arguments to `handle_error`
  - `ctx.obj=None` graceful handling in setup command

- Added 68 lines of static prompt tests in `tests/test_mock_vs_production_fix.py` verifying:
  - `fix_verification_errors_LLM.prompt` contains mock guidance section, mentions MagicMock, `__getitem__` pattern, and prioritizes mock fixes
  - `find_verification_errors_LLM.prompt` has mock identification step

- Added 154-line integration test script `tests/test_mock_fix_integration.sh` for validating LLM behavior with mock vs production code scenarios

## v0.0.85 (2025-12-16)

### Feat

- **Unit Test Inclusion in Code Generation:** Added `--unit-test` and `--exclude-tests` options to the `generate` command. When `--unit-test <file>` is specified, the test file content is included in the prompt wrapped in `<unit_test_content>` tags, enabling the LLM to generate code that passes specific tests. When neither option is provided, PDD automatically discovers and includes test files matching `test_{code_stem}*.py` from the configured `tests_dir`. Use `--exclude-tests` to disable automatic test file discovery.

Many thanks to Jiamin Cai for your contributions on the unit test inclusion feature!

- **Example Error Detection:** Implemented `_detect_example_errors()` and `_run_example_with_error_detection()` in `sync_orchestration.py` to detect true crashes/errors in example outputs. Detects Python tracebacks and ERROR-level log messages while intentionally ignoring HTTP status codes (examples may test error responses) and exception type names in logs (prevents false positives). For server-style examples that block, runs until timeout then analyzes output for errors—no errors means success.

- **Bytecode Filtering in Directory Summarization:** Added filtering to `summarize_directory()` to skip `__pycache__` directories and `.pyc`/`.pyo` bytecode files, preventing noise in directory summaries.

### Fix

- **Update Command Mode Detection:** Fixed the `update` command to properly distinguish between single-file mode and repository-wide mode. When a single positional argument is provided, it's now correctly treated as the code file (not the prompt file), enabling `pdd update <CODE_FILE>` to generate a new prompt. Added validation to prevent mixing file-specific flags (`--git`, `--input-code`) with repository-wide mode, and `--extensions` with single-file mode.

Many thanks to Jiamin Cai for your contributions to the update fix!

- **Output Formatting and File Handling:** Corrected output formatting in code generation and test files. Replaced `os.remove()` with `Path.unlink()` for more robust file handling with pathlib.

- **Test Path Resolution:** Updated `PDD_PATH` in tests to point to the 'pdd' directory for accurate file resolution. Fixed test output directory path to use project root and ensured test file cleanup after execution.

### Refactor

- **Sync Regression Script:** Updated `sync_regression.sh` to check for generated Python files in the `src/` directory, enhancing file location handling and error logging.

### CI

- **Public Repo Sync Workflow:** Added `.github/workflows/sync-from-public.yml` GitHub Actions workflow to automatically sync changes from public repositories (`promptdriven/pdd` and `promptdriven/pdd_cap`). Creates PRs with changed files from specified patterns (Python modules, tests, configs) and runs tests before PR creation.

### Docs

- **Prompting Guide:** Expanded the prompting guide with improved guidance and examples.

- **README:** Enhanced README with documentation for the new `--unit-test` and `--exclude-tests` options in the `generate` command.

### Tests

- Added 230+ lines of unit test inclusion tests in `tests/test_code_generator_main.py` covering:
  - Explicit `--unit-test` file inclusion with content wrapped in `<unit_test_content>` tags
  - Front matter conflict handling (test files that look like they have front matter)
  - Automatic test file discovery based on code filename pattern
  - `--exclude-tests` flag preventing automatic inclusion
  - Explicit unit test file precedence over automatic discovery

- Added 109 lines of example error detection tests in `tests/test_example_error_detection.py` verifying:
  - Python traceback detection (catches all unhandled exceptions)
  - ERROR-level log message detection
  - No false positives for exception names in log messages
  - No false positives for HTTP status codes
  - Clean success output handling

- Added 135+ lines of update command tests in `tests/test_commands_modify.py` covering:
  - Repository-wide mode with no arguments
  - Single-file mode treating argument as code file
  - `--extensions` flag validation (repo mode only)
  - `--git` flag validation (file mode only)

- Enhanced `tests/test_summarize_directory.py` with tests for `__pycache__` and `.pyc` file filtering.

- Enhanced exception handling in `tests/test_insert_includes.py` by mocking file opening.

## v0.0.84 (2025-12-15)

### Feat

- **True Agentic Mode for CLI Agents:** Rewrote `_run_openai_variants()`, `_run_anthropic_variants()`, and `_run_google_variants()` in `pdd/agentic_fix.py` to invoke agents in full agentic mode with file tool access. Previously, agents were invoked in completion/print mode (`-p` flag for Claude and Gemini, `--sandbox read-only` for Codex) which prevented file modifications. Now agents write prompts to temp files and receive instructions to read them, enabling full read/write file access for autonomous fixes.

- **Agentic Fallback Prompt for Test Failures:** Added `prompts/agentic_fix_explore_LLM.prompt` providing structured guidance for agentic fallback when PDD's normal fix loop fails. The prompt explains PDD principles (prompt is source of truth), lists available files, shows previous fix attempts to avoid repetition, and outlines the task workflow for diagnosing and fixing test failures.

- **Strength/Temperature Propagation to Sub-Commands:** Updated `fix_main()`, `crash_main()`, `fix_verification_main()`, `cmd_test_main()`, and `update_main()` to accept optional `strength` and `temperature` parameters. These parameters are resolved with precedence: function parameter → `ctx.obj` → default constant. This enables `sync_orchestration` to pass explicit values that override CLI context defaults.

- **Click Context Parameters Documentation:** Added `context/ctx_obj_params.prompt` documenting the standard `ctx.obj` dictionary keys available in PDD CLI commands (`verbose`, `strength`, `temperature`, `time`, `force`, `quiet`, `context`, `confirm_callback`) and the resolution pattern for optional parameters.

### Fix

- **Auto-Deps Directory Path Bug:** Fixed `sync_orchestration.py` to pass the examples directory path (`examples_dir`) to `auto_deps_main()` instead of a glob pattern (`f"{examples_dir}/*"`). The glob pattern caused `os.path.isdir()` to return `False`, preventing recursive file discovery in subdirectories. Added regression test `test_auto_deps_passes_directory_not_glob_pattern`.

- **Sync Orchestration Parameter Propagation:** Updated all operation calls in `sync_orchestration()` (`crash_main`, `fix_verification_main`, `cmd_test_main`, `fix_main`, `update_main`) to pass `strength=strength` and `temperature=temperature` parameters, ensuring `.pddrc` configuration values propagate correctly through the sync workflow.

### Docs

- **Onboarding Documentation Enhancements:** Updated `docs/ONBOARDING.md` with:
  - Clarification that developers/contributors must use a Conda environment (not UV) for development
  - Instructions for creating and activating the `pdd` conda environment
  - Recommended test execution order: unit tests → regression tests → sync regression tests
  - Note on API key requirements explaining that some tests require multiple providers (OpenAI + at least one other)

- **Prompt Template Cleanup:** Updated 15+ prompt files to include `ctx_obj_params.prompt` reference for Click context details and removed outdated Click examples to streamline documentation.

### Tests

- Added 156 lines of agentic mode invocation tests in `tests/test_agentic_fix.py` verifying:
  - Claude is NOT invoked with `-p` flag (which prevents file tool access)
  - Codex is NOT invoked with `--sandbox read-only` (which prevents file writes)
  - Gemini is NOT invoked with `-p` flag (which prevents tool access)

- Added 175 lines of strength/temperature propagation tests in `tests/test_sync_orchestration.py` using source code inspection to verify all sub-command calls include `strength=strength` parameter.

- Added 72 lines of `.pddrc` configuration hierarchy tests in `tests/test_construct_paths.py` verifying that `.pddrc` values are used when CLI doesn't pass explicit values, and explicit CLI values override `.pddrc`.

## v0.0.83 (2025-12-14)

### Feat

- **Multi-Language Test Execution:** Added `pdd/get_test_command.py` module that resolves appropriate test commands based on file language using a three-tier resolution order: (1) CSV `run_test_command` column, (2) smart detection via `default_verify_cmd_for()`, (3) None (triggers agentic fallback). This enables the sync workflow to run tests for TypeScript, Go, Rust, and other languages instead of only Python.

- **Language Format CSV Enhancement:** Added `run_test_command` column to `data/language_format.csv` with language-specific test runners: `python -m pytest {file} -v` for Python, `go test -v {file}` for Go, `cargo test` for Rust, `swift test` for Swift, and `dotnet test` for C#. Supports `{file}` placeholder substitution.

- **Multi-Language Test Output Parsing:** Added `_parse_test_output()` function to `sync_orchestration.py` that extracts passed/failed/coverage metrics from test runner output for Python (pytest), JavaScript/TypeScript (Jest/Vitest/Mocha), Go, and Rust (cargo test), with fallback patterns for other languages.

- **Agentic Fallback CLI Options:** Added `--agentic-fallback/--no-agentic-fallback` flags to the `verify` and `fix` commands, allowing users to control whether the agentic fallback mechanism is invoked when standard fixes fail.

- **Example Usage for get_test_command:** Added `context/get_test_command_example.py` demonstrating test command resolution for various file types including Python, Go, TypeScript, and Rust, with coverage of language override and agentic fallback scenarios.

### Fix

- **Race Condition in Parallel Regression Tests:** Fixed a race condition in `tests/sync_regression_parallel.sh` where `wait -n` could misattribute exit statuses when multiple jobs finished close together. Replaced with explicit `wait "$pid"` for each job to ensure accurate pass/fail reporting.

- **Parameter Name Mismatch in sync_orchestration:** Fixed `sync_orchestration.py` to use `use_git` instead of `git` when calling `update_main()`, preventing silent failures when the update operation was invoked. Added regression test to prevent future issues.

- **Core Dump Timestamp:** Updated `pdd/core/dump.py` to use local time instead of UTC for timestamp generation, improving readability of core dump filenames.

- **Z3 Import Formatting:** Corrected import statement formatting for Z3 library in `test_get_test_command.py`.

### Refactor

- **User Cancellation Handling:** Replaced `sys.exit(1)` with `click.Abort()` across all command modules (`analysis.py`, `fix.py`, `generate.py`, `maintenance.py`, `misc.py`, `modify.py`, `utility.py`) for consistent user cancellation handling. Added `except click.Abort: raise` guards to prevent these exceptions from being swallowed by generic error handlers.

- **CSV Path and Documentation:** Updated CSV file path handling in `get_test_command.py` to use `Path(__file__).parent.parent / "data"` pattern. Improved function docstrings with clear resolution order documentation.

### Tests

- Added 398 lines of comprehensive tests in `tests/test_get_test_command.py` covering Python/Go/TypeScript/Rust file handling, resolution order verification, CSV priority over smart detection, language override behavior, and formal verification of resolution logic using Z3 solver.

- Added 249 lines of multi-language test execution tests in `tests/test_sync_orchestration.py` including bug detection tests for non-Python infinite fix loops and TypeScript/Go test runner verification.

- Added CLI tests in `tests/test_core_cli.py` for click.Abort propagation through command handlers.

## v0.0.82 (2025-12-12)

### Feat

- **Stale Run Report Detection:** Added `test_hash` field to `RunReport` dataclass to track which version of the test file produced the test results. The `_is_workflow_complete()` function now compares this hash against the current test file, detecting when run reports are stale. For legacy run reports without `test_hash`, a timestamp-based fallback compares fingerprint vs. run report timestamps. This prevents sync from incorrectly returning "nothing" when tests need re-running.

- **Smart Coverage Target Selection:** Added `_python_cov_target_for_code_file()` and `_python_cov_target_for_test_and_code()` functions in `sync_orchestration.py`. These analyze test file imports to determine the correct `--cov` target for pytest coverage. Handles both package-based imports (e.g., `backend.functions.module_name`) and stem-based imports (e.g., `from module_name import ...`) that add directories to `sys.path`.

- **ANSI Escape Sequence Handling:** Added `_strip_ansi()` function to `pytest_output.py` that removes ANSI color codes before parsing test results. Added safety net: if return code is non-zero but parsing found no failures/errors (due to formatting), at least one failure/error is recorded. Fixes incorrect `tests_failed=0` when pytest output contains color codes.

- **`.pddrc` Path Resolution Fix:** Added `config_base_dir` parameter to `generate_output_paths()`. Relative paths in `.pddrc` configurations now resolve relative to the `.pddrc` file location (not the input file directory). This parameter is passed through `construct_paths()` when `.pddrc` is present.

- **Auto-Include XML Tag Naming Rules:** Updated `auto_include_LLM.prompt` with strict rules for Step 4 output. Wrapper tags must be canonical dotted Python module paths (e.g., `<utils.auth_helpers>`, `<models.user>`), never `*_example` tags. Added inference rules for deriving module paths from context example files and a third example demonstrating proper tag naming.

- **Prompting Guide - Automatic Update Propagation:** Added new section explaining how `<include>` directives automatically propagate changes from included files to all prompts that reference them. Documents use cases (authoritative documentation, shared constraints, interface definitions) and the token-cost tradeoff of large includes.

### Refactor

- **Conflict Analysis Logic (PDD Doctrine Fix):** Updated `_perform_sync_analysis()` to differentiate between true conflicts (prompt + derived artifacts changed) and interrupted workflows (only derived artifacts changed). Per PDD doctrine, only changes involving the prompt (source of truth) are conflicts. When only code/example/test changed but prompt is unchanged, sync continues the workflow with `verify` or `test` operations instead of triggering `analyze_conflict`. Added `prompt_changed` field to decision details.

### Tests

- Added 300+ lines of regression tests in `test_sync_determine_operation.py` for stale run report detection, PDD doctrine derived artifacts handling, and conflict analysis edge cases
- Added coverage target selection tests in `test_sync_orchestration.py` for package-based and stem-based import patterns
- Added ANSI escape sequence and non-zero return code tests in `test_pytest_output.py`
- Added `config_base_dir` propagation tests in `test_construct_paths.py`

## v0.0.81 (2025-12-11)

### Feat

- **LLM Location Override:** Added `location` column to `data/llm_model.csv` enabling per-model Vertex AI region configuration. Models like `deepseek-r1-0528-maas` can now specify a region (e.g., `us-central1`) that overrides the default `VERTEX_LOCATION` environment variable. The `llm_invoke` module detects and uses this per-model location for both credential-based and API-key-based Vertex AI calls.
- **LM Studio JSON Schema Support:** Added `extra_body` workaround for LM Studio to properly pass `json_schema` response format, bypassing LiteLLM's `drop_params` behavior that was stripping the schema.
- **Regression Test Fallback:** Regression tests now copy the verified output file for subsequent tests when available, with automatic fallback to the original file when the verify step hasn't run.
- **Onboarding Guide Publishing:** Added onboarding guide to public and CAP repositories in the publish process.
- **Model Range Calculation:** Added midpoint calculation for strength sampling to improve model invocation distribution.

### Fix

- **Infinite Fix Loop Prevention:** Fixed critical bug where `sync_orchestration` failed to pass the `context` parameter to nested operations, causing infinite loops when context-specific configuration was needed. Added explicit test re-execution after successful fix operations to update `run_report` state.
- **Run Report Stale State Bug:** After a successful fix operation, the orchestrator now explicitly re-runs tests via `_execute_tests_and_create_run_report()` to update the state machine. Previously, stale `run_report` data caused the sync to incorrectly repeat fix operations.
- **Pytest Error Parsing:** Fixed `_execute_tests_and_create_run_report()` to count pytest ERRORS (fixture/setup failures) in addition to FAILURES. Previously, output like "1 passed, 10 errors" was incorrectly recorded as `tests_failed=0`.
- **Boolean False Detection Bug:** Changed `result[0] is not None` to `bool(result[0])` when checking fix operation success. Previously, `fix_main` returning `(False, ...)` was incorrectly treated as success because `False is not None` evaluates to `True`.
- **Default Strength Constant:** Changed hardcoded `strength=0.5` default to use `DEFAULT_STRENGTH` constant (0.75) for consistency.
- **Model Name in Error Logs:** Fix attempt logs now include the model name used. Error handling returns distinguishable error indicators (e.g., `"Error: ValidationError - ..."`) instead of empty strings.

## v0.0.80 (2025-12-09)

### Feat

- **`report-core` Command:** New `pdd report-core` command for streamlined bug reporting. Automatically finds the most recent core dump, creates GitHub issues with terminal output and tracked file contents, and supports both browser-based (default) and API-based submission (`--api` flag). API mode creates private GitHub Gists containing all relevant files and links them in the issue body. Authenticates via standard methods: `gh` CLI, `GITHUB_TOKEN`, `GH_TOKEN`, or `PDD_GITHUB_TOKEN` environment variables. 

- **Core Dump Enhancements:** Core dumps now capture terminal output (stdout/stderr) with ANSI code stripping for clean logs. File tracking includes content of all files read/written during execution, plus auto-inclusion of relevant `.pdd/meta/` files and PDD config files. Added `OutputCapture` class that acts as a tee to capture output while still displaying it normally. 

Thanks to Jiamin Cai for your contributions on the report core and core dump enhancements!

- **Dependency Synchronization Tooling:** Added `make check-deps` target with `scripts/check_deps.py` to verify that `pyproject.toml` dependencies match `requirements.txt`. The `make release` target now runs this check automatically before version bumping.

- **Documentation Checklists:** Added comprehensive checklists for performance optimization (`docs/checklists/performance-optimization.md`) targeting cold-start reduction from ~1.5s to ~0.3-0.4s, and prompt caching implementation (`docs/checklists/prompt-caching-implementation.md`) for reducing LLM costs.

### Fix

- **Workflow Completion Validation:** Fixed a critical bug where newly generated code would incorrectly be marked as "workflow complete" without crash/verify validation. `_is_workflow_complete()` now requires that `run_report` exists with `exit_code == 0`, and verifies that the `verify` or `test` command has been executed (unless `skip_verify` is set). This prevents the sync workflow from prematurely declaring success.

- **Stale Run Report Cleanup:** After code generation (`generate` operation), the stale `run_report` file is now deleted. This ensures crash/verify validation is always required for freshly generated code, closing a gap where old validation results could incorrectly pass new code.

- **Crash Retry on Failure:** Fixed bug where failed crash fixes (exit_code != 0) would incorrectly proceed to verify. Now properly retries the crash operation when the fix didn't work.

- **Temperature Range Validation:** Updated validation to allow temperature values between 0 and 2 (was incorrectly limited to 0-1). Error messages updated to reflect correct ranges: "Strength and time must be between 0 and 1. Temperature must be between 0 and 2."

- **LiteLLM Responses API:** Switched GPT-5 calls from direct OpenAI API to LiteLLM's `responses()` function for better abstraction. Fixed structured output handling to use `text.format` with `json_schema` and added `additionalProperties: false` for strict mode compliance. Added JSON repair fallback for Pydantic parsing failures.

### Deps

- Added `python-dotenv==1.1.0`, `PyYAML==6.0.1`, `jsonschema==4.23.0`, and `z3-solver` to main dependencies
- Moved `httpx==0.28.1` to dev dependencies
- Reorganized `requirements.txt` with clear production/dev sections

### Tests

- Added comprehensive test coverage for core dump file tracking and terminal output capture
- Added tests for `report-core` command including gist creation and GitHub issue posting
- Added regression tests for workflow completion checks ensuring generated code requires validation
- Expanded sync determine operation tests for crash retry and verify completion scenarios

## v0.0.79 (2025-12-08)

### Deps

- **Textual Dependency in pyproject.toml:** Added `textual` to `pyproject.toml` dependencies. This was previously added to `requirements.txt` in v0.0.77 for the Textual TUI feature but was missing from the package manifest, causing installation issues when installing via `pip install pdd-cli`.

Thanks to James Levine for reporting this issue!

## v0.0.78 (2025-12-08)

### Fix

- **Path Resolution for `examples_dir`:** Fixed a bug where `examples_dir` was incorrectly resolved when `example_output_path` was a directory path (e.g., `context/`) rather than a file path. Previously, `Path('context/').parent` would incorrectly evaluate to `.` instead of `context`. The fix now detects directory paths (ending with `/` or having no file extension) and preserves them correctly.

- **Custom `prompts_dir` from Context Config:** Fixed sync discovery mode to respect `prompts_dir` from `.pddrc` context configuration. Previously, the code hardcoded `"prompts"` even when a custom subdirectory like `prompts/backend` was specified in the context config.

- **Empty Prompt Validation in Update:** Added defense-in-depth validation to prevent writing empty prompts. The `update_prompt` module now validates that the LLM returns a non-empty `modified_prompt` (minimum 10 characters via Pydantic), and `update_main` double-checks before writing to disk.

### Tests

- Added regression test `test_construct_paths_sync_discovery_examples_dir_from_directory_path` to verify correct `examples_dir` resolution when `example_output_path` is a directory.
- Added regression test `test_construct_paths_sync_discovery_custom_prompts_dir` to ensure `prompts_dir` respects `.pddrc` context configuration.

## v0.0.77 (2025-12-07)

### Feat

- **Textual TUI for Sync:** Introduced a rich Terminal User Interface (TUI) for the `sync` command using `Textual`. This includes real-time log streaming, progress animations, and modal dialogs for user input/confirmation, replacing the previous CLI output.
- **Enhance LLM Response Handling:** Added smart code unescaping, malformed JSON detection, and automatic syntax repair to improve robustness against noisy LLM outputs.
- **Sync Orchestration:** Improved project root detection (`_find_project_root`), added operation fingerprinting to skip redundant steps, and integrated language-specific run commands.
- **Universal Execution:** Updated `agentic_langtest` to support more language execution paths.

### Fix

- **Fix Command:** Added validation for error file existence (`--error-file`) and improved error reporting when files are missing.
- **Boundary Checks:** Fixed boundary checks in project root finding to prevent traversing above the project ceiling.

### Refactor

- **Verification Logic:** Simplified `fix_verification_errors.py` by removing legacy XML parsing fallbacks in favor of Pydantic-based processing.
- **Tests:** Extensive refactoring of `tests/test_fix_main.py` and addition of new tests for the TUI and orchestration logic.

### Ops

- **Dependencies:** Added `textual` to `requirements.txt`.

## v0.0.76 (2025-12-05)

### LLM Response Handling & Python Syntax Repair

- **Smart Code Unescaping:** Added `_smart_unescape_code()` function that intelligently unescapes `\n` sequences in code while preserving escape sequences inside Python string literals (e.g., `print("line1\nline2")` remains intact).
- **Malformed JSON Detection:** Added `_is_malformed_json_response()` to detect truncated JSON responses caused by LLMs (particularly Gemini) generating thousands of `\n` characters, causing response truncation before closing braces.
- **Python Syntax Repair:** Added `_repair_python_syntax()` to validate and automatically fix common syntax errors in LLM-generated Python code, such as spurious trailing quotes at string boundaries.
- **Pydantic Model Processing:** Added `_unescape_code_newlines()` to recursively process Pydantic model fields, fixing double-escaped newlines in code strings and repairing Python syntax errors.
- **Automatic Retry on Invalid Syntax:** Enhanced `llm_invoke` to detect invalid Python syntax after initial repair attempts and retry the LLM call with cache bypass, improving reliability for structured code output.

### Prompt Templates

- **JSON Formatting Rules:** Updated `extract_program_code_fix_LLM.prompt` with explicit documentation on proper JSON escaping for newlines (use `\n` not `\\n` for actual line breaks).
- **Clean JSON Output:** Added instruction to `extract_code_LLM.prompt` requiring output of only the JSON object without trailing whitespace or newlines.
- **Architecture Schema Fix:** Fixed architecture JSON schema in `architecture_json.prompt` to include `type: string` alongside `enum` properties, ensuring proper JSON Schema compliance.

### Agentic Fix

- **Unattended Execution:** Added `--dangerously-skip-permissions` flag to the Anthropic Claude variant in `agentic_fix.py`, enabling fully automated fix attempts without interactive permission prompts.

### Fix Verification

- **Improved Code Unescaping:** Refactored `fix_verification_errors.py` to use the new `_smart_unescape_code()` function instead of naive string replacement, properly preserving escape sequences inside string literals.

### Examples

- **Architecture Example:** Added comprehensive `examples/arch/` directory demonstrating architecture generation workflow, including `ORDER_MANAGEMENT_PRD.md` (product requirements), `architecture.json` (generated architecture), `architecture_diagram.html` (Mermaid visualization), and `tech_stack.md`.

### Refactor

- **Regression Test Simplification:** Replaced environment variable manipulation (`unset GITHUB_CLIENT_ID`) with the cleaner `--local` CLI flag approach in both `regression.sh` and `sync_regression.sh`.
- **Code Generator Check:** Changed empty content check from `is None` to falsy check in `code_generator_main.py` to properly handle empty strings from cloud execution.

### Tests

- **LLM Invoke Coverage:** Added 270+ lines of new tests for Python code repair, syntax validation, retry logic, and structured output handling in `test_llm_invoke.py`.

## v0.0.75 (2025-11-30)

### Architecture & CLI Refactor

- **Modular Command Structure:** Massive refactoring of the monolithic `pdd/cli.py` into a modular architecture. The CLI is now organized into distinct command modules under `pdd/commands/` (`analysis`, `fix`, `generate`, `maintenance`, `misc`, `modify`, `templates`, `utility`) and core logic under `pdd/core/` (`cli`, `dump`, `errors`, `utils`). This significantly improves maintainability and extensibility.
- **Test Suite Restructuring:** The monolithic `tests/test_cli.py` has been split into granular test files (`tests/test_commands_*.py`, `tests/test_core_*.py`) mirroring the new module structure, with enhanced coverage.

### Feat

- **Universal Execution Engine:** Introduced `pdd/get_run_command.py` and updated `data/language_format.csv` to define execution commands for supported languages (e.g., `python {file}`, `node {file}`, `go run {file}`). This allows the agentic fixer (`pdd/agentic_fix.py`) to verify fixes across multiple languages without hardcoded fallbacks.
- **JavaScript Automation:** Enhanced `agentic_fix` and `agentic_langtest` to support JavaScript/TypeScript workflows, including Node.js and NPM detection. Added a comprehensive `examples/agentic_fallback_example_javascript` to demonstrate this capability.
- **Analysis Module:** Consolidated analysis-related commands (`detect`, `conflicts`, `bug`, `crash`, `trace`) into a unified `pdd/commands/analysis.py` module.
- **Core Dump Module:** Extracted and formalized core dump generation logic into `pdd/core/dump.py`, supporting the `report-core` functionality.
- **Example Organization:** Reorganized context examples into structured subdirectories (e.g., `context/commands/`, `context/core/`) and added new examples for `dump`, `errors`, and `utils` usage.
- **Goldilocks Prompt Image:** Added the "Goldilocks Zone" diagram asset to the public repository for documentation consistency.

### Fix

- **Agentic Fix Loops:** Refined `fix_code_loop` and `fix_error_loop` to leverage the new universal execution engine, improving stability and language support.
- **JWT Token Handling:** Enhanced `get_jwt_token.py` with better environment configuration and error handling.
- **Agentic Fallback Tests:** Updated `tests/test_agentic_fix.py` and `tests/test_agentic_langtest.py` to validate the new Node.js/NPM detection and universal execution paths.

### Docs

- **Prompting Guide:** Updated `docs/prompting_guide.md` with new insights and structural improvements.
- **Example Generation:** Updated internal logic and prompts for generating core examples, ensuring they align with the new modular CLI structure.

## v0.0.74 (2025-11-24)

### Feat

- **Orchestration Cycle Detection:** Implemented logic to detect and break infinite loops of alternating `test` and `fix` operations in the sync orchestration process, preventing wasted compute cycles.
- **Structured Output Schemas:** Added `output_schema` support in code generation and LLM invocation, enabling strict JSON schema validation for structured responses.
- **Architecture Template Normalization:** Added automatic detection and repair of unsupported interface types in generated architecture JSON templates.
- **Robust Local Fallback:** Enhanced the local execution fallback strategy to default to the first available input file if no prompt files are found, and improved `OPENAI_API_KEY` handling for regression tests.

### Fix

- **Web Scraping Resilience:** Enhanced error handling in web scraping modules to improve stability during regression tests.

### Refactor

- **Regression Test Simplification:** Simplified command usage patterns in synchronization regression tests for better maintainability.

### Data

- **Model Catalog Update:** Updated the LLM catalog to support the latest Claude 4.5 family. Replaced Claude Opus 4.1 with **Claude Opus 4.5** (via Anthropic and Vertex AI) and introduced **Claude Haiku 4.5**, including updated pricing and context window configurations.

### Docs

- **Prompting Guide Visuals:** Added and updated the "Goldilocks" zone diagram to visually illustrate the optimal level of abstraction for prompts. Thanks Rudi Cilibrasi for your feedback!

### Tests

- **Schema Validation Coverage:** Expanded tests in `test_code_generator_main.py` to validate `output_schema` parameter handling across local and cloud fallback scenarios.

## v0.0.73 (2025-11-21)

### Feat

- **Core Dump & Issue Reporting:** Added global `--core-dump` flag to capture detailed execution state, environment variables, and error traces into JSON files on failure. Introduced `pdd report-core` command to parse these dumps into markdown issue reports or automatically post them to GitHub. Thank you Jiamin Cai for your contributions!
- **Windows Support:** Added comprehensive `SETUP_WITH_WINDOWS.md` guide covering environment variable configuration for PowerShell, CMD, and Git Bash. Thank you Grant Petersen for your contributions!

### Fix

- **Prompt Loading:** Enhanced `load_prompt_template` to search `pdd/prompts/` subdirectories, ensuring packaged prompt templates are correctly discovered when PDD is installed via tools like `uv` or `pip`. Thank you Danial Toktarbayev for your contributions!

### Docs

- **Prompting Guide:** Added a "Quickstart: PDD in 5 Minutes" recipe and a "Glossary" of key terms. Clarified that `<include>` tags are PDD pre-processing directives rather than standard XML.

## v0.0.72 (2025-11-18)

### Feat

- Enhance agentic fallback and path handling: The `run_agentic_fix` function now returns a list of all files modified by the agent. Agentic fix loops (`fix_code_loop`, `fix_error_loop`, `fix_verification_errors_loop`) now display a summary of files changed by the agent and ensure error logs are properly initialized with parent directories created.
- Improve CLI help structure: The `pdd` CLI now uses a custom `Click` group to organize "Generate Suite" commands (`generate`, `test`, `example`) in its root help, enhancing readability and discoverability. The `generate` command's help text is also expanded for clarity.
- Refine output path derivation: The `construct_paths` and `generate_output_paths` functions are enhanced to support more granular control over output file locations, allowing different output keys (e.g., `output_code`, `output_test`) to derive their paths from specific input file directories in commands like `fix`, `crash`, and `verify`.

### Fix

- Improve file writing robustness: Commands like `fix` and `verify` now proactively create parent directories for output files (e.g., fixed code, tests, results) before writing, preventing errors in cases where the target directory structure does not yet exist.

### Docs

- **Prompting Guide Improvements:**
    - Added new references to "Effective Context Engineering" and "Anthropic Prompt Engineering Overview."
    - Expanded "Steps" guidance to "Steps & Chain of Thought," emphasizing deterministic planning and explicit step-by-step reasoning for complex tasks.
    - Introduced an "Advanced Tips" section covering: Shared Preamble for Consistency, Positive over Negative Constraints, Positioning Critical Instructions (Hierarchy of Attention), and Command-Specific Context Files.
    - Added a "Level of Abstraction (The \"Goldilocks\" Zone\")" section, guiding users to focus on architecture, contract, and intent, with examples of effective prompt abstraction.
    - Updated "Dependencies & Composability (Token-Efficient Examples)" to clarify examples as "compressed interfaces" and module interfaces, with a tip to use `pdd auto-deps`.
    - Refined PDD Workflow steps and added a "Workflow Cheatsheet: Features vs. Bugs" table, with a strong emphasis on writing new failing tests for bugs and updating prompts (not patching code) for fixes.

### Tests

- Update agentic fix tests: Test assertions in `tests/test_agentic_fix.py` are updated to account for the new `changed_files` return value.
- Enhance path construction tests: `tests/test_construct_paths.py` includes new tests for the improved `input_file_dirs` handling.
- Refactor file writing tests: `tests/test_fix_main.py` and `tests/test_fix_verification_main.py` are adjusted to use `pathlib.Path` objects consistently for file operations and verify the new directory creation logic.

Many thanks to Jiamin Cai for your contributions around your continued improvements to the agentic fallback and path handling and thank you to Kante Tran for your work on the CLI help improvements!

## v0.0.71 (2025-11-18)

### Feat

- `pdd update` repository mode now walks the Git root, creates/updates prompts inside the shared `prompts/` directory, honors `--output` directories during regeneration, and blocks file-only switches (`--input-code`, `--git`, etc.) so repo-wide refreshes can be scripted safely.
- Default output derivation for file-scoped commands (`fix`, `crash`, `verify`, `split`, `change`, `update`) now anchors to the input file’s directory (including relative `.pddrc` or env overrides), so regenerated prompts/tests land beside their sources instead of the current working directory.

### Docs

- README and PyPI description bumped to 0.0.71, moved the agentic fallback guide next to the `fix` command docs (noting `crash`/`verify` support), and clarified the `update` examples/options.

### Data

- Refreshed the LLM catalog and defaults: replaced Gemini 2.5 entries with Gemini 3 previews, switched the CLI default to `gpt-5.1-codex-mini`, and added the latest GPT‑5.1 SKUs.

### Tests

- Added coverage for repo-wide prompt regeneration, prompt-directory summaries, construct-path defaults that follow input directories, CLI summary rendering with the new default model, and LLM invocation to lock in the catalog updates.

Many thanks to Jiamin Cai for your contributions around fixing the directory issues!


## v0.0.70 (2025-11-13)

### Feat

- Image includes in prompts: `<include>` now embeds images as base64 data URLs with sensible defaults. Supports `.png`, `.jpg/.jpeg`, `.gif`, `.webp`, and `.heic`; enforces max dimension ~1024px while preserving aspect ratio; converts GIFs to first‑frame PNG and HEIC to JPEG for compatibility.
- Multimodal generation: `code_generator` detects `data:image/...;base64,...` in prompts and calls the model with mixed `text` + `image_url` content, enabling image‑conditioned generations alongside normal text prompts.
- Prompt templates updated: clarify parameter validation/defaults (including `time=None` semantics) and document multimodal message construction and image include behavior.
- Minor: small enhancements around crash/agentic fallback flows.

### Examples

- Added `examples/image_prompt_example/` showing how to include an image in a prompt and generate a Python script that describes it.

### Docs

- Prompting guide notes that `<include>` handles images in addition to text; README and PyPI long description updated with the new version badge.

### Tests

- Expanded coverage for preprocess include flows (include‑many, recursive deferral for shell/web, curly‑brace handling) and added multimodal path tests for `code_generator`.

### Chore

- Version bump to 0.0.70 and dependency updates: add `Pillow` and `pillow-heif`; update `requirements.txt`, `pyproject.toml`, and internal version strings.

Thank you Jiamin Cai for your amazing contributions!

## v0.0.69 (2025-11-12)

### Feat

- crash command: add `--agentic-fallback/--no-agentic-fallback` (default on), wire into the iterative fixer, and always write `--output` and `--output-program` even when unchanged; improve path resolution, messaging, and summary output
- agentic fallback: normalize result shapes in fix loops, roll agentic cost/model into totals, and re-read final files on success to return the actual post-fix content

### Docs

- README and language examples updated to document crash flow with agentic fallback; refreshed agentic_fallback example READMEs for Python, Java (Maven/Gradle), JavaScript, and TypeScript

### Tests

- strengthen fix verification tests to ensure outputs are written on failure/no-op, propagate `agentic_fallback=True`, validate verbose/force handling, and refine attempt counting

Many thanks to Jiamin Cai for bringing the entire agentic fallback suite contributions to the project!

## v0.0.68 (2025-11-12)

### Feat

- add agentic fallback fixer with multi‑provider support (Anthropic, Google, OpenAI) and deterministic multi‑file patch application using explicit BEGIN/END file markers
- add language‑aware verification with sensible defaults (pytest, npm/jest, Maven/Gradle) and optional agent‑supplied TESTCMD execution on failure
- integrate agentic fallback path into CLI fix flow and harden the error loop with clearer logging, timeouts, and safer env handling
- add new prompt templates for agentic fix and langtest; refine CLI/fix prompt templates

### Examples

- add agentic_fallback examples for Python, Java (Maven and Gradle), JavaScript, and TypeScript, each with prompts, minimal source, and tests

### Tests

- add tests for agentic fixer and language‑aware verification (tests/test_agentic_fix.py, tests/test_agentic_langtest.py)
- move pytest configuration into tests/conftest.py and update fix error‑loop coverage

### Docs

- update README and examples documentation to cover agentic fallback workflows; refresh PyPI long description

### Chore

- update .gitignore for Node/Yarn artifacts; adjust Makefile test targets and pyproject settings

Many thanks to Jiamin Cai for your amazing contributions!

## v0.0.67 (2025-11-11)

### Feat

- add pdd-local.sh to the list of public root files for publishing
- add support for --local option in regression tests to enhance context argument handling
- improve template listing in CLI by enhancing output formatting for better readability
- implement error recovery in regression tests by adding a 'crash' command to fix failed example runs
- extend sync command in regression tests with additional options for budget and max attempts
- add regression test summary parsing to TestRunner for improved pass/fail reporting
- enhance TestRunner with detailed parsing for sync regression results and improve error handling
- enhance TestRunner to extract additional log paths and improve regression output parsing
- improve test result parsing and logging in TestRunner to handle multiple log files
- enhance Makefile to copy regression scripts and update TestRunner to parse full log files
- add sync log and analysis tests to regression suite
- add parallel execution for sync regression tests and update test command in Makefile
- add make pr-test command to test public PRs against private codebase
- include PR link in test results comment
- extract and display failed test numbers in results
- add manual workflow trigger support without requiring keys in code
- automate test execution with GitHub Actions and Infisical

### Fix

- improve error logging in sync regression tests by capturing exit status for failed commands
- improve patch application process in PR tests workflow with fallback mechanism
- simplify comment body parsing in PR tests workflow
- update sync command to include local flag for multi-language tests
- update Infisical environment variable usage and improve sync regression test logging
- update repository references from pdd_cloud to gltanaka/pdd
- update all repository URLs to promptdriven/pdd_cloud
- update repository references to promptdriven organization

### Refactor

- enhance `update` command functionality in CLI to support repository-wide updates and improved prompt handling (Thank you Jiamin Cai for your contributions!)
- enhance test logging and output handling in TestRunner
- enhance Infisical integration in test scripts and update workflow for token usage
- update GitHub Actions workflow to apply public PR patches on private repo
- use pr-url instead of pr-num for flexibility
- change workflow to manual-only execution

### Docs

- add developer setup section with test optimization and dependencies

## v0.0.66 (2025-11-07)

### Architecture & Code Generation

- Architecture JSON emission and Mermaid rendering now produce deterministic formatting, `.pddrc` defaults stay in sync with those paths, and the regression suite (`tests/test_code_generator_main.py`, `tests/test_render_mermaid.py`) locks the behavior down so downstream tools always find the generated assets.
- The LLM toggle plus force flag flows through `code_generator_main.py`, prompt templates, and the Mermaid renderer, letting templates skip or re-run expensive post-processing per invocation; the CLI now pre-parses front matter, writes JSON outputs before post-process scripts run, and always regenerates architecture diagrams when `architecture.json` changes.

### Templates & Examples

- Prompt assets and their drivers now ship module-aware metadata (source/test paths, module names) so generated examples/tests import the right files; they also showcase the new `context/python_env_detector_example.py`, adopt the `--template` flag in docs, and drop the obsolete `mermaid_diagram.prompt`.
- `.pddrc` now declares explicit `src/` and `tests/` output paths for example contexts, and `generate_output_paths.py` bootstraps an `examples/` directory automatically so newly generated artifacts never depend on `context/example.prompt` or `context/test.prompt`.
- The hello sample workspace was rebuilt around `examples/hello/src/hello.py` with refreshed metadata, updated `pdd/generate_test.py`, and rewritten prompts/tests so the example mirrors the current CLI workflow.

### Docs & Quality

- Issue #88’s test-generation failures were fixed by tightening `construct_paths`, cleaning prompt instructions, passing resolved file paths into the LLM, and enforcing absolute output paths during code-generation—covered by new tests in `tests/test_construct_paths.py`, `tests/test_generate_test.py`, and `tests/test_generate_output_paths.py`.
- Onboarding and troubleshooting docs now cover `~/.pdd/llm_model.csv` quota issues and explain the LLM toggle workflow, with the README/model docs updated to match.

## v0.0.65 (2025-10-24)

### Architecture Visualization

- Shipped `pdd/render_mermaid.py`, a turnkey helper plus `examples/tictactoe` assets for turning architecture JSON specs into Mermaid diagrams and interactive HTML, backed by regression coverage in `tests/test_render_mermaid.py`.
- Wired the architecture JSON generator's post-process hook so `pdd/code_generator_main.py` can toggle Mermaid rendering after each run, letting templates emit diagrams automatically.

### Data & Models

- Documented the Snowflake-hosted `openai/claude-sonnet-4-5` endpoint in `data/llm_model.csv`, including credentials, context limits, and billing metadata.

## v0.0.64 (2025-10-12)

### Data & Formats

- Added Lean and Agda entries to `data/language_format.csv`, expanding supported language metadata with the correct comment markers and extensions for theorem-proving workflows.

Thanks to Rudi Cilibrasi for your contributions!

## v0.0.63 (2025-10-12)

### Prompt Templates

- architecture JSON template now requires a `filepath` alongside each filename and enforces typed `params` objects for page routes, clarifying how generators should emit file locations.

Thanks to James Levine for your contributions!

## v0.0.62 (2025-10-02)

### CLI & Templates

- `pdd templates show` now renders summary, variables, and examples with Rich tables for clearer output.
- Hardened `pdd/templates/generic/generate_prompt.prompt`: responses must return `<prompt>...</prompt>`, `ARCHITECTURE_FILE` is now required, and optional variables are normalized to avoid brace issues.

### Prompt Validation & Regression

- Regression harnesses wrap prompts with the required tags, validate architecture `dataSources`, and surface schema errors earlier in `tests/regression.sh`. Thanks James Levine and Sai Vathsavayi for your debugging efforts!
- Expanded coverage in `tests/test_preprocess.py` and `tests/test_code_generator_main.py` to exercise brace protection, optional template variables, and architecture generation workflows.

### Docs

- Added `docs/prompting_guide.md`, refreshed onboarding/tutorial guides, and introduced `AGENTS.md` as a quick-reference to repository conventions.
- Documented the `dataSources` contract in the README and architecture template, highlighting required fields and schema expectations.

### Data & Model Metadata

- Added Prisma, Verilog, and SystemVerilog entries to `data/language_format.csv` to expand supported formats. Thanks Dan Barrowman for the Contributions!
- Renamed Anthropic and Google entries in `data/llm_model.csv` for consistent model naming. Sonnet 4.5 is now the default model for Anthropic.

### Tooling

- Improved double-curly brace handling in `pdd/preprocess.py` to preserve `${IDENT}` placeholders and added targeted regression coverage.
- VS Code prompt-highlighter extension 0.0.2 ships with Open VSX metadata/docs plus Makefile targets to publish and verify releases.

## v0.0.61 (2025-09-23)

### VS Code Extension

- Improve compatibility across OpenVSX‑compatible IDEs (VS Code, Cursor, VSCodium, Gitpod, Kiro, Windsurf). Update extension metadata, keywords, and docs to reflect broader support.

### CLI

- Normalize command result handling in `process_commands`: treat a single 3‑tuple as one step in the execution summary; wrap unexpected scalar results and warn once; keep total‑cost calculation correct. Add tests for these cases.

### Prompts & Templates

- Add `pdd/templates/generic/generate_prompt.prompt` with detailed variable descriptions and usage examples for generating module prompts.

Thanks Sai Vathsavayi for altering me that this was missing!

### Tests

- CLI: expand `tests/test_cli.py` with coverage for single‑tuple normalization and non‑tuple result warnings.
- Template registry: clarify behavior so packaged templates still list while project files with missing/malformed front matter are ignored.

### Docs

- README: note that the extension supports all OpenVSX‑compatible IDEs.
- VS Code extension quickstart: add installation guidance for VSCodium, Kiro, Windsurf, and other OpenVSX‑compatible IDEs.

Thanks Shrenya Mathur for your contributions on OpenVSX compatibility!

## v0.0.60 (2025-09-23)

### Setup Tool

- Make the interactive `pdd.setup_tool` more capable and user-friendly: add Anthropic Claude key support alongside OpenAI and Google Gemini, improve environment variable handling, and refine API key validation flows.
- Enhance config persistence with shell-specific env snippets and a clear exit summary; add a sample prompt and restructure the script for clarity.

Thanks Sai Vathsavayi for testing and James Levine for your contributions!

### CLI Completion

- Expand completions with new global options `--context` and `--list-contexts` and add command completions for `sync`, `setup`, and `install_completion`.
- Update option completions for `sync` and `pytest-output` and improve help completion coverage.
- Fix Fish completion syntax for environment-variable option on `generate` to properly source variables from the environment.

## v0.0.59 (2025-09-21)

### CLI & Setup

- Update `pdd setup` to invoke the packaged interactive tool via `python -m pdd.setup_tool`, simplifying onboarding and avoiding path issues.
- Remove the deprecated `pdd-setup.py` from distribution (drop MANIFEST/data-files entry).

### Testing

- Add `--run-all` pytest option (exports `PDD_RUN_ALL_TESTS=1`) to run the full suite including integration tests.
- Add dev dependencies `pytest-testmon` and `pytest-xdist` for faster, selective, and parallel test runs.
- Ignore Testmon cache (`.testmon*`) in `.gitignore`.

### Tooling

- Add `pyrightconfig.json` and update VS Code settings.

Thankes James Levine and Parth Patil for identifying and root causing the setup issue.

## v0.0.58 (2025-09-21)

### Docs & Demos

- Embed a new hand-paint workflow demo GIF in the README and sync the asset into the public repo alongside the full video recording.

### Packaging

- Bundle the interactive setup utility as `pdd.setup_tool` and invoke it via `python -m pdd.setup_tool` so `pdd setup` works after wheel installs (pip/uv).

## v0.0.57 (2025-09-19)

### CLI & Templates

- Introduce `pdd templates` command group with `list`, `show`, and `copy` subcommands backed by a new registry that unifies packaged and project prompts.
- Enhance `pdd generate` with front-matter-aware templates that auto-populate defaults, enforce required variables, and optionally discover project files.
- Improve `pdd trace` normalization and fallback heuristics to produce a line match even when LLM output is noisy.

### Examples & Tooling

- Ship a comprehensive `edit_file_tool_example` project with scripts, prompts, CLI entrypoints, utilities, and tests demonstrating edit-file workflows end-to-end.
- Add a `hello_you` example to showcase personalized greeting prompts and outputs. thanks to Sai Vathsavayi for the PR and contributions.
- Provide `utils/pdd-setup.py` to guide interactive configuration of API keys and local environment prerequisites. Thanks James Levine for your contributions!

### Docs

- Rewrite README with template workflow walkthroughs, edit-file tool instructions, onboarding checklists, and expanded troubleshooting. Thanks Sai Vathsavayi for your edits!
- Expand CONTRIBUTING with detailed testing expectations and guidance for contributing templates and examples.
- Promote the Gemini setup guide and generation guidelines into top-level docs and examples, keeping onboarding in sync.

### Tests

- Add targeted coverage for the template registry, new CLI template commands, code generation path handling, and edit-file tool modules.
- Update regression harnesses and `test_trace` expectations to align with the new behaviors.

### Dependencies

- Package bundled templates with the CLI distribution and add `jsonschema` for metadata validation.
- Extend language format mappings with `.yaml` and INI support.

Thanks Rudi Cilibrasi for all your feedback!

## v0.0.56 (2025-09-14)

### CLI & Context

- Add `--list-contexts` flag to list available contexts from `.pddrc` and exit.
- Add `--context` override with early validation against `.pddrc` entries.
- Harmonize and improve automatic context detection and propagation across CLI and core modules.

### Tests

- Expand and refactor regression tests to exercise new context handling across CLI, `sync`, and main flows.
- Update test fixtures and expectations to align with context harmonization.

### Prompts

- Refactor prompt files to enhance clarity and functionality.

### Docs

- README: Document context handling improvements and usage guidance.

### Dependencies

- Add `litellm[caching]` and `psutil` to requirements.

### Build/Tooling

- Update `.gitignore` and `language_format.csv` (Thanks cilibrar@gmail.com) related to context handling workflows.

## v0.0.55 (2025-09-12)

### CLI & Code Generation

- Add environment variable support across CLI and code generation.
- Refactor incremental generation options; clarify and document behavior.
- Parameterize prompts and expand output options in CLI flows.

### Paths & Discovery

- Improve `construct_paths` handling of `generate_output_path` during sync discovery.
- Honor `.pddrc` `generate_output_path` in discovery logic.

### Docs

- README: Document parameterized prompts, output expansion, and clarify PDD vs. “Vibe coding”.

### VS Code Extension

- Initial release of the "prompt-highlighter" extension providing `.prompt` syntax highlighting, TextMate grammar, and language configuration.

### Build/Tooling

- Add `.gitignore`. Thanks cilibrar@gmail.com!

## v0.0.54 (2025-09-07)

### CLI & Orchestration

- Improve command tracking and reporting in the CLI (`pdd/cli.py`) and orchestration (`pdd/sync_orchestration.py`).
- Refine cost tracking/reporting integration in `pdd/track_cost.py`.

## v0.0.53 (2025-09-07)

### Docs

- README: Clarify that `sync` commonly needs the global `--force` flag to overwrite generated files; update all `sync` examples accordingly.
- README: Improve usage clarity and reporting notes for `sync`; add version badge and link to Prompt‑Driven Development Doctrine.
- Doctrine: Add new doctrine document outlining core principles and workflow; referenced from README.
- Examples: Add/setup Gemini guide (`SETUP_WITH_GEMINI.md`) — thanks to Sai Vathsavayi for the PR and contributions.

### CLI

- `pdd --help`: Expand `--force` help to note it’s commonly used with `sync` to update outputs.
- `pdd sync --help`: Add note recommending `pdd --force sync BASENAME` for typical runs.

### Orchestration

- Improve sync orchestration reporting and logic around handling missing examples.

### Models

- Update model configuration CSVs for Anthropic and improve temperature handling in `llm_invoke.py`.

### Build/Tooling

- Add `pytest-cov` dependency for coverage reporting.
- Makefile: Enhance `publish-public` target to include copying the doctrine document.

## v0.0.52 (2025-09-05)

- Models: update Google model naming in `.pdd/llm_model.csv` and `data/llm_model.csv` to correct naming convention

## v0.0.51 (2025-09-01)

- Dependencies: add `google-cloud-aiplatform>=1.3`
- Dev dependencies: add `build` and `twine`

## v0.0.50 (2025-09-01)

- Many thanks to Rudi Cilibrasi (cilibrar@gmail.com) for your work on the GPT-5 support
- README: add reference to bundled CSV of supported models and example rows

## v0.0.49 (2025-08-13)

- CONTRIBUTING:
  - Add section on adding/updating tests and why it matters
  - Specify test locations and the red/green workflow
  - Emphasize regression focus and coverage goals

## v0.0.48 (2025-08-12)

- Examples: add "Hello World" and "Pi Calc" examples with prompts, generated modules, example runners, and tests; update examples README
- Core CLI: refactor output path handling in code generator and command modules; improve language validation and output path resolution in `construct_paths.py`
- Orchestration/Invoke: enhance error handling and fix validation in `sync_orchestration.py` and `llm_invoke.py`
- Prompts/Docs: update `prompts/auto_include_python.prompt`; expand README with new example references

## v0.0.47 (2025-08-04)

- CLI/Test Integration:
  - Add `pytest-output` command to capture structured pytest results
  - Improve JSON parsing for pytest output handling
- Sync Workflow:
  - Enhance path resolution and missing-file error handling in sync command
  - Improve `get_pdd_file_paths` and test file path management
  - Fix decision logic to prioritize `verify` after `crash`
  - Resolve sync regression scenario ("4a") and strengthen decision tests
  - Improve directory summarization in `summarize_directory`
- Auto-Deps:
  - Add cycle detection and safeguards to prevent infinite loops
  - Add regression tests for loop prevention
- Model Config & Paths:
  - Refactor LLM model CSV path resolution and loading
  - Update README and tests to reflect new CSV path structure
- Prompts/Docs:
  - Update `prompts/auto_include_LLM.prompt` with new structure and examples
- Repo/Build:
  - Add `.gitattributes`; update local settings with helpful Bash snippets

## v0.0.46 (2025-08-02)

- Build/Release:
  - Update Makefile to use conda for build and upload workflows
  - Add `scripts/extract_wheel.py`; enhance `scripts/preprocess_wheel.py` to dynamically locate and extract wheel files
- Docs: refresh README and PyPI description for the release

## v0.0.45 (2025-07-29)

- Release LLM prompt files in the PyPi release

## v0.0.44 (2025-07-28)

- Sync & Orchestration:
  - Improve sync orchestration with enhanced logging, loop control, and output management
  - Refine decision logic for crash handling and test generation
  - Add verification program parameter; enhance coverage reporting in tests
  - Improve directory summarization and context-aware decision logic
- Environment & Tooling:
  - Add `pdd/python_env_detector.py` and corresponding prompt; detect Python env for subprocess calls
  - Replace `pdd-local` helper with `pdd-local.sh`; update `.gitignore`, `.pddrc`, and VS Code launch configs
- Data & Models:
  - Add JSONL format to `data/language_format.csv`
  - Update `data/llm_model.csv`; add example lockfile `.pdd/locks/simple_math_python.lock`
- Prompts/Docs:
  - Update prompts for code fixing and orchestration
  - README: installation updates
- Tests:
  - Add `test_model_selection.py`
  - Enhance `construct_paths` context detection test

## v0.0.43 (2025-07-12)

- Paths & Discovery:
  - Fix `prompts_dir` calculation and refine prompt directory resolution in `construct_paths.py`
  - Enhance sync discovery logic; add regression test for path calculation
- Release Assets:
  - Include additional whitepaper assets in the release process

## v0.0.42 (2025-07-11)

### Feat

- add factorial function and test program
- add GEMINI customization documentation and enhance construct_paths functionality
- add .pddrc configuration file and enhance sync command behavior
- add analysis and documentation for output paths and sync command
- add sync_main module and example for PDD workflow
- introduce sync orchestration module and example for PDD workflow

### Fix

- improve error handling in test program for divide function

### Refactor

- remove unused factorial function and test program
- enhance sync operation decision-making and add regression testing
- enhance context handling and directory resolution in sync_main
- update construct_paths function to include resolved_config
- streamline sync_orchestration logic and enhance context configuration
- improve variable naming and streamline crash handling logic
- remove get_extension.py and enhance sync command functionality
- remove get_extension.py and enhance sync command functionality

## v0.0.41 (2025-06-18)

### Feat

- enhance sync command with logging and conflict resolution capabilities
- add logo animation example and enhance sync animation functionality
- enhance sync_animation for 'auto-deps' command and improve animation flow
- enhance arrow animation in sync_animation for 'generate' command
- introduce logo animation module and integrate with sync_animation
- enhance sync_animation example and module for improved functionality
- add sync_animation module and example script for terminal animation
- update linting checklist and improve cmd_test_main functionality
- update linting checklist and enhance change_main functionality
- update linting checklist and enhance bug_to_unit_test and xml_tagger modules
- enhance auto_update functionality with version fetching and upgrade logic

### Fix

- improve language parameter handling and update test assertions
- update logo animation module and improve related documentation

### Refactor

- update output file handling in verification process
- update sync_determine_operation module and example for clarity and functionality
- simplify arrow animation logic in sync_animation
- update sync_animation example and module for improved clarity and functionality
- enhance Makefile and Python modules for improved functionality and clarity
- improve preprocess function to handle None results from preprocess_main

## v0.0.40 (2025-06-05)

### Feat

- improve auto_deps_main function with enhanced error handling and encoding support
- enhance get_extension function with detailed docstring and error handling

## v0.0.39 (2025-06-05)

### Feat

- add global `--time` option support across CLI commands

## v0.0.38 (2025-05-30)

### Fix

- update upgrade command in auto_update function to use install with --force

## v0.0.37 (2025-05-30)

### Feat

- add new task for design compiler strategy in TODO list

## v0.0.36 (2025-05-30)

### Feat

- enhance auto_update function with detailed version checking and user interaction

## v0.0.35 (2025-05-29)

### Feat

- enhance auto-update functionality with installation method detection

## v0.0.34 (2025-05-29)

### Feat

- enhance CLI and documentation with new features

## v0.0.33 (2025-05-25)

### Feat

- enhance code generation and context handling
- enhance postprocess example and improve code extraction functionality

## v0.0.32 (2025-05-23)

### Feat

- implement get_extension function for file type retrieval
- add budget option to change command and update Makefile for execution
- enhance handpaint functionality with gesture recognition and skeleton display
- enhance Makefile with new commands for prompt detection and modification

### Refactor

- update handpaint prompt and separate three.js imports into a new file

## v0.0.31 (2025-05-17)

### Feat

- enhance Makefile and code generation example for improved usability
- implement incremental code generation functionality
- add real file verification test for CLI

### Fix

- update TODO list and enhance test assertions in test_fix_verification_main.py
- update TODO list and correct mock return values in tests
- update output path key in code generator and enhance prompt documentation

### Refactor

- clean up code formatting and improve readability in fix_verification_main.py and tests
- improve verification process and logging in CLI and verification loop
- enhance test coverage and improve mock setups in test_code_generator_main.py
- enhance code generation example and improve CLI options
- update PDD configuration and add get_comment function
- update code generation function parameters for clarity and consistency
- streamline code generation logic and improve incremental handling
- update output directory and enhance code generation feedback
- enhance incremental code generation example and improve code structure

## v0.0.30 (2025-05-10)

### Feat

- update installation instructions and recommend uv package manager

## v0.0.29 (2025-05-10)

### Feat

- ensure PDD_PATH is set before command execution in CLI

## v0.0.28 (2025-05-10)

### Fix

- update string handling and improve test assertions in CLI

## v0.0.27 (2025-05-10)

### Feat

- add output paths for fixed code and program in verification process
- add output program option to verify command and enhance documentation

### Fix

- correct newline character in program file and enhance test assertions

### Refactor

- enhance logging configuration in llm_invoke_python.prompt
- update logging configuration and example usage in llm_invoke.py
- enhance logging and remove print statements in llm_invoke.py

## v0.0.26 (2025-05-09)

### Fix

- update environment variable for Firebase API key and enhance VSCode launch configuration

## v0.0.25 (2025-04-28)

## v0.0.24 (2025-04-17)

### Feat

- update model configurations and enhance prompt documentation
- enhance verification error handling and output reporting
- implement iterative error fixing loop for code verification
- restructure MCP server and enhance documentation
- introduce `verify` command for functional correctness validation
- enhance pdd-fix functionality with loop mode support
- add fix_verification_errors functionality and example script
- add new guidelines for project standards and best practices
- expand README and server initialization with PDD workflows and concepts
- improve output path handling in bug_main and generate_output_paths
- update handle_pdd_bug function to include additional required parameters
- enhance prompt splitting functionality and update documentation
- enhance JSON kwargs handling in main.py and update tool definitions
- update tool definitions in definitions.py for improved clarity and parameter requirements
- enhance README and definitions with usage guidance for PDD commands
- enhance tool definitions and command handling in PDD MCP server
- update tool definitions to enforce 'force' parameter for file overwrites
- enhance PDD MCP server with improved parameter handling and new test tool
- enhance PDD MCP server with logging improvements and parameter validation
- add initial PDD MCP server structure and tool imports
- enhance PDD MCP server with command-line argument parsing and FastMCP integration
- enhance PDD MCP server functionality and add new tools
- update server example and core server functionality
- enhance PDD command execution and API key management
- add script to regenerate test files for weather API
- enhance handler examples with file existence checks and improved argument handling
- enhance PDD MCP handlers with multiple command implementations
- implement main server functionality and example client for PDD MCP
- add example handler for PDD code generation
- implement core MCP server functionality and tool definitions
- add README.md and prompt file for MCP server implementation
- add PDD theme prompt file for .prompt extension
- update Makefile and enhance VS Code extension for PDD
- add initial VS Code extension for Prompt Driven Development
- enhance ZSH completion script for PDD CLI
- add release target to Makefile for version bump and package upload

### Fix

- update llm_model.csv and regression_analysis_log.prompt for accuracy

### Refactor

- enhance fix_verification_errors functionality and output structure
- remove unused PDD tools and their handlers from definitions and handlers
- simplify parameter guidance in definitions.py
- remove PDD_TEST_TOOL and its handler from PDD MCP server
- update handler examples and result formatting in PDD MCP
- clean up prompt files by removing example references

## v0.0.23 (2025-04-06)

### Feat

- replace 'quiet' parameter with 'verbose' in crash_main for detailed logging
- update main function parameters and enable verbose logging
- add verbose mode to fix_code_loop and related functions for detailed logging
- add verbose mode to fix_error_loop function and update parameters
- implement code generation CLI with prompt file handling and output options
- add clean target to Makefile for removing generated files and update documentation
- add validation for input requirements in update_main function all 5 tests pass
- add verbose option to git_update function and update documentation
- implement CLI for generating and enhancing unit tests with cmd_test_main untested
- add cmd_test_main prompt file for generating unit tests via CLI
- add fix_command for automated error correction in code and unit tests

### Fix

- update command references in cli_python.prompt for code generation
- update prompt file names in tests for consistency 18 of 20 pass

### Refactor

- update output paths for prompt and generated code files
- streamline unit test generation and coverage enhancement processes working
- update file path handling in fix_error_loop and enhance prompt documentation
- update input_strings documentation and loading logic for error files
