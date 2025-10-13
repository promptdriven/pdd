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
