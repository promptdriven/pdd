<!-- pdd-story-contract derived-from-story="../story__pdd_nested_ts_runner_resolution.md" story-hash="229c71ee07a5655d" issue-ref="https://github.com/promptdriven/pdd/pull/2003" -->

# Contract: Nested TypeScript tests use the correct runner safely

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_nested_ts_runner_resolution.md`), not this contract.

## Covers

- `prompts/get_test_command_python.prompt#R1`: Resolve through smart TypeScript detection before safe fallbacks.
- `prompts/get_test_command_python.prompt#R2`: Select the nearest applicable Playwright, Jest, or Vitest runner.
- `prompts/get_test_command_python.prompt#R3`: Discover runner configuration without a shallow parent limit.
- `prompts/get_test_command_python.prompt#R4`: Inherit runner configuration only through a declared workspace boundary.
- `prompts/get_test_command_python.prompt#R5`: Never adopt an unrelated or out-of-repository runner.
- `prompts/get_test_command_python.prompt#R6`: Match ecosystem-specific workspace inclusion and exclusion semantics.
- `prompts/get_test_command_python.prompt#R7`: Treat pnpm workspace declarations as authoritative.
- `prompts/get_test_command_python.prompt#R8`: Fail closed on malformed workspace declarations.
- `prompts/get_test_command_python.prompt#R9`: Bound discovery work on hostile metadata.
- `prompts/get_test_command_python.prompt#R10`: Keep resolved tests and runner configurations inside the repository.
- `prompts/get_test_command_python.prompt#R11`: Pass dynamic-route test paths to each runner with literal-equivalent targeting.
- `prompts/get_test_command_python.prompt#R12`: Preserve the test path as one shell-safe argument.
- `prompts/get_test_command_python.prompt#R13`: Return the owning runner directory and safely finalize CSV commands.
- `prompts/get_test_command_python.prompt#R14`: Never re-template a finalized test command.
- `prompts/get_test_command_python.prompt#R15`: Recognize executable-position Vitest invocations behind ordinary shell wrappers without accepting queries or argument mentions.
- `prompts/get_run_command_python.prompt#R1`: Substitute command placeholders once and reject unsafe surrounding shell syntax.
- `prompts/agentic_langtest_python.prompt#R1`: Return only a finalized command with a shell-safe test path.
- `prompts/fix_error_loop_python.prompt#R1`: Execute finalized non-Python verification commands without re-substitution.
- `prompts/agentic_fix_python.prompt#R1`: Execute finalized fallback verification commands without re-substitution.

## Context

The regression fixtures create standalone repositories, npm and pnpm workspaces,
nested dynamic-route tests, runner configurations, hostile manifests, symlinks,
and shell-metacharacter-bearing paths. The checks use local temporary files and
do not require an external service.

## Acceptance Criteria

1. Given a TypeScript test nested more than five directories below its project runner configuration, when PDD resolves its test command, then it selects the nearest runner owned by that package and returns the runner's directory as the working directory.
2. Given a workspace package, when PDD walks beyond its nearest package manifest, then it inherits only through a workspace declaration that includes that package under the declaration's ecosystem semantics.
3. Given an unrelated, excluded, malformed, oversized, or computationally hostile workspace declaration, when PDD performs runner discovery, then it terminates within bounded work and does not inherit a foreign runner.
4. Given a dynamic-route test path containing brackets or a path containing spaces and shell metacharacters, when PDD constructs and executes the test command, then the runner receives the intended test target as data rather than regex or shell syntax.
5. Given a test path or runner configuration that resolves outside the lexical repository root, when PDD performs discovery, then it refuses the foreign configuration while continuing to accept symlinks that stay inside the repository.
6. Given a Vite configuration and a package script that executes Vitest directly or through `env`, `command`, or `exec`, when PDD inspects the manifest, then it recognizes Vitest; argument-only mentions and `command -v` or `command -V` queries do not prove Vitest, genuine heredoc/here-string operators fail proof closed, and quoted, escaped, or commented literal `<<` text does not suppress a later executable Vitest clause.
7. Given any test command already finalized by command discovery, when downstream verification receives it, then every participating dev unit executes that command without a second placeholder substitution pass.

## Oracle

- The selected runner, test target, and working directory identify the owning project.
- Excluded, unrelated, or out-of-repository packages receive no inherited runner.
- Jest uses literal path targeting, Playwright receives an equivalent escaped regex, and Vitest receives a literal path.
- Hostile inputs terminate within the declared budgets without an exception.
- Shell wrappers are distinguished from query and argument-only uses of `vitest`, and only active heredoc/here-string operators trigger fail-closed handling.
- A finalized command reaches execution unchanged.

## Non-Oracle

- Private helper names, matcher implementation, and cache layout do not matter.
- Internal traversal order does not matter when observable runner selection is unchanged.
- Exact diagnostic wording does not matter.
- The particular shell lexer implementation does not matter.

## Negative Cases

- PDD must not report success after Jest matched zero tests because route brackets were interpreted as regex syntax.
- PDD must not execute under an unrelated ancestor or outside the repository through a symlink.
- PDD must not treat `echo vitest`, `node vitest`, or `command -v vitest` as a Vitest invocation.
- PDD must not reject `echo '<<' && vitest run`, escaped `<<` text, or a comment containing `<<` merely because the literal characters occur before Vitest.
- PDD must not re-evaluate a substituted path as shell syntax or substitute placeholders in a finalized command again.
- Repository-controlled metadata must not cause unbounded CPU, recursion, or memory use.

## Candidate Prompts

- `prompts/get_test_command_python.prompt` — owns runner discovery, targeting, and finalized test commands (primary).
- `prompts/get_run_command_python.prompt` — owns the shared single-pass shell-safe placeholder contract (primary).
- `prompts/agentic_langtest_python.prompt` — produces finalized language-specific verification commands (primary).
- `prompts/fix_error_loop_python.prompt` — consumes finalized non-Python test commands (primary).
- `prompts/agentic_fix_python.prompt` — consumes finalized fallback verification commands (primary).

## Non-Goals

- This story does not require native `cmd.exe` or PowerShell command syntax.
- This story does not prescribe private parsing, matching, traversal, or caching helpers.
- This story does not select or install a JavaScript test framework for a project that has not configured one.
- This story does not validate application behavior inside the selected JavaScript test suite.

## Notes

- The motivating PR records the original deep-discovery and Jest dynamic-route failures.
- The contract is cross-dev-unit because command production, safe substitution, and downstream execution must preserve one observable invariant end to end.
