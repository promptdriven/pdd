<!-- pdd-story-prompts: get_test_command_python.prompt -->
<!-- pdd-story-dev-units: agentic_fix_python.prompt, agentic_langtest_python.prompt, fix_error_loop_python.prompt, get_run_command_python.prompt, get_test_command_python.prompt -->

# User Story: Nested TypeScript tests use the correct runner safely

## Story

As a developer working in a nested JavaScript workspace, I want PDD to execute a test with the runner and project that actually own it, so a verification cannot silently run zero tests, cross a repository boundary, or reinterpret an untrusted path as shell syntax.

## Covers

- R1: Command resolution follows the documented priority and falls back safely.
- R2: TypeScript tests select the nearest applicable Playwright, Jest, or Vitest runner.
- R3: Deeply nested tests can inherit a runner without a fixed shallow walk limit.
- R4: Workspace members inherit only through their declared workspace boundary.
- R5: Unrelated or excluded packages never borrow an ancestor runner.
- R6: Workspace include, exclude, and re-inclusion decisions match the declaring ecosystem.
- R7: A pnpm workspace declaration remains authoritative over stale npm metadata.
- R8: Malformed, unsafe, or oversized workspace declarations fail closed.
- R9: Hostile manifests and patterns are evaluated within deterministic resource bounds.
- R10: Symlinks and path traversal cannot escape the repository boundary.
- R11: Jest and Playwright receive literal-equivalent test targets.
- R12: Appended test paths remain one shell-safe argument.
- R13: Runner working directories and CSV placeholder substitution remain safe and deterministic.
- R14: A completed command is never subjected to a second placeholder substitution pass.

## Context / Fixtures

The regression suite creates temporary standalone repositories, npm and pnpm workspaces, nested Next.js-style dynamic routes, runner configurations, hostile manifests, symlinks, and shell-metacharacter-bearing paths. No external service is required.

## Acceptance Criteria

1. Given a deeply nested TypeScript test, when PDD resolves its command, then it selects only the nearest runner that the owning package may inherit and returns that runner's configuration directory as the working directory.
2. Given npm/yarn/lerna or pnpm include and exclude patterns, when membership is evaluated, then the result matches that ecosystem's re-inclusion behavior and never grants membership to an excluded, unrelated, or `node_modules` package.
3. Given malformed, oversized, recursively nested, or computationally hostile workspace input, when discovery runs, then it terminates within the configured budgets, returns no inherited runner, and raises no exception.
4. Given a dynamic-route or shell-metacharacter-bearing test path, when the command is returned, then the intended runner receives exactly one path argument, its metacharacters remain literal characters, and the command is not re-substituted.
5. Given a path or configuration symlink that escapes the repository, when discovery runs, then no foreign runner configuration is adopted; an in-repository symlink continues to work.

## Oracle

- The selected runner, test target, and working directory identify the owning project.
- Excluded or foreign packages receive no inherited runner.
- Literal dynamic-route tests are collected and shell metacharacters remain data.
- Hostile inputs terminate deterministically and fail closed.

## Non-Oracle

- Private helper names and matcher implementation strategy.
- Cache layout and internal traversal order when observable selection is unchanged.
- Exact diagnostic wording.

## Forbidden Outcomes

- Reporting success after Jest matched zero tests because route brackets were treated as regex.
- Executing under an unrelated ancestor or outside the repository through a symlink.
- Re-evaluating a substituted path as active shell syntax.
- Hanging or exhausting memory on repository-controlled workspace metadata.
