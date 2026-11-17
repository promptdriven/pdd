# Repo hygiene lint

Own `src/repo-hygiene-lint.mjs`. Its module function `lintRepoAntiPatterns({root, files, promptPaths, tests})` returns a deterministic sorted array of advisory `"Warning: …"` lines with `<path>:<line>` and fix guidance for fake source-matching tests, imperative or oversized fenced code blocks in prompts, and Story criteria hygiene. It reads local files inside `root` only, makes no AI or network call, writes no file, and never blocks `pdd lint --local` (which keeps exit code 0 on warnings).

## Workspace scope and safety

Default `files` to Git-visible repository-relative paths (`gitFiles(root)`), filter out secret paths (`isSecretPath`) and paths outside the workspace policy (`workspace.policy({root})`, `workspace.allows(policy, path)`), and skip nested `fixtures/` folders unless explicitly selected in `promptPaths` or `tests`. Open only regular in-root files without following symlinks and skip unreadable, escaping, symlinked or oversized candidates without throwing.

- **Prompts:** With `promptPaths`, inspect only those allowed `.prompt.md` paths; without `promptPaths`, inspect every scoped `.prompt.md`.
- **Stories:** When neither `promptPaths` nor `tests` scopes the run, inspect every scoped `isLintableStoryPath(path)` file. When `tests` or `promptPaths` scopes a Story run, inspect only lintable Stories matched by `tests` or referenced via `story_path` in scoped scenario JSON files whose `steps[].entry_path` or `entry_paths` intersect `promptPaths`.
- **Tests:** Inspect scoped code test files (`isTestOwnedPath(path)` with a code file extension, excluding `fixtures/`, `helpers/`, `.json` scenario files, and structural `*seam.test.*` boundary guards). When `promptPaths` is supplied, keep only fake-test warnings whose inspected target matches one of `promptPaths`.

## Advisory rules

Also export pure single-file helpers `lintFakeTests(text, {path})` and `lintPromptCodeBlocks(text, {path})` returning warning strings in rule and line order:

1. **Fake tests (`Warning: fake test: <path>:<line> [<code>] …`):** Strip comments and ignore code embedded inside string or template literals (such as child-process snippets or synthetic fixture files written to temporary directories), resolve simple local constant string bindings, and ignore targets inside `fixtures`, `harbor` or temporary sandbox roots. Warn when a test:
   - `fake-test-prompt-read`: reads a `.prompt.md` file via `readFileSync` or `readFile` instead of exercising module exports or CLI behavior;
   - `fake-test-exists-check`: calls `existsSync`, `statSync` or `lstatSync` on repository `prompts/` or `src/` paths instead of testing observable behavior;
   - `fake-test-source-match`: reads repository `src/` code text via `readFileSync` or `readFile` and asserts substring or regex matches (`.includes`, `.match`, `.search`, `.indexOf`, `.startsWith`, `.test`, `assert.match`, `assert.doesNotMatch`, `toMatch` or `toContain`) instead of calling exported functions or running the CLI.
2. **Prompt code and pseudo-code bloat (`Warning: prompt code block: <path>:<line> [<code>] …`):** Blank YAML frontmatter, `<details><summary>Runtime interface</summary>` blocks (`## Runtime interface` sections), and HTML comments outside fences while preserving line breaks and 1-based line numbers. Allow `mermaid` and `pdd-boundary` fences unconditionally, and allow short declarative examples (`<= 15` body lines with no imperative control flow, including valid JSON objects or arrays). Warn when:
   - `prompt-code-fence-length`: a non-`mermaid` fence body exceeds 15 lines (at the opening fence line);
   - `prompt-code-fence-total`: total non-`mermaid` fenced body lines across the prompt exceed 30 lines (at the first non-`mermaid` fence line);
   - `prompt-imperative-code`: a non-JSON fence body contains imperative control-flow tokens (`export `, `function `, `const `, `let `, `if (`, `for (`, `while (`, `return `, `=>`, `def `, `impl `, `try {`) (at the first offending line in the fence).
3. **Story criteria hygiene (`Warning: Story hygiene: <path>:<line> [<code>] …`):** Run `lintStory(text, {path, criteriaHygiene: true})` on each scoped Story file and emit one warning per reported problem (`story-missing-criteria`, `story-bloated-criteria`, `story-vague-criterion`, `story-implementation-path`, `story-code-internals`, `story-raw-digest`, `story-generic-role`).

## Dependencies

- [Story quality lint](story-lint.prompt.md): required generation context for `isLintableStoryPath` and `lintStory`.
- [File owner lookup](file-owner.prompt.md): required generation context for `isTestOwnedPath`.
