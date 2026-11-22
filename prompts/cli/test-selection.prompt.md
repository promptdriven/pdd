# Test selection by PDD file names and affected dependency graph

Own `src/test-selection.mjs`: the one PDD owner of Story and test pairing by file names, selector-word resolution (`pdd test`, `pdd lint`, `pdd simulate`), affected native test selection from changed files, and the no-tests explanation. Pairings by name open no `*.json` file; affected native test selection reads source imports and scenario links only through repository or injected ports.

<a id="test-name-rule"></a>
## Test name rule

The tests of Story `S` (`user_stories/**/S.md`) are the Git-visible regular files `S.json` and `S.<variant>.json` in a folder named `test` or `tests`, at any depth (`tests/S.json`, `tests/runtime/S.json`, `runtime/tests/S.json`, `tests/S.empty-shop.json`).

- A *Story file* (`isStoryPath(path)`) is a path ending in `.md` with `user_stories` in its directory components whose basename is neither `PLAN.md` nor `README.md` (case-insensitive).
- A Story file counts as a Story (`hasAcceptance(text)`) when its text contains a line-starting `## Acceptance` or `## Acceptance Criteria` heading (`\n` line boundaries, case-insensitive, horizontal spaces or tabs only). A Story file with no acceptance heading still claims tests matching its basename, so those files do not become orphans, while never receiving a `has no test` warning.
- A *test-folder JSON file* is a path ending in `.json` with `test` or `tests` as any directory component, excluding non-scenario subdirectories (`fixtures`, `__fixtures__`, `mocks`, `__mocks__`, `snapshots`, `__snapshots__`, `data`, `testdata`, `golden`, `cassettes`) beneath the innermost `test` or `tests` directory and excluding standard project/tooling config filenames (`tsconfig*.json`, `jsconfig.json`, `package.json`, `package-lock.json`, `npm-shrinkwrap.json`, `composer.json`, `biome.json`, `deno.json`, `jsr.json`, `eslint.json`, `prettier.json`, `vitest.json`, `jest.json`, `babel.json`). Nested projects that contain their own inner `test/` or `tests/` directory still pair normally.
- `expectedTestPath(storyPath)` returns `<dir>tests/<S>.json`, where `<dir>` is the path prefix before the Story's nearest `user_stories` directory (empty when `user_stories` is at the repository root) and `<S>` is the Story basename without `.md`.
- A test-folder JSON file named `N.json` fits Story name `N` and every Story name `S` where `N` is `S.<variant>`. One fit pairs the file with that Story; zero fits is an orphan; two or more fits (`tests/a.b.json` with Stories `a` and `a.b`) is a conflict, and pdd never picks one.

| Names found | Result | Line (without `Warning: ` prefix unless noted) |
|---|---|---|
| A Story and its files, each basename used once | Paired tests | none |
| A Story name with no matching file and not claimed by a multi-Story conflict | Untested | `<story> has no test: expected <expectedTestPath(story)> (or <S>.json in any test or tests folder).` |
| Test-folder JSON files fitting no Story name | Orphans | Per file: `<file> matches no Story (user_stories/**/N.md).` Summary (`orphanSummary(orphans)`): for 1 file `Warning: <line>`; for `K > 1`, `Warning: K JSON files in test folders match no Story (the tests of user_stories/**/S.md are S.json and S.<variant>.json). pdd test --files lists them.` |
| Two or more files sharing `<name>.json` for one Story | Conflict | `<story> has N files named <name>.json: <files>. Keep one.` |
| A file fitting two or more Story names, or multiple Story files sharing a Story name that has test files | Conflict | `<files> match[es] N Stories: <stories>. Rename one.` |

Lists are sorted ASCII-lexicographically; three or more items join with `, ` and final ` and `.

Export synchronous `matchTests(storyPaths, files)` returning `{tests, untested, orphans}`:
- `tests`: sorted by `path`, each `{path, files, story, storyPath, storyPaths, problem}` (`path` is `files[0]`, `storyPath` is the single Story path or `null` when multiple Story paths share the name, `problem` is the conflict sentence or `null`).
- `untested`: sorted by `storyPath`, each `{story, storyPath, line}`.
- `orphans`: sorted by `path`, each `{path, line}`.

## Selector words and native Story descriptors

Export synchronous `selectTests(found, words = [], { native = false, captureSource } = {})`:
- Empty `words` returns `{selected: [...found.tests], unknown: [], untested: []}` (without `nativeSelections`).
- Strip a leading `./` from each word. A word matches a discovered test when it equals `test.path`, any member of `test.files`, `test.storyPath`, any member of `test.storyPaths`, `test.story`, the test basename without `.json`, any `test.storyPaths` basename without `.md`, `.` (all discovered tests), or a non-escaping directory prefix (`word` is neither `..` nor `../...`, and `test.path`, `test.files`, `test.storyPaths` or `test.storyPath` starts with `${word.replace(/\/$/, '')}/`).
- Preserve `found.tests` order without duplicates across multiple words.
- When `native` is true, also match `found.nativeSelections` (`{storyPath, story, section}`) by `storyPath`, `story`, `.`, or bounded directory prefix. Resolve each unique matched native Story's single local `[...](REL#native-validation-profile-ID)` link relative to `storyPath`, require a `.prompt.md` target, and capture `{tests: [storyPath, promptPath]}` through the injected `captureSource` port (throwing an unbound-port `Error` if `captureSource` is omitted when a native link is selected). Rethrow source/workspace boundary errors (`PreflightError` or numeric `exitCode`); convert missing/ambiguous links, non-prompt targets, or ordinary capture errors into `{storyPath, promptPath, profileId, reason}`, and return `{storyPath, promptPath, profileId, sourceReferences: captured.files}` on success.
- A word with neither test nor native hits checks `found.untested` by `storyPath` or `story`: matches append `item.line` to `untested`, never `unknown`; otherwise append the original `raw` word to `unknown`. Return `{selected, nativeSelections, unknown, untested}` for nonempty `words`.

## Empty-repository explanation

Export `NO_TESTS` (`'No tests found. The test of Story user_stories/S.md is S.json in a test or tests folder. See RUNBOOK.md §2.'`) and synchronous `whyNoTests(root, visible, found, ports = {})`:
- Require `ports.allowsPath(root, path)` (and `ports.discoverTests(root, [...visible])` when `found` is omitted), throwing a clear unbound-port `Error` when omitted.
- Filter `visible` by `ports.allowsPath(root, path)` and sort. Collect lines in order: `found.untested` lines, `found.orphans` lines, and `PDD prompts must end in .prompt.md: rename <path> to <path>.md.` for each `*.prompt` file. Plain `*.prompt.md` files without embedded Runtime interface blocks are valid and emit no diagnostic.
- Return at most 5 lines; when more exist, return the first 5 followed by `…and N more`. Open no JSON file.

## Affected native test selection

Export synchronous `isRunnableTestPath(path)`, `classifyGlobalSuiteTrigger(changedFiles, options = {})`, `formatAffectedTestsSummary(plan)`, and `selectAffectedTests(options = {}, ports = {})` so iterative worker check and verify runs execute only affected native test files while reserving the full suite for global infrastructure changes and pre-merge verification:

- **Runnable test entries (`isRunnableTestPath(path)`).** Normalize Windows `\` separators to `/` before path checks, reject absolute/drive-letter/UNC/`..` paths, and accept safe repository-relative paths outside `src/`, `node_modules/`, `.git/`, `dist/`, `build/`, `vendor/`, `fixtures/`, and `helpers/` directories whose filename matches `*.test.*` or `*.spec.*` across JavaScript and TypeScript extensions (`js`, `mjs`, `cjs`, `jsx`, `ts`, `mts`, `cts`, `tsx`).
- **Safe global full-suite fallback (`classifyGlobalSuiteTrigger`).** Normalize `\` separators before classification and fall back to `mode: 'full'` (`selectedTests = totalTests`) ONLY when changed files cannot be determined safely, contain unsafe path traversal, or touch:
  - `global-test-helper`: shared helper or fixture paths under `test/helpers/**`, `tests/helpers/**`, `__tests__/helpers/**`, `test/fixtures/**`, `tests/fixtures/**`, `__tests__/fixtures/**`, or root test setup preload files;
  - `package-config`: `package.json`, lockfiles (`package-lock.json`, `npm-shrinkwrap.json`, `pnpm-lock.yaml`, `yarn.lock`, `bun.lock`, `bun.lockb`), `pdd.json`, `pdd-bindings.json`, `tsconfig*.json`, `jsconfig.json`, `.npmrc`, `.nvmrc`, `.node-version`, or test runner config files;
  - `core-shared-infrastructure`: CLI entrypoints under `bin/**`, shared suite runner modules (`src/test-suite-*.mjs` and their prompts), the shared runtime seam (`src/runtime-seam.mjs` and its prompt), or caller-declared `coreInfrastructure` paths.
- **Affected graph resolution (`selectAffectedTests`).** Normalize `\` separators across `files` and `changedFiles` (defaulting to Git branch diff against `baseRef` plus working-tree changes via `ports.readChangedFiles`), discover `totalTests` from `options.files` or `ports.listFiles`, and inspect code/test files through `ports.readFile`:
  - *Direct and stem matches:* select changed existing runnable test files directly; for changed code modules (`src/**`, `lib/**`, `app/**`), module prompts (`prompts/**/*.prompt.md`), Stories (`user_stories/**/*.md`), and scenario files, select runnable tests matching `<stem>.test.*`, `<stem>.<variant>.test.*`, or `<stem>-<suffix>.test.*` (normalizing `_` and `-` equivalents).
  - *Reverse-import closure (`src/` -> `src/` -> `test/`):* lex JS/TS sources with comment, string, `/…/` regex-literal, and nested `` `…${…}…` `` template-interpolation awareness to extract relative `import`, `export * from`, `export { … } from`, two-statement `import … from` + `export { … }` re-exports, dynamic `import()`, `require()`/`req()`, and `new URL(..., import.meta.url)` specifiers across code modules and non-global test helper modules. Propagate transitively across affected code modules and local test helpers to runnable `test/` files; bound fan-out at untouched high-fanout dispatcher hubs (`outgoingSrcImports >= dispatcherImportThreshold`, default `12`) while bridging `export *`, aliased one- or two-statement re-exports, and shared exported symbols through hubs and local test helpers to consuming tests. When a changed production module still yields `0` selected tests, bridge through its reached dispatcher hubs (matching specific stem-part tests and hub-importing tests referencing its stem/subcommand, else direct test importers of those hubs), and fall back to `mode: 'full'` (`unmapped-code-change`) if any changed production path under `src/**`, `lib/**`, or `app/**` still resolves to `0` tests. Record unresolved relative code targets so deleted modules still select existing importers.
  - *Prompt, Story, doc, and skill contracts:* map changed `prompts/**/*.prompt.md` to owned code modules (`Prompt:` / `Generated from` headers, `pdd-bindings.json`, and stem matches), scenario `entry_path` tests, path-referencing tests, and existing prompt contract tests under `test/` or `test/core/lint/` (frontmatter, prompt approval, file ownership, authoring/repo hygiene lint). Map changed `user_stories/**/*.md` and scenario JSON files to paired Story/replay/formal tests, path-referencing tests, and existing Story lint/discovery contract tests under `test/` or `test/core/lint/`. Map changed `docs/**` (and root `README.md`, `RUNBOOK.md`, `AGENTS.md`, `CLAUDE.md`) to `docs*`/`runbook*` contract tests, path-referencing tests, and guide-parity tests. Map changed `skills/**` to `*skill*`/`runbook*`/authoring/setup contract tests and path-referencing tests. Include existing `smokeTests` when supplied.
- **Reporting (`formatAffectedTestsSummary`).** Return `{mode, selectedTests, totalTests, selectedCount, totalCount, changedFiles, smokeTests, fallbackReason, fallbackCategory, reasons, summary}` where `summary` always states `selectedCount` vs `totalCount` (`Affected tests: selected K of M test files (...)` or `Affected tests: running full suite (M of M test files; fallback: REASON).`).

## Dependencies

Node `node:path` (`basename`, `posix`), `node:fs`, and `node:child_process` (`execFileSync`) supply path operations and default local repository file/diff ports when callers omit injected `ports`.

## Caller navigation

[PDD to Runtime seam](runtime-seam.prompt.md) supplies these functions to `@promptdriven/runtime-client` as ports, and binds preflight's `captureSource`, `discoverTests`, and workspace path check when pdd callers invoke `selectTests` or `whyNoTests`.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"approved","prose_sha256":"29f73bf12b94782bbed04a2d350046e478a1a828ae176446ad9b81c2fbe1360f","reason":"Exposes synchronous host-bound callbacks for native Story capture, repository import-graph inspection, and pure path-matching functions consumed across pdd and Runtime ports."}
```
</details>
