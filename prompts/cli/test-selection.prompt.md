# Test selection by PDD file names

Own `src/test-selection.mjs`: the one PDD owner of Story and test pairing by file names, selector-word resolution (`pdd test`, `pdd lint`, `pdd simulate`), and the no-tests explanation. It opens no `*.json` file to decide what is a test.

<a id="test-name-rule"></a>
## Test name rule

The tests of Story `S` (`user_stories/**/S.md`) are the Git-visible regular files `S.json` and `S.<variant>.json` in a folder named `test` or `tests`, at any depth (`tests/S.json`, `tests/runtime/S.json`, `runtime/tests/S.json`, `tests/S.empty-shop.json`).

- A *Story file* (`isStoryPath(path)`) is a path ending in `.md` with `user_stories` in its directory components whose basename is neither `PLAN.md` nor `README.md` (case-insensitive).
- A Story file counts as a Story (`hasAcceptance(text)`) when its text contains a line-starting `## Acceptance` or `## Acceptance Criteria` heading (`\n` line boundaries, case-insensitive, horizontal spaces or tabs only). A Story file with no acceptance heading still claims tests matching its basename, so those files do not become orphans, while never receiving a `has no test` warning.
- A *test-folder JSON file* is a path ending in `.json` with `test` or `tests` as any directory component.
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
- Require `ports.allowsPath(root, path)` and `ports.hasInterfaceBlock(root, path)` (and `ports.discoverTests(root, [...visible])` when `found` is omitted), throwing a clear unbound-port `Error` when omitted.
- Filter `visible` by `ports.allowsPath(root, path)` and sort. Collect lines in order: `found.untested` lines, `found.orphans` lines, `PDD prompts must end in .prompt.md: rename <path> to <path>.md.` for each `*.prompt` file, and `<path> has no Runtime interface block. See RUNBOOK.md §2.` for each `*.prompt.md` file where `ports.hasInterfaceBlock(root, path)` is false.
- Return at most 5 lines; when more exist, return the first 5 followed by `…and N more`. Open no JSON file.

## Dependencies

Node `node:path` (`basename`, `posix`) supplies pure path operations.

## Caller navigation

[`src/runtime-seam.mjs`](runtime-seam.prompt.md) supplies these functions to [`src/runtime/runtime-preflight.mjs`](runtime-preflight.prompt.md), [`src/runtime/agent-project.mjs`](agent-project.prompt.md), [`src/runtime/product-composition.mjs`](product-composition.prompt.md), and [`src/runtime/runtime-client.mjs`](runtime-client.prompt.md) as ports, and binds preflight's `captureSource`, `discoverTests`, workspace path check, and interface reader when pdd callers invoke `selectTests` or `whyNoTests`.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"draft","prose_sha256":"ae48e4fbcf451e13eba44fd5f3ac81d3095faf45410ca428c0ee90f09f1c0da0","reason":"Exposes synchronous host-bound callbacks for native Story capture and repository interface inspection alongside pure path-matching functions consumed across pdd and Runtime ports."}
```
</details>
