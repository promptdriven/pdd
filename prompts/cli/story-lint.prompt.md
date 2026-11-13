# Story quality lint

Own `src/story-lint.mjs`. Check authored Story files locally so that Stories state user-observable behavior instead of implementation plumbing. Never call GitHub, Herdr, the PDD interpreter or a model, and never write a file.

## Scope

`isLintableStoryPath(path)` returns `true` when `path` is a canonical repository-relative `.md` path (at most 1,000 characters, `/` separators, no empty, `.`, `..`, `.git` or control-character segments) with a `user_stories` parent folder at any depth, except `PLAN.md` and `README.md` (any letter case).

When scanning a Story's lines (1-based line numbers):

- Ignore fenced code blocks (```` ``` ```` or `~~~`, closed by a fence of the same mark and at least the opening length) and HTML comments (`<!-- … -->`), including multi-line comments, while keeping the original line numbers of surrounding text.
- Inspect the `# ` title heading, the opening lines before the first `## ` heading, `## Acceptance criteria`, and `## What must not change` (also `## Must not change`; any letter case).
- Skip other `## ` sections such as `## Rules to check`, `## Native checks`, `## Native validation` and `## Verification boundary`, where formal invariants or boundary notes belong.

## Problems

Check each inspected non-empty line in rule order and emit at most one problem per `(line, code)`:

1. `story-implementation-path`: the line names a repository implementation folder path (`src/…`, `lib/…`, `dist/…`, `build/…`, `internal/…`, `pkg/…`, `cmd/…`, `__tests__/…`, `prompts/cli/…`, `prompts/test/…`, `prompts/tests/…` or `prompts/__tests__/…`) or a source-code file path ending in `.mjs`, `.cjs`, `.js`, `.ts`, `.tsx`, `.jsx`, `.py`, `.rs`, `.go`, `.java`, `.kt`, `.rb`, `.php`, `.cs`, `.cpp`, `.cc`, `.c`, `.hpp`, `.h` or `.swift`. Ignore source extensions inside a quoted or backticked test-runner command (`node`, `npm`, `pnpm`, `yarn`, `pytest`, `cargo` or `go`) when a Story describes passing a command string to a CLI tool; still flag implementation folder paths (`src/…`, `lib/…`, `prompts/cli/…`, `prompts/test/…`). User commands such as `` `todo done 4` `` or `` `pdd test` `` and user data files such as `report.csv`, `notes.txt` or `pdd.json` are allowed.
2. `story-code-internals`: the line contains low-level code syntax, signatures or runtime/byte internals: `export function` / `export async function` / `export const` / `export class` / `export default`, `async function`, `function name(`, arrow functions (` => `), camelCase call signatures (`fooBar(…)`), multi-argument snake_case call signatures (`foo_bar(a, …)`), or internal terms `AST`, `Abstract Syntax Tree`, `bit-flip` (`bit-flips`, `bit-flipping`), `bitmask` (`bitmasks`), hexadecimal masks (`0x…` with two or more hex digits), `Uint8Array`, `Int32Array`, `Float64Array`, `ArrayBuffer`, `Buffer.from`, `RegExp`, `process.exit`, `child_process`, `fs.read…` / `fs.write…` / `fs.lstat…` / `fs.stat…` / `fs.open…` / `fs.exists…`, `TypeError`, `ReferenceError` or `SyntaxError`.
3. `story-raw-digest`: the line contains a raw 64-character hex digest, a raw 40-character hex object id, a `sha256:…` digest prefix (7 or more hex digits), or a raw UUID (`8-4-4-4-12` hex).
4. `story-generic-role`: the line names a non-person role with `As a user`, `As an end user`, `As the user`, `As a system` or `As the system` (any letter case) instead of a real person or role. Stories that open with `I can …`, a named role (`As a customer`, `As a shop owner`, `As a PDD user`), or go straight to `# Title` and `## Acceptance criteria` are allowed.
5. `story-vague-criterion`: inside `## Acceptance criteria`, the line uses an uncheckable filler phrase (`works correctly`, `work correctly`, `handled gracefully`, `handle gracefully`, `properly handled`, `as expected`, `seamlessly`, `gracefully` or `correctly`) instead of stating the observable result.

Each problem is `{path, line, code, message, excerpt}`, where `excerpt` is the trimmed offending line cut to at most 140 characters, and `message` states both why the match failed and how to rewrite it in user-observable terms.

## Public contract

- `isLintableStoryPath(path)`: return `true` when `path` is a lintable Story path as above.
- `lintStory(text, {path = 'user_stories/story.md'} = {})`: pure. Return `{ok, path, problems}`, with `ok` equal to `problems.length === 0`.
- `lintStories(entries = [])`: pure. Accept `{path, text}` rows, skip rows where `!isLintableStoryPath(path)`, lint the rest in order, and return `{ok, problems}`.
- `formatStoryLint(result)`: pure. Return `''` when `!result` or `result.ok` or `!result.problems?.length`. Otherwise return plain text starting with `Story quality check failed:`, listing each `  PATH:LINE [CODE] MESSAGE` and `    > EXCERPT`, and ending with one rewrite instruction telling the author to state who uses the behavior, what they do and what they see, while keeping file paths, function signatures, hashes and bit-level internals in module prompts or tests.

## Callers and context

- [Story guide](../../docs/story-guide.md): authoring rules that this check enforces locally.
- [Prompt approve](prompt-approve.prompt.md) and [workflow runner](workflow-runner.prompt.md): run `lintStories` on changed Story files at approval and pre-PR gates.
