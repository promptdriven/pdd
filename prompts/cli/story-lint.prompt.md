# Story quality lint

Own `src/story-lint.mjs`. Check authored Story files locally so that Stories state user-observable behavior and bounded acceptance criteria instead of implementation plumbing. Never call GitHub, Herdr, the PDD interpreter or a model, and never write a file.

## Scope

`isLintableStoryPath(path)` returns `true` when `path` is a canonical repository-relative `.md` path (at most 1,000 characters, `/` separators, no empty, `.`, `..`, `.git` or control-character segments) inside a `user_stories` or `pdd/stories` folder at any depth, except `PLAN.md` and `README.md` (any letter case).

When scanning a Story's lines (1-based line numbers):

- Ignore fenced code blocks (``` ``` ``` or `~~~`, closed by a fence of the same mark and at least the opening length) and HTML comments (`<!-- … -->`), including multi-line comments, while keeping the original line numbers of surrounding text.
- Inspect the `# ` title heading, the opening lines before the first `## ` heading, `## Acceptance criteria` (also `## Acceptance`; any letter case), and `## What must not change` (also `## Must not change`; any letter case).
- Skip other `## ` sections such as `## Rules to check`, `## Native checks`, `## Native validation` and `## Verification boundary`, where formal invariants or boundary notes belong.

## Problems

Check each inspected non-empty line in rule order and emit at most one problem per `(line, code)`:

1. `story-implementation-path`: the line names a repository implementation folder path (`src/…`, `lib/…`, `dist/…`, `build/…`, `internal/…`, `pkg/…`, `cmd/…`, `__tests__/…`, `prompts/cli/…`, `prompts/test/…`, `prompts/tests/…` or `prompts/__tests__/…`), a JS/TS module filename ending in `.mjs`, `.cjs`, `.ts`, `.tsx` or `.jsx`, a `*.test.*` / `*.spec.*` / `test_*` / `*_test.*` test file, or a slash-qualified source path (`folder/file.ext`) ending in `.js`, `.py`, `.rs`, `.go`, `.java`, `.kt`, `.rb`, `.php`, `.cs`, `.cpp`, `.cc`, `.c`, `.hpp`, `.h` or `.swift`. Ignore URLs (`http://…`, `https://…`) and source extensions inside a quoted or backticked test-runner command (`node`, `npm`, `pnpm`, `yarn`, `pytest`, `cargo` or `go`); bare product or domain names such as `Next.js`, `Node.js` or `shop.rs`, user commands such as `` `todo done 4` `` or `` `pdd test` ``, and user data files such as `report.csv`, `notes.txt` or `pdd.json` are allowed.
2. `story-code-internals`: the line contains low-level code syntax, signatures or runtime/byte internals: `export function` / `export async function` / `export const` / `export class` / `export default`, `async function`, `function name(`, arrow functions (` => `), camelCase call signatures (`fooBar(…)`), multi-argument snake_case call signatures (`foo_bar(a, …)`), or internal terms `AST`, `Abstract Syntax Tree`, `bit-flip` (`bit-flips`, `bit-flipping`), `bitmask` (`bitmasks`), hexadecimal masks (`0x…` with two or more hex digits), `Uint8Array`, `Int32Array`, `Float64Array`, `ArrayBuffer`, `Buffer.from`, `RegExp`, `process.exit`, `child_process`, `fs.read…` / `fs.write…` / `fs.lstat…` / `fs.stat…` / `fs.open…` / `fs.exists…`, `TypeError`, `ReferenceError` or `SyntaxError`.
3. `story-raw-digest`: the line contains a raw 64-character hex digest, a raw 40-character hex object id, a `sha256:…` digest prefix (7 or more hex digits), or a raw UUID (`8-4-4-4-12` hex).
4. `story-generic-role`: the line names an unqualified non-person role (`As a user`, `As an end user`, `As the user`, `As a system`, `As the system` or `As a caller`, followed directly by punctuation, end-of-line or `I want` / `I can` / `I need`) instead of a real person or narrowed role. Qualified roles (`As a user of …`, `As a user with …`, `As a person who …`), named roles (`As a customer`, `As a shop owner`), `I can …`, or `# Title` followed by `## Acceptance criteria` are allowed.
5. `story-vague-criterion`: inside `## Acceptance criteria`, the unquoted prose uses an ungrounded filler phrase (`works correctly`, `work correctly`, `handled gracefully`, `handle gracefully`, `properly handled`, `as expected`, `seamlessly`, `gracefully`, `properly` or `correctly`) without a concrete observable anchor on the same line (such as a quoted UI literal or an explicit exit/HTTP status or call count).

When `criteriaHygiene` is enabled (`true` by default in `lintStory`):

6. `story-missing-criteria`: the Story has no `## Acceptance criteria` (`## Acceptance`) heading or that section has zero numbered (`1.`, `1)`) or top-level bullet (`-`, `*`, `+`) items outside fenced blocks and comments. Report at the heading line when present, otherwise line 1.
7. `story-bloated-criteria`: `## Acceptance criteria` (`## Acceptance`) has more than 6 acceptance items (counted across numbered items when any numbered item is present, otherwise top-level bullet items, without counting wrapped continuation lines). Report at the 7th item's line with the total count and advise keeping 1 Story per cohesive user loop and moving technical invariants to `.prompt.md` `## Domain decisions` or `## Rules to check`.
8. `story-too-long`: the Story exceeds 35 lines (ignoring trailing blank lines). Report at line 36 with the total line count and advise keeping Stories concise (`<= 35` lines) and routing technical invariants, edge-case tables or fixtures to `.prompt.md` `## Domain decisions` or test JSON files.

Each problem is `{path, line, code, message, excerpt}`, where `excerpt` is the trimmed offending line cut to at most 140 characters, and `message` states both why the match failed and how to rewrite it in user-observable terms.

## Public contract

- `isLintableStoryPath(path)`: return `true` when `path` is a lintable Story path as above.
- `lintStory(text, {path = 'user_stories/story.md', criteriaHygiene = true} = {})`: pure. Return `{ok, path, problems}`, with `ok` equal to `problems.length === 0`.
- `lintStories(entries = [], {criteriaHygiene = false} = {})`: pure. Accept `{path, text}` rows, skip rows where `!isLintableStoryPath(path)`, lint the rest with `{path: entry.path, criteriaHygiene}` in order, and return `{ok, problems}` so pre-PR and approval callers preserve existing admission unless `criteriaHygiene: true` is requested.
- `formatStoryLint(result)`: pure. Return `''` when `!result` or `result.ok` or `!result.problems?.length`. Otherwise return plain text starting with `Story quality check failed:`, listing each `  PATH:LINE [CODE] MESSAGE` and `    > EXCERPT`, and ending with one rewrite instruction telling the author to state who uses the behavior, what they do and what they see, while keeping file paths, function signatures, hashes and bit-level internals in module prompts or tests.

## Callers and context

- [Story guide](../../skills/pdd/references/stories.md): authoring rules that this check enforces locally.
- [Prompt approve](prompt-approve.prompt.md) and workflow runner: run `lintStories` on changed Story files at approval and pre-PR gates.
