# Story structural lint

Own `src/story-lint.mjs`. Run deterministic structural checks on authored Story files offline so every Story declares a non-empty `## Acceptance criteria` section. Semantic review for role specificity, vague criteria, criterion count, length, or leaked implementation details belongs in AI lint (`pdd lint --ai`), never offline prose regexes. Never call GitHub, Herdr, the PDD interpreter or a model, and never write a file.

## Scope

`isLintableStoryPath(path)` returns `true` when `path` is a canonical repository-relative `.md` path (at most 1,000 characters, `/` separators, no empty, `.`, `..`, `.git` or control-character segments) inside a `user_stories` or `pdd/stories` folder at any depth, except `PLAN.md` and `README.md` (any letter case).

When scanning a Story's lines (1-based line numbers):

- Treat Markdown fenced code blocks (```` ``` ```` or `~~~`, closed by a fence of the same mark and at least the opening length) and HTML comments (`<!-- … -->`, including multi-line comments) strictly as formatting while preserving original line numbers of surrounding text.

## Problems

When `criteriaHygiene` is enabled (`true` by default in `lintStory`):

1. `story-missing-criteria`: the Story has no `## Acceptance criteria` (`## Acceptance`) heading or that section has zero numbered (`1.`, `1)`) or top-level bullet (`-`, `*`, `+`) items outside fenced blocks and comments. Report at the heading line when present, otherwise the first non-empty line (or line 1).

Each problem is `{path, line, code, message, fix, excerpt}`, where `excerpt` is the trimmed offending line cut to at most 140 characters.

## Public contract

- `isLintableStoryPath(path)`: return `true` when `path` is a lintable Story path as above.
- `lintStory(text, {path = 'user_stories/story.md', criteriaHygiene = true} = {})`: pure. Return `{ok, path, problems}`, with `ok` equal to `problems.length === 0`.
- `lintStories(entries = [], {criteriaHygiene = false} = {})`: pure. Accept `{path, text}` rows, skip rows where `!isLintableStoryPath(path)`, lint the rest with `{path: entry.path, criteriaHygiene}` in order, and return `{ok, problems}`.
- `formatStoryLint(result)`: pure. Return `''` when `!result` or `result.ok` or `!result.problems?.length`. Otherwise return plain text starting with `Story quality check failed:`, listing each `  PATH:LINE [CODE] MESSAGE` and `    > EXCERPT`, and ending with one rewrite instruction.

## Callers and context

- [Story guide](../../skills/pdd/references/stories.md): authoring rules that this check enforces locally.
- Local lint and verification callers: run `lintStories` or `lintStory` on authored Story files.
