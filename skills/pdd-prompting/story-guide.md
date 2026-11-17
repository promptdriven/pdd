# Story guide

A Story states what one person does and what observable result they get. Its scenario test checks each numbered criterion against the prompt, and the person reads and approves the Story in about one minute. Read this page in full before writing or changing a Story.

## Files and structure

- **Story (`user_stories/<story>.md`):** `user_stories/PLAN.md` is a build-order index, not a Story. One user behavior = one Story (`1` to `4` criteria).
- **Scenario test (`<story>.json` in `tests/` or `test/`, following RUNBOOK §2 when the repo already has `tests/`):** Copy every numbered criterion into `criteria` word for word on one line, using straight quotes (`"`).

Write a Story with these parts:

1. `# Title`: the user action in a few plain words.
2. One role line: `As a <specific role>, I want <action>, so that <reason>.` (Requires `As a`/`As an`, `I want`, and `so that`.)
3. `## Acceptance criteria`: a numbered list starting at `1.` (the only numbered list in the file).
4. Optional bullet-only (`-`) sections: `## What must not change` (context for the person) and `## Rules to check` (invariants proved in PR 2's formal check, each naming its `Forbidden:` outcome).

```markdown
# Finish a task

As a person who keeps a to-do list in the terminal, I want to mark a task as done, so that I see what is left.

## Acceptance criteria

1. `todo done 4` prints "Done #4: Call mom", exits with code 0 and saves task #4 as done.
2. Task #1 stays not done.
3. `todo done 9` prints "todo: no task #9" to stderr, exits with code 1 and saves nothing.

## Rules to check

- Marking an unknown task fails cleanly. Forbidden: mutating any saved task when the id is missing.
```

## Five rules

1. **Name a real person or narrowed role** ("a customer", "a shop owner", "a developer running `pdd test`") and concrete values ("Sam", "08:30", "$9.00"). Never write generic roles ("a user", "the system").
2. **One criterion = one action and its observable outcome.** Split compound actions. Never put file paths (`src/…`, `*.mjs`), function signatures, schema keys, raw hashes/UUIDs, or vague fillers ("correctly", "gracefully", "as expected") in a Story; workflow Story lint refuses them.
3. **Every criterion needs at least one exact check** (`equals`, `not_equals`, `one_of`, `count`, `at_least`, `at_most`, `not_contains`, `all_in`, `equals_ignore_case`, or HTML `exists`) on `result`, `error`, `world`, or `calls`. Unchecked criteria block automatic PR 1 opening; zero exact checks refuses with `unchecked-criteria`.
4. **Negative and failure criteria need an observable target:** count `0` calls on a declared `<port>.<op>` (`calls`), read unchanged state in `world`, or inject a failure on a declared `<port>.<op>` via `simulation_overrides` (with a checked `criterion_id` and un-negated `failure_quote` from that criterion). Put unobservable invariants or physical disk/process failures in `## Rules to check` and PR 2 native tests.
5. **Keep long fixtures in the test JSON**, describing them in plain words in the Story. Prompts own production modules, never test files.

## Before showing the Story

- Verify every criterion maps to `result`, `error`, `world`, or `calls`, uses straight quotes (`"`), and enters a checkable prompt (never a `kind: native-only` adapter).
- Run `pdd lint --local` for fast local hygiene checks; do not run hosted `pdd lint` right before `pdd test` because `pdd test` includes lint.
