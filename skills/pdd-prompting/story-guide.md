# Story guide

A Story states one cohesive standalone user loop—who acts, what they do, and what observable outcome they get—so a person can read and approve it in about one minute (`<= 35` lines, `1` to `6` criteria). Read this page in full before writing or changing a Story.

## When to write, edit, or skip a Story

- **`0` Stories + `"No Story: <reason>"` PR line:** Use for internal refactors, `kind: native-only` plumbing, or changes whose user-observable slice is unchanged or already covered by an existing Story.
- **Edit the existing Story:** When modifying or extending an existing user-facing slice, update its Story in `user_stories/` and its paired scenario instead of minting a parallel Story.
- **`1` Story per cohesive standalone user loop:** Keep related steps of one user loop together (never split on `"and"` or into micro-Stories per sub-action). Create `2–3` Stories (indexed in `user_stories/PLAN.md`, which is an index, not a Story) only for genuinely independent user loops, and ask the person before `> 3`.
- **Paired Short JSON scenario (`<story>.json`):** Place `<story>.json` in `tests/` or `test/` (RUNBOOK §2 names the folder when the repo already has `tests/`). Write Short JSON (RUNBOOK §2): omit `criteria` so PDD binds numbered `## Acceptance criteria` automatically from `user_stories/<story>.md` to current `ac-sha256-...` content IDs, set top-level `entry_path` (plus `"app_maps": ["app-map.json"]` when the Story exercises an app map), give steps independent starting states via `seeds` and `{"$use": "base", "patch": {...}}` so steps run concurrently on the server (chaining `$step` or shared `world` only for persistence criteria), and write compact criterion-keyed tuple `checks` (`"1": [["result", "/stdout", "=", "Done #4: Call mom\n"]]`). Standard `program-scenario.v1` JSON is also accepted (`pdd lint --emit-v1 <story>` prints the expanded `v1` JSON locally, and `pdd lint --bind-criteria <story>` binds legacy `AC1` IDs on disk for review at 0 AI calls).

## Structure

1. `# Title`: the user loop in a few plain words.
2. One role line: `As a <specific role>, I want <action>, so that <reason>.`
3. `## Acceptance criteria`: `1` to `6` numbered items starting at `1.` (the only numbered list in the file), written one item per line with straight quotes (`"`). When `<story>.json` omits `criteria`, PDD binds these numbered items automatically (`1`, `2`, ...) to current `ac-sha256-...` content IDs (`tests/` or `test/`, following RUNBOOK §2 when native tests already use `tests/`).
4. Optional bullet (`-`) sections: `## What must not change` (short user context) and `## Rules to check` (user-visible forbidden outcomes only). Route technical invariants and edge cases (symlinks, `.GIT` casing, V1/V2 schemas, numeric/buffer bounds) to `.prompt.md` `## Domain decisions`, never `user_stories/*.md`.

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

## Five authoring rules

1. **Name a real person or narrowed role** ("a customer", "a shop owner", "a developer running `pdd test`") and concrete values ("Sam", "08:30", "$9.00"). Never write generic roles ("a user", "the system").
2. **Keep implementation out of Stories:** Never put file paths (`src/…`, `*.mjs`), function signatures, schema keys, raw hashes/UUIDs, technical edge-case matrices, or vague fillers ("correctly", "gracefully", "as expected") in a Story.
3. **`1` observable check per material claim:** Check every criterion with an exact operator (`equals`, `not_equals`, `one_of`, `count`, `at_least`, `at_most`, `not_contains`, `all_in`, `equals_ignore_case`, or HTML `exists`) on `result`, `error`, `world`, or `calls` without piling duplicate assertions onto one claim.
4. **Ground negative and failure criteria:** Count `0` calls on `<port>.<op>` (`calls`), read unchanged `world` state, or inject a `<port>.<op>` failure via `simulation_overrides` (with a checked `criterion_id` and un-negated `failure_quote`).
5. **Keep long fixtures in `<story>.json`:** Describe boards, seeds, or tables in plain words in the Story. Check `pdd files` + `pdd lint --local` (`<= 35` lines, `<= 6` criteria, checkable `entry_path`) before `pdd test`.
