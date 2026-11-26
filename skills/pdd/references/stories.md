# Stories and scenario JSON

A **Story** states one cohesive standalone user loop — who acts, what they do, and what observable outcome they get — so a person can read and approve it in about one minute (`<= 35` lines, `1` to `6` criteria).

## 1. When to write, edit, or skip a Story

- **`0` Stories + `"No Story: <reason>"` PR line:** Internal refactors, `kind: native-only` plumbing, or changes already covered by an existing Story over an injected port.
- **Edit the existing Story:** When extending or changing an existing user-facing slice, update its Story and scenario rather than minting a duplicate.
- **`1` Story per cohesive standalone user loop:** Keep related steps of one loop together. Create `2–3` Stories only for genuinely independent user loops, and ask before `> 3`.
- **Technical invariants belong in `.prompt.md`:** Keep symlinks, `.GIT` casing, schema edge cases, and buffer limits in `.prompt.md` `## Domain decisions` (verified natively), never in `user_stories/*.md`.

## 2. Story structure

1. `# Title`: the user loop in plain words.
2. One role line: `As a <specific role>, I want <action>, so that <reason>.`
3. `## Acceptance criteria`: `1` to `6` numbered items starting at `1.` (the only numbered list in the file), one item per line, straight quotes (`"`). AC1 should name the real user-facing surface.
4. Optional bullet (`-`) sections: `## What must not change` and `## Rules to check` (user-visible forbidden outcomes only).

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

### Five authoring rules

1. Name a specific role (`"a customer"`, `"a shop owner"`) and concrete values (`"Sam"`, `"08:30"`, `"$9.00"`), never generic `"a user"` or `"the system"`.
2. Keep implementation code and internal plumbing out of Stories (including inside fenced code blocks) — move implementation details to the owning `.prompt.md` and large sample fixtures to `tests/` or `fixtures/`. Exact values and short examples are fine when they define what the user actually sees; avoid vague fillers (`"correctly"`, `"gracefully"`).
3. Write `1` observable check per material claim without piling redundant assertions onto one claim.
4. Ground negative and failure criteria with `calls = 0`, unchanged `world` state, or `simulation_overrides`.
5. Keep long fixtures in the paired scenario JSON, not inline in the Story.

## 3. Compact scenario JSON (`tests/<slug>.json`)

Place `<slug>.json` in `tests/` or `test/` (use `tests/runtime/` or `test/runtime/` when the repo keeps native tests in `tests/` or `test/`). Keep compact scenario JSON directly on disk (`/v1/check`, `/v1/lint`, `/v1/try` accept it natively):

- Omit `schema_version`, `story_path`, and `criteria` so PDD infers `user_stories/<slug>.md` and binds numbered criteria automatically to current `ac-sha256-...` IDs.
- Set top-level `"entry_path"` (override per step when calling another prompt).
- Use top-level `"seeds"` + step `"from"` + `"patch"` to template repeated step inputs cleanly (do not combine `"from"` and `"input"` on the same step). All steps execute against top-level `"initial_world"` (carrying world mutations forward across sequential steps). Because `"patch"` uses RFC 7396 JSON Merge Patch (where `null` deletes keys), use `"set": {"/a/b": null}` to assign literal `null` or replace array elements.
- Chain `{"$step": "step-id#/field"}` or mutate shared `"initial_world"` only for persistence criteria.
- Keep scenarios compact: **every criterion needs at least one exact check** (one cohesive step may verify multiple criteria; `5–8` steps typical, cap `15` steps, `<= 10` moves/rows/calls per step, `10` min server cap per step). Omit step `"model"`.

```json
{
  "entry_path": "prompts/todo.prompt.md",
  "initial_world": {
    "kv": {
      "tasks": [
        {"id": 1, "title": "Buy milk", "done": false},
        {"id": 4, "title": "Call mom", "done": false}
      ]
    }
  },
  "simulation": {
    "store.load": {"action": "key-value.get", "world_pointer": "/kv", "key_argument_pointer": "/key", "value_argument_pointer": null, "item_key_pointer": null, "item_value_pointer": null, "result_template": {"value": null}, "result_value_pointer": "/value"},
    "store.save": {"action": "key-value.put", "world_pointer": "/kv", "key_argument_pointer": "/key", "value_argument_pointer": "/value", "item_key_pointer": null, "item_value_pointer": null, "result_template": {"value": []}, "result_value_pointer": "/value"}
  },
  "steps": [
    {
      "id": "done-4",
      "op": "main",
      "input": {"argv": ["done", "4"]},
      "checks": {
        "1": [["result", "/stdout", "=", "Done #4: Call mom\n"], ["result", "/exit_code", "=", 0], ["world", "/kv/tasks/1/done", "=", true]],
        "2": [["world", "/kv/tasks/0/done", "=", false]]
      }
    },
    {
      "id": "missing-9",
      "op": "main",
      "input": {"argv": ["done", "9"]},
      "checks": {
        "3": [["result", "/stderr", "=", "todo: no task #9\n"], ["result", "/exit_code", "=", 1], ["calls", "store.save", "=", 0]]
      }
    }
  ]
}
```

## 4. Check targets, operators, schemas, and dates

- **4 targets:** `result`, `error` (shorthand `["error", "=", "code"]`), `world`, `calls` (never `output`), plus HTML shorthands (see [ui-and-screens.md §3](ui-and-screens.md#3-html-checks-and-prompt-interpreter-rules)). `input` is valid only as a `ref_target` reference source.
- **14 exact operators:** `equals` (`=`), `not_equals` (`!=`), `not_contains`, `count`, `one_of`, `all_in`, `equals_ignore_case`, `at_least` (`>=`), `at_most` (`<=`), `lt` (`<`), `lte`, `gt` (`>`), `gte`, `integer_relation` (plus `html_exists`, `len>=`, `len<=`).
- **2 supplemental operators** (pair with at least one exact check on the same criterion): `contains` (`contains_all`), non-HTML `exists`.
- **Exact integer conservation (`integer_relation`):** check object `{"target": "result", "path": "", "op": "integer_relation", "value": {"left": <expr>, "compare": "eq"|"le"|"ge", "right": <expr>}}` (or tuple `["result", "", "integer_relation", {"left": <expr>, "compare": "eq"|"le"|"ge", "right": <expr>}]`) across `result`, `input`, and `world` using `field`, `ref_target`/`ref_path`, `integer`, `sum`, `product`.
- **Explicit `$contract` / `state_schema` rules:** top-level `"type": "object"`, explicit `properties`, `required`, `"additionalProperties": false`; single-string `type` (nullable uses `oneOf`); arrays require `items`; `$ref`, `$defs`, `anyOf`, `if` are refused.
- **Money & dates:** follow [prompting.md §4](prompting.md#4-behavioral-preservation-and-numerical-meaning) for integer minor units and rounding; use ISO-8601 date strings and inject clocks as input or a `clock.now` port.
- **Commands:** `pdd lint` (offline deterministic check), `pdd lint --remote` (hosted whole-program cross-prompt lint, 0 AI calls), `pdd test [STORY...]`, `pdd test --read <batch> --details`.
