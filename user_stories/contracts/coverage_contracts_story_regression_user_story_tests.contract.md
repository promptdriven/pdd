<!-- pdd-story-contract derived-from-story="../story__coverage_contracts_story_regression_user_story_tests.md" story-hash="ca3bbf7c37b23113" issue-ref="https://github.com/promptdriven/pdd/issues/1699" -->

# Contract: Story regression foundation: @pytest.mark.story marker + story→test traceability API

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__coverage_contracts_story_regression_user_story_tests.md`), not this contract.

## Covers
- AC1: `pytest -m story` selects exactly the story-backed regression tests and nothing else.
- AC2: Given a story file, the API returns its linked regression tests; given a test node id, it returns the owning story.
- AC3: `pdd checkup coverage <prompt>` shows, per story, whether an executable regression test exists.
- AC4: Unit tests cover the marker registration, the id convention, and the bidirectional resolution.
- R1: A `@pytest.mark.story(story_id=...)` marker is registered in `pytest.ini` alongside existing markers (`e2e`, `integration`, `slow`, `real`, `private_prompt`).
- R2: A `story_id` convention is derived from the `story__<name>.md` filename and is stable across renames where practical.
- R3: The traceability API lives in `pdd/user_story_tests.py` or `pdd/story_regression.py`.
- R4: The existing coverage matrix (`pdd checkup coverage`, `docs/coverage_contracts.md`) surfaces a new dimension: whether a story has an executable regression test, distinct from the existing `story-only` / `test-only` rule statuses.

## Context
- A PDD project with `pytest.ini` already defining markers `e2e`, `integration`, `slow`, `real`, and `private_prompt`.
- One or more story files exist under `user_stories/` following the naming convention `story__<name>.md`.
- One or more pytest test files exist that may or may not be decorated with `@pytest.mark.story(story_id="...")`.
- The `pdd checkup coverage` command and `docs/coverage_contracts.md` already report rule-level coverage statuses (`story-only`, `test-only`, etc.) keyed off `test_R<n>` naming.
- No test generation has occurred; this contract only validates the marker, the API, and the coverage reporting.

## Acceptance Criteria
1. Given a pytest configuration with the `story` marker registered, when `pytest -m story` is executed, then only tests decorated with `@pytest.mark.story` are collected and run; tests without the marker are excluded.
2. Given a story file path `user_stories/story__login.md`, when the traceability API's story-to-tests function is called, then it returns the set of test node ids that carry `@pytest.mark.story(story_id="login")`.
3. Given a test node id for a test decorated with `@pytest.mark.story(story_id="login")`, when the traceability API's test-to-story function is called, then it returns the story file path `user_stories/story__login.md`.
4. Given a prompt file, when `pdd checkup coverage <prompt>` is executed, then the output includes, for each story associated with that prompt, an indication of whether an executable regression test exists, presented as a dimension separate from the existing `story-only` / `test-only` rule statuses.
5. Given the `story_id` convention, when a story file is renamed from `story__foo.md` to `story__bar.md`, then the `story_id` derived from the filename remains stable where practical (e.g., the id is not purely the filename but a stable slug derived at story creation time).

## Oracle
These details matter for pass/fail:
- The `story` marker is present in `pytest.ini` under the `markers` key.
- `pytest --markers` lists `@pytest.mark.story(story_id=...)` as a registered marker.
- `pytest -m story` collects zero tests when no tests carry the marker, and collects exactly the marked tests when some do.
- The traceability API returns an empty collection when no tests are linked to a story, and returns the correct test node ids when they are.
- The traceability API raises or returns a sentinel when a test node id has no linked story.
- `pdd checkup coverage <prompt>` output contains a per-story section or column indicating regression test presence (e.g., `has_regression_test: true/false` or equivalent).
- The `story_id` is derived from the story filename in a documented, repeatable way.

## Non-Oracle
These details should not matter:
- The exact module name (`user_story_tests.py` vs `story_regression.py`) as long as the API is importable and functional.
- The internal data structure used to store the story-to-test mapping (dict, set, database, etc.).
- The exact formatting of the `pdd checkup coverage` output (table, JSON, YAML) as long as the regression-test dimension is present and distinguishable.
- The specific pytest version, as long as custom markers are supported.
- The order of markers in `pytest.ini`.
- The exact algorithm for `story_id` stability across renames, as long as a documented convention exists and is followed.

## Negative Cases
- `pytest -m story` must not collect tests that lack the `@pytest.mark.story` marker, even if their function names contain the word "story".
- The traceability API must not return a story for a test that carries a `story_id` that does not correspond to any existing story file.
- `pdd checkup coverage` must not conflate the new regression-test dimension with the existing `story-only` / `test-only` rule statuses.
- The `story` marker must not interfere with selection by other markers (e.g., `pytest -m e2e` must still work independently).

## Non-Goals
- Generating the actual regression test code.
- The Make/CI lane that runs story-backed tests automatically.
- A gating mechanism that blocks merges based on missing regression tests.
- Backfilling `@pytest.mark.story` onto existing tests.

## Candidate Prompts
- `coverage_contracts_python.prompt` — (primary) implements the coverage matrix and `pdd checkup coverage` reporting that must surface the new regression-test dimension.
- `story_regression_python.prompt` — (primary) implements the traceability API and `story_id` convention.
- `user_story_tests_python.prompt` — (primary) implements the marker registration and pytest integration.
- `checkup_report_python.prompt` — (related) grouping and classification helpers for checkup sessions may need to incorporate the new regression-test dimension.
- `checkup_tools_python.prompt` — (related) adapter layer from prompt source-set reports to agentic checkup tools may surface the regression-test status.
- `agentic_test_generate_python.prompt` — (possible) future test generation will consume the traceability API to know which stories lack tests.
- `agentic_test_orchestrator_python.prompt` — (possible) the orchestrator for test generation will need to resolve story-to-test mappings.

## Notes
- The `story_id` stability requirement ("stable across renames where practical") implies the id should be a slug stored in the story file's frontmatter or derived once at creation time, not recomputed from the filename on every lookup. The contract does not prescribe the mechanism, only that the convention exists and is documented.
- The existing `story-only` / `test-only` rule statuses key off `test_R<n>` naming conventions; the new dimension must be clearly distinct and not alter the existing status logic.
- This contract is derived from EPIC #1698, sub-issue 1 of 4.
