# Story Regression Backfill

Tracking document for issue #1703, the backfill phase of EPIC #1698.

## Scope

The first regression-story backfill covers the top single-dev-unit PDD workflow
features called out by the issue and the workflow documentation:

- `pdd generate`
- `pdd sync`
- `pdd fix`
- `pdd change`
- `pdd update`

These are intentionally single-dev-unit stories. Cross-dev-unit stories are a
follow-up phase.

The cross-dev-unit follow-up covers documented PDD workflows that naturally span
more than one dev unit:

- PRD-backed `pdd generate` output handed to `pdd sync`
- Feature-request `pdd change` output carried through story/contract artifacts
  and reviewable PR creation
- Bug-report `pdd bug` reproduction handed to `pdd fix` verification
- Story-mode `pdd test` artifacts surfaced through `pdd checkup coverage`

Cross-dev-unit stories use both `pdd-story-prompts` and `pdd-story-dev-units`
metadata so the same story is attributed to every linked dev unit while still
counting as one global regression oracle.

## Verification

This backfill uses the existing PDD user-story file model:

- human stories in `user_stories/story__*.md`
- generated-style contract sidecars in `user_stories/contracts/*.contract.md`
- `pdd-story-prompts` metadata linking each story to the owning prompt
- `story-hash` metadata aligned with the human story text

No LLM-backed PDD commands are required to verify this branch. Verification is
deterministic and local: tests inspect the PDD story metadata, contract headers,
required contract sections, rule coverage, and prompt links.

## Sub PRs

Sub PRs target this EPIC branch and are merged here after deterministic local
verification. The EPIC PR itself must not be merged into `main` until the full
issue is reviewed and ready.

Completed sub PRs:

- #1801 — `pdd sync`: aligned the existing story contract hash and added the
  deterministic top-flow story check.
- #1802 — `pdd fix`: aligned the existing story contract hash and extended the
  top-flow story check.
- #1803 — `pdd change`: aligned the existing story contract hash and extended
  the top-flow story check.
- #1804 — `pdd generate`: added the missing story, contract, and top-flow story
  check coverage.
- #1806 — `pdd update`: added the missing story, contract, and top-flow story
  check coverage.

Final local verification:

```bash
python -m py_compile tests/test_story_backfill_top_flows.py
python -c "import importlib.util; spec=importlib.util.spec_from_file_location('story_checks','tests/test_story_backfill_top_flows.py'); mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); mod.test_top_flow_story_backfill_artifacts_are_complete(); print('story backfill checks passed')"
python -m py_compile tests/test_story_backfill_cross_unit_flows.py
python -c "import importlib.util; spec=importlib.util.spec_from_file_location('cross_story_checks','tests/test_story_backfill_cross_unit_flows.py'); mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); mod.test_cross_unit_story_backfill_artifacts_are_complete(); print('cross-unit story checks passed')"
```
