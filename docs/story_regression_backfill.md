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
