# Issue #820 — user story contract coverage (design note)

This document records the product spec for [promptdriven/pdd#820](https://github.com/promptdriven/pdd/issues/820).
It is **not** a packaged PDD module prompt. The canonical implementation prompt is
`pdd/prompts/user_story_tests_python.prompt`; code lives in `pdd/user_story_tests.py`.

## Goal

Align `user_stories/story__template.md` and `pdd test <*.prompt>` story generation with
contract-rule coverage evidence (`## Covers`, Oracle / Non-Oracle, Negative Cases) without
breaking legacy stories.

## Canonical template

See `user_stories/story__template.md` in the repository.

## Generator behavior

- Seed `## Covers` from `contract_ir.parse_prompt_contracts(Path)`.
- Cross-module format: `prompts/<file>.prompt#R{n}: <summary>` when multiple prompts are in scope.
- Seed `## Negative Cases` from MUST/SHALL/MAY NOT obligations in contract rules.
- Do not emit `## Prompt Scope`.

## Related docs

- `docs/prompting_guide.md` (Story Template)
- `docs/coverage_contracts.md`, `docs/contract_check.md`
