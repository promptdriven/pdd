<!-- pdd-story-prompts: prompts/user_story_tests_python.prompt, prompts/generate_story_contract_LLM.prompt, prompts/coverage_contracts_python.prompt -->
<!-- pdd-story-dev-units: user_story_tests_python.prompt, generate_story_contract_LLM.prompt, coverage_contracts_python.prompt -->

# User Story: Story edits invalidate stale contracts

## Story

As a maintainer evolving user stories, I want edited human stories to invalidate stale generated contract sidecars until their hashes and coverage evidence are synchronized, so that story regressions behave like precise unit-test fixtures.
