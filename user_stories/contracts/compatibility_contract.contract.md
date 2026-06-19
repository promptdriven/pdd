<!-- pdd-story-contract derived-from-story="../story__compatibility_contract.md" story-hash="e2c187fc9e67c134" issue-ref="https://github.com/promptdriven/pdd/issues/1652" -->

# Contract: Implement compatibility contract extraction module

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__compatibility_contract.md`), not this contract.

## Covers
- AC1: The prompt file `compatibility_contract_python.prompt` is created and synced to generated code.
- AC2: The generated module exports a callable `extract_compatibility_contract(py_file: Path) -> CompatibilityContract`.
- AC3: The contract captures public symbols, callable signatures, and underscore helpers that tests patch.
- AC4: The contract is bounded — it does not dump every private symbol or dunder internal.
- AC5: Unit tests verify extraction against a representative fixture `.py` file.

## Context
A generated Python file exists on disk. The extraction module receives its path and must parse the file to identify its public interface and any private helpers that downstream tests reference as patch targets. The output is a structured `CompatibilityContract` that can be serialized into a prompt-friendly text block for injection into generation context. The module must not execute the target file or make any LLM calls.

## Acceptance Criteria
1. Given a path to a generated Python file containing public symbols, callable signatures, and at least one underscore-prefixed helper that is referenced by a test patch, when `extract_compatibility_contract` is called with that path, then the returned `CompatibilityContract` includes the public symbols, the callable signatures, and the patched underscore helper.
2. Given a generated Python file containing dunder internals and private symbols not referenced by any test patch, when the contract is extracted, then those dunder internals and unreferenced private symbols are absent from the contract.
3. Given a generated Python file whose public surface exceeds a configurable symbol count cap, when the contract is extracted, then the output is truncated to respect that cap rather than returning an unbounded dump.
4. Given the extracted `CompatibilityContract`, when it is serialized to a text block, then the output is structured as a prompt-friendly section suitable for injection into generation context.

## Oracle
These details matter for pass/fail:
- The module exports a callable named `extract_compatibility_contract` that accepts a `Path` and returns a `CompatibilityContract`.
- The returned contract contains three categories: public symbols, callable signatures, and underscore patch-target helpers.
- Dunder names and private symbols not referenced by test patches are absent from the contract.
- The contract respects a configurable symbol count cap and does not produce an unbounded dump.
- The serialized output is a text block formatted for prompt injection.

## Non-Oracle
These details should not matter:
- The internal implementation strategy for parsing the Python file.
- The exact serialization format of the text block, as long as it is prompt-friendly and structured.
- The specific configurable cap value, as long as one exists and is honored.
- The names or contents of the fixture file used in unit tests.

## Negative Cases
- The contract must not include dunder internals.
- The contract must not include private symbols that are not referenced by any test patch.
- The contract must not return an unbounded dump of all symbols when the file exceeds the cap.
- The extraction must not execute or import the target Python file.

## Non-Goals
- This story does not cover the downstream consumption of the contract by the sync pipeline or code generators.
- This story does not cover extraction from non-Python files.
- This story does not cover dynamic analysis or runtime inspection of the target file.

## Candidate Prompts
- `compatibility_contract_python.prompt` — primary prompt for this story (primary)
- `sync_orchestration_python.prompt` — consumes the compatibility contract format downstream (related)
- `code_generator_python.prompt` — receives generation context that includes the contract text block (related)
- `incremental_code_generator_python.prompt` — receives generation context that includes the contract text block (related)
- `api_contract_slicer_python.prompt` — performs related AST-based contract slicing for compressed context (possible)

## Notes
- The issue specifies that the contract must be bounded and skip dunder internals and implementation-private names not referenced by tests.
- The configurable symbol count cap is mentioned in the issue as a bounding mechanism.
- The serialized output is described as a `% Compatibility Surface` section in the issue, but the exact heading is non-oracle as long as the block is prompt-friendly.
- Unit tests must use a representative fixture `.py` file; the fixture is not specified in the story and is left to the implementation.
- Issue reference: https://github.com/promptdriven/pdd/issues/1647
