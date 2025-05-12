# tests/test_incremental_code_generator.py
"""
Detailed Test Plan for incremental_code_generator
===============================================

Objective:
----------
Ensure the `incremental_code_generator` function behaves correctly across various scenarios, including edge cases,
normal operation, and error conditions, while maintaining good code coverage.

Test Strategy:
--------------
- Use unit tests with pytest for all scenarios, leveraging fixtures and mocking to isolate dependencies.
- Focus on functional behavior (inputs leading to expected outputs) rather than internal implementation details.
- Mock external dependencies (`llm_invoke`, `code_generator`, `load_prompt_template`) to simulate responses and failures.
- Test both incremental patching and full regeneration paths.
- Verify error handling, cost tracking, and model name selection.
- Minimize mocking to ensure real code paths are tested where possible, but mock LLM interactions to avoid external calls.

Test Categories and Cases:
--------------------------
1. Input Validation Tests:
   - Test empty or None values for required inputs (`original_prompt`, `new_prompt`, `existing_code`, `language`).
   - Test invalid ranges for `strength`, `temperature`, and `time` (e.g., -1, 2).

2. Decision Logic Tests:
   - Test when diff analyzer indicates a big change (`is_big_change=True`) with `force_incremental=False` (should regenerate).
   - Test when diff analyzer indicates a big change with `force_incremental=True` (should patch incrementally).
   - Test when diff analyzer indicates a small change (`is_big_change=False`) (should patch incrementally).

3. Path Execution Tests:
   - Test full regeneration path: Ensure `code_generator` is called and returns updated code.
   - Test incremental patching path: Ensure `llm_invoke` with `code_patcher_LLM` is called and returns patched code.

4. Cost and Model Name Tracking Tests:
   - Test cost accumulation across multiple LLM calls (diff analyzer + regeneration or patching).
   - Test model name prioritization (should use the first or main operation's model name).

5. Verbose Mode Tests:
   - Test with `verbose=True` to ensure logging occurs (capture console output if needed).
   - Test with `verbose=False` to ensure no impact on functionality.

6. Error Handling Tests:
   - Test failure in `llm_invoke` for diff analyzer (should raise exception).
   - Test failure in `code_generator` during regeneration (should raise exception).
   - Test failure in `llm_invoke` for patching (should raise exception).
   - Test failure to load prompt templates (should raise exception).

7. Preprocessing Tests:
   - Test with `preprocess_prompt=True` (ensure preprocessing is applied).
   - Test with `preprocess_prompt=False` (ensure raw template is used).

8. Language Handling Tests:
   - Test with different languages (e.g., 'python', 'bash') to ensure correct delegation to `code_generator`.

Fixtures and Setup:
-------------------
- Use pytest fixtures to provide common test data (e.g., sample prompts, code snippets).
- Mock `llm_invoke`, `code_generator`, and `load_prompt_template` to return predefined responses or raise exceptions.
- Use `capsys` to capture console output for verbose mode tests.

Test Isolation:
---------------
- Ensure tests are independent by resetting mocks and using fresh fixtures for each test.
- Avoid manipulating internal state; rely on public APIs only.
"""

import pytest
from unittest.mock import patch, MagicMock
from pdd.incremental_code_generator import incremental_code_generator, DiffAnalysis, PatchResult

# Fixtures for common test data
@pytest.fixture
def sample_prompts():
    return {
        "original": "Original prompt to generate code",
        "new": "Updated prompt with changes",
        "existing_code": "def sample_function():\n    return 42",
        "language": "python"
    }

@pytest.fixture
def diff_analysis_big_change():
    return DiffAnalysis(
        is_big_change=True,
        change_description="Significant changes detected.",
        analysis="Analysis indicates a major overhaul is needed."
    )

@pytest.fixture
def diff_analysis_small_change():
    return DiffAnalysis(
        is_big_change=False,
        change_description="Minor changes detected.",
        analysis="Analysis indicates small updates are sufficient."
    )

@pytest.fixture
def patch_result():
    return PatchResult(
        patched_code="def updated_function():\n    return 43",
        analysis="Patching completed successfully.",
        planned_modifications="Updated return value."
    )

# Input Validation Tests
def test_empty_original_prompt(sample_prompts):
    with pytest.raises(ValueError, match="All required inputs.*must be provided"):
        incremental_code_generator(
            original_prompt="",
            new_prompt=sample_prompts["new"],
            existing_code=sample_prompts["existing_code"],
            language=sample_prompts["language"]
        )

def test_empty_new_prompt(sample_prompts):
    with pytest.raises(ValueError, match="All required inputs.*must be provided"):
        incremental_code_generator(
            original_prompt=sample_prompts["original"],
            new_prompt="",
            existing_code=sample_prompts["existing_code"],
            language=sample_prompts["language"]
        )

def test_empty_existing_code(sample_prompts):
    with pytest.raises(ValueError, match="All required inputs.*must be provided"):
        incremental_code_generator(
            original_prompt=sample_prompts["original"],
            new_prompt=sample_prompts["new"],
            existing_code="",
            language=sample_prompts["language"]
        )

def test_empty_language(sample_prompts):
    with pytest.raises(ValueError, match="All required inputs.*must be provided"):
        incremental_code_generator(
            original_prompt=sample_prompts["original"],
            new_prompt=sample_prompts["new"],
            existing_code=sample_prompts["existing_code"],
            language=""
        )

def test_invalid_strength(sample_prompts):
    with pytest.raises(ValueError, match="Strength, temperature, and time must be between 0 and 1"):
        incremental_code_generator(
            original_prompt=sample_prompts["original"],
            new_prompt=sample_prompts["new"],
            existing_code=sample_prompts["existing_code"],
            language=sample_prompts["language"],
            strength=1.5
        )

def test_invalid_temperature(sample_prompts):
    with pytest.raises(ValueError, match="Strength, temperature, and time must be between 0 and 1"):
        incremental_code_generator(
            original_prompt=sample_prompts["original"],
            new_prompt=sample_prompts["new"],
            existing_code=sample_prompts["existing_code"],
            language=sample_prompts["language"],
            temperature=-0.1
        )

def test_invalid_time(sample_prompts):
    with pytest.raises(ValueError, match="Strength, temperature, and time must be between 0 and 1"):
        incremental_code_generator(
            original_prompt=sample_prompts["original"],
            new_prompt=sample_prompts["new"],
            existing_code=sample_prompts["existing_code"],
            language=sample_prompts["language"],
            time=2.0
        )

# Decision Logic and Path Execution Tests
@patch('pdd.incremental_code_generator.load_prompt_template')
@patch('pdd.incremental_code_generator.llm_invoke')
@patch('pdd.incremental_code_generator.code_generator')
def test_full_regeneration_big_change(mock_code_generator, mock_llm_invoke, mock_load_template, sample_prompts, diff_analysis_big_change):
    mock_load_template.return_value = "diff_analyzer_template"
    mock_llm_invoke.return_value = {"result": diff_analysis_big_change, "cost": 0.01, "model_name": "model1"}
    mock_code_generator.return_value = ("def regenerated_code():\n    return 100", 0.02, "model2")

    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(
        original_prompt=sample_prompts["original"],
        new_prompt=sample_prompts["new"],
        existing_code=sample_prompts["existing_code"],
        language=sample_prompts["language"],
        force_incremental=False
    )

    assert is_incremental == False
    assert updated_code == "def regenerated_code():\n    return 100"
    assert total_cost == 0.03
    assert model_name == "model1"
    mock_code_generator.assert_called_once()

@patch('pdd.incremental_code_generator.load_prompt_template')
@patch('pdd.incremental_code_generator.llm_invoke')
def test_incremental_patch_small_change(mock_llm_invoke, mock_load_template, sample_prompts, diff_analysis_small_change, patch_result):
    mock_load_template.side_effect = ["diff_analyzer_template", "patcher_template"]
    mock_llm_invoke.side_effect = [
        {"result": diff_analysis_small_change, "cost": 0.01, "model_name": "model1"},
        {"result": patch_result, "cost": 0.015, "model_name": "model1"}
    ]

    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(
        original_prompt=sample_prompts["original"],
        new_prompt=sample_prompts["new"],
        existing_code=sample_prompts["existing_code"],
        language=sample_prompts["language"],
        force_incremental=False
    )

    assert is_incremental == True
    assert updated_code == patch_result.patched_code
    assert total_cost == 0.025
    assert model_name == "model1"

@patch('pdd.incremental_code_generator.load_prompt_template')
@patch('pdd.incremental_code_generator.llm_invoke')
def test_force_incremental_big_change(mock_llm_invoke, mock_load_template, sample_prompts, diff_analysis_big_change, patch_result):
    mock_load_template.side_effect = ["diff_analyzer_template", "patcher_template"]
    mock_llm_invoke.side_effect = [
        {"result": diff_analysis_big_change, "cost": 0.01, "model_name": "model1"},
        {"result": patch_result, "cost": 0.015, "model_name": "model1"}
    ]

    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(
        original_prompt=sample_prompts["original"],
        new_prompt=sample_prompts["new"],
        existing_code=sample_prompts["existing_code"],
        language=sample_prompts["language"],
        force_incremental=True
    )

    assert is_incremental == True
    assert updated_code == patch_result.patched_code
    assert total_cost == 0.025
    assert model_name == "model1"

# Verbose Mode Test (basic check; detailed console output capture optional)
@patch('pdd.incremental_code_generator.load_prompt_template')
@patch('pdd.incremental_code_generator.llm_invoke')
def test_verbose_mode(mock_llm_invoke, mock_load_template, sample_prompts, diff_analysis_small_change, patch_result, capsys):
    mock_load_template.side_effect = ["diff_analyzer_template", "patcher_template"]
    mock_llm_invoke.side_effect = [
        {"result": diff_analysis_small_change, "cost": 0.01, "model_name": "model1"},
        {"result": patch_result, "cost": 0.015, "model_name": "model1"}
    ]

    incremental_code_generator(
        original_prompt=sample_prompts["original"],
        new_prompt=sample_prompts["new"],
        existing_code=sample_prompts["existing_code"],
        language=sample_prompts["language"],
        verbose=True
    )

    captured = capsys.readouterr()
    assert "Diff Analysis" in captured.out or "Change Type" in captured.out

# Error Handling Tests
@patch('pdd.incremental_code_generator.load_prompt_template')
@patch('pdd.incremental_code_generator.llm_invoke')
def test_diff_analyzer_failure(mock_llm_invoke, mock_load_template, sample_prompts):
    mock_load_template.return_value = "diff_analyzer_template"
    mock_llm_invoke.side_effect = Exception("LLM invocation failed")

    with pytest.raises(Exception, match="LLM invocation failed"):
        incremental_code_generator(
            original_prompt=sample_prompts["original"],
            new_prompt=sample_prompts["new"],
            existing_code=sample_prompts["existing_code"],
            language=sample_prompts["language"]
        )

@patch('pdd.incremental_code_generator.load_prompt_template')
@patch('pdd.incremental_code_generator.llm_invoke')
@patch('pdd.incremental_code_generator.code_generator')
def test_code_generator_failure(mock_code_generator, mock_llm_invoke, mock_load_template, sample_prompts, diff_analysis_big_change):
    mock_load_template.return_value = "diff_analyzer_template"
    mock_llm_invoke.return_value = {"result": diff_analysis_big_change, "cost": 0.01, "model_name": "model1"}
    mock_code_generator.side_effect = Exception("Code generation failed")

    with pytest.raises(Exception, match="Code generation failed"):
        incremental_code_generator(
            original_prompt=sample_prompts["original"],
            new_prompt=sample_prompts["new"],
            existing_code=sample_prompts["existing_code"],
            language=sample_prompts["language"],
            force_incremental=False
        )

# Language Handling Test
@patch('pdd.incremental_code_generator.load_prompt_template')
@patch('pdd.incremental_code_generator.llm_invoke')
@patch('pdd.incremental_code_generator.code_generator')
def test_different_language(mock_code_generator, mock_llm_invoke, mock_load_template, sample_prompts, diff_analysis_big_change):
    mock_load_template.return_value = "diff_analyzer_template"
    mock_llm_invoke.return_value = {"result": diff_analysis_big_change, "cost": 0.01, "model_name": "model1"}
    mock_code_generator.return_value = ("#!/bin/bash\necho 'Hello'", 0.02, "model2")

    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(
        original_prompt=sample_prompts["original"],
        new_prompt=sample_prompts["new"],
        existing_code=sample_prompts["existing_code"],
        language="bash",
        force_incremental=False
    )

    assert "bash" in updated_code
    assert is_incremental == False
    assert total_cost == 0.03
    assert model_name == "model1"