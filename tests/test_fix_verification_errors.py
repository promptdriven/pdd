import pytest
from unittest.mock import patch, MagicMock, call
import sys
import os

# Assume the tests directory is parallel to the pdd directory
# Add the parent directory of 'pdd' to the sys.path to allow absolute import
# Adjust this path if your directory structure is different
TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(TESTS_DIR)
PDD_DIR = os.path.join(PROJECT_ROOT, 'pdd')

if PDD_DIR not in sys.path:
    sys.path.insert(0, PDD_DIR)
if PROJECT_ROOT not in sys.path:
     sys.path.insert(0, PROJECT_ROOT) # Needed for finding pdd package

# Now import the function using absolute path from the package root
from pdd.fix_verification_errors import fix_verification_errors, VerificationOutput, FixerOutput

# Define standard inputs
STD_PROGRAM = "def main():\n  print(my_module.hello())"
STD_PROMPT = "Write a module with a hello function"
STD_CODE = "def hello():\n  return 'Hello'"
STD_OUTPUT = "Traceback...\nNameError: name 'my_module' is not defined"
STD_STRENGTH = 0.5
STD_TEMP = 0.1

# Define expected error return structure for input validation/load errors
EXPECTED_ERROR_RETURN = {
    "explanation": None,
    "fixed_program": STD_PROGRAM,
    "fixed_code": STD_CODE,
    "total_cost": 0.0,
    "model_name": None,
    "verification_issues_count": -1,
}

# Define expected error return structure for parsing errors after verification LLM call
def expected_parse_error_return(cost=0.0, model=None):
    return {
        "explanation": None,
        "fixed_program": STD_PROGRAM,
        "fixed_code": STD_CODE,
        "total_cost": cost,
        "model_name": model,
        "verification_issues_count": -1,
    }

# Mock the rich print function to avoid cluttering test output
@patch('pdd.fix_verification_errors.rprint')
def test_happy_path_no_issues(mock_rprint):
    """Tests the scenario where verification finds no issues."""
    mock_load_template = MagicMock(side_effect=["find_template_content", "fix_template_content"])
    mock_llm_invoke = MagicMock(return_value={
        'result': VerificationOutput(issues_count=0, details='Looks good.'),
        'cost': 0.01,
        'model_name': 'model-A'
    })

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):

        result = fix_verification_errors(
            program=STD_PROGRAM,
            prompt=STD_PROMPT,
            code=STD_CODE,
            output=STD_OUTPUT,
            strength=STD_STRENGTH,
            temperature=STD_TEMP,
            verbose=False
        )

    assert result == {
        "explanation": None, # No actionable issues, so final_explanation is None
        "fixed_program": STD_PROGRAM,
        "fixed_code": STD_CODE,
        "total_cost": 0.01,
        "model_name": 'model-A',
        "verification_issues_count": 0,
    }
    mock_load_template.assert_has_calls([call("find_verification_errors_LLM"), call("fix_verification_errors_LLM")])
    mock_llm_invoke.assert_called_once()
    assert mock_llm_invoke.call_args[1]['prompt'] == "find_template_content"


@patch('pdd.fix_verification_errors.rprint')
def test_happy_path_issues_fixed(mock_rprint):
    """Tests the scenario where issues are found and fixed."""
    mock_load_template = MagicMock(side_effect=["find_template_content", "fix_template_content"])

    verification_details_text = "The program uses my_module but the code defines hello directly."
    fix_explanation_text = "Imported the module and called the function correctly. Also updated return string."
    expected_fixed_program_text = "import code_module\ndef main():\n  print(code_module.hello())"
    expected_fixed_code_text = 'def hello():\n  return "Hello World!"'

    mock_llm_invoke = MagicMock(side_effect=[
        # Verification call result
        {'result': VerificationOutput(issues_count=1, details=verification_details_text),
         'cost': 0.015, 'model_name': 'model-A'},
        # Fix call result
        {'result': FixerOutput(
            fixed_program=expected_fixed_program_text,
            fixed_code=expected_fixed_code_text,
            explanation=fix_explanation_text
         ),
         'cost': 0.025, 'model_name': 'model-B'}
    ])

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):

        result = fix_verification_errors(
            program=STD_PROGRAM,
            prompt=STD_PROMPT,
            code=STD_CODE,
            output=STD_OUTPUT,
            strength=STD_STRENGTH,
            temperature=STD_TEMP,
            verbose=False
        )

    expected_explanation = f"<verification_details>{verification_details_text}</verification_details>\n<fix_explanation>{fix_explanation_text}</fix_explanation>"

    assert result == {
        "explanation": expected_explanation,
        "fixed_program": expected_fixed_program_text,
        "fixed_code": expected_fixed_code_text,
        "total_cost": 0.015 + 0.025,
        "model_name": 'model-B',
        "verification_issues_count": 1,
    }
    mock_load_template.assert_has_calls([call("find_verification_errors_LLM"), call("fix_verification_errors_LLM")])
    assert mock_llm_invoke.call_count == 2
    assert mock_llm_invoke.call_args_list[0][1]['prompt'] == "find_template_content"
    assert mock_llm_invoke.call_args_list[0][1]['input_json']['code'] == STD_CODE
    assert mock_llm_invoke.call_args_list[1][1]['prompt'] == "fix_template_content"
    assert mock_llm_invoke.call_args_list[1][1]['input_json']['issues'] == verification_details_text


@patch('pdd.fix_verification_errors.rprint')
@pytest.mark.parametrize("missing_arg", ["program", "prompt", "code"])
def test_input_missing(mock_rprint, missing_arg):
    """Tests missing required string inputs (program, prompt, code)."""
    inputs = {
        "program": STD_PROGRAM,
        "prompt": STD_PROMPT,
        "code": STD_CODE,
        "output": STD_OUTPUT,
        "strength": STD_STRENGTH,
        "temperature": STD_TEMP,
    }
    inputs[missing_arg] = ""

    result = fix_verification_errors(**inputs)
    expected_return = EXPECTED_ERROR_RETURN.copy()
    if missing_arg == "program":
        expected_return['fixed_program'] = ""
    elif missing_arg == "code":
        expected_return['fixed_code'] = ""

    assert result == expected_return
    mock_rprint.assert_called_once_with(
        "[bold red]Error:[/bold red] Missing one or more required inputs (program, prompt, code)."
    )


@patch('pdd.fix_verification_errors.rprint')
@pytest.mark.parametrize("invalid_strength", [-0.1, 1.1])
def test_input_invalid_strength(mock_rprint, invalid_strength):
    """Tests invalid strength values."""
    result = fix_verification_errors(
        program=STD_PROGRAM,
        prompt=STD_PROMPT,
        code=STD_CODE,
        output=STD_OUTPUT,
        strength=invalid_strength,
        temperature=STD_TEMP
    )
    assert result == EXPECTED_ERROR_RETURN
    mock_rprint.assert_called_once_with(
        f"[bold red]Error:[/bold red] Strength must be between 0.0 and 1.0, got {invalid_strength}."
    )


@patch('pdd.fix_verification_errors.rprint')
@patch('pdd.fix_verification_errors.llm_invoke')
@patch('pdd.fix_verification_errors.load_prompt_template')
def test_empty_output_proceeds_normally(mock_load_template, mock_llm_invoke, mock_rprint):
    """Tests that an empty output string does not cause an error and proceeds to LLM call."""
    mock_load_template.side_effect = ["find_template_content", "fix_template_content"]
    mock_llm_invoke.return_value = {
        'result': VerificationOutput(issues_count=0, details='No issues found with empty output.'),
        'cost': 0.01,
        'model_name': 'model-empty-output'
    }

    result = fix_verification_errors(
        program=STD_PROGRAM,
        prompt=STD_PROMPT,
        code=STD_CODE,
        output="",
        strength=STD_STRENGTH,
        temperature=STD_TEMP,
        verbose=False
    )

    assert result["explanation"] is None
    assert result["model_name"] == 'model-empty-output'
    assert result["verification_issues_count"] == 0

    for call_args in mock_rprint.call_args_list:
        assert "Missing one or more required inputs" not in call_args[0][0]

    mock_load_template.assert_called()
    mock_llm_invoke.assert_called_once()
    assert mock_llm_invoke.call_args[1]['input_json']['output'] == ""


@patch('pdd.fix_verification_errors.rprint')
def test_load_template_failure(mock_rprint):
    """Tests failure during prompt template loading."""
    mock_load_template = MagicMock(side_effect=FileNotFoundError("Template not found"))

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template):
        result = fix_verification_errors(
            program=STD_PROGRAM,
            prompt=STD_PROMPT,
            code=STD_CODE,
            output=STD_OUTPUT,
            strength=STD_STRENGTH,
            temperature=STD_TEMP,
            verbose=False
        )

    assert result == EXPECTED_ERROR_RETURN
    mock_rprint.assert_any_call("[bold red]Error loading prompt templates:[/bold red] Template not found")
    verbose_call = call("[blue]Loading prompt templates...[/blue]")
    assert verbose_call not in mock_rprint.call_args_list


@patch('pdd.fix_verification_errors.rprint')
def test_verification_llm_invoke_failure(mock_rprint):
    """Tests failure during the verification LLM call."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(side_effect=Exception("API Error"))

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM,
            prompt=STD_PROMPT,
            code=STD_CODE,
            output=STD_OUTPUT,
            strength=STD_STRENGTH,
            temperature=STD_TEMP
        )

    expected_return = EXPECTED_ERROR_RETURN.copy()
    expected_return['total_cost'] = 0.0
    expected_return['model_name'] = None
    expected_return['verification_issues_count'] = -1 # Ensure this is -1 on LLM error
    assert result == expected_return
    mock_rprint.assert_any_call("[bold red]Error during verification LLM call:[/bold red] API Error")


@patch('pdd.fix_verification_errors.rprint')
def test_fix_llm_invoke_failure(mock_rprint):
    """Tests failure during the fix LLM call."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    verification_details_text = "Issue details here"
    mock_llm_invoke = MagicMock(side_effect=[
        {'result': VerificationOutput(issues_count=1, details=verification_details_text),
         'cost': 0.01, 'model_name': 'model-A'},
        Exception("Fix API Error")
    ])

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM,
            prompt=STD_PROMPT,
            code=STD_CODE,
            output=STD_OUTPUT,
            strength=STD_STRENGTH,
            temperature=STD_TEMP
        )

    expected_explanation = f"<verification_details>{verification_details_text}</verification_details>\n<fix_explanation>[Error during fix generation: Fix API Error]</fix_explanation>"
    assert result == {
        "explanation": expected_explanation,
        "fixed_program": STD_PROGRAM,
        "fixed_code": STD_CODE,
        "total_cost": 0.01,
        "model_name": 'model-A',
        "verification_issues_count": 1,
    }
    mock_rprint.assert_any_call("[bold red]Error during fix LLM call or processing structured output:[/bold red] Fix API Error")


@patch('pdd.fix_verification_errors.rprint')
def test_parsing_verification_llm_returns_non_pydantic(mock_rprint):
    """Tests verification result being a non-Pydantic object (llm_invoke should always return Pydantic when specified)."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(return_value={
        'result': 'Some random text from LLM that is not VerificationOutput.',
        'cost': 0.01,
        'model_name': 'model-A',
    })

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM, prompt=STD_PROMPT, code=STD_CODE, output=STD_OUTPUT,
            strength=STD_STRENGTH, verbose=True
        )

    assert result == expected_parse_error_return(cost=0.01, model='model-A')
    mock_llm_invoke.assert_called_once()
    # Now expects the generic error since we no longer do XML fallback parsing
    mock_rprint.assert_any_call(
        "[bold red]Error:[/bold red] Verification LLM call did not return the expected structured output."
    )


@patch('pdd.fix_verification_errors.rprint')
def test_parsing_verification_no_details_tag(mock_rprint):
    """Tests verification result with issues_count > 0 but no details tag (details=None)."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(return_value={
        'result': VerificationOutput(issues_count=2, details=None), # details is None
        'cost': 0.01,
        'model_name': 'model-A'
    })

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM, prompt=STD_PROMPT, code=STD_CODE, output=STD_OUTPUT,
            strength=STD_STRENGTH, verbose=True
        )

    assert result['verification_issues_count'] == 0
    assert result['explanation'] is None
    assert result['total_cost'] == 0.01
    mock_llm_invoke.assert_called_once()
    mock_rprint.assert_any_call("[yellow]Warning:[/yellow] issues_count is 2, but details field is empty or missing. Treating as no actionable issues found.")


@patch('pdd.fix_verification_errors.rprint')
def test_parsing_verification_empty_details_tag(mock_rprint):
    """Tests verification result with issues_count > 0 but empty details tag."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(return_value={
        'result': VerificationOutput(issues_count=1, details='  \n '), # Empty details
        'cost': 0.01,
        'model_name': 'model-A'
    })

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM, prompt=STD_PROMPT, code=STD_CODE, output=STD_OUTPUT,
            strength=STD_STRENGTH, verbose=True
        )

    assert result['verification_issues_count'] == 0
    assert result['explanation'] is None
    assert result['total_cost'] == 0.01
    mock_llm_invoke.assert_called_once()
    mock_rprint.assert_any_call("[yellow]Warning:[/yellow] issues_count is 1, but details field is empty or missing. Treating as no actionable issues found.")


@patch('pdd.fix_verification_errors.rprint')
def test_parsing_fix_llm_returns_non_pydantic(mock_rprint):
    """Tests fix result being a non-Pydantic object (llm_invoke should always return Pydantic when specified)."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    verification_details_text = "Issue details for fix parsing test"
    mock_llm_invoke = MagicMock(side_effect=[
        {'result': VerificationOutput(issues_count=1, details=verification_details_text), 'cost': 0.01, 'model_name': 'model-A'},
        {'result': 'Unparseable string for fix', 'cost': 0.02, 'model_name': 'model-B'}
    ])

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM, prompt=STD_PROMPT, code=STD_CODE, output=STD_OUTPUT,
            strength=STD_STRENGTH, verbose=True
        )

    assert result['fixed_program'] == STD_PROGRAM
    assert result['fixed_code'] == STD_CODE
    assert result['explanation'] == f"<verification_details>{verification_details_text}</verification_details>\n<fix_explanation>[Error: Failed to parse structured output from LLM for fix explanation]</fix_explanation>"
    assert result['verification_issues_count'] == 1
    assert result['total_cost'] == 0.01 + 0.02
    assert result['model_name'] == 'model-B'
    mock_rprint.assert_any_call(
        "[bold red]Error:[/bold red] Fix generation LLM call did not return the expected structured output."
    )
    mock_rprint.assert_any_call(f"  [dim]Expected type:[/dim] {FixerOutput}")
    mock_rprint.assert_any_call(f"  [dim]Received type:[/dim] {type('string')}")


@patch('pdd.fix_verification_errors.rprint')
@patch('pdd.fix_verification_errors.Markdown')
def test_verbose_mode_runs(mock_markdown, mock_rprint):
    """Tests that verbose mode runs without errors (doesn't check exact print output)."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    verification_details_text = "Verbose issue"
    fix_explanation_text = "ve"
    fixed_program_text = "vp"
    fixed_code_text = "vc"

    mock_llm_invoke = MagicMock(side_effect=[
        {'result': VerificationOutput(issues_count=1, details=verification_details_text), 'cost': 0.01, 'model_name': 'model-A'},
        {'result': FixerOutput(fixed_program=fixed_program_text, fixed_code=fixed_code_text, explanation=fix_explanation_text), 'cost': 0.02, 'model_name': 'model-B'}
    ])

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):

        result = fix_verification_errors(
            program=STD_PROGRAM, prompt=STD_PROMPT, code=STD_CODE, output=STD_OUTPUT,
            strength=STD_STRENGTH, verbose=True
        )

    assert result['verification_issues_count'] == 1
    assert result['total_cost'] == 0.03
    assert result['fixed_program'] == fixed_program_text
    assert result['fixed_code'] == fixed_code_text
    assert result['explanation'] == f"<verification_details>{verification_details_text}</verification_details>\n<fix_explanation>{fix_explanation_text}</fix_explanation>"

    mock_rprint.assert_called()
    mock_markdown.assert_called()

# Renamed old parsing tests that are now covered by test_parsing_verification_llm_returns_unparseable_string
# and test_parsing_fix_llm_returns_unparseable_string or specific Pydantic field handling.
# The original tests for missing XML tags are no longer directly applicable as Pydantic handles parsing.

# test_parsing_verification_no_issues_count_tag -> covered by test_parsing_verification_llm_returns_unparseable_string
# test_parsing_verification_invalid_issues_count_value -> covered by test_parsing_verification_llm_returns_unparseable_string

# test_parsing_fix_missing_program_tag -> covered by test_parsing_fix_llm_returns_unparseable_string
# test_parsing_fix_missing_code_tag -> covered by test_parsing_fix_llm_returns_unparseable_string
# test_parsing_fix_missing_explanation_tag -> covered by test_parsing_fix_llm_returns_unparseable_string

# The tests test_parsing_verification_no_details_tag and test_parsing_verification_empty_details_tag
# were updated to correctly mock Pydantic objects and test the logic for handling empty/None details.


# --- Bug #305 Regression Tests ---
# These tests verify that LLM call failures return verification_issues_count: -1 (error signal)
# instead of 0 (false success). See: https://github.com/promptdriven/pdd/issues/305

@patch('pdd.fix_verification_errors.rprint')
def test_verification_llm_invoke_failure_returns_error_signal(mock_rprint):
    """
    Regression test for GitHub issue #305: False success when LLM call fails.

    When the verification LLM call fails with an exception (e.g., "Insufficient credits",
    API timeout, network error), the function should return verification_issues_count: -1
    to signal an error state, NOT 0 which the caller interprets as "success, no issues".

    Bug behavior: Returns verification_issues_count: 0 → caller thinks success
    Expected behavior: Returns verification_issues_count: -1 → caller knows error occurred

    This test FAILS on the buggy code and PASSES once the fix is applied.
    """
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(side_effect=Exception("Insufficient credits"))

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM,
            prompt=STD_PROMPT,
            code=STD_CODE,
            output=STD_OUTPUT,
            strength=STD_STRENGTH,
            temperature=STD_TEMP
        )

    # CRITICAL ASSERTION: Must return -1 to signal error, NOT 0
    # The current buggy code returns 0, which the loop misinterprets as "0 issues = success"
    assert result['verification_issues_count'] == -1, \
        f"Expected verification_issues_count=-1 to signal error, but got {result['verification_issues_count']}. " \
        "This causes false success reporting when LLM fails (GitHub issue #305)."

    # Other expected error state values
    assert result['explanation'] is None
    assert result['fixed_program'] == STD_PROGRAM
    assert result['fixed_code'] == STD_CODE
    assert result['model_name'] is None
    mock_rprint.assert_any_call("[bold red]Error during verification LLM call:[/bold red] Insufficient credits")


@patch('pdd.fix_verification_errors.rprint')
def test_load_template_failure_returns_error_signal(mock_rprint):
    """
    Regression test for GitHub issue #305: Error signal on template loading failure.

    When prompt template loading fails, the function should return verification_issues_count: -1
    to signal an error state. This is another error path that currently returns 0.
    """
    mock_load_template = MagicMock(side_effect=FileNotFoundError("Template not found"))

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template):
        result = fix_verification_errors(
            program=STD_PROGRAM,
            prompt=STD_PROMPT,
            code=STD_CODE,
            output=STD_OUTPUT,
            strength=STD_STRENGTH,
            temperature=STD_TEMP,
            verbose=False
        )

    # CRITICAL ASSERTION: Must return -1 to signal error
    assert result['verification_issues_count'] == -1, \
        f"Expected verification_issues_count=-1 to signal error, but got {result['verification_issues_count']}. " \
        "This causes false success reporting when template loading fails (GitHub issue #305)."

    assert result['explanation'] is None
    assert result['model_name'] is None
    mock_rprint.assert_any_call("[bold red]Error loading prompt templates:[/bold red] Template not found")


@patch('pdd.fix_verification_errors.rprint')
def test_parsing_failure_returns_error_signal(mock_rprint):
    """
    Regression test for GitHub issue #305: Error signal on parsing failure.

    When the LLM returns an unparseable response (not VerificationOutput),
    the function should return verification_issues_count: -1 to signal an error state.
    """
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(return_value={
        'result': 'Random unparseable text from LLM',  # Not a VerificationOutput
        'cost': 0.01,
        'model_name': 'model-A',
    })

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM,
            prompt=STD_PROMPT,
            code=STD_CODE,
            output=STD_OUTPUT,
            strength=STD_STRENGTH,
            verbose=True
        )

    # CRITICAL ASSERTION: Must return -1 to signal error
    assert result['verification_issues_count'] == -1, \
        f"Expected verification_issues_count=-1 to signal error, but got {result['verification_issues_count']}. " \
        "This causes false success reporting when LLM response parsing fails (GitHub issue #305)."

    mock_rprint.assert_any_call(
        "[bold red]Error:[/bold red] Verification LLM call did not return the expected structured output."
    )


@patch('pdd.fix_verification_errors.rprint')
@pytest.mark.parametrize("missing_arg", ["program", "prompt", "code"])
def test_missing_input_returns_error_signal(mock_rprint, missing_arg):
    """
    Regression test for GitHub issue #305: Error signal on missing required inputs.

    When required inputs are missing, the function should return verification_issues_count: -1
    to signal an error state, not 0 which implies success.
    """
    inputs = {
        "program": STD_PROGRAM,
        "prompt": STD_PROMPT,
        "code": STD_CODE,
        "output": STD_OUTPUT,
        "strength": STD_STRENGTH,
        "temperature": STD_TEMP,
    }
    inputs[missing_arg] = ""  # Make input empty

    result = fix_verification_errors(**inputs)

    # CRITICAL ASSERTION: Must return -1 to signal error
    assert result['verification_issues_count'] == -1, \
        f"Expected verification_issues_count=-1 to signal error when {missing_arg} is empty, " \
        f"but got {result['verification_issues_count']}. This causes false success (GitHub issue #305)."


@patch('pdd.fix_verification_errors.rprint')
@pytest.mark.parametrize("invalid_strength", [-0.1, 1.1])
def test_invalid_strength_returns_error_signal(mock_rprint, invalid_strength):
    """
    Regression test for GitHub issue #305: Error signal on invalid parameters.

    When strength is out of valid range, the function should return verification_issues_count: -1.
    """
    result = fix_verification_errors(
        program=STD_PROGRAM,
        prompt=STD_PROMPT,
        code=STD_CODE,
        output=STD_OUTPUT,
        strength=invalid_strength,
        temperature=STD_TEMP
    )

    # CRITICAL ASSERTION: Must return -1 to signal error
    assert result['verification_issues_count'] == -1, \
        f"Expected verification_issues_count=-1 to signal error for invalid strength={invalid_strength}, " \
        f"but got {result['verification_issues_count']}. This causes false success (GitHub issue #305)."
