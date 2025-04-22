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
from pdd.fix_verification_errors import fix_verification_errors

# Define standard inputs
STD_PROGRAM = "def main():\n  print(my_module.hello())"
STD_PROMPT = "Write a module with a hello function"
STD_CODE = "def hello():\n  return 'Hello'" # Intentionally simple, maybe buggy
STD_OUTPUT = "Traceback...\nNameError: name 'my_module' is not defined"
STD_STRENGTH = 0.5
STD_TEMP = 0.1

# Define expected error return structure for input validation/load errors
EXPECTED_ERROR_RETURN = {
    "explanation": None,
    "fixed_program": STD_PROGRAM, # Should return original inputs on error
    "fixed_code": STD_CODE,
    "total_cost": 0.0,
    "model_name": None,
    "verification_issues_count": 0,
}

# Define expected error return structure for parsing errors after verification LLM call
def expected_parse_error_return(cost=0.0, model=None):
    return {
        "explanation": None,
        "fixed_program": STD_PROGRAM,
        "fixed_code": STD_CODE,
        "total_cost": cost,
        "model_name": model,
        "verification_issues_count": 0, # Reset on parsing error
    }

# Mock the rich print function to avoid cluttering test output
@patch('pdd.fix_verification_errors.rprint')
def test_happy_path_no_issues(mock_rprint):
    """Tests the scenario where verification finds no issues."""
    mock_load_template = MagicMock(side_effect=["find_template_content", "fix_template_content"])
    mock_llm_invoke = MagicMock(return_value={
        'result': '<issues_count>0</issues_count><details>Looks good.</details>',
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
        "explanation": None,
        "fixed_program": STD_PROGRAM,
        "fixed_code": STD_CODE,
        "total_cost": 0.01,
        "model_name": 'model-A',
        "verification_issues_count": 0,
    }
    mock_load_template.assert_has_calls([call("find_verification_errors_LLM"), call("fix_verification_errors_LLM")])
    mock_llm_invoke.assert_called_once() # Only verification call should happen
    assert mock_llm_invoke.call_args[1]['prompt'] == "find_template_content"


@patch('pdd.fix_verification_errors.rprint')
def test_happy_path_issues_fixed(mock_rprint):
    """Tests the scenario where issues are found and fixed."""
    mock_load_template = MagicMock(side_effect=["find_template_content", "fix_template_content"])
    mock_llm_invoke = MagicMock(side_effect=[
        # Verification call result
        {'result': '<issues_count>1</issues_count><details>The program uses my_module but the code defines hello directly.</details>',
         'cost': 0.015, 'model_name': 'model-A'},
        # Fix call result
        {'result': '<fixed_program>import code_module\ndef main():\n  print(code_module.hello())</fixed_program><fixed_code>def hello():\n  return "Hello World!"</fixed_code><explanation>Imported the module and called the function correctly. Also updated return string.</explanation>',
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

    expected_explanation = "<verification_details>The program uses my_module but the code defines hello directly.</verification_details>\n<fix_explanation>Imported the module and called the function correctly. Also updated return string.</fix_explanation>"
    expected_fixed_program = "import code_module\ndef main():\n  print(code_module.hello())"
    expected_fixed_code = 'def hello():\n  return "Hello World!"'

    assert result == {
        "explanation": expected_explanation,
        "fixed_program": expected_fixed_program,
        "fixed_code": expected_fixed_code,
        "total_cost": 0.015 + 0.025,
        "model_name": 'model-B', # Should be the last model used
        "verification_issues_count": 1,
    }
    mock_load_template.assert_has_calls([call("find_verification_errors_LLM"), call("fix_verification_errors_LLM")])
    assert mock_llm_invoke.call_count == 2
    # Check args for verification call
    assert mock_llm_invoke.call_args_list[0][1]['prompt'] == "find_template_content"
    assert mock_llm_invoke.call_args_list[0][1]['input_json']['code'] == STD_CODE
    # Check args for fix call
    assert mock_llm_invoke.call_args_list[1][1]['prompt'] == "fix_template_content"
    assert mock_llm_invoke.call_args_list[1][1]['input_json']['issues'] == "The program uses my_module but the code defines hello directly."


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
    inputs[missing_arg] = "" # Test with empty string for program, prompt, or code

    result = fix_verification_errors(**inputs)
    # Adjust expected return to match the specific input used
    expected_return = EXPECTED_ERROR_RETURN.copy()
    # Update expected return based on which input was missing
    if missing_arg == "program":
        expected_return['fixed_program'] = ""
    elif missing_arg == "code":
        expected_return['fixed_code'] = ""
    # If prompt is missing, fixed_program/fixed_code remain STD_PROGRAM/STD_CODE

    assert result == expected_return
    # Check that rprint was called once with the updated message
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
    # Check that rprint was called once with the correct message
    mock_rprint.assert_called_once_with(
        f"[bold red]Error:[/bold red] Strength must be between 0.0 and 1.0, got {invalid_strength}."
    )


@patch('pdd.fix_verification_errors.rprint')
@patch('pdd.fix_verification_errors.llm_invoke')
@patch('pdd.fix_verification_errors.load_prompt_template')
def test_empty_output_proceeds_normally(mock_load_template, mock_llm_invoke, mock_rprint):
    """Tests that an empty output string does not cause an error and proceeds to LLM call."""
    # Mock dependencies to simulate successful execution after input validation
    mock_load_template.side_effect = ["find_template_content", "fix_template_content"]
    mock_llm_invoke.return_value = {
        'result': '<issues_count>0</issues_count><details>No issues found with empty output.</details>',
        'cost': 0.01,
        'model_name': 'model-empty-output'
    }

    result = fix_verification_errors(
        program=STD_PROGRAM,
        prompt=STD_PROMPT,
        code=STD_CODE,
        output="",  # Key: Provide empty output
        strength=STD_STRENGTH,
        temperature=STD_TEMP,
        verbose=False
    )

    # Assert that the function did not return the input error state
    assert result["explanation"] is not None or result["verification_issues_count"] is not None # Check it's not the specific error dict structure
    assert result["model_name"] == 'model-empty-output' # Check model name from mocked LLM call
    assert result["verification_issues_count"] == 0 # Check issues count from mocked LLM call

    # Assert that the initial validation error was NOT printed
    for call_args in mock_rprint.call_args_list:
        assert "Missing one or more required inputs" not in call_args[0][0]

    # Assert that the LLM invocation was attempted
    mock_load_template.assert_called()
    mock_llm_invoke.assert_called_once()
    assert mock_llm_invoke.call_args[1]['input_json']['output'] == "" # Verify empty output was passed to LLM


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
            verbose=False # Explicitly set verbose=False for clarity
        )

    assert result == EXPECTED_ERROR_RETURN
    # Only check for the error message, not the verbose one
    mock_rprint.assert_any_call("[bold red]Error loading prompt templates:[/bold red] Template not found")
    # Ensure the verbose message was NOT called
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

    # Cost and model might be None or 0 depending on when error happens
    expected_return = EXPECTED_ERROR_RETURN.copy()
    expected_return['total_cost'] = 0.0 # Error before cost is assigned
    expected_return['model_name'] = None
    assert result == expected_return
    mock_rprint.assert_any_call("[bold red]Error during verification LLM call:[/bold red] API Error")


@patch('pdd.fix_verification_errors.rprint')
def test_fix_llm_invoke_failure(mock_rprint):
    """Tests failure during the fix LLM call."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(side_effect=[
        # Verification call result (success)
        {'result': '<issues_count>1</issues_count><details>Issue details here</details>',
         'cost': 0.01, 'model_name': 'model-A'},
        # Fix call result (failure)
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

    # Should return original code, but with verification details and error message
    expected_explanation = "<verification_details>Issue details here</verification_details>\n<fix_explanation>[Error during fix generation: Fix API Error]</fix_explanation>"
    assert result == {
        "explanation": expected_explanation,
        "fixed_program": STD_PROGRAM,
        "fixed_code": STD_CODE,
        "total_cost": 0.01, # Only cost from verification call
        "model_name": 'model-A', # Model from verification call
        "verification_issues_count": 1,
    }
    mock_rprint.assert_any_call("[bold red]Error during fix LLM call or extraction:[/bold red] Fix API Error")


@patch('pdd.fix_verification_errors.rprint')
def test_parsing_verification_no_issues_count_tag(mock_rprint):
    """Tests verification result missing the issues_count tag."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(return_value={
        'result': 'Some random text from LLM.',
        'cost': 0.01,
        'model_name': 'model-A'
    })

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM, prompt=STD_PROMPT, code=STD_CODE, output=STD_OUTPUT,
            strength=STD_STRENGTH, verbose=True # Enable verbose for warning check
        )

    assert result['verification_issues_count'] == 0
    assert result['explanation'] is None
    assert result['total_cost'] == 0.01
    mock_llm_invoke.assert_called_once() # Fix should not be called
    mock_rprint.assert_any_call("[yellow]Warning:[/yellow] Could not find <issues_count> tag in verification result. Assuming 0 issues.")


@patch('pdd.fix_verification_errors.rprint')
def test_parsing_verification_invalid_issues_count_value(mock_rprint):
    """Tests verification result with non-integer issues_count."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(return_value={
        'result': '<issues_count>abc</issues_count><details>details</details>',
        'cost': 0.01,
        'model_name': 'model-A'
    })

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM, prompt=STD_PROMPT, code=STD_CODE, output=STD_OUTPUT,
            strength=STD_STRENGTH
        )

    assert result == expected_parse_error_return(cost=0.01, model='model-A')
    # Check that the specific error message was printed
    mock_rprint.assert_any_call("[bold red]Error:[/bold red] Could not parse integer value from <issues_count> tag.")
    # Ensure the warning message was NOT printed in this case
    warning_call = call("[yellow]Warning:[/yellow] Could not find <issues_count> tag in verification result. Assuming 0 issues.")
    assert warning_call not in mock_rprint.call_args_list


@patch('pdd.fix_verification_errors.rprint')
def test_parsing_verification_no_details_tag(mock_rprint):
    """Tests verification result with issues_count > 0 but no details tag."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(return_value={
        'result': '<issues_count>2</issues_count> Some text but no details tag.',
        'cost': 0.01,
        'model_name': 'model-A'
    })

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM, prompt=STD_PROMPT, code=STD_CODE, output=STD_OUTPUT,
            strength=STD_STRENGTH, verbose=True # Enable verbose for warning check
        )

    assert result['verification_issues_count'] == 0 # Reset because details are missing
    assert result['explanation'] is None
    assert result['total_cost'] == 0.01
    mock_llm_invoke.assert_called_once() # Fix should not be called
    mock_rprint.assert_any_call("[yellow]Warning:[/yellow] <issues_count> is > 0, but could not find <details> tag. Treating as no issues found.")


@patch('pdd.fix_verification_errors.rprint')
def test_parsing_verification_empty_details_tag(mock_rprint):
    """Tests verification result with issues_count > 0 but empty details tag."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(return_value={
        'result': '<issues_count>1</issues_count><details>  \n </details>', # Empty details
        'cost': 0.01,
        'model_name': 'model-A'
    })

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM, prompt=STD_PROMPT, code=STD_CODE, output=STD_OUTPUT,
            strength=STD_STRENGTH, verbose=True # Enable verbose for warning check
        )

    assert result['verification_issues_count'] == 0 # Reset because details are empty
    assert result['explanation'] is None
    assert result['total_cost'] == 0.01
    mock_llm_invoke.assert_called_once() # Fix should not be called
    mock_rprint.assert_any_call("[yellow]Warning:[/yellow] <issues_count> is > 0, but <details> tag is empty. Treating as no issues found.")


@patch('pdd.fix_verification_errors.rprint')
def test_parsing_fix_missing_program_tag(mock_rprint):
    """Tests fix result missing the fixed_program tag."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(side_effect=[
        {'result': '<issues_count>1</issues_count><details>Issue details</details>', 'cost': 0.01, 'model_name': 'model-A'},
        {'result': '<fixed_code>fixed code</fixed_code><explanation>Fix explanation</explanation>', 'cost': 0.02, 'model_name': 'model-B'} # Missing fixed_program
    ])

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM, prompt=STD_PROMPT, code=STD_CODE, output=STD_OUTPUT,
            strength=STD_STRENGTH, verbose=True # Enable verbose for warning check
        )

    assert result['fixed_program'] == STD_PROGRAM # Should revert to original
    assert result['fixed_code'] == "fixed code"
    assert result['explanation'] == "<verification_details>Issue details</verification_details>\n<fix_explanation>Fix explanation</fix_explanation>"
    assert result['verification_issues_count'] == 1
    assert result['total_cost'] == 0.03
    mock_rprint.assert_any_call("[yellow]Warning:[/yellow] Could not find <fixed_program> tag in fix result. Using original program.")


@patch('pdd.fix_verification_errors.rprint')
def test_parsing_fix_missing_code_tag(mock_rprint):
    """Tests fix result missing the fixed_code tag."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(side_effect=[
        {'result': '<issues_count>1</issues_count><details>Issue details</details>', 'cost': 0.01, 'model_name': 'model-A'},
        {'result': '<fixed_program>fixed program</fixed_program><explanation>Fix explanation</explanation>', 'cost': 0.02, 'model_name': 'model-B'} # Missing fixed_code
    ])

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM, prompt=STD_PROMPT, code=STD_CODE, output=STD_OUTPUT,
            strength=STD_STRENGTH, verbose=True # Enable verbose for warning check
        )

    assert result['fixed_program'] == "fixed program"
    assert result['fixed_code'] == STD_CODE # Should revert to original
    assert result['explanation'] == "<verification_details>Issue details</verification_details>\n<fix_explanation>Fix explanation</fix_explanation>"
    assert result['verification_issues_count'] == 1
    assert result['total_cost'] == 0.03
    mock_rprint.assert_any_call("[yellow]Warning:[/yellow] Could not find <fixed_code> tag in fix result. Using original code module.")


@patch('pdd.fix_verification_errors.rprint')
def test_parsing_fix_missing_explanation_tag(mock_rprint):
    """Tests fix result missing the explanation tag."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(side_effect=[
        {'result': '<issues_count>1</issues_count><details>Issue details</details>', 'cost': 0.01, 'model_name': 'model-A'},
        {'result': '<fixed_program>fixed program</fixed_program><fixed_code>fixed code</fixed_code>', 'cost': 0.02, 'model_name': 'model-B'} # Missing explanation
    ])

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):
        result = fix_verification_errors(
            program=STD_PROGRAM, prompt=STD_PROMPT, code=STD_CODE, output=STD_OUTPUT,
            strength=STD_STRENGTH, verbose=True # Enable verbose for warning check
        )

    expected_explanation = "<verification_details>Issue details</verification_details>\n<fix_explanation>[Fix explanation not provided by LLM]</fix_explanation>"
    assert result['fixed_program'] == "fixed program"
    assert result['fixed_code'] == "fixed code"
    assert result['explanation'] == expected_explanation
    assert result['verification_issues_count'] == 1
    assert result['total_cost'] == 0.03
    mock_rprint.assert_any_call("[yellow]Warning:[/yellow] Could not find <explanation> tag in fix result.")


@patch('pdd.fix_verification_errors.rprint')
@patch('pdd.fix_verification_errors.Markdown') # Mock Markdown as well for verbose checks
def test_verbose_mode_runs(mock_markdown, mock_rprint):
    """Tests that verbose mode runs without errors (doesn't check exact print output)."""
    mock_load_template = MagicMock(side_effect=["find_template", "fix_template"])
    mock_llm_invoke = MagicMock(side_effect=[
        {'result': '<issues_count>1</issues_count><details>Verbose issue</details>', 'cost': 0.01, 'model_name': 'model-A'},
        {'result': '<fixed_program>vp</fixed_program><fixed_code>vc</fixed_code><explanation>ve</explanation>', 'cost': 0.02, 'model_name': 'model-B'}
    ])

    with patch('pdd.fix_verification_errors.load_prompt_template', mock_load_template), \
         patch('pdd.fix_verification_errors.llm_invoke', mock_llm_invoke):

        result = fix_verification_errors(
            program=STD_PROGRAM, prompt=STD_PROMPT, code=STD_CODE, output=STD_OUTPUT,
            strength=STD_STRENGTH, verbose=True # VERBOSE = TRUE
        )

    # Check that the function completed and returned expected structure
    assert result['verification_issues_count'] == 1
    assert result['total_cost'] == 0.03
    assert result['fixed_program'] == "vp"
    assert result['fixed_code'] == "vc"
    assert result['explanation'] == "<verification_details>Verbose issue</verification_details>\n<fix_explanation>ve</fix_explanation>"

    # Check that rprint and Markdown were called (indicating verbose paths were likely hit)
    mock_rprint.assert_called()
    mock_markdown.assert_called()