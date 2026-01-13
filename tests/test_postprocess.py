# Test Plan:
# I. Input Validation Tests
#   1.  test_postprocess_invalid_llm_output_empty: llm_output="". Expect ValueError with specific message.
#   2.  test_postprocess_invalid_llm_output_type_none: llm_output=None. Expect ValueError with specific message.
#   3.  test_postprocess_invalid_language_empty: language="". Expect ValueError with specific message.
#   4.  test_postprocess_invalid_language_type_none: language=None. Expect ValueError with specific message.
#   5.  test_postprocess_invalid_strength_low: strength=-0.1. Expect ValueError with specific message.
#   6.  test_postprocess_invalid_strength_high: strength=1.1. Expect ValueError with specific message.
#   7.  test_postprocess_invalid_temperature_low: temperature=-0.1. Expect ValueError with specific message.
#   8.  test_postprocess_invalid_temperature_high: temperature=1.1. Expect ValueError with specific message.
#   9.  test_postprocess_invalid_strength_type_string: strength="abc". Expect TypeError (due to comparison operators).
#   10. test_postprocess_invalid_temperature_type_string: temperature="abc". Expect TypeError (due to comparison operators).

# II. Strength = 0 Path (Simple Extraction - `postprocess_0` behavior)
#   These tests call `postprocess` with `strength=0`.
#   11. test_strength_0_no_code_blocks: llm_output="some text without code". Expect ("", 0.0, "simple_extraction").
#   12. test_strength_0_single_code_block_with_lang: llm_output="text\n```python\nprint('hello')\n```\nmore text". Expect ("print('hello')", 0.0, "simple_extraction").
#   13. test_strength_0_single_code_block_no_lang: llm_output="text\n```\nprint('hello')\n```\nmore text". Expect ("print('hello')", 0.0, "simple_extraction").
#   14. test_strength_0_multiple_code_blocks: llm_output="```python\ncode1\n```\ntext\n```javascript\ncode2\n```". Expect ("code1\ncode2", 0.0, "simple_extraction").
#   15. test_strength_0_empty_code_block: llm_output="```python\n```". Expect ("", 0.0, "simple_extraction").
#   16. test_strength_0_code_block_at_start: llm_output="```python\ncode\n```text". Expect ("code", 0.0, "simple_extraction").
#   17. test_strength_0_code_block_at_end: llm_output="text```python\ncode\n```". Expect ("code", 0.0, "simple_extraction").
#   18. test_strength_0_malformed_only_opening_ticks: llm_output="```python\ncode". Expect ("code", 0.0, "simple_extraction").
#   19. test_strength_0_malformed_only_closing_ticks: llm_output="code\n```". Expect ("", 0.0, "simple_extraction").
#   20. test_strength_0_verbose_output: strength=0, verbose=True. Mock `rich.print` and check for "Using simple code extraction" message.

# III. Strength > 0 Path (LLM Invocation)
#   These tests will require mocking `load_prompt_template` and `llm_invoke`.
#   Use a default `strength=0.5` for these unless specified.
#   21. test_strength_gt_0_load_template_fails: Mock `load_prompt_template` to return `None`. Expect ValueError.
#   22. test_strength_gt_0_llm_invoke_fails_returns_none: Mock `llm_invoke` to return `None`. Expect ValueError.
#   23. test_strength_gt_0_llm_invoke_fails_no_result_key: Mock `llm_invoke` to return `{'cost': 0.1, 'model_name': 'test_model'}` (missing 'result'). Expect ValueError.
#   24. test_strength_gt_0_llm_invoke_raises_exception: Mock `llm_invoke` to raise `Exception("LLM error")`. Expect the function to print error and re-raise.
#   25. test_strength_gt_0_successful_extraction_no_backticks:
#       Mock `llm_invoke` to return `{'result': ExtractedCode(extracted_code="print('hello')"), 'cost': 0.05, 'model_name': 'gpt-4'}`.
#       Expect `("print('hello')", 0.05, "gpt-4")`.
#   26. test_strength_gt_0_successful_extraction_with_backticks_and_lang:
#       Mock `llm_invoke` to return `{'result': ExtractedCode(extracted_code="```python\nprint('world')\n```"), 'cost': 0.06, 'model_name': 'gpt-3.5'}`.
#       Expect `("print('world')", 0.06, "gpt-3.5")`.
#   27. test_strength_gt_0_successful_extraction_with_backticks_no_lang:
#       Mock `llm_invoke` to return `{'result': ExtractedCode(extracted_code="```\nprint('test')\n```"), 'cost': 0.07, 'model_name': 'claude-2'}`.
#       Expect `("print('test')", 0.07, "claude-2")`.
#   28. test_strength_gt_0_successful_extraction_empty_code_from_llm:
#       Mock `llm_invoke` to return `{'result': ExtractedCode(extracted_code=""), 'cost': 0.01, 'model_name': 'gemini-pro'}`.
#       Expect `("", 0.01, "gemini-pro")`.
#   29. test_strength_gt_0_successful_extraction_llm_returns_backticks_only_with_lang:
#       Mock `llm_invoke` to return `{'result': ExtractedCode(extracted_code="```python\n```"), 'cost': 0.02, 'model_name': 'gpt-4o'}`.
#       Expect `("", 0.02, "gpt-4o")`.
#   30. test_strength_gt_0_successful_extraction_llm_returns_just_opening_backtick_and_lang:
#       Mock `llm_invoke` to return `{'result': ExtractedCode(extracted_code="```python\n"), 'cost': 0.02, 'model_name': 'gpt-4o'}`.
#       Expect `("", 0.02, "gpt-4o")`. (After stripping, it becomes empty)
#   31. test_strength_gt_0_successful_extraction_llm_returns_code_with_internal_backticks_string:
#       Mock `llm_invoke` to return `{'result': ExtractedCode(extracted_code="```python\ntext = \"```\"\nprint(text)\n```"), 'cost': 0.08, 'model_name': 'gpt-4'}`.
#       Expect `("text = \"```\"\nprint(text)", 0.08, "gpt-4")`.
#   32. test_strength_gt_0_verbose_output: strength=0.5, verbose=True. Mock `rich.print`, `load_prompt_template`, `llm_invoke`. Check for specific print calls.
#   33. test_strength_gt_0_parameters_passed_to_llm_invoke:
#       Mock `llm_invoke` and capture its arguments.
#       Verify `prompt`, `input_json`, `strength`, `temperature`, `time`, `verbose`, `output_pydantic` are passed correctly.

# IV. Default Parameter Values
#   34. test_default_parameters: Call `postprocess` with only `llm_output` and `language`.
#       Mock `llm_invoke` to check if it receives default `strength=DEFAULT_STRENGTH`, `temperature=0`, `time=DEFAULT_TIME`, `verbose=False`.

import pytest
from unittest.mock import patch, MagicMock, call

from pdd.postprocess import postprocess, ExtractedCode
from pdd import DEFAULT_TIME, DEFAULT_STRENGTH # Corrected import


# I. Input Validation Tests
def test_postprocess_invalid_llm_output_empty():
    with pytest.raises(ValueError, match="llm_output must be a non-empty string"):
        postprocess(llm_output="", language="python")

def test_postprocess_invalid_llm_output_type_none():
    with pytest.raises(ValueError, match="llm_output must be a non-empty string"):
        postprocess(llm_output=None, language="python")

def test_postprocess_invalid_language_empty():
    with pytest.raises(ValueError, match="language must be a non-empty string"):
        postprocess(llm_output="some code", language="")

def test_postprocess_invalid_language_type_none():
    with pytest.raises(ValueError, match="language must be a non-empty string"):
        postprocess(llm_output="some code", language=None)

def test_postprocess_invalid_strength_low():
    with pytest.raises(ValueError, match="strength must be between 0 and 1"):
        postprocess(llm_output="some code", language="python", strength=-0.1)

def test_postprocess_invalid_strength_high():
    with pytest.raises(ValueError, match="strength must be between 0 and 1"):
        postprocess(llm_output="some code", language="python", strength=1.1)

def test_postprocess_invalid_temperature_low():
    with pytest.raises(ValueError, match="temperature must be between 0 and 1"):
        postprocess(llm_output="some code", language="python", temperature=-0.1)

def test_postprocess_invalid_temperature_high():
    with pytest.raises(ValueError, match="temperature must be between 0 and 1"):
        postprocess(llm_output="some code", language="python", temperature=1.1)

def test_postprocess_invalid_strength_type_string():
    with pytest.raises(TypeError): # Comparison "0 <= 'abc'" raises TypeError
        postprocess(llm_output="some code", language="python", strength="abc")

def test_postprocess_invalid_temperature_type_string():
    with pytest.raises(TypeError): # Comparison "0 <= 'abc'" raises TypeError
        postprocess(llm_output="some code", language="python", temperature="abc")


# II. Strength = 0 Path
def test_strength_0_no_code_blocks():
    llm_output = "some text without code"
    expected_code = ""
    extracted_code, cost, model_name = postprocess(llm_output, "python", strength=0)
    assert extracted_code == expected_code
    assert cost == 0.0
    assert model_name == "simple_extraction"

def test_strength_0_single_code_block_with_lang():
    llm_output = "text\n```python\nprint('hello')\n```\nmore text"
    expected_code = "print('hello')"
    extracted_code, cost, model_name = postprocess(llm_output, "python", strength=0)
    assert extracted_code == expected_code
    assert cost == 0.0
    assert model_name == "simple_extraction"

def test_strength_0_single_code_block_no_lang():
    llm_output = "text\n```\nprint('hello')\n```\nmore text"
    expected_code = "print('hello')"
    extracted_code, cost, model_name = postprocess(llm_output, "python", strength=0)
    assert extracted_code == expected_code
    assert cost == 0.0
    assert model_name == "simple_extraction"

def test_strength_0_multiple_code_blocks():
    llm_output = "```python\ncode1\n```\ntext\n```javascript\ncode2\n```"
    expected_code = "code1\ncode2" # postprocess_0 concatenates content from all blocks
    extracted_code, cost, model_name = postprocess(llm_output, "python", strength=0)
    assert extracted_code == expected_code
    assert cost == 0.0
    assert model_name == "simple_extraction"

def test_strength_0_empty_code_block():
    llm_output = "```python\n```"
    expected_code = ""
    extracted_code, cost, model_name = postprocess(llm_output, "python", strength=0)
    assert extracted_code == expected_code
    assert cost == 0.0
    assert model_name == "simple_extraction"

def test_strength_0_code_block_at_start():
    llm_output = "```python\ncode\n```text"
    expected_code = "code"
    extracted_code, cost, model_name = postprocess(llm_output, "python", strength=0)
    assert extracted_code == expected_code
    assert cost == 0.0
    assert model_name == "simple_extraction"

def test_strength_0_code_block_at_end():
    llm_output = "text```python\ncode\n```" # Assuming ``` is on a new line or handled by split
    expected_code = "code"
    extracted_code, cost, model_name = postprocess(llm_output, "python", strength=0)
    assert extracted_code == expected_code
    assert cost == 0.0
    assert model_name == "simple_extraction"

def test_strength_0_malformed_only_opening_ticks():
    llm_output = "```python\ncode"
    expected_code = "code"
    extracted_code, cost, model_name = postprocess(llm_output, "python", strength=0)
    assert extracted_code == expected_code
    assert cost == 0.0
    assert model_name == "simple_extraction"

def test_strength_0_malformed_only_closing_ticks():
    llm_output = "code\n```"
    expected_code = "" # `in_code_block` becomes true on the last line, but loop ends
    extracted_code, cost, model_name = postprocess(llm_output, "python", strength=0)
    assert extracted_code == expected_code
    assert cost == 0.0
    assert model_name == "simple_extraction"

@patch('pdd.postprocess.print') # Mock rich.print used in postprocess module
def test_strength_0_verbose_output(mock_rich_print):
    postprocess("```code```", "python", strength=0, verbose=True)
    mock_rich_print.assert_any_call("[blue]Using simple code extraction (strength = 0)[/blue]")


# III. Strength > 0 Path
@patch('pdd.postprocess.llm_invoke')
@patch('pdd.postprocess.load_prompt_template')
def test_strength_gt_0_load_template_fails(mock_load_template, mock_llm_invoke):
    mock_load_template.return_value = None
    with pytest.raises(ValueError, match="Failed to load prompt template"):
        postprocess("some output", "python", strength=0.5)

@patch('pdd.postprocess.load_prompt_template', return_value="dummy_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_strength_gt_0_llm_invoke_fails_returns_none(mock_llm_invoke, mock_load_template):
    mock_llm_invoke.return_value = None
    with pytest.raises(ValueError, match="Failed to get valid response from LLM"):
        postprocess("some output", "python", strength=0.5)

@patch('pdd.postprocess.load_prompt_template', return_value="dummy_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_strength_gt_0_llm_invoke_fails_no_result_key(mock_llm_invoke, mock_load_template):
    mock_llm_invoke.return_value = {'cost': 0.1, 'model_name': 'test_model'} # Missing 'result'
    with pytest.raises(ValueError, match="Failed to get valid response from LLM"):
        postprocess("some output", "python", strength=0.5)

@patch('pdd.postprocess.print') # To check error print
@patch('pdd.postprocess.load_prompt_template', return_value="dummy_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_strength_gt_0_llm_invoke_raises_exception(mock_llm_invoke, mock_load_template, mock_rich_print):
    llm_error_message = "LLM communication error"
    mock_llm_invoke.side_effect = Exception(llm_error_message)
    with pytest.raises(Exception, match=llm_error_message):
        postprocess("some output", "python", strength=0.5)
    mock_rich_print.assert_any_call(f"[red]Error in postprocess: {llm_error_message}[/red]")


@patch('pdd.postprocess.load_prompt_template', return_value="dummy_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_strength_gt_0_successful_extraction_no_backticks(mock_llm_invoke, mock_load_template):
    code_content = "print('hello')"
    mock_llm_invoke.return_value = {
        'result': ExtractedCode(extracted_code=code_content),
        'cost': 0.05,
        'model_name': 'gpt-4'
    }
    extracted_code, cost, model_name = postprocess("llm raw output", "python", strength=0.5)
    assert extracted_code == code_content
    assert cost == 0.05
    assert model_name == 'gpt-4'

@patch('pdd.postprocess.load_prompt_template', return_value="dummy_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_strength_gt_0_successful_extraction_with_backticks_and_lang(mock_llm_invoke, mock_load_template):
    llm_code = "```python\nprint('world')\n```"
    expected_code = "print('world')"
    mock_llm_invoke.return_value = {
        'result': ExtractedCode(extracted_code=llm_code),
        'cost': 0.06,
        'model_name': 'gpt-3.5'
    }
    extracted_code, cost, model_name = postprocess("llm raw output", "python", strength=0.5)
    assert extracted_code == expected_code
    assert cost == 0.06
    assert model_name == 'gpt-3.5'

@patch('pdd.postprocess.load_prompt_template', return_value="dummy_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_strength_gt_0_successful_extraction_with_backticks_no_lang(mock_llm_invoke, mock_load_template):
    llm_code = "```\nprint('test')\n```"
    expected_code = "print('test')"
    mock_llm_invoke.return_value = {
        'result': ExtractedCode(extracted_code=llm_code),
        'cost': 0.07,
        'model_name': 'claude-2'
    }
    extracted_code, cost, model_name = postprocess("llm raw output", "python", strength=0.5)
    assert extracted_code == expected_code
    assert cost == 0.07
    assert model_name == 'claude-2'

@patch('pdd.postprocess.load_prompt_template', return_value="dummy_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_strength_gt_0_successful_extraction_empty_code_from_llm(mock_llm_invoke, mock_load_template):
    llm_code = ""
    expected_code = ""
    mock_llm_invoke.return_value = {
        'result': ExtractedCode(extracted_code=llm_code),
        'cost': 0.01,
        'model_name': 'gemini-pro'
    }
    extracted_code, cost, model_name = postprocess("llm raw output", "python", strength=0.5)
    assert extracted_code == expected_code
    assert cost == 0.01
    assert model_name == 'gemini-pro'

@patch('pdd.postprocess.load_prompt_template', return_value="dummy_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_strength_gt_0_successful_extraction_llm_returns_backticks_only_with_lang(mock_llm_invoke, mock_load_template):
    llm_code = "```python\n```"
    expected_code = ""
    mock_llm_invoke.return_value = {
        'result': ExtractedCode(extracted_code=llm_code),
        'cost': 0.02,
        'model_name': 'gpt-4o'
    }
    extracted_code, cost, model_name = postprocess("llm raw output", "python", strength=0.5)
    assert extracted_code == expected_code
    assert cost == 0.02
    assert model_name == 'gpt-4o'

@patch('pdd.postprocess.load_prompt_template', return_value="dummy_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_strength_gt_0_successful_extraction_llm_returns_just_opening_backtick_and_lang(mock_llm_invoke, mock_load_template):
    llm_code = "```python\n" # Note: no closing backtick line
    expected_code = "" # The first line "```python" is removed, remaining is empty
    mock_llm_invoke.return_value = {
        'result': ExtractedCode(extracted_code=llm_code),
        'cost': 0.02,
        'model_name': 'gpt-4o'
    }
    extracted_code, cost, model_name = postprocess("llm raw output", "python", strength=0.5)
    assert extracted_code == expected_code
    assert cost == 0.02
    assert model_name == 'gpt-4o'

@patch('pdd.postprocess.load_prompt_template', return_value="dummy_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_strength_gt_0_successful_extraction_llm_returns_code_with_internal_backticks_string(mock_llm_invoke, mock_load_template):
    llm_code = "```python\ntext = \"```\"\nprint(text)\n```"
    expected_code = "text = \"```\"\nprint(text)"
    mock_llm_invoke.return_value = {
        'result': ExtractedCode(extracted_code=llm_code),
        'cost': 0.08,
        'model_name': 'gpt-4'
    }
    extracted_code, cost, model_name = postprocess("llm raw output", "python", strength=0.5)
    assert extracted_code == expected_code
    assert cost == 0.08
    assert model_name == 'gpt-4'

@patch('pdd.postprocess.print')
@patch('pdd.postprocess.load_prompt_template', return_value="dummy_prompt_template")
@patch('pdd.postprocess.llm_invoke')
def test_strength_gt_0_verbose_output(mock_llm_invoke, mock_load_template, mock_rich_print):
    mock_llm_invoke.return_value = {
        'result': ExtractedCode(extracted_code="code"),
        'cost': 0.01,
        'model_name': 'test_model'
    }
    postprocess("llm_output", "python", strength=0.5, verbose=True)
    
    expected_calls = [
        call("[blue]Loaded prompt template for code extraction[/blue]"),
        call("[green]Successfully extracted code[/green]")
    ]
    mock_rich_print.assert_has_calls(expected_calls, any_order=False) # Check order if important
    # To be more robust if other prints occur due to llm_invoke verbose:
    mock_rich_print.assert_any_call("[blue]Loaded prompt template for code extraction[/blue]")
    mock_rich_print.assert_any_call("[green]Successfully extracted code[/green]")


@patch('pdd.postprocess.load_prompt_template', return_value="test_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_strength_gt_0_parameters_passed_to_llm_invoke(mock_llm_invoke, mock_load_template):
    mock_llm_invoke.return_value = {
        'result': ExtractedCode(extracted_code="code"), 'cost': 0.1, 'model_name': 'model'
    }
    
    llm_output_val = "Test LLM Output"
    language_val = "python"
    strength_val = 0.7
    temperature_val = 0.5
    time_val = 0.3
    verbose_val = True

    postprocess(
        llm_output_val,
        language_val,
        strength=strength_val,
        temperature=temperature_val,
        time=time_val,
        verbose=verbose_val
    )

    mock_load_template.assert_called_once_with("extract_code_LLM")
    
    mock_llm_invoke.assert_called_once()
    args, kwargs = mock_llm_invoke.call_args
    
    assert kwargs['prompt'] == "test_prompt"
    assert kwargs['input_json'] == {"llm_output": llm_output_val, "language": language_val}
    assert kwargs['strength'] == strength_val
    assert kwargs['temperature'] == temperature_val
    assert kwargs['time'] == time_val
    assert kwargs['verbose'] == verbose_val
    assert kwargs['output_pydantic'] == ExtractedCode


# IV. Default Parameter Values
@patch('pdd.postprocess.load_prompt_template', return_value="default_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_default_parameters(mock_llm_invoke, mock_load_template):
    mock_llm_invoke.return_value = {
        'result': ExtractedCode(extracted_code="default_code"), 'cost': 0.1, 'model_name': 'default_model'
    }
    
    llm_output_val = "Default Test LLM Output"
    language_val = "javascript"

    postprocess(llm_output_val, language_val) # Use defaults for strength, temp, time, verbose

    mock_llm_invoke.assert_called_once()
    args, kwargs = mock_llm_invoke.call_args
    
    assert kwargs['prompt'] == "default_prompt"
    assert kwargs['input_json'] == {"llm_output": llm_output_val, "language": language_val}
    assert kwargs['strength'] == DEFAULT_STRENGTH  # Default strength
    assert kwargs['temperature'] == 0    # Default temperature
    assert kwargs['time'] == DEFAULT_TIME # Default time
    assert kwargs['verbose'] == False   # Default verbose
    assert kwargs['output_pydantic'] == ExtractedCode


# V. Regression Tests
@patch('pdd.postprocess.load_prompt_template', return_value="test_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_extracted_code_with_focus_and_explanation_no_json_leakage(mock_llm_invoke, mock_load_template):
    """
    Regression test for JSON leakage bug.

    When the LLM returns ExtractedCode with focus, explanation, and extracted_code fields,
    only the extracted_code should be returned. The focus and explanation fields should
    NOT leak into the output as JSON markers.

    This bug occurred when the Pydantic schema only had extracted_code but the prompt
    asked for 3 fields, causing some LLMs to embed the extra fields inside the
    extracted_code string value.
    """
    complex_code = '''def add(a: float, b: float) -> float:
    """Add two numbers."""
    return a + b

def subtract(a: float, b: float) -> float:
    """Subtract b from a."""
    return a - b

if __name__ == "__main__":
    print(add(1, 2))'''

    mock_llm_invoke.return_value = {
        'result': ExtractedCode(
            focus="Python arithmetic module",
            explanation="The code implements basic arithmetic operations with type hints.",
            extracted_code=complex_code
        ),
        'cost': 0.05,
        'model_name': 'test_model'
    }

    result_code, cost, model_name = postprocess(
        "some llm output",
        "python",
        strength=0.5
    )

    # Verify no JSON markers leaked into the extracted code
    json_markers = ['"explanation":', '"focus":', '"description":', '"extracted_code":']
    for marker in json_markers:
        assert marker not in result_code, f"JSON marker '{marker}' leaked into extracted code"

    # Verify the code is exactly what was in extracted_code
    assert result_code == complex_code
    assert cost == 0.05
    assert model_name == 'test_model'


@patch('pdd.postprocess.load_prompt_template', return_value="test_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_extracted_code_model_has_all_prompt_fields(mock_llm_invoke, mock_load_template):
    """
    Verify ExtractedCode model accepts focus and explanation fields.

    The extract_code_LLM.prompt asks for 3 fields: focus, explanation, extracted_code.
    The Pydantic model must accept all 3 to prevent LLMs from embedding extra fields
    inside the extracted_code string.
    """
    # This should not raise any validation errors
    extracted = ExtractedCode(
        focus="test focus",
        explanation="test explanation",
        extracted_code="print('hello')"
    )

    assert extracted.focus == "test focus"
    assert extracted.explanation == "test explanation"
    assert extracted.extracted_code == "print('hello')"


@patch('pdd.postprocess.load_prompt_template', return_value="test_prompt")
@patch('pdd.postprocess.llm_invoke')
def test_extracted_code_model_optional_fields(mock_llm_invoke, mock_load_template):
    """
    Verify focus and explanation fields have defaults (are optional).

    Some LLMs may only return extracted_code, so the other fields should be optional.
    """
    # This should not raise - focus and explanation should have defaults
    extracted = ExtractedCode(extracted_code="print('hello')")

    assert extracted.focus == ""
    assert extracted.explanation == ""
    assert extracted.extracted_code == "print('hello')"


# Tests for issue #264: Strip <prompt> tags from generated .prompt files
def test_strength_0_prompt_tags_stripped():
    """Test that <prompt> and </prompt> tags are stripped when language is 'prompt'."""
    llm_output = """<prompt>
This is the actual prompt content that should be kept.
</prompt>"""
    expected_code = """This is the actual prompt content that should be kept."""
    extracted_code, cost, model_name = postprocess(llm_output, "prompt", strength=0)
    assert extracted_code == expected_code
    assert cost == 0.0
    assert model_name == "simple_extraction"


def test_strength_0_prompt_tags_with_extra_whitespace():
    """Test that <prompt> tags with extra whitespace are handled correctly."""
    llm_output = """  <prompt>  
Content with whitespace.
  </prompt>  """
    expected_code = """Content with whitespace."""
    extracted_code, cost, model_name = postprocess(llm_output, "prompt", strength=0)
    assert extracted_code == expected_code


def test_strength_0_prompt_tags_nested_content():
    """Test that nested content within <prompt> tags is preserved."""
    llm_output = """<prompt>
Outer content
<inner>nested</inner>
More content
</prompt>"""
    expected_code = """Outer content
<inner>nested</inner>
More content"""
    extracted_code, cost, model_name = postprocess(llm_output, "prompt", strength=0)
    assert extracted_code == expected_code


def test_strength_0_prompt_tags_empty():
    """Test that empty <prompt> tags return empty string."""
    llm_output = """<prompt></prompt>"""
    expected_code = """"""
    extracted_code, cost, model_name = postprocess(llm_output, "prompt", strength=0)
    assert extracted_code == expected_code


def test_prompt_tags_stripped_with_llm_strength():
    """CRITICAL: This is the real-world scenario (EXTRACTION_STRENGTH=0.5)."""
    llm_output = """<prompt>
This is the actual prompt content.
</prompt>"""
    expected_code = """This is the actual prompt content."""
    extracted_code, cost, model_name = postprocess(llm_output, "prompt", strength=0.5)
    assert extracted_code == expected_code
    assert cost == 0.0
    assert model_name == "simple_extraction"


def test_prompt_language_strips_triple_backticks():
    """Test that triple backticks are also stripped for language="prompt"."""
    llm_output = """```xml
<prompt>
This is the actual prompt content.
</prompt>
```"""
    expected_code = """This is the actual prompt content."""
    extracted_code, cost, model_name = postprocess(llm_output, "prompt", strength=0.5)
    assert extracted_code == expected_code


def test_prompt_language_strips_backticks_and_tags():
    """Test that both backticks and prompt tags are stripped."""
    llm_output = """```
<prompt>
Clean prompt content.
</prompt>
```"""
    expected_code = """Clean prompt content."""
    extracted_code, cost, model_name = postprocess(llm_output, "prompt", strength=0.5)
    assert extracted_code == expected_code


def test_prompt_language_strips_backticks_only():
    """Test that backticks are stripped even without prompt tags."""
    llm_output = """```xml
Clean prompt without tags.
```"""
    expected_code = """Clean prompt without tags."""
    extracted_code, cost, model_name = postprocess(llm_output, "prompt", strength=0)
    assert extracted_code == expected_code
