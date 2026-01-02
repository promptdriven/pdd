import pytest
from unittest.mock import patch, MagicMock
from pdd import EXTRACTION_STRENGTH
from pdd.code_generator import code_generator
from pathlib import Path
from pdd import DEFAULT_STRENGTH

# Define constants for mock returns
MOCK_PROCESSED_PROMPT = "processed prompt"
MOCK_INITIAL_RESPONSE = {
    'result': "initial LLM output",
    'cost': 0.05,
    'model_name': "model_v1"
}
MOCK_UNFINISHED_RESPONSE_COMPLETE = ( "Reasoning complete", True, 0.01, "model_v1" )
MOCK_UNFINISHED_RESPONSE_INCOMPLETE = ( "Reasoning incomplete", False, 0.01, "model_v1" )
MOCK_FINAL_OUTPUT = "completed LLM output"
MOCK_CONTINUE_RESPONSE = ("completed LLM output", 0.05, "model_v2")
MOCK_POSTPROCESS_RESPONSE = ("runnable_code_here", 0.02, "model_v1")

@pytest.fixture
def mock_preprocess():
    with patch('pdd.code_generator.preprocess') as mock:
        mock.return_value = MOCK_PROCESSED_PROMPT
        yield mock

@pytest.fixture
def mock_llm_invoke():
    with patch('pdd.code_generator.llm_invoke') as mock:
        mock.return_value = MOCK_INITIAL_RESPONSE
        yield mock

@pytest.fixture
def mock_unfinished_prompt():
    with patch('pdd.code_generator.unfinished_prompt') as mock:
        # Default to complete
        mock.return_value = MOCK_UNFINISHED_RESPONSE_COMPLETE
        yield mock

@pytest.fixture
def mock_continue_generation():
    with patch('pdd.code_generator.continue_generation') as mock:
        mock.return_value = MOCK_CONTINUE_RESPONSE
        yield mock

@pytest.fixture
def mock_postprocess():
    with patch('pdd.code_generator.postprocess') as mock:
        mock.return_value = MOCK_POSTPROCESS_RESPONSE
        yield mock

def test_code_generator_valid_input_complete(
    mock_preprocess,
    mock_llm_invoke,
    mock_unfinished_prompt,
    mock_continue_generation,
    mock_postprocess
):
    """
    Test code_generator with valid inputs where generation is complete.
    """
    runnable_code, total_cost, model_name = code_generator(
        prompt="Generate a Python function to add two numbers.",
        language="python",
        strength=0.8,
        temperature=0.5,
        verbose=True
    )

    # Assertions
    mock_preprocess.assert_called_once_with("Generate a Python function to add two numbers.", recursive=False, double_curly_brackets=True)
    mock_llm_invoke.assert_called_once_with(
        prompt=MOCK_PROCESSED_PROMPT,
        input_json={},
        strength=0.8,
        temperature=0.5,
        time=None,
        verbose=True,
        output_schema=None,
        language='python',
    )
    mock_unfinished_prompt.assert_called_once_with(
        prompt_text=MOCK_INITIAL_RESPONSE['result'][-600:],
        strength=0.5,
        temperature=0.0,
        time=None,
        language="python",
        verbose=True
    )
    mock_continue_generation.assert_not_called()
    mock_postprocess.assert_called_once_with(
        llm_output=MOCK_INITIAL_RESPONSE['result'],
        language="python",
        strength=EXTRACTION_STRENGTH,
        temperature=0.0,
        time=None,
        verbose=True
    )
    assert runnable_code == "runnable_code_here"
    assert total_cost == MOCK_INITIAL_RESPONSE['cost'] + MOCK_UNFINISHED_RESPONSE_COMPLETE[2] + MOCK_POSTPROCESS_RESPONSE[1]
    assert model_name == MOCK_INITIAL_RESPONSE['model_name']

def test_code_generator_valid_input_incomplete(
    mock_preprocess,
    mock_llm_invoke,
    mock_unfinished_prompt,
    mock_continue_generation,
    mock_postprocess
):
    """
    Test code_generator with valid inputs where generation is incomplete and requires continuation.
    """
    # Modify the unfinished_prompt mock to indicate incomplete generation
    mock_unfinished_prompt.return_value = MOCK_UNFINISHED_RESPONSE_INCOMPLETE

    runnable_code, total_cost, model_name = code_generator(
        prompt="Generate a Python function to multiply two numbers.",
        language="python",
        strength=DEFAULT_STRENGTH,
        temperature=0.7,
        verbose=False
    )

    # Assertions
    mock_preprocess.assert_called_once_with("Generate a Python function to multiply two numbers.", recursive=False, double_curly_brackets=True)
    mock_llm_invoke.assert_called_once_with(
        prompt=MOCK_PROCESSED_PROMPT,
        input_json={},
        strength=DEFAULT_STRENGTH,
        temperature=0.7,
        time=None,
        verbose=False,
        output_schema=None,
        language='python',
    )
    mock_unfinished_prompt.assert_called_once_with(
        prompt_text=MOCK_INITIAL_RESPONSE['result'][-600:],
        strength=0.5,
        temperature=0.0,
        time=None,
        language="python",
        verbose=False
    )
    mock_continue_generation.assert_called_once_with(
        formatted_input_prompt=MOCK_PROCESSED_PROMPT,
        llm_output=MOCK_INITIAL_RESPONSE['result'],
        strength=DEFAULT_STRENGTH,
        temperature=0.7,
        time=None,
        language="python",
        verbose=False
    )
    mock_postprocess.assert_called_once_with(
        llm_output=MOCK_FINAL_OUTPUT,
        language="python",
        strength=EXTRACTION_STRENGTH,
        temperature=0.0,
        time=None,
        verbose=False
    )
    assert runnable_code == "runnable_code_here"
    assert total_cost == (
        MOCK_INITIAL_RESPONSE['cost'] +
        MOCK_UNFINISHED_RESPONSE_INCOMPLETE[2] +
        MOCK_CONTINUE_RESPONSE[1] +
        MOCK_POSTPROCESS_RESPONSE[1]
    )
    assert model_name == MOCK_CONTINUE_RESPONSE[2]

@pytest.mark.parametrize("prompt,language,strength,temperature,expected_error", [
    ("", "python", 0.5, 0.5, ValueError),
    ("   ", "python", 0.5, 0.5, ValueError),
    ("Valid prompt", "", 0.5, 0.5, ValueError),
    ("Valid prompt", "   ", 0.5, 0.5, ValueError),
    ("Valid prompt", "python", -0.1, 0.5, ValueError),
    ("Valid prompt", "python", 1.1, 0.5, ValueError),
    ("Valid prompt", "python", 0.5, -0.1, ValueError),
    ("Valid prompt", "python", 0.5, 2.1, ValueError),
])
def test_code_generator_invalid_inputs(prompt, language, strength, temperature, expected_error):
    """
    Test code_generator with various invalid input parameters.
    """
    with pytest.raises(expected_error):
        code_generator(
            prompt=prompt,
            language=language,
            strength=strength,
            temperature=temperature,
            verbose=False
        )

@patch('pdd.code_generator.preprocess', side_effect=Exception("Preprocess failed"))
def test_code_generator_preprocess_exception(mock_preprocess, mock_llm_invoke, mock_unfinished_prompt, mock_continue_generation, mock_postprocess):
    """
    Test code_generator when preprocess raises an exception.
    """
    with pytest.raises(Exception) as exc_info:
        code_generator(
            prompt="Generate a Python function to subtract two numbers.",
            language="python",
            strength=0.7,
            temperature=0.3,
            verbose=True
        )
    assert str(exc_info.value) == "Preprocess failed"

@patch('pdd.code_generator.llm_invoke', side_effect=Exception("LLM Invoke failed"))
def test_code_generator_llm_invoke_exception(mock_llm_invoke, mock_preprocess, mock_unfinished_prompt, mock_continue_generation, mock_postprocess):
    """
    Test code_generator when llm_invoke raises an exception.
    """
    with pytest.raises(Exception) as exc_info:
        code_generator(
            prompt="Generate a Python function to divide two numbers.",
            language="python",
            strength=0.6,
            temperature=0.4,
            verbose=False
        )
    assert str(exc_info.value) == "LLM Invoke failed"

@patch('pdd.code_generator.unfinished_prompt', side_effect=Exception("Unfinished Prompt failed"))
def test_code_generator_unfinished_prompt_exception(mock_unfinished_prompt, mock_preprocess, mock_llm_invoke, mock_continue_generation, mock_postprocess):
    """
    Test code_generator when unfinished_prompt raises an exception.
    """
    with pytest.raises(Exception) as exc_info:
        code_generator(
            prompt="Generate a Python function to modulo two numbers.",
            language="python",
            strength=0.5,
            temperature=0.2,
            verbose=False
        )
    assert str(exc_info.value) == "Unfinished Prompt failed"

@patch('pdd.code_generator.continue_generation', side_effect=Exception("Continue Generation failed"))
def test_code_generator_continue_generation_exception(mock_continue_generation, mock_preprocess, mock_llm_invoke, mock_unfinished_prompt, mock_postprocess):
    """
    Test code_generator when continue_generation raises an exception.
    """
    # Indicate that generation is incomplete
    mock_unfinished_prompt.return_value = MOCK_UNFINISHED_RESPONSE_INCOMPLETE

    with pytest.raises(Exception) as exc_info:
        code_generator(
            prompt="Generate a Python function to exponentiate two numbers.",
            language="python",
            strength=0.85,
            temperature=0.6,
            verbose=True
        )
    assert str(exc_info.value) == "Continue Generation failed"

@patch('pdd.code_generator.postprocess', side_effect=Exception("Postprocess failed"))
def test_code_generator_postprocess_exception(mock_postprocess, mock_preprocess, mock_llm_invoke, mock_unfinished_prompt, mock_continue_generation):
    """
    Test code_generator when postprocess raises an exception.
    """
    with pytest.raises(Exception) as exc_info:
        code_generator(
            prompt="Generate a Python function to find the maximum of two numbers.",
            language="python",
            strength=0.75,
            temperature=0.5,
            verbose=False
        )
    assert str(exc_info.value) == "Postprocess failed"

def test_code_generator_edge_case_exact_600_chars(
    mock_preprocess,
    mock_llm_invoke,
    mock_unfinished_prompt,
    mock_continue_generation,
    mock_postprocess
):
    """
    Test code_generator with an initial output exactly 600 characters long.
    """
    # Modify the mock_initial_response to have exactly 600 chars
    mock_llm_invoke.return_value = {
        'result': 'a' * 600,
        'cost': 0.05,
        'model_name': "model_v1"
    }
    # Indicate that generation is complete
    mock_unfinished_prompt.return_value = MOCK_UNFINISHED_RESPONSE_COMPLETE

    runnable_code, total_cost, model_name = code_generator(
        prompt="Generate a Python function with exactly 600 characters output.",
        language="python",
        strength=0.8,
        temperature=0.5,
        verbose=False
    )

    # Assertions
    mock_unfinished_prompt.assert_called_once_with(
        prompt_text='a' * 600,
        strength=0.5,
        temperature=0.0,
        time=None,
        language="python",
        verbose=False
    )
    mock_continue_generation.assert_not_called()
    mock_postprocess.assert_called_once_with(
        llm_output='a' * 600,
        language="python",
        strength=EXTRACTION_STRENGTH,
        temperature=0.0,
        time=None,
        verbose=False
    )
    assert runnable_code == "runnable_code_here"
    assert total_cost == 0.05 + 0.01 + 0.02
    assert model_name == "model_v1"

def test_code_generator_with_image(
    mock_preprocess,
    mock_llm_invoke,
    mock_unfinished_prompt,
    mock_postprocess
):
    """
    Test code_generator with a prompt containing an image.
    """
    image_data = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mNkYAAAAAYAAjCB0C8AAAAASUVORK5CYII="
    prompt_with_image = f"Generate code based on this image: {image_data}"
    mock_preprocess.return_value = prompt_with_image

    code_generator(
        prompt=prompt_with_image,
        language="python",
        strength=0.8,
        temperature=0.5,
        verbose=True
    )

    mock_llm_invoke.assert_called_once()
    call_args = mock_llm_invoke.call_args[1]
    messages = call_args['messages']
    
    assert len(messages) == 1
    assert messages[0]['role'] == 'user'
    
    content = messages[0]['content']
    assert isinstance(content, list)
    assert len(content) == 2
    assert content[0]['type'] == 'text'
    assert content[0]['text'] == 'Generate code based on this image: '
    assert content[1]['type'] == 'image_url'
    assert content[1]['image_url']['url'] == image_data

def test_generate_loops_when_unfinished_never_true(monkeypatch):
    """
    Replicates the loop by forcing unfinished_prompt to always return False.
    This simulates the case where a syntactically complete Python snippet is
    (incorrectly) judged as unfinished, causing continue_generation to loop
    until its MAX_GENERATION_LOOPS guard kicks in.
    """
    # Ensure PDD_PATH is set so load_prompt_template can find prompts
    repo_root = Path(__file__).resolve().parents[1]
    pdd_dir = repo_root / "pdd"
    monkeypatch.setenv("PDD_PATH", str(pdd_dir))

    # Import targets after env is set
    from pdd.code_generator import code_generator as cg_func
    import pdd.code_generator as code_gen_mod
    import pdd.continue_generation as cont_mod

    # Keep MAX loops small so test runs quickly
    monkeypatch.setattr(cont_mod, "MAX_GENERATION_LOOPS", 3, raising=False)

    # Count how many times unfinished is called (initial + loop checks)
    call_counts = {"unfinished": 0}

    def always_unfinished_stub(*args, **kwargs):
        # unfinished_prompt returns: (reasoning: str, is_finished: bool, total_cost: float, model_name: str)
        call_counts["unfinished"] += 1
        return ("mock reasoning", False, 0.0, "mock-model")

    # Patch both the reference used in code_generator and in continue_generation
    monkeypatch.setattr(code_gen_mod, "unfinished_prompt", always_unfinished_stub, raising=False)
    monkeypatch.setattr(cont_mod, "unfinished_prompt", always_unfinished_stub, raising=False)

    # Initial model call during code_generator to produce first output
    initial_code = "def add(a, b):\n    return a + b\n"

    def code_gen_llm_invoke_stub(*args, **kwargs):
        # Return an initial LLM output resembling a complete python function
        return {"result": initial_code, "cost": 0.0, "model_name": "mock"}

    # Continue/trimming LLM calls inside continue_generation
    def cont_llm_invoke_stub(*, prompt, input_json, strength, temperature, time, verbose=False, output_pydantic=None, language=None):
        text_prompt = str(prompt)
        # Trim start prompt (typed output)
        if "expert editor and JSON creator" in text_prompt:
            result = cont_mod.TrimResultsStartOutput(explanation="trim start", code_block=initial_code)
            return {"result": result, "cost": 0.0, "model_name": "mock"}
        # Continue prompt (string output)
        if "continue, by outputting only the rest of the code" in text_prompt:
            return {"result": "\n# cont", "cost": 0.0, "model_name": "mock"}
        # Trim overlap prompt (typed output)
        if "expert JSON editor" in text_prompt and output_pydantic is cont_mod.TrimResultsOutput:
            result = cont_mod.TrimResultsOutput(explanation="trim", trimmed_continued_generation="# cont")
            return {"result": result, "cost": 0.0, "model_name": "mock"}
        # Default: behave like no-op
        if output_pydantic is not None:
            # Generic typed response: create an instance with permissive defaults if possible
            field_names = list(output_pydantic.model_fields.keys())
            values = {field_names[0]: "ok"}
            return {"result": output_pydantic(**values), "cost": 0.0, "model_name": "mock"}
        return {"result": "", "cost": 0.0, "model_name": "mock"}

    # Patch llm_invoke in both modules
    monkeypatch.setattr(code_gen_mod, "llm_invoke", code_gen_llm_invoke_stub, raising=False)
    monkeypatch.setattr(cont_mod, "llm_invoke", cont_llm_invoke_stub, raising=False)

    # Postprocess: bypass LLM and return the combined code directly
    def postprocess_passthrough(llm_output, language, strength=DEFAULT_STRENGTH, temperature=0.0, time=None, verbose=False):
        return (llm_output, 0.0, "mock")

    monkeypatch.setattr(code_gen_mod, "postprocess", postprocess_passthrough, raising=False)

    # Run generator with the simple math prompt content
    prompt_text = (repo_root / "prompts" / "simple_math_python.prompt").read_text()
    final_code, total_cost, model_name = cg_func(
        prompt=prompt_text,
        language="python",
        strength=0.6,
        temperature=0.0,
        time=0.0,
        preprocess_prompt=True,
    )

    # Assert: unfinished was called multiple times (initial + loop checks)
    assert call_counts["unfinished"] >= 2, f"Expected multiple unfinished checks, got {call_counts['unfinished']}"

    # Assert: final code includes the continuation at least once (loop happened)
    assert "# cont" in final_code
