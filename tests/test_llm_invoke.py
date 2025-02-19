import pytest
import os  # Added import for 'os' module
from unittest.mock import patch, MagicMock
from pydantic import BaseModel
from pdd.llm_invoke import llm_invoke

# NEW: Define MockModelInfo by aliasing the ModelInfo from our module.
from pdd.llm_invoke import ModelInfo as MockModelInfo

@pytest.fixture
def mock_select_model():
    with patch('pdd.llm_invoke.select_model') as mock:
        yield mock

# Define a sample Pydantic model for testing
class SampleOutputModel(BaseModel):
    field1: str
    field2: int

@pytest.fixture
def mock_load_models():
    with patch('pdd.llm_invoke.load_models') as mock:
        mock_models = [
            MockModelInfo(
                provider='OpenAI',
                model='gpt-4o-mini',
                input_cost=0.02,
                output_cost=0.03,
                coding_arena_elo=1500,
                structured_output=True,
                base_url="",
                api_key="",
                counter="",
                encoder="",
                max_tokens="",
                max_completion_tokens=""
            ),
            MockModelInfo(
                provider='OpenAI',
                model='cheap-model',
                input_cost=0.01,
                output_cost=0.015,
                coding_arena_elo=1200,
                structured_output=False,
                base_url="",
                api_key="",
                counter="",
                encoder="",
                max_tokens="",
                max_completion_tokens=""
            ),
            MockModelInfo(
                provider='Anthropic',
                model='claude-3',
                input_cost=0.025,
                output_cost=0.035,
                coding_arena_elo=1600,
                structured_output=False,
                base_url="",
                api_key="",
                counter="",
                encoder="",
                max_tokens="",
                max_completion_tokens=""
            ),
            MockModelInfo(
                provider='Google',
                model='gemini-pro',
                input_cost=0.015,
                output_cost=0.025,
                coding_arena_elo=1550,
                structured_output=False,
                base_url="",
                api_key="",
                counter="",
                encoder="",
                max_tokens="",
                max_completion_tokens=""
            )
        ]
        mock.return_value = mock_models
        yield mock

@pytest.fixture
def mock_create_llm_instance():
    with patch('pdd.llm_invoke.create_llm_instance') as mock:
        mock_llm = MagicMock()
        mock_llm.invoke.return_value = "Mocked LLM response"
        mock_llm.with_structured_output.return_value = mock_llm
        mock.return_value = mock_llm
        yield mock

@pytest.fixture
def mock_set_llm_cache():
    with patch('pdd.llm_invoke.set_llm_cache') as mock:
        yield mock

class MockLLM:
    def __init__(self, response):
        self.response = response

    def __call__(self, prompt, **kwargs):
        return self.response

    def invoke(self, prompt, **kwargs):
        return self.response

    def generate(self, prompts, **kwargs):
        from langchain.schema import Generation, LLMResult
        return LLMResult(generations=[[Generation(text=self.response)] for _ in prompts])

    def with_structured_output(self, pydantic_model):
        if isinstance(self.response, str):
            self.response = pydantic_model.model_validate_json(self.response)
        return self

def test_llm_invoke_valid_input(mock_load_models, mock_set_llm_cache):
    with patch('pdd.llm_invoke.create_llm_instance') as mock_create_llm_instance:
        mock_create_llm_instance.return_value = MockLLM("Mocked LLM response")

        # Set first model as candidate
        mock_load_models.return_value[0].api_key = "EXISTING_KEY"

        response = llm_invoke(
            "Valid prompt", 
            {"topic": "cats"}, 
            0.5, 0.7, False
        )

        assert response['model_name'] == 'gpt-4o-mini'

def test_llm_invoke_missing_prompt(mock_load_models, mock_create_llm_instance, mock_select_model, mock_set_llm_cache):
    input_json = {"topic": "cats"}
    strength = 0.5
    temperature = 0.7
    verbose = False

    with pytest.raises(ValueError, match="Prompt is required."):
        llm_invoke(None, input_json, strength, temperature, verbose)

def test_llm_invoke_missing_input_json(mock_load_models, mock_create_llm_instance, mock_select_model, mock_set_llm_cache):
    prompt = "Tell me a joke about cats."
    strength = 0.5
    temperature = 0.7
    verbose = False

    with pytest.raises(ValueError, match="Input JSON is required."):
        llm_invoke(prompt, None, strength, temperature, verbose)

def test_llm_invoke_invalid_input_json_type(mock_load_models, mock_create_llm_instance, mock_select_model, mock_set_llm_cache):
    prompt = "Tell me a joke about cats."
    input_json = "not_a_dict"
    strength = 0.5
    temperature = 0.7
    verbose = False

    with pytest.raises(ValueError, match="Input JSON must be a dictionary."):
        llm_invoke(prompt, input_json, strength, temperature, verbose)

def test_llm_invoke_invalid_prompt_template(mock_load_models, mock_create_llm_instance, mock_select_model, mock_set_llm_cache):
    prompt = "{invalid_placeholder"
    input_json = {"topic": "cats"}
    strength = 0.5
    temperature = 0.7
    verbose = False

    # Assuming that an invalid template raises a ValueError in PromptTemplate.from_template
    with patch('pdd.llm_invoke.PromptTemplate.from_template', side_effect=ValueError("Invalid prompt template")):
        with pytest.raises(ValueError, match="Invalid prompt template"):
            llm_invoke(prompt, input_json, strength, temperature, verbose)

def test_llm_invoke_strength_less_than_half(mock_load_models, mock_set_llm_cache):
    # Configure mock models
    mock_load_models.return_value[1].api_key = "EXISTING_KEY"

    with patch('pdd.llm_invoke.create_llm_instance') as mock_create:
        mock_create.return_value = MockLLM("Mocked response")

        response = llm_invoke(
            "Test prompt",
            {"topic": "test"},
            0.3, 0.7, False
        )

        assert response['model_name'] == 'cheap-model'

def test_llm_invoke_strength_greater_than_half(mock_load_models, mock_set_llm_cache):
    # Configure mock models
    mock_load_models.return_value[2].api_key = "EXISTING_KEY"

    with patch('pdd.llm_invoke.create_llm_instance') as mock_create:
        mock_create.return_value = MockLLM("Mocked response")

        response = llm_invoke(
            "Test prompt",
            {"topic": "test"},
            0.7, 0.7, False
        )

        assert response['model_name'] == 'claude-3'

def test_llm_invoke_output_pydantic(mock_load_models, mock_set_llm_cache):
    with patch('pdd.llm_invoke.create_llm_instance') as mock_create:
        json_response = '{"field1": "value1", "field2": 123}'
        mock_create.return_value = MockLLM(json_response)

        prompt = "Provide data."
        input_json = {"query": "Provide data."}
        strength = 0.5
        temperature = 0.7
        verbose = False
        output_pydantic = SampleOutputModel

        response = llm_invoke(prompt, input_json, strength, temperature, verbose, output_pydantic)

        expected_result = SampleOutputModel(field1="value1", field2=123)
        assert response['result'] == expected_result
        assert response['model_name'] == 'gpt-4o-mini'

def test_llm_invoke_llm_error(mock_load_models, mock_set_llm_cache):
    class FaultyLLM:
        def __call__(self, prompt, **kwargs):
            raise Exception("LLM failure")

        def with_structured_output(self, pydantic_model):
            return self

    with patch('pdd.llm_invoke.create_llm_instance') as mock_create:
        mock_create.return_value = FaultyLLM()

        prompt = "Tell me a joke about cats."
        input_json = {"topic": "cats"}
        strength = 0.5
        temperature = 0.7
        verbose = False
        output_pydantic = None

        with pytest.raises(RuntimeError, match="Error during LLM invocation: LLM failure"):
            llm_invoke(prompt, input_json, strength, temperature, verbose, output_pydantic)

def test_llm_invoke_verbose(mock_load_models, mock_set_llm_cache, capsys):
    with patch('pdd.llm_invoke.create_llm_instance') as mock_create:
        with patch('pdd.llm_invoke.select_model') as mock_select:
            mock_model = mock_load_models.return_value[0]
            mock_select.return_value = mock_model
            mock_create.return_value = MockLLM("Mocked LLM response")

            prompt = "Tell me a joke about cats."
            input_json = {"topic": "cats"}
            strength = 0.5
            temperature = 0.7
            verbose = True
            output_pydantic = None

            # Mock calculate_cost to return a specific value
            with patch('pdd.llm_invoke.calculate_cost', return_value=0.00005):
                response = llm_invoke(prompt, input_json, strength, temperature, verbose, output_pydantic)

            captured = capsys.readouterr()
            assert "Selected model: gpt-4o-mini" in captured.out
            assert "Per input token cost: $0.02 per million tokens" in captured.out
            assert "Per output token cost: $0.03 per million tokens" in captured.out
            assert "Number of input tokens: None" in captured.out
            assert "Number of output tokens: None" in captured.out
            assert "Cost of invoke run: $5e-05" in captured.out
            assert "Strength used: 0.5" in captured.out
            assert "Temperature used: 0.7" in captured.out
            assert "Input JSON: {'topic': 'cats'}" in captured.out
            assert "Result: Mocked LLM response" in captured.out

def test_llm_invoke_with_env_variables(mock_load_models, mock_set_llm_cache):
    # Mock environment variables
    with patch.dict(os.environ, {
        'PDD_MODEL_DEFAULT': 'gpt-4o-mini',
        'PDD_PATH': '/fake/path'
    }):
        with patch('pdd.llm_invoke.create_llm_instance') as mock_create:
            mock_create.return_value = MockLLM("Mocked LLM response")

            prompt = "Tell me a joke about cats."
            input_json = {"topic": "cats"}
            strength = 0.5
            temperature = 0.7
            verbose = False
            output_pydantic = None

            response = llm_invoke(prompt, input_json, strength, temperature, verbose, output_pydantic)

            # Ensure load_models was called
            mock_load_models.assert_called_once()

            assert response['result'] == "Mocked LLM response"
            assert response['model_name'] == 'gpt-4o-mini'

def test_llm_invoke_with_structured_output_not_supported(mock_load_models, mock_create_llm_instance, mock_set_llm_cache):
    # Select a model that does not support structured output
    with patch('pdd.llm_invoke.select_model') as mock_select:
        mock_model = MockModelInfo(
            provider='OpenAI',
            model='cheap-model',
            input_cost=0.01,
            output_cost=0.015,
            coding_arena_elo=1200,
            structured_output=False,
            base_url="",
            api_key="",
            counter="",
            encoder="",
            max_tokens="",
            max_completion_tokens=""
        )
        mock_select.return_value = mock_model

        with patch('pdd.llm_invoke.create_llm_instance') as mock_create:
            mock_create.return_value = MockLLM('{"field1": "value1", "field2": 123}')

            prompt = "Provide data."
            input_json = {"query": "Provide data."}
            strength = 0.3
            temperature = 0.7
            verbose = False
            output_pydantic = SampleOutputModel

            response = llm_invoke(prompt, input_json, strength, temperature, verbose, output_pydantic)

            expected_result = SampleOutputModel(field1="value1", field2=123)
            assert response['result'] == expected_result
            assert response['model_name'] == 'cheap-model'

def test_llm_invoke_load_models_file_not_found(mock_create_llm_instance, mock_select_model, mock_set_llm_cache):
    with patch('pdd.llm_invoke.load_models', side_effect=FileNotFoundError("llm_model.csv not found")):
        prompt = "Tell me a joke about cats."
        input_json = {"topic": "cats"}
        strength = 0.5
        temperature = 0.7
        verbose = False
        output_pydantic = None

        with pytest.raises(FileNotFoundError, match="llm_model.csv not found"):
            llm_invoke(prompt, input_json, strength, temperature, verbose, output_pydantic)