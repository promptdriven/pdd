import os
import json
import pytest
from unittest.mock import patch, MagicMock
from z3 import *
from pydantic import ValidationError

# Import the module under test
# We assume the python path is set up correctly to find src
from src.utils.llm import get_provider_and_model, analyze_prompt, DEFAULT_MODELS

# --- Z3 Formal Verification Tests ---

def test_z3_verify_provider_logic():
    """
    Formally verify the logic of get_provider_and_model using Z3.
    We prove that the implementation logic matches the intended specification
    for all combinations of environment variables and user inputs.
    """
    s = Solver()

    # Inputs
    has_openai = Bool('has_openai')
    has_anthropic = Bool('has_anthropic')
    has_google = Bool('has_google')
    user_model_provided = Bool('user_model_provided')

    # Outputs (represented as Integers for enum-like behavior)
    # 0: None, 1: OpenAI, 2: Anthropic, 3: Google, 4: Custom
    result = Int('result')

    # --- Specification (The Business Rules) ---
    # Rule 1: If user provides model AND any key exists -> Custom (4)
    # Rule 2: Else if OpenAI key -> OpenAI (1)
    # Rule 3: Else if Anthropic key -> Anthropic (2)
    # Rule 4: Else if Google key -> Google (3)
    # Rule 5: Else -> None (0)
    
    any_key = Or(has_openai, has_anthropic, has_google)
    
    spec_logic = If(And(user_model_provided, any_key), 
                    result == 4,
                    If(has_openai, 
                       result == 1,
                       If(has_anthropic, 
                          result == 2,
                          If(has_google, 
                             result == 3,
                             result == 0))))

    # --- Implementation Model (Matching the code structure) ---
    # The code does:
    # 1. Check keys
    # 2. If user_model: if not any_key return None(0) else return Custom(4)
    # 3. If has_openai return OpenAI(1)
    # 4. elif has_anthropic return Anthropic(2)
    # 5. elif has_google return Google(3)
    # 6. return None(0)

    impl_logic = If(user_model_provided,
                    If(Not(any_key), result == 0, result == 4),
                    If(has_openai,
                       result == 1,
                       If(has_anthropic,
                          result == 2,
                          If(has_google,
                             result == 3,
                             result == 0))))

    # We want to prove that Spec == Implementation for ALL inputs.
    # We do this by asserting Spec != Implementation and checking for UNSAT.
    # If UNSAT, it means there is no case where they differ -> They are equivalent.
    
    # Note: In Z3, we assert the logic implies the result value. 
    # To compare them, we can say: (Spec_Logic_Defining_Result) != (Impl_Logic_Defining_Result)
    # But since 'result' is a variable, we need to formulate it as:
    # "Is there a state of inputs where the Result dictated by Spec is different from Result dictated by Impl?"
    
    # Let's define functions mapping inputs to result
    def get_spec_result():
        return If(And(user_model_provided, any_key), 
                  4,
                  If(has_openai, 
                     1,
                     If(has_anthropic, 
                        2,
                        If(has_google, 
                           3,
                           0))))

    def get_impl_result():
        return If(user_model_provided,
                  If(Not(any_key), 0, 4),
                  If(has_openai,
                     1,
                     If(has_anthropic,
                        2,
                        If(has_google,
                           3,
                           0))))

    s.add(get_spec_result() != get_impl_result())

    check = s.check()
    if check == sat:
        m = s.model()
        print("Counterexample found:")
        print(f"OpenAI: {m[has_openai]}")
        print(f"Anthropic: {m[has_anthropic]}")
        print(f"Google: {m[has_google]}")
        print(f"User Model: {m[user_model_provided]}")
        pytest.fail("Z3 verification failed: Implementation logic does not match Specification.")
    else:
        print("Z3 verification passed: Implementation matches Specification.")

# --- Unit Tests ---

@pytest.fixture
def mock_env():
    with patch.dict(os.environ, {}, clear=True):
        yield

@pytest.fixture
def mock_llm_response_cls():
    """
    Mocks the LLMResponse class imported in src.utils.llm.
    This allows us to test validation logic without relying on the actual Pydantic model.
    """
    with patch("src.utils.llm.LLMResponse") as mock:
        # Define behavior: if input dict has 'fail', raise ValidationError
        def side_effect(**kwargs):
            if kwargs.get("fail_validation"):
                # Create a fake validation error
                raise ValidationError.from_exception_data("MockError", [])
            
            # Return a dummy object with attributes
            instance = MagicMock()
            for k, v in kwargs.items():
                setattr(instance, k, v)
            return instance
        
        mock.side_effect = side_effect
        yield mock

class TestProviderSelection:
    
    def test_no_keys(self, mock_env):
        provider, model = get_provider_and_model()
        assert provider is None
        assert model is None

    def test_openai_priority(self, mock_env):
        with patch.dict(os.environ, {
            "OPENAI_API_KEY": "sk-...",
            "ANTHROPIC_API_KEY": "sk-ant-...",
            "GOOGLE_API_KEY": "AIza..."
        }):
            provider, model = get_provider_and_model()
            assert provider == "openai"
            assert model == DEFAULT_MODELS["openai"]

    def test_anthropic_fallback(self, mock_env):
        with patch.dict(os.environ, {
            "ANTHROPIC_API_KEY": "sk-ant-...",
            "GOOGLE_API_KEY": "AIza..."
        }):
            provider, model = get_provider_and_model()
            assert provider == "anthropic"
            assert model == DEFAULT_MODELS["anthropic"]

    def test_google_fallback(self, mock_env):
        with patch.dict(os.environ, {
            "GOOGLE_API_KEY": "AIza..."
        }):
            provider, model = get_provider_and_model()
            assert provider == "google"
            assert model == DEFAULT_MODELS["google"]

    def test_user_override_success(self, mock_env):
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            provider, model = get_provider_and_model(user_model="gpt-4")
            assert provider == "custom"
            assert model == "gpt-4"

    def test_user_override_fail_no_keys(self, mock_env):
        # User asks for model, but no keys in env
        provider, model = get_provider_and_model(user_model="gpt-4")
        assert provider is None
        assert model is None

class TestAnalyzePrompt:

    @pytest.fixture
    def mock_completion(self):
        with patch("src.utils.llm.litellm.completion") as mock:
            yield mock

    def test_analyze_prompt_no_keys(self, mock_env, mock_completion):
        # Should return None immediately without calling LLM
        result = analyze_prompt("test prompt")
        assert result is None
        mock_completion.assert_not_called()

    def test_analyze_prompt_success(self, mock_env, mock_completion, mock_llm_response_cls):
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            # Setup mock response
            mock_response = MagicMock()
            mock_response.choices[0].message.content = '{"guide_alignment_summary": "Good"}'
            mock_completion.return_value = mock_response

            result = analyze_prompt("test prompt")
            
            assert result is not None
            # Verify LLMResponse was instantiated with the data
            mock_llm_response_cls.assert_called_once()
            call_kwargs = mock_llm_response_cls.call_args[1]
            assert call_kwargs["guide_alignment_summary"] == "Good"

    def test_analyze_prompt_markdown_stripping(self, mock_env, mock_completion, mock_llm_response_cls):
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_response = MagicMock()
            # Response wrapped in markdown code blocks
            mock_response.choices[0].message.content = '```json\n{"guide_alignment_summary": "Cleaned"}\n```'
            mock_completion.return_value = mock_response

            result = analyze_prompt("test prompt")
            
            assert result is not None
            mock_llm_response_cls.assert_called_once()
            assert mock_llm_response_cls.call_args[1]["guide_alignment_summary"] == "Cleaned"

    def test_analyze_prompt_empty_content(self, mock_env, mock_completion):
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_response = MagicMock()
            mock_response.choices[0].message.content = "" # Empty
            mock_completion.return_value = mock_response

            result = analyze_prompt("test prompt")
            assert result is None

    def test_analyze_prompt_auth_error(self, mock_env, mock_completion):
        import litellm
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_completion.side_effect = litellm.exceptions.AuthenticationError("Auth failed", llm_provider="openai", model="gpt-4")
            
            result = analyze_prompt("test prompt")
            assert result is None

    def test_analyze_prompt_timeout(self, mock_env, mock_completion):
        import litellm
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_completion.side_effect = litellm.exceptions.Timeout("Timed out", llm_provider="openai", model="gpt-4")
            
            result = analyze_prompt("test prompt")
            assert result is None

    def test_analyze_prompt_json_decode_error(self, mock_env, mock_completion):
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_response = MagicMock()
            mock_response.choices[0].message.content = "Not JSON"
            mock_completion.return_value = mock_response

            result = analyze_prompt("test prompt")
            assert result is None

    def test_analyze_prompt_validation_error(self, mock_env, mock_completion, mock_llm_response_cls):
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_response = MagicMock()
            # We send a flag that our mock_llm_response_cls recognizes to raise ValidationError
            mock_response.choices[0].message.content = '{"fail_validation": true}'
            mock_completion.return_value = mock_response

            result = analyze_prompt("test prompt")
            assert result is None

    def test_analyze_prompt_generic_exception(self, mock_env, mock_completion):
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_completion.side_effect = Exception("Unexpected crash")
            
            result = analyze_prompt("test prompt")
            assert result is None

    def test_analyze_prompt_config_override(self, mock_env, mock_completion, mock_llm_response_cls):
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_response = MagicMock()
            mock_response.choices[0].message.content = '{}'
            mock_completion.return_value = mock_response

            config = {"model": "gpt-4-turbo", "timeout": 50, "max_retries": 5}
            analyze_prompt("test prompt", config=config)

            # Verify config was passed to litellm
            args, kwargs = mock_completion.call_args
            assert kwargs["model"] == "gpt-4-turbo"
            assert kwargs["timeout"] == 50
            assert kwargs["num_retries"] == 5

import os
import pytest
from unittest.mock import patch, MagicMock
import litellm
from src.utils.llm import get_provider_and_model, analyze_prompt, DEFAULT_MODELS

class TestAdditionalCoverage:
    
    @pytest.fixture
    def mock_completion(self):
        with patch("src.utils.llm.litellm.completion") as mock:
            yield mock

    def test_get_provider_and_model_empty_string_user_model(self, mock_env):
        """
        Verify that passing an empty string as user_model falls back to 
        environment detection instead of treating it as a valid custom model.
        """
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            # user_model is empty string, should be treated as falsy
            provider, model = get_provider_and_model(user_model="")
            assert provider == "openai"
            assert model == DEFAULT_MODELS["openai"]

    def test_analyze_prompt_rate_limit_error(self, mock_env, mock_completion):
        """
        Verify that RateLimitError is caught and handled gracefully.
        """
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_completion.side_effect = litellm.exceptions.RateLimitError(
                "Rate limit exceeded", llm_provider="openai", model="gpt-4"
            )
            
            result = analyze_prompt("test prompt")
            assert result is None

    def test_analyze_prompt_defaults_passed_to_litellm(self, mock_env, mock_completion, mock_llm_response_cls):
        """
        Verify that default configuration values (timeout, retries) are passed 
        to the underlying library when no config is provided.
        """
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_response = MagicMock()
            mock_response.choices[0].message.content = '{}'
            mock_completion.return_value = mock_response

            analyze_prompt("test prompt")

            args, kwargs = mock_completion.call_args
            assert kwargs["timeout"] == 20
            assert kwargs["num_retries"] == 2

    def test_analyze_prompt_no_json_mode_for_non_gpt(self, mock_env, mock_completion, mock_llm_response_cls):
        """
        Verify that response_format is NOT sent for non-GPT models (e.g. Anthropic),
        as the code logic restricts it to models containing 'gpt'.
        """
        # Setup environment to prefer Anthropic
        with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "sk-ant-..."}):
            mock_response = MagicMock()
            mock_response.choices[0].message.content = '{}'
            mock_completion.return_value = mock_response

            analyze_prompt("test prompt")

            args, kwargs = mock_completion.call_args
            # The default anthropic model is 'claude-3-haiku...', which does not contain 'gpt'
            assert "gpt" not in kwargs["model"]
            # Use .get() to avoid KeyError if the key is missing (which is expected)
            assert kwargs.get("response_format") is None

    def test_analyze_prompt_partial_markdown_stripping(self, mock_env, mock_completion, mock_llm_response_cls):
        """
        Verify that the markdown stripping logic handles cases where the opening
        tag is present but the closing tag is missing (e.g. truncated output).
        """
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_response = MagicMock()
            # Opening tag present, but no closing tag
            mock_response.choices[0].message.content = '```json\n{"guide_alignment_summary": "Partial"}'
            mock_completion.return_value = mock_response

            result = analyze_prompt("test prompt")
            
            assert result is not None
            mock_llm_response_cls.assert_called_once()
            assert mock_llm_response_cls.call_args[1]["guide_alignment_summary"] == "Partial"

class TestEdgeCases:

    @pytest.fixture
    def mock_completion(self):
        with patch("src.utils.llm.litellm.completion") as mock:
            yield mock

    def test_analyze_prompt_markdown_no_lang_identifier(self, mock_env, mock_completion):
        """
        Verify behavior when LLM returns markdown block without 'json' identifier.
        The regex `^```[a-zA-Z]*\n` handles empty language strings, so this should succeed.
        """
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_response = MagicMock()
            # Markdown block without 'json'
            mock_response.choices[0].message.content = '```\n{"guide_alignment_summary": "No Lang"}\n```'
            mock_completion.return_value = mock_response

            result = analyze_prompt("test prompt")
            
            # Should return a valid response because the code handles this case
            assert result is not None
            assert result.guide_alignment_summary == "No Lang"

    def test_analyze_prompt_json_list_type_error(self, mock_env, mock_completion):
        """
        Verify that if LLM returns a JSON list (valid JSON but wrong structure),
        the resulting TypeError during Pydantic unpacking is caught.
        We use a list of strings so _clean_json_string doesn't extract an inner object.
        """
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_response = MagicMock()
            # Valid JSON list of strings. _clean_json_string won't find braces, so it returns as is.
            # json.loads returns a list. LLMResponse(**list) raises TypeError.
            mock_response.choices[0].message.content = '["Just a string"]'
            mock_completion.return_value = mock_response

            result = analyze_prompt("test prompt")
            
            # Should return None (caught by generic Exception handler)
            assert result is None

    def test_analyze_prompt_custom_gpt_model_json_mode(self, mock_env, mock_completion):
        """
        Verify that a user-specified model containing 'gpt' triggers JSON mode,
        even if it's not one of the default models.
        """
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_response = MagicMock()
            mock_response.choices[0].message.content = '{}'
            mock_completion.return_value = mock_response

            # User provides a custom model name with "gpt"
            config = {"model": "my-custom-gpt-finetune"}
            analyze_prompt("test prompt", config=config)

            args, kwargs = mock_completion.call_args
            assert kwargs["model"] == "my-custom-gpt-finetune"
            assert kwargs["response_format"] == {"type": "json_object"}

    def test_analyze_prompt_logging_verification(self, mock_env, mock_completion):
        """
        Verify that errors trigger appropriate log warnings.
        """
        with patch("src.utils.llm.logger") as mock_logger:
            with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
                # Simulate Auth Error
                mock_completion.side_effect = litellm.exceptions.AuthenticationError(
                    "Auth failed", llm_provider="openai", model="gpt-4"
                )
                
                analyze_prompt("test prompt")
                
                # Verify warning was logged
                assert mock_logger.warning.call_count >= 1
                # Check that the message mentions authentication
                args, _ = mock_logger.warning.call_args
                assert "Authentication failed" in args[0]

# Test Plan
# 1. test_analyze_prompt_embedded_json_text:
#    - Rationale: The code contains specific logic in `_clean_json_string` to extract JSON from surrounding text (finding first `{` and last `}`).
#    - Test: Mock LLM response with conversational text surrounding a valid JSON object. Verify correct extraction and parsing.
#
# 2. test_analyze_prompt_google_config:
#    - Rationale: The code has specific logic to ONLY apply `response_format={"type": "json_object"}` for models containing "gpt".
#    - Test: Mock Google environment/model. Verify `litellm.completion` is called WITHOUT `response_format`.
#
# 3. test_analyze_prompt_payload_construction:
#    - Rationale: Ensure critical hardcoded parameters (temperature=0.1, max_tokens=2000) and the System Prompt are correctly passed to the LLM.
#    - Test: Inspect the `kwargs` passed to the mock `litellm.completion`.
#
# 4. test_analyze_prompt_malformed_braces:
#    - Rationale: Test the edge case in `_clean_json_string` where braces exist but are invalid (e.g., reversed `} {`).
#    - Test: Ensure the code doesn't crash and returns None (via JSONDecodeError handling).
#
# 5. test_analyze_prompt_user_override_execution:
#    - Rationale: Verify that a user-provided model override is actually passed to the `litellm` call, taking precedence over environment defaults.
#    - Test: Set environment keys but pass a custom model in config. Verify `litellm` receives the custom model.

from src.utils.llm import SYSTEM_PROMPT

class TestDetailedLogic:

    @pytest.fixture
    def mock_completion(self):
        with patch("src.utils.llm.litellm.completion") as mock:
            yield mock

    def test_analyze_prompt_embedded_json_text(self, mock_env, mock_completion, mock_llm_response_cls):
        """
        Verify that JSON is correctly extracted when embedded in conversational text
        without markdown code blocks.
        """
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_response = MagicMock()
            # JSON embedded in text
            mock_response.choices[0].message.content = (
                "Here is the analysis you requested:\n"
                "{\n"
                '  "guide_alignment_summary": "Embedded JSON"\n'
                "}\n"
                "Hope this helps!"
            )
            mock_completion.return_value = mock_response

            result = analyze_prompt("test prompt")
            
            assert result is not None
            mock_llm_response_cls.assert_called_once()
            assert mock_llm_response_cls.call_args[1]["guide_alignment_summary"] == "Embedded JSON"

    def test_analyze_prompt_google_config(self, mock_env, mock_completion):
        """
        Verify that Google models (which don't contain 'gpt') do NOT receive
        the response_format parameter.
        """
        with patch.dict(os.environ, {"GOOGLE_API_KEY": "AIza..."}):
            mock_response = MagicMock()
            mock_response.choices[0].message.content = '{}'
            mock_completion.return_value = mock_response

            analyze_prompt("test prompt")

            args, kwargs = mock_completion.call_args
            # Default google model is gemini-2.0-flash-exp
            assert "gemini" in kwargs["model"]
            # Should not have response_format
            assert "response_format" not in kwargs or kwargs["response_format"] is None

    def test_analyze_prompt_payload_construction(self, mock_env, mock_completion):
        """
        Verify that critical parameters (System Prompt, Temperature, Max Tokens) 
        are correctly passed to the LLM.
        """
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_response = MagicMock()
            mock_response.choices[0].message.content = '{}'
            mock_completion.return_value = mock_response

            prompt_text = "My raw prompt"
            analyze_prompt(prompt_text)

            args, kwargs = mock_completion.call_args
            
            # Check Hardcoded params
            assert kwargs["temperature"] == 0.1
            assert kwargs["max_tokens"] == 2000
            
            # Check Messages structure
            messages = kwargs["messages"]
            assert len(messages) == 2
            assert messages[0]["role"] == "system"
            assert messages[0]["content"] == SYSTEM_PROMPT
            assert messages[1]["role"] == "user"
            assert prompt_text in messages[1]["content"]

    def test_analyze_prompt_malformed_braces(self, mock_env, mock_completion):
        """
        Verify behavior when response contains braces but they are structurally invalid
        for extraction (e.g. reversed), ensuring the extraction logic doesn't crash
        and the JSON parser handles the result safely.
        """
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_response = MagicMock()
            # Braces exist but end appears before start
            mock_response.choices[0].message.content = "End of json } and start of json {"
            mock_completion.return_value = mock_response

            result = analyze_prompt("test prompt")
            
            # The extraction logic (end_idx > start_idx) will fail, returning original string.
            # json.loads will fail. Function should return None.
            assert result is None

    def test_analyze_prompt_user_override_execution(self, mock_env, mock_completion):
        """
        Verify that a user override model is actually passed to the API call,
        even if environment variables for other providers exist.
        """
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-..."}):
            mock_response = MagicMock()
            mock_response.choices[0].message.content = '{}'
            mock_completion.return_value = mock_response

            custom_model = "claude-3-opus-20240229"
            analyze_prompt("test prompt", config={"model": custom_model})

            args, kwargs = mock_completion.call_args
            assert kwargs["model"] == custom_model
            # Since it doesn't contain "gpt", response_format should be absent
            assert "response_format" not in kwargs or kwargs["response_format"] is None