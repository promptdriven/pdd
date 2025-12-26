import sys
import os
import pytest
from unittest.mock import MagicMock, patch, AsyncMock
from pathlib import Path
import click
import ast

# Adjust path to import the module under test
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from pdd.context_generator_main import context_generator_main, _validate_and_fix_python_syntax

# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def mock_ctx():
    ctx = MagicMock(spec=click.Context)
    ctx.obj = {
        'verbose': False,
        'strength': 0.5,
        'temperature': 0.0,
        'time': None,
        'force': False,
        'quiet': True,
        'local': False,  # Default to cloud execution
        'context': None,
        'confirm_callback': None
    }
    ctx.params = {}
    return ctx

@pytest.fixture
def mock_construct_paths():
    with patch('pdd.context_generator_main.construct_paths') as mock:
        yield mock

@pytest.fixture
def mock_context_generator():
    with patch('pdd.context_generator_main.context_generator') as mock:
        yield mock

@pytest.fixture
def mock_get_jwt_token():
    with patch('pdd.context_generator_main.get_jwt_token', new_callable=AsyncMock) as mock:
        yield mock

@pytest.fixture
def mock_httpx_client():
    with patch('httpx.AsyncClient') as mock:
        yield mock

@pytest.fixture
def mock_preprocess():
    with patch('pdd.context_generator_main.preprocess') as mock:
        mock.side_effect = lambda x, **kwargs: x
        yield mock

# ------------------------------------------------="--------------------------
# Unit Tests
# ---------------------------------------------------------------------------

def test_local_execution_success(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "test.py"
    output_file = tmp_path / "test_example.py"
    prompt_file.write_text("Prompt content")
    code_file.write_text("def foo(): pass")
    mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt content", "code_file": "def foo(): pass"}, {"output": str(output_file)}, "python")
    mock_context_generator.return_value = ("# Generated Example", 0.01, "gpt-4-local")
    result_code, cost, model = context_generator_main(mock_ctx, str(prompt_file), str(code_file), None)
    assert result_code == "# Generated Example"
    assert output_file.read_text() == "# Generated Example"

def test_cloud_execution_success(mock_ctx, mock_construct_paths, mock_get_jwt_token, mock_httpx_client, mock_preprocess, tmp_path):
    with patch.dict(os.environ, {"NEXT_PUBLIC_FIREBASE_API_KEY": "fake_key", "GITHUB_CLIENT_ID": "fake_id"}):
        mock_ctx.obj['local'] = False
        prompt_file = tmp_path / "test.prompt"
        code_file = tmp_path / "test.py"
        output_file = tmp_path / "test_example.py"
        prompt_file.write_text("Prompt content")
        code_file.write_text("def foo(): pass")
        mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt content", "code_file": "def foo(): pass"}, {"output": str(output_file)}, "python")
        mock_get_jwt_token.return_value = "fake_jwt_token"
        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_response.json.return_value = {"generatedExample": "# Cloud Code", "totalCost": 0.05, "modelName": "gpt-4-cloud"}
        mock_client_instance = AsyncMock()
        mock_client_instance.post.return_value = mock_response
        mock_httpx_client.return_value.__aenter__.return_value = mock_client_instance
        result_code, cost, model = context_generator_main(mock_ctx, str(prompt_file), str(code_file), None)
        assert result_code == "# Cloud Code"

def test_cloud_fallback_to_local(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    with patch.dict(os.environ, {"NEXT_PUBLIC_FIREBASE_API_KEY": "fake_key"}):
        mock_ctx.obj['local'] = False
        prompt_file = tmp_path / "test.prompt"
        code_file = tmp_path / "test.py"
        output_file = tmp_path / "test_example.py"
        prompt_file.write_text("Prompt")
        code_file.write_text("Code")
        mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt", "code_file": "Code"}, {"output": str(output_file)}, "python")
        from pdd.get_jwt_token import AuthError
        mock_get_jwt_token.side_effect = AuthError("Auth failed")
        mock_context_generator.return_value = ("# Local Code", 0.02, "local-model")
        result_code, cost, model = context_generator_main(mock_ctx, str(prompt_file), str(code_file), None)
        assert result_code == "# Local Code"
        mock_context_generator.assert_called_once()

def test_syntax_fix_json_garbage(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "test.py"
    output_file = tmp_path / "test_example.py"
    prompt_file.write_text("Prompt")
    code_file.write_text("Code")
    mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt", "code_file": "Code"}, {"output": str(output_file)}, "python")
    bad_code = "def hello():\n    print(\"Hello\")\n```json\n{\"explanation\": \"This is code\"}\n```"
    mock_context_generator.return_value = (bad_code, 0.0, "model")
    context_generator_main(mock_ctx, str(prompt_file), str(code_file), None)
    saved_content = output_file.read_text()
    assert 'def hello():' in saved_content
    assert '{\"explanation\":' not in saved_content
    ast.parse(saved_content)

def test_syntax_fix_failure_preserves_code(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "test.py"
    output_file = tmp_path / "test_example.py"
    prompt_file.write_text("Prompt")
    code_file.write_text("Code")
    mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt", "code_file": "Code"}, {"output": str(output_file)}, "python")
    broken_code = "def hello(:"
    mock_context_generator.return_value = (broken_code, 0.0, "model")
    context_generator_main(mock_ctx, str(prompt_file), str(code_file), None)
    assert output_file.read_text() == broken_code

def test_explicit_output_path(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "test.py"
    explicit_output = tmp_path / "custom_dir" / "custom_output.py"
    explicit_output.parent.mkdir()
    prompt_file.write_text("Prompt")
    code_file.write_text("Code")
    mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt", "code_file": "Code"}, {"output": "default.py"}, "python")
    mock_context_generator.return_value = ("code", 0.0, "model")
    context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(explicit_output))
    assert explicit_output.exists()

def test_empty_generation_raises_error(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "test.py"
    prompt_file.write_text("Prompt")
    code_file.write_text("Code")
    mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt", "code_file": "Code"}, {"output": "out.py"}, "python")
    mock_context_generator.return_value = ("", 0.0, "model")
    with pytest.raises(click.UsageError, match="Example generation failed"):
        context_generator_main(mock_ctx, str(prompt_file), str(code_file), None)

def test_local_flag_read_from_ctx_obj_not_params(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """Regression test: Ensure --local flag is read from ctx.obj, not ctx.params.

    This prevents a bug where setting ctx.params['local'] = True would be ignored
    because the code should read from ctx.obj['local'] (set by the CLI group).
    """
    # Provide env vars so cloud path would proceed to get_jwt_token if local flag is misread
    with patch.dict(os.environ, {"NEXT_PUBLIC_FIREBASE_API_KEY": "fake_key", "GITHUB_CLIENT_ID": "fake_id"}):
        # Set local=True in ctx.obj but not in ctx.params
        mock_ctx.obj['local'] = True
        mock_ctx.params = {}  # Explicitly empty to prove we don't read from params

        prompt_file = tmp_path / "test.prompt"
        code_file = tmp_path / "test.py"
        output_file = tmp_path / "test_example.py"
        prompt_file.write_text("Prompt content")
        code_file.write_text("def foo(): pass")

        mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt content", "code_file": "def foo(): pass"}, {"output": str(output_file)}, "python")
        mock_context_generator.return_value = ("# Local Example", 0.01, "local-model")

        result_code, cost, model = context_generator_main(mock_ctx, str(prompt_file), str(code_file), None)

        # Should use local execution, so context_generator must be called
        mock_context_generator.assert_called_once()
        assert result_code == "# Local Example"
        # Verify no cloud auth was attempted - this would fail if local flag was misread from ctx.params
        mock_get_jwt_token.assert_not_called()

def test_z3_syntax_fixer_logic():
    try:
        import z3
    except ImportError:
        pytest.skip("Z3 not installed")
    def binary_search_simulator(validity_map):
        low = 0
        high = len(validity_map)
        valid_len = 0
        for _ in range(10):
            if low >= high: break
            mid = (low + high + 1) // 2
            is_valid = validity_map[mid-1] if 0 < mid <= len(validity_map) else False
            if is_valid:
                valid_len = mid
                low = mid
            else:
                high = mid - 1
        return valid_len
    for i in range(32):
        v_map = [(i >> bit) & 1 == 1 for bit in range(5)]
        result_len = binary_search_simulator(v_map)
        is_monotonic = True
        for j in range(4):
            if v_map[j] and not v_map[j+1]:
                if any(v_map[k] for k in range(j+2, 5)): is_monotonic = False; break
            if not v_map[j] and v_map[j+1]: is_monotonic = False; break
        if is_monotonic:
            last_true = 0
            for idx, val in enumerate(v_map): 
                if val: last_true = idx + 1
            assert result_len == last_true