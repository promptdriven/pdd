import os
import asyncio
import pytest
from unittest.mock import MagicMock, patch, AsyncMock
from pathlib import Path
import click
import ast

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
    with patch('pdd.context_generator_main.CloudConfig.get_jwt_token') as mock:
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

# ---------------------------------------------------------------------------
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
        # CloudConfig.get_jwt_token returns None when auth fails
        mock_get_jwt_token.return_value = None
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

def test_jwt_token_obtained_before_async_context(mock_ctx, mock_construct_paths, mock_get_jwt_token, mock_httpx_client, mock_preprocess, tmp_path):
    """Regression test: JWT token must be obtained BEFORE entering asyncio.run().

    This prevents the nested asyncio.run() bug where:
    1. context_generator_main calls asyncio.run(_run_cloud_generation(...))
    2. _run_cloud_generation calls CloudConfig.get_jwt_token()
    3. get_jwt_token internally calls asyncio.run(device_flow_get_token(...))
    4. This causes RuntimeError: "asyncio.run() cannot be called from a running event loop"

    The fix is to call get_jwt_token() BEFORE asyncio.run() and pass the token as a parameter.
    """
    with patch.dict(os.environ, {"NEXT_PUBLIC_FIREBASE_API_KEY": "fake_key", "GITHUB_CLIENT_ID": "fake_id"}):
        mock_ctx.obj['local'] = False
        prompt_file = tmp_path / "test.prompt"
        code_file = tmp_path / "test.py"
        output_file = tmp_path / "test_example.py"
        prompt_file.write_text("Prompt content")
        code_file.write_text("def foo(): pass")
        mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt content", "code_file": "def foo(): pass"}, {"output": str(output_file)}, "python")

        # Track when get_jwt_token is called relative to asyncio.run
        call_order = []

        def track_jwt_call(*args, **kwargs):
            call_order.append('get_jwt_token')
            return "fake_jwt_token"

        mock_get_jwt_token.side_effect = track_jwt_call

        # Mock the httpx response
        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_response.json.return_value = {"generatedExample": "# Cloud Code", "totalCost": 0.05, "modelName": "test-model"}
        mock_client_instance = AsyncMock()
        mock_client_instance.post.return_value = mock_response
        mock_httpx_client.return_value.__aenter__.return_value = mock_client_instance

        # Patch asyncio.run to track when it's called
        original_asyncio_run = asyncio.run
        def tracked_asyncio_run(coro, **kwargs):
            call_order.append('asyncio_run')
            return original_asyncio_run(coro, **kwargs)

        with patch('pdd.context_generator_main.asyncio.run', side_effect=tracked_asyncio_run):
            result_code, cost, model = context_generator_main(mock_ctx, str(prompt_file), str(code_file), None)

        # Verify get_jwt_token was called BEFORE asyncio.run
        assert 'get_jwt_token' in call_order, "get_jwt_token should be called"
        assert 'asyncio_run' in call_order, "asyncio.run should be called for cloud execution"
        jwt_index = call_order.index('get_jwt_token')
        asyncio_index = call_order.index('asyncio_run')
        assert jwt_index < asyncio_index, (
            f"get_jwt_token must be called BEFORE asyncio.run to avoid nested event loop. "
            f"Call order was: {call_order}"
        )
        assert result_code == "# Cloud Code"


def test_cloud_generation_receives_token_parameter(mock_ctx, mock_construct_paths, mock_get_jwt_token, mock_preprocess, tmp_path):
    """Verify that _run_cloud_generation receives token as a parameter, not acquiring it internally.

    Regression guard: protects the nested asyncio.run() fix. If the JWT is fetched inside the
    async cloud generation function instead of being passed in, CloudConfig.get_jwt_token()'s
    internal asyncio.run() will be called from inside an already-running event loop and raise
    "asyncio.run() cannot be called from a running event loop".
    """
    import inspect
    from pdd.context_generator_main import _run_cloud_generation

    sig = inspect.signature(_run_cloud_generation)
    param_names = list(sig.parameters.keys())
    assert 'token' in param_names, (
        f"_run_cloud_generation must accept 'token' as a parameter to avoid nested asyncio.run(). "
        f"Current parameters: {param_names}"
    )


def test_format_md_with_explicit_output_path(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """Test that --format md option overrides extension even with explicit --output path."""
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "test.py"
    explicit_output = tmp_path / "custom_example.py"  # User provides .py extension
    prompt_file.write_text("Prompt")
    code_file.write_text("Code")
    # construct_paths returns format-adjusted path with .md extension
    format_adjusted_path = str(tmp_path / "test_example.md")
    mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt", "code_file": "Code"}, {"output": format_adjusted_path}, "python")
    mock_context_generator.return_value = ("# Markdown Example", 0.0, "model")
    
    # Call with format="md" and explicit output path
    context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(explicit_output), format="md")
    
    # Should have saved to .md file (extension overridden from .py)
    expected_output = tmp_path / "custom_example.md"
    assert expected_output.exists(), f"Expected output file {expected_output} to exist"
    assert expected_output.read_text() == "# Markdown Example"
    # Original .py path should not exist
    assert not explicit_output.exists(), f"Original path {explicit_output} should not exist (extension was changed)"

def test_format_code_with_explicit_output_path(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """Issue #1205: with --format code (the default), an explicit user-supplied --output suffix must be honored verbatim.

    The previous behavior — silently rewriting the suffix to match the language — caused the
    extension-rewrite bug (.yml → .yaml, .md → .markdown, .m → .matlab). The corrected contract
    is: when the user supplied a non-empty suffix on --output, write to that exact path. Users
    who want a different extension for a Markdown-style narrative example can pass --format md.
    """
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "test.py"
    explicit_output = tmp_path / "custom_example.md"  # User-supplied suffix must win
    prompt_file.write_text("Prompt")
    code_file.write_text("Code")
    default_path = str(tmp_path / "test_example.py")
    mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt", "code_file": "Code"}, {"output": default_path}, "python")
    mock_context_generator.return_value = ("# Python Example", 0.0, "model")

    context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(explicit_output), format="code")

    # User-supplied .md path must be honored — no silent rewrite to .py
    assert explicit_output.exists(), f"Expected user-supplied path {explicit_output} to exist"
    assert explicit_output.read_text() == "# Python Example"
    rewritten = tmp_path / "custom_example.py"
    assert not rewritten.exists(), f"Path {rewritten} must not exist (user supplied .md explicitly)"

def test_format_md_without_explicit_output(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """Test that --format md option works with default output path generation."""
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "test.py"
    output_file = tmp_path / "test_example.md"  # Default path with .md extension
    prompt_file.write_text("Prompt")
    code_file.write_text("Code")
    # construct_paths should return path with .md extension due to format option
    mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt", "code_file": "Code"}, {"output": str(output_file)}, "python")
    mock_context_generator.return_value = ("# Markdown Example", 0.0, "model")
    
    # Call with format="md" but no explicit output
    context_generator_main(mock_ctx, str(prompt_file), str(code_file), None, format="md")
    
    assert output_file.exists()
    assert output_file.read_text() == "# Markdown Example"

def test_format_code_default_behavior(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """Test that --format code (default) uses language extension."""
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "test.py"
    output_file = tmp_path / "test_example.py"  # Default path with language extension
    prompt_file.write_text("Prompt")
    code_file.write_text("Code")
    # construct_paths returns path with language extension (.py for Python)
    mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt", "code_file": "Code"}, {"output": str(output_file)}, "python")
    mock_context_generator.return_value = ("# Python Example", 0.0, "model")
    
    # Call with format="code" (explicitly)
    context_generator_main(mock_ctx, str(prompt_file), str(code_file), None, format="code")
    
    assert output_file.exists()
    assert output_file.read_text() == "# Python Example"

def test_format_option_passed_to_construct_paths(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """Test that format option is passed through to construct_paths."""
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "test.py"
    output_file = tmp_path / "test_example.md"
    prompt_file.write_text("Prompt")
    code_file.write_text("Code")
    mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt", "code_file": "Code"}, {"output": str(output_file)}, "python")
    mock_context_generator.return_value = ("# Example", 0.0, "model")
    
    context_generator_main(mock_ctx, str(prompt_file), str(code_file), None, format="md")
    
    # Verify construct_paths was called with format in command_options
    call_args = mock_construct_paths.call_args
    assert call_args is not None
    command_options = call_args.kwargs.get('command_options', {})
    assert command_options.get('format') == 'md', "format option should be passed to construct_paths"

def test_format_md_skips_python_syntax_validation(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """Test that --format md option skips Python syntax validation for markdown output."""
    from unittest.mock import patch
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "test.py"
    output_file = tmp_path / "test_example.md"
    prompt_file.write_text("Prompt")
    code_file.write_text("Code")
    # Markdown content that would fail Python syntax validation
    markdown_content = "# Example Usage\n\nThis is markdown, not Python code.\n- Item 1\n- Item 2"
    mock_construct_paths.return_value = ({}, {"prompt_file": "Prompt", "code_file": "Code"}, {"output": str(output_file)}, "python")
    mock_context_generator.return_value = (markdown_content, 0.0, "model")
    
    # Patch _validate_and_fix_python_syntax to verify it's NOT called
    with patch('pdd.context_generator_main._validate_and_fix_python_syntax') as mock_validate:
        context_generator_main(mock_ctx, str(prompt_file), str(code_file), None, format="md")
        
        # Verify Python syntax validation was NOT called (markdown shouldn't be validated as Python)
        mock_validate.assert_not_called()
        
        # Verify the markdown content was saved unchanged
        assert output_file.exists()
        assert output_file.read_text() == markdown_content

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


# ---------------------------------------------------------------------------
# Issue #1205 regression tests: --output extension must not be silently rewritten
# ---------------------------------------------------------------------------

def test_yml_output_not_rewritten_to_yaml(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """Bug #1205: --output foo.yml with a YAML-language prompt must land at foo.yml, not foo.yaml.

    Previously, format="code" (the Click default) caused with_suffix(".yaml") to
    silently rename the file. This test fails on buggy code and passes once the
    extension-rewrite guard is added.
    """
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "ci_YAML.prompt"
    code_file = tmp_path / "ci.yml"
    prompt_file.write_text("Prompt content")
    code_file.write_text("steps: []")
    requested_output = tmp_path / "test_example.yml"
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "Prompt content", "code_file": "steps: []"},
        {"output": str(requested_output)},
        "yaml",
    )
    mock_context_generator.return_value = ("steps:\n  - run: echo hi\n", 0.01, "local-model")

    context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(requested_output), format="code")

    # The requested .yml path must exist
    assert requested_output.exists(), (
        f"Bug #1205: output was written to the wrong path. "
        f"Expected {requested_output} to exist but it does not. "
        f"(File may have been silently renamed to test_example.yaml)"
    )
    # The silently-rewritten path must NOT exist
    rewritten = tmp_path / "test_example.yaml"
    assert not rewritten.exists(), (
        f"Bug #1205: output was silently rewritten from .yml to .yaml. "
        f"Found unexpected file {rewritten}"
    )


def test_md_output_not_rewritten_to_markdown(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """Bug #1205: --output foo.md with a Markdown-language prompt must land at foo.md, not foo.markdown.

    The BUILTIN_EXT_MAP has no 'markdown' key, so the fallback f".{lang_key}"
    synthesises '.markdown'. This test fails on buggy code.
    """
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "impl_markdown.prompt"
    code_file = tmp_path / "impl.md"
    prompt_file.write_text("Prompt content")
    code_file.write_text("# Implementation")
    requested_output = tmp_path / "impl_example.md"
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "Prompt content", "code_file": "# Implementation"},
        {"output": str(requested_output)},
        "markdown",
    )
    mock_context_generator.return_value = ("# Example\n\nSome markdown.\n", 0.01, "local-model")

    context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(requested_output), format="code")

    assert requested_output.exists(), (
        f"Bug #1205: output was written to the wrong path. "
        f"Expected {requested_output} to exist. "
        f"(File may have been silently renamed to impl_example.markdown)"
    )
    rewritten = tmp_path / "impl_example.markdown"
    assert not rewritten.exists(), (
        f"Bug #1205: output was silently rewritten from .md to .markdown. "
        f"Found unexpected file {rewritten}"
    )


def test_py_output_not_rewritten_regression(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """Regression guard: --output foo.py with Python language must still land at foo.py after the fix."""
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "auth_python.prompt"
    code_file = tmp_path / "auth.py"
    prompt_file.write_text("Prompt content")
    code_file.write_text("def auth(): pass")
    requested_output = tmp_path / "auth_example.py"
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "Prompt content", "code_file": "def auth(): pass"},
        {"output": str(requested_output)},
        "python",
    )
    mock_context_generator.return_value = ("def auth_example(): pass", 0.0, "local-model")

    context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(requested_output), format="code")

    assert requested_output.exists(), f"Expected {requested_output} to exist"
    assert requested_output.read_text() == "def auth_example(): pass"


def test_format_none_honors_yml_output(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """When format=None (the pre-bug safe path), --output foo.yml must land at foo.yml."""
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "ci_YAML.prompt"
    code_file = tmp_path / "ci.yml"
    prompt_file.write_text("Prompt content")
    code_file.write_text("steps: []")
    requested_output = tmp_path / "test_example.yml"
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "Prompt content", "code_file": "steps: []"},
        {"output": str(requested_output)},
        "yaml",
    )
    mock_context_generator.return_value = ("steps:\n  - run: echo hi\n", 0.0, "local-model")

    # format=None triggers the else branch — the safe path that must keep working
    context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(requested_output), format=None)

    assert requested_output.exists(), f"Expected {requested_output} to exist when format=None"
    rewritten = tmp_path / "test_example.yaml"
    assert not rewritten.exists(), f"Extension must not be rewritten when format=None"


def test_no_output_yaml_uses_construct_paths_result(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """When --output is omitted, the path returned by construct_paths is used unchanged."""
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "ci_YAML.prompt"
    code_file = tmp_path / "ci.yml"
    prompt_file.write_text("Prompt content")
    code_file.write_text("steps: []")
    auto_output = tmp_path / "ci_example.yaml"  # construct_paths decides the name
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "Prompt content", "code_file": "steps: []"},
        {"output": str(auto_output)},
        "yaml",
    )
    mock_context_generator.return_value = ("steps: []\n", 0.0, "local-model")

    # No output argument — construct_paths result should be used as-is
    context_generator_main(mock_ctx, str(prompt_file), str(code_file), None, format="code")

    assert auto_output.exists(), f"Expected construct_paths-derived output {auto_output} to exist"


def test_cloud_execution_honors_yml_output(mock_ctx, mock_construct_paths, mock_get_jwt_token, mock_httpx_client, mock_preprocess, tmp_path):
    """Bug #1205: cloud path must also honor --output foo.yml (extension not rewritten before/after cloud call)."""
    mock_ctx.obj['local'] = False
    prompt_file = tmp_path / "ci_YAML.prompt"
    code_file = tmp_path / "ci.yml"
    prompt_file.write_text("Prompt content")
    code_file.write_text("steps: []")
    requested_output = tmp_path / "ci_example.yml"
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "Prompt content", "code_file": "steps: []"},
        {"output": str(requested_output)},
        "yaml",
    )
    mock_get_jwt_token.return_value = "fake_jwt_token"
    mock_response = MagicMock()
    mock_response.status_code = 200
    mock_response.json.return_value = {
        "generatedExample": "steps:\n  - run: echo ok\n",
        "totalCost": 0.02,
        "modelName": "cloud-model",
    }
    mock_client_instance = AsyncMock()
    mock_client_instance.post.return_value = mock_response
    mock_httpx_client.return_value.__aenter__.return_value = mock_client_instance

    context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(requested_output), format="code")

    assert requested_output.exists(), (
        f"Bug #1205 (cloud path): expected output at {requested_output} but it was not found. "
        f"May have been silently renamed to ci_example.yaml"
    )
    rewritten = tmp_path / "ci_example.yaml"
    assert not rewritten.exists(), (
        f"Bug #1205 (cloud path): output silently rewritten to {rewritten}"
    )


def test_matlab_m_output_not_rewritten_to_matlab(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """Bug #1205 generalization: --output foo.m with language='matlab' must land at foo.m, not foo.matlab.

    BUILTIN_EXT_MAP has no 'matlab' entry so the synthesized extension is the literal '.matlab'.
    An alias-whitelist fix that only knows about yaml/markdown still rewrites .m → .matlab.
    This test discriminates between the narrow alias fix and the correct general fix
    (honor any user-supplied non-empty suffix verbatim).
    """
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "calc_MATLAB.prompt"
    code_file = tmp_path / "calc.m"
    prompt_file.write_text("Prompt content")
    code_file.write_text("function y = calc(x); y = x + 1; end")
    requested_output = tmp_path / "calc_example.m"
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "Prompt content", "code_file": "function y = calc(x); y = x + 1; end"},
        {"output": str(requested_output)},
        "matlab",
    )
    mock_context_generator.return_value = ("function y = calc_example(); y = calc(1); end\n", 0.0, "local-model")

    context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(requested_output), format="code")

    assert requested_output.exists(), (
        f"Bug #1205: expected MATLAB output at {requested_output}, but it does not exist "
        f"(likely silently renamed to calc_example.matlab)."
    )
    rewritten = tmp_path / "calc_example.matlab"
    assert not rewritten.exists(), (
        f"Bug #1205: MATLAB output silently rewritten from .m to .matlab at {rewritten}"
    )


def test_bare_name_rewrite_to_existing_py_prompts_for_overwrite(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path, monkeypatch):
    """Bug #1205 follow-up: bare --output name that rewrites to an existing language-extension file must prompt for overwrite.

    construct_paths checks `auth_example` (no suffix, does not exist), so no confirmation is
    raised there. The wrapper then rewrites the path to `auth_example.py`, which DOES exist
    on disk. Without a re-confirmation, the pre-existing file is silently clobbered.
    """
    mock_ctx.obj['local'] = True
    mock_ctx.obj['force'] = False
    prompt_file = tmp_path / "auth_python.prompt"
    code_file = tmp_path / "auth.py"
    prompt_file.write_text("Prompt content")
    code_file.write_text("def auth(): pass")
    pre_existing = tmp_path / "auth_example.py"
    pre_existing.write_text("ORIGINAL CONTENT")
    bare_output = tmp_path / "auth_example"  # no suffix → wrapper rewrites to .py
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "Prompt content", "code_file": "def auth(): pass"},
        {"output": str(bare_output)},
        "python",
    )
    mock_context_generator.return_value = ("def auth_example(): pass", 0.0, "local-model")

    # User declines the overwrite confirmation
    monkeypatch.setattr("pdd.context_generator_main.click.confirm", lambda *a, **k: False)

    with pytest.raises(click.Abort):
        context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(bare_output), format="code")

    # Pre-existing file must be untouched
    assert pre_existing.read_text() == "ORIGINAL CONTENT", (
        "Pre-existing auth_example.py was clobbered without confirmation when the wrapper "
        "rewrote a bare-name --output to .py."
    )


def test_format_md_rewrite_to_existing_md_prompts_for_overwrite(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path, monkeypatch):
    """Bug #1205 follow-up: --format md with a non-.md --output must re-confirm before clobbering an existing .md.

    User passes `--format md --output custom_example.py`. construct_paths sees `custom_example.py`
    (does not exist), no confirmation. Wrapper rewrites to `custom_example.md` which DOES exist
    on disk. Must prompt.
    """
    mock_ctx.obj['local'] = True
    mock_ctx.obj['force'] = False
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "test.py"
    prompt_file.write_text("Prompt content")
    code_file.write_text("def f(): pass")
    pre_existing = tmp_path / "custom_example.md"
    pre_existing.write_text("ORIGINAL MARKDOWN")
    user_output = tmp_path / "custom_example.py"  # wrapper rewrites to .md under --format md
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "Prompt content", "code_file": "def f(): pass"},
        {"output": str(user_output)},
        "python",
    )
    mock_context_generator.return_value = ("# Markdown Example", 0.0, "local-model")

    monkeypatch.setattr("pdd.context_generator_main.click.confirm", lambda *a, **k: False)

    with pytest.raises(click.Abort):
        context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(user_output), format="md")

    assert pre_existing.read_text() == "ORIGINAL MARKDOWN", (
        "Pre-existing custom_example.md was clobbered without confirmation when --format md "
        "rewrote a .py --output to .md."
    )


def test_directory_output_does_not_double_prompt(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path, monkeypatch):
    """Bug #1205 follow-up: --output examples/ must not trigger the wrapper's re-confirmation.

    When --output is a directory (or path ending in '/'), construct_paths already resolves the
    final filename and runs its own overwrite confirmation. The wrapper's new re-confirmation
    step must not fire a second time for the same target.
    """
    mock_ctx.obj['local'] = True
    mock_ctx.obj['force'] = False
    examples_dir = tmp_path / "examples"
    examples_dir.mkdir()
    prompt_file = tmp_path / "auth_python.prompt"
    code_file = tmp_path / "auth.py"
    prompt_file.write_text("Prompt content")
    code_file.write_text("def auth(): pass")
    pre_existing = examples_dir / "auth_example.py"
    pre_existing.write_text("ORIGINAL CONTENT")  # construct_paths would prompt for THIS
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "Prompt content", "code_file": "def auth(): pass"},
        {"output": str(pre_existing)},  # construct_paths already resolved & confirmed
        "python",
    )
    mock_context_generator.return_value = ("def auth_example(): pass", 0.0, "local-model")

    confirm_calls = []

    def tracking_confirm(*args, **kwargs):
        confirm_calls.append(args)
        return True

    monkeypatch.setattr("pdd.context_generator_main.click.confirm", tracking_confirm)

    context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(examples_dir) + "/", format="code")

    assert confirm_calls == [], (
        f"Wrapper should not re-prompt for directory --output (construct_paths already did). "
        f"Got {len(confirm_calls)} unexpected click.confirm call(s)."
    )
    assert pre_existing.read_text() == "def auth_example(): pass"


def test_format_md_uppercase_suffix_normalized_to_lowercase(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """Bug #1205 follow-up: --format md must rewrite .MD → .md so the resolved path uses lowercase.

    Docs promise .md is forced. We can't always observe a separate .MD vs .md on case-insensitive
    filesystems (macOS APFS default), so this test verifies the *stored* filename on disk is
    lowercase by listing the directory — the contract README/help describes.
    """
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "test.py"
    prompt_file.write_text("Prompt content")
    code_file.write_text("def f(): pass")
    user_output = tmp_path / "example.MD"
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "Prompt content", "code_file": "def f(): pass"},
        {"output": str(user_output)},
        "python",
    )
    mock_context_generator.return_value = ("# Markdown Example", 0.0, "local-model")

    context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(user_output), format="md")

    # The file on disk must be stored with the lowercase .md suffix regardless of FS case-sensitivity.
    on_disk = [p.name for p in tmp_path.iterdir() if p.is_file() and p.stem == "example"]
    assert on_disk == ["example.md"], (
        f"Expected exactly one file 'example.md' (lowercase), found {on_disk}. "
        f"--format md must normalize the suffix to lowercase .md."
    )


def test_force_skips_rewrite_overwrite_prompt(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path, monkeypatch):
    """--force must skip the rewrite overwrite-confirmation prompt."""
    mock_ctx.obj['local'] = True
    mock_ctx.obj['force'] = True
    prompt_file = tmp_path / "auth_python.prompt"
    code_file = tmp_path / "auth.py"
    prompt_file.write_text("Prompt content")
    code_file.write_text("def auth(): pass")
    pre_existing = tmp_path / "auth_example.py"
    pre_existing.write_text("ORIGINAL CONTENT")
    bare_output = tmp_path / "auth_example"
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "Prompt content", "code_file": "def auth(): pass"},
        {"output": str(bare_output)},
        "python",
    )
    mock_context_generator.return_value = ("def auth_example(): pass", 0.0, "local-model")

    # confirm would refuse, but --force must bypass it
    monkeypatch.setattr("pdd.context_generator_main.click.confirm", lambda *a, **k: False)

    context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(bare_output), format="code")

    expected_output = tmp_path / "auth_example.py"
    assert expected_output.exists() and expected_output.read_text() == "def auth_example(): pass"


def test_code_format_no_suffix_uses_language_extension(mock_ctx, mock_construct_paths, mock_context_generator, mock_get_jwt_token, tmp_path):
    """Regression guard: when --output has no suffix, the language extension is still applied.

    Honoring user-supplied suffixes must not break the "user gave a bare name" path: bare names
    should still pick up the language-derived extension from BUILTIN_EXT_MAP.
    """
    mock_ctx.obj['local'] = True
    prompt_file = tmp_path / "auth_python.prompt"
    code_file = tmp_path / "auth.py"
    prompt_file.write_text("Prompt content")
    code_file.write_text("def auth(): pass")
    bare_output = tmp_path / "auth_example"  # no suffix
    expected_output = tmp_path / "auth_example.py"
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "Prompt content", "code_file": "def auth(): pass"},
        {"output": str(bare_output)},
        "python",
    )
    mock_context_generator.return_value = ("def auth_example(): pass", 0.0, "local-model")

    context_generator_main(mock_ctx, str(prompt_file), str(code_file), str(bare_output), format="code")

    assert expected_output.exists(), (
        f"Expected language-derived path {expected_output} to exist when user supplied a bare output name."
    )