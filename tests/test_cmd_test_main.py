import os
import sys
import pytest
from unittest.mock import MagicMock, patch, mock_open
from pathlib import Path
import click

# Adjust path to import the module under test
# Assuming the test file is in tests/ and the code is in pdd/
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from pdd.cmd_test_main import cmd_test_main

# Mock constants
MOCK_PROMPT_CONTENT = "Task: Write a factorial function."
MOCK_CODE_CONTENT = "def factorial(n): return 1 if n==0 else n*factorial(n-1)"
MOCK_TEST_CONTENT = "def test_factorial(): assert factorial(0) == 1"
MOCK_GENERATED_TEST = "def test_factorial_generated(): assert factorial(5) == 120"
MOCK_COVERAGE_REPORT = "Coverage: 50%"

@pytest.fixture
def mock_ctx():
    ctx = MagicMock(spec=click.Context)
    ctx.obj = {
        "verbose": False,
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
        "force": False,
        "quiet": False,
        "local": False,
        "context": None,
        "confirm_callback": None
    }
    return ctx

@pytest.fixture
def mock_dependencies():
    with patch("pdd.cmd_test_main.construct_paths") as mock_cp, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_rec, \
         patch("pdd.cmd_test_main.generate_test") as mock_gen, \
         patch("pdd.cmd_test_main.increase_tests") as mock_inc, \
         patch("pdd.cmd_test_main.get_jwt_token") as mock_jwt, \
         patch("pdd.cmd_test_main.requests.post") as mock_post, \
         patch("pathlib.Path.read_text") as mock_read, \
         patch("pathlib.Path.write_text") as mock_write, \
         patch("pathlib.Path.mkdir") as mock_mkdir:
        
        # Default setup for construct_paths
        mock_cp.return_value = (
            {}, # resolved_config (unused in function)
            {
                "prompt_file": MOCK_PROMPT_CONTENT,
                "code_file": MOCK_CODE_CONTENT
            }, # input_strings
            {"output": "tests/test_code.py"}, # output_file_paths (key is "output" not "output_file")
            "python" # detected_language
        )

        # Default setup for resolve_effective_config
        mock_rec.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25
        }

        # Default setup for file reading
        mock_read.return_value = "" 

        yield {
            "construct_paths": mock_cp,
            "resolve_effective_config": mock_rec,
            "generate_test": mock_gen,
            "increase_tests": mock_inc,
            "get_jwt_token": mock_jwt,
            "post": mock_post,
            "read_text": mock_read,
            "write_text": mock_write,
            "mkdir": mock_mkdir
        }

def test_validation_missing_existing_tests_for_coverage(mock_ctx):
    """Test that providing coverage_report without existing_tests returns an error."""
    code, cost, model = cmd_test_main(
        ctx=mock_ctx,
        prompt_file="prompt.txt",
        code_file="code.py",
        coverage_report="coverage.xml",
        existing_tests=None
    )
    assert code == ""
    assert cost == 0.0
    assert "Error: Missing existing_tests" in model

def test_local_execution_generate_new_tests(mock_ctx, mock_dependencies):
    """Test local generation of new tests."""
    mock_ctx.obj["local"] = True
    mock_dependencies["generate_test"].return_value = (MOCK_GENERATED_TEST, 0.01, "gpt-4-local")
    
    code, cost, model = cmd_test_main(
        ctx=mock_ctx,
        prompt_file="prompt.txt",
        code_file="code.py",
        output="tests/custom_test.py"
    )

    # Verify generate_test called correctly
    mock_dependencies["generate_test"].assert_called_once()
    args, kwargs = mock_dependencies["generate_test"].call_args
    assert kwargs["prompt"] == MOCK_PROMPT_CONTENT
    assert kwargs["code"] == MOCK_CODE_CONTENT
    assert kwargs["language"] == "python"
    
    # Verify output written
    mock_dependencies["write_text"].assert_called_once_with(MOCK_GENERATED_TEST, encoding="utf-8")
    assert code == MOCK_GENERATED_TEST
    assert model == "gpt-4-local"

def test_local_execution_increase_tests(mock_ctx, mock_dependencies):
    """Test local enhancement of existing tests using coverage report."""
    mock_ctx.obj["local"] = True
    
    # Setup file reading to return specific content for existing tests and coverage
    def side_effect_read(encoding="utf-8"):
        return "content" # Simplified, usually we'd check self.name but Path is mocked
    
    # We need to mock Path instantiation inside the function to control read_text for specific files
    # However, since we patched Path.read_text globally, we can just rely on input_strings from construct_paths
    # or the manual read_text calls in the function.
    
    # The function manually reads existing tests and coverage report.
    # Let's mock read_text to return different things based on the instance, 
    # but since `read_text` is patched on the class, we use side_effect.
    mock_dependencies["read_text"].return_value = "FILE_CONTENT"

    mock_dependencies["increase_tests"].return_value = (MOCK_GENERATED_TEST, 0.02, "claude-3-local")

    code, cost, model = cmd_test_main(
        ctx=mock_ctx,
        prompt_file="prompt.txt",
        code_file="code.py",
        coverage_report="coverage.xml",
        existing_tests=["tests/existing.py"]
    )

    mock_dependencies["increase_tests"].assert_called_once()
    _, kwargs = mock_dependencies["increase_tests"].call_args
    assert kwargs["existing_unit_tests"] == "FILE_CONTENT" # From read_text
    assert kwargs["coverage_report"] == "FILE_CONTENT"
    
    assert code == MOCK_GENERATED_TEST

def test_cloud_execution_success(mock_ctx, mock_dependencies):
    """Test successful cloud execution."""
    mock_ctx.obj["local"] = False
    
    # Mock Env vars
    with patch.dict(os.environ, {"NEXT_PUBLIC_FIREBASE_API_KEY": "key", "GITHUB_CLIENT_ID": "id"}):
        # Mock JWT
        mock_dependencies["get_jwt_token"].return_value = "fake_token"
        
        # Mock Response
        mock_response = MagicMock()
        mock_response.json.return_value = {
            "generatedCode": MOCK_GENERATED_TEST,
            "totalCost": 0.05,
            "modelName": "gpt-4-cloud"
        }
        mock_response.raise_for_status.return_value = None
        mock_dependencies["post"].return_value = mock_response

        code, cost, model = cmd_test_main(
            ctx=mock_ctx,
            prompt_file="prompt.txt",
            code_file="code.py"
        )

        assert code == MOCK_GENERATED_TEST
        assert cost == 0.05
        assert model == "gpt-4-cloud"
        
        # Verify Payload
        mock_dependencies["post"].assert_called_once()
        _, kwargs = mock_dependencies["post"].call_args
        assert kwargs["json"]["promptContent"] == MOCK_PROMPT_CONTENT
        assert kwargs["headers"]["Authorization"] == "Bearer fake_token"

def test_cloud_execution_fallback_to_local(mock_ctx, mock_dependencies):
    """Test fallback to local execution when cloud fails."""
    mock_ctx.obj["local"] = False
    
    with patch.dict(os.environ, {"NEXT_PUBLIC_FIREBASE_API_KEY": "key"}):
        # Simulate Cloud Failure
        mock_dependencies["get_jwt_token"].side_effect = Exception("Auth Failed")
        
        # Setup Local Fallback
        mock_dependencies["generate_test"].return_value = (MOCK_GENERATED_TEST, 0.01, "fallback-local")

        code, cost, model = cmd_test_main(
            ctx=mock_ctx,
            prompt_file="prompt.txt",
            code_file="code.py"
        )

        # Verify Cloud attempted
        mock_dependencies["get_jwt_token"].assert_called()
        
        # Verify Local Fallback called
        mock_dependencies["generate_test"].assert_called()
        assert code == MOCK_GENERATED_TEST
        assert model == "fallback-local"

def test_output_merge_logic(mock_ctx, mock_dependencies):
    """Test that merge=True writes to the first existing test file."""
    mock_ctx.obj["local"] = True
    mock_dependencies["generate_test"].return_value = (MOCK_GENERATED_TEST, 0.0, "model")
    
    # We need to verify the path written to.
    # The function uses Path(existing_tests_list[0]).write_text(...)
    
    # Since we patched Path.write_text on the class, we can check the instance it was called on?
    # No, patch on class methods makes it hard to check 'self'.
    # Instead, we can check that construct_paths output was ignored for the write.
    
    # However, the code does: final_output_path = Path(existing_tests_list[0])
    # We can mock Path to track instantiation.
    
    with patch("pdd.cmd_test_main.Path") as MockPath:
        # Setup MockPath instances
        mock_path_instance = MagicMock()
        MockPath.return_value = mock_path_instance
        mock_path_instance.read_text.return_value = ""
        mock_path_instance.stem = "code"
        
        cmd_test_main(
            ctx=mock_ctx,
            prompt_file="prompt.txt",
            code_file="code.py",
            existing_tests=["tests/existing_1.py", "tests/existing_2.py"],
            merge=True
        )
        
        # Verify we instantiated Path with the first existing test
        # The code does Path(existing_tests_list[0]) inside the write block
        # It also does Path(et_path) for reading.
        
        # Let's verify write_text was called on an instance created with "tests/existing_1.py"
        # This is tricky with a global Path mock.
        # Alternative: Check logic flow.
        pass 

    # Re-run with standard dependencies to check behavior via side effects if possible, 
    # or just trust the logic if we can't easily mock Path constructor args in this setup.
    # Actually, let's look at the code:
    # if merge and existing_tests_list: final_output_path = Path(existing_tests_list[0])
    
    # We can verify this by ensuring construct_paths output is NOT used if merge is True.
    # construct_paths returns "tests/test_code.py".
    # existing_tests is "tests/existing_1.py".
    
    # We can use a spy on Path or just check that the file written matches expectation if we use real paths?
    # No, use mocks.
    
    # Let's use `wraps` on Path to see what it's called with.
    real_path = Path
    with patch("pdd.cmd_test_main.Path") as mock_path_cls:
        mock_instance = MagicMock()
        mock_path_cls.return_value = mock_instance
        mock_instance.read_text.return_value = ""
        mock_instance.stem = "code"
        
        cmd_test_main(
            ctx=mock_ctx,
            prompt_file="prompt.txt",
            code_file="code.py",
            existing_tests=["tests/existing_1.py"],
            merge=True
        )
        
        # Verify write_text called on the instance
        mock_instance.write_text.assert_called_with(MOCK_GENERATED_TEST, encoding="utf-8")
        
        # Verify Path was initialized with existing test path at some point
        # It is initialized multiple times.
        call_args_list = mock_path_cls.call_args_list
        # We expect one of the calls to be Path("tests/existing_1.py")
        assert any(call.args[0] == "tests/existing_1.py" for call in call_args_list)

def test_empty_generation_error(mock_ctx, mock_dependencies):
    """Test that empty generated code returns an error."""
    mock_ctx.obj["local"] = True
    mock_dependencies["generate_test"].return_value = ("", 0.0, "model")
    
    code, cost, model = cmd_test_main(
        ctx=mock_ctx,
        prompt_file="prompt.txt",
        code_file="code.py"
    )
    
    assert code == ""
    assert "Error: Empty output" in model

def test_exception_handling(mock_ctx, mock_dependencies):
    """Test general exception handling."""
    mock_dependencies["construct_paths"].side_effect = Exception("Path Error")
    
    code, cost, model = cmd_test_main(
        ctx=mock_ctx,
        prompt_file="prompt.txt",
        code_file="code.py"
    )
    
    assert code == ""
    assert "Error: Path Error" in model

def test_construct_paths_arguments(mock_ctx, mock_dependencies):
    """Verify arguments passed to construct_paths."""
    cmd_test_main(
        ctx=mock_ctx,
        prompt_file="p.txt",
        code_file="c.py",
        output="out.py",
        language="python",
        merge=True,
        target_coverage=95.0,
        existing_tests=["t.py"]
    )
    
    mock_dependencies["construct_paths"].assert_called_once()
    _, kwargs = mock_dependencies["construct_paths"].call_args
    
    assert kwargs["input_file_paths"]["prompt_file"] == "p.txt"
    assert kwargs["input_file_paths"]["code_file"] == "c.py"
    assert kwargs["input_file_paths"]["existing_tests"] == "t.py"
    
    assert kwargs["command_options"]["output"] == "out.py"
    assert kwargs["command_options"]["language"] == "python"
    assert kwargs["command_options"]["merge"] is True
    assert kwargs["command_options"]["target_coverage"] == 95.0

def test_resolve_effective_config_usage(mock_ctx, mock_dependencies):
    """Verify resolve_effective_config is called with correct overrides."""
    cmd_test_main(
        ctx=mock_ctx,
        prompt_file="p.txt",
        code_file="c.py",
        strength=0.9,
        temperature=0.7
    )

    mock_dependencies["resolve_effective_config"].assert_called_once()
    _, kwargs = mock_dependencies["resolve_effective_config"].call_args

    # Verify correct API: ctx, resolved_config, param_overrides
    assert kwargs["ctx"] == mock_ctx
    assert kwargs["resolved_config"] == {}  # Empty dict from mock_dependencies fixture
    assert kwargs["param_overrides"] == {"strength": 0.9, "temperature": 0.7}