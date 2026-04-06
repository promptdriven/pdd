"""Tests for the auto_deps_main function."""
import os
import tempfile
import shutil
from unittest.mock import patch, MagicMock, call
import pytest
import click

from pdd import DEFAULT_STRENGTH, DEFAULT_TIME
from pdd.auto_deps_main import auto_deps_main


@pytest.fixture
def mock_ctx():
    """Provide a Click context with default obj dict."""
    ctx = click.Context(click.Command("auto-deps"))
    ctx.obj = {
        "force": False,
        "quiet": False,
        "strength": DEFAULT_STRENGTH,
        "temperature": 0,
        "time": DEFAULT_TIME,
    }
    return ctx


@pytest.fixture
def tmp_dir():
    """Provide a temporary directory, cleaned up after test."""
    d = tempfile.mkdtemp()
    yield d
    shutil.rmtree(d, ignore_errors=True)


def _make_construct_paths_return(output_path, csv_path, prompt_content="Prompt content"):
    """Build a standard construct_paths return value."""
    return (
        {},  # resolved_config
        {"prompt_file": prompt_content},
        {"output": output_path, "csv": csv_path},
        None,  # language (unused)
    )


def _make_insert_includes_return(
    modified_prompt="Modified prompt with includes",
    csv_output="full_path,file_summary,content_hash\nfoo.py,Foo,hash1\n",
    cost=0.123456,
    model="test-model",
):
    """Build a standard insert_includes return value."""
    return (modified_prompt, csv_output, cost, model)


# ---------------------------------------------------------------------------
# 1. Normal operation
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("csv_path_return", [None, "custom_deps.csv"])
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_normal_operation(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_dir,
    csv_path_return,
):
    """Test basic operation: construct_paths → insert_includes → write files → return."""
    output_path = os.path.join(tmp_dir, "output.prompt")
    csv_path = os.path.join(tmp_dir, csv_path_return or "project_dependencies.csv")

    mock_construct_paths.return_value = _make_construct_paths_return(output_path, csv_path)
    mock_insert_includes.return_value = _make_insert_includes_return()

    modified_prompt, total_cost, model_name = auto_deps_main(
        ctx=mock_ctx,
        prompt_file="sample_prompt_python.prompt",
        directory_path="context/",
        auto_deps_csv_path=csv_path_return,
        output=None,
        force_scan=False,
    )

    # Verify construct_paths was called
    mock_construct_paths.assert_called_once()
    cp_kwargs = mock_construct_paths.call_args
    assert cp_kwargs[1]["command"] == "auto-deps"

    # Verify insert_includes was called with all expected params
    mock_insert_includes.assert_called_once_with(
        input_prompt="Prompt content",
        directory_path="context/",
        csv_filename=csv_path,
        prompt_filename="sample_prompt_python.prompt",
        strength=mock_ctx.obj["strength"],
        temperature=mock_ctx.obj["temperature"],
        time=mock_ctx.obj["time"],
        verbose=True,
        progress_callback=None,
        include_docs=False,
        dedup=True,
        max_workers=1,
    )

    assert modified_prompt == "Modified prompt with includes"
    assert total_cost == 0.123456
    assert model_name == "test-model"

    # Output files should have been written
    assert os.path.exists(output_path)
    assert os.path.exists(csv_path)


# ---------------------------------------------------------------------------
# 2. Force scan deletes CSV
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_force_scan_operation(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_dir,
):
    """When force_scan=True and CSV exists, it should be deleted before processing."""
    output_path = os.path.join(tmp_dir, "output.prompt")
    csv_path = os.path.join(tmp_dir, "forced_scan_deps.csv")

    # Create an existing CSV
    with open(csv_path, "w") as f:
        f.write("full_path,file_summary,content_hash\nold.py,Old,oldhash\n")

    mock_construct_paths.return_value = _make_construct_paths_return(output_path, csv_path)
    mock_insert_includes.return_value = _make_insert_includes_return()

    modified_prompt, total_cost, model_name = auto_deps_main(
        ctx=mock_ctx,
        prompt_file="another_prompt_python.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output="output/here",
        force_scan=True,
    )

    # CSV should have been replaced (old content gone, new content written)
    assert os.path.exists(csv_path)
    with open(csv_path) as f:
        content = f.read()
    # The new CSV content from insert_includes should be there
    assert "foo.py" in content

    assert modified_prompt == "Modified prompt with includes"
    assert total_cost == 0.123456
    assert model_name == "test-model"


# ---------------------------------------------------------------------------
# 3. Error handling returns tuple
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
def test_auto_deps_handles_error_scenario(
    mock_construct_paths,
    mock_ctx,
):
    """Errors should return ('', 0.0, 'Error: {exc}') instead of raising."""
    mock_construct_paths.side_effect = Exception("Test exception")

    modified_prompt, total_cost, model_name = auto_deps_main(
        ctx=mock_ctx,
        prompt_file="bad_prompt_file.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
    )

    assert modified_prompt == ""
    assert total_cost == 0.0
    assert "Error:" in model_name
    assert "Test exception" in model_name


# ---------------------------------------------------------------------------
# 4. click.Abort re-raised
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
def test_auto_deps_reraises_click_abort(
    mock_construct_paths,
    mock_ctx,
):
    """click.Abort should propagate so the orchestrator can stop the sync loop."""
    mock_construct_paths.side_effect = click.Abort()

    with pytest.raises(click.Abort):
        auto_deps_main(
            ctx=mock_ctx,
            prompt_file="cancelled_prompt.prompt",
            directory_path="context/",
            auto_deps_csv_path=None,
            output=None,
            force_scan=False,
        )


# ---------------------------------------------------------------------------
# 5. Progress callback forwarding
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_progress_callback_forwarded(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_dir,
):
    """progress_callback should be forwarded to insert_includes."""
    output_path = os.path.join(tmp_dir, "output.prompt")
    csv_path = os.path.join(tmp_dir, "deps.csv")
    mock_construct_paths.return_value = _make_construct_paths_return(output_path, csv_path)
    mock_insert_includes.return_value = _make_insert_includes_return()

    def my_callback(current, total):
        pass

    auto_deps_main(
        ctx=mock_ctx,
        prompt_file="prompt.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
        progress_callback=my_callback,
    )

    call_kwargs = mock_insert_includes.call_args[1]
    assert call_kwargs["progress_callback"] is my_callback


# ---------------------------------------------------------------------------
# 6. include_docs forwarding
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_include_docs_forwarded(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_dir,
):
    """include_docs should be passed through to insert_includes."""
    output_path = os.path.join(tmp_dir, "output.prompt")
    csv_path = os.path.join(tmp_dir, "deps.csv")
    mock_construct_paths.return_value = _make_construct_paths_return(output_path, csv_path)
    mock_insert_includes.return_value = _make_insert_includes_return()

    auto_deps_main(
        ctx=mock_ctx,
        prompt_file="prompt.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
        include_docs=True,
    )

    call_kwargs = mock_insert_includes.call_args[1]
    assert call_kwargs["include_docs"] is True


# ---------------------------------------------------------------------------
# 7. no_dedup inverts to dedup
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_no_dedup_inverts(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_dir,
):
    """no_dedup=True should pass dedup=False to insert_includes."""
    output_path = os.path.join(tmp_dir, "output.prompt")
    csv_path = os.path.join(tmp_dir, "deps.csv")
    mock_construct_paths.return_value = _make_construct_paths_return(output_path, csv_path)
    mock_insert_includes.return_value = _make_insert_includes_return()

    auto_deps_main(
        ctx=mock_ctx,
        prompt_file="prompt.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
        no_dedup=True,
    )

    call_kwargs = mock_insert_includes.call_args[1]
    assert call_kwargs["dedup"] is False


# ---------------------------------------------------------------------------
# 8. concurrency forwarded as max_workers
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_concurrency_forwarded(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_dir,
):
    """concurrency param should map to max_workers in insert_includes."""
    output_path = os.path.join(tmp_dir, "output.prompt")
    csv_path = os.path.join(tmp_dir, "deps.csv")
    mock_construct_paths.return_value = _make_construct_paths_return(output_path, csv_path)
    mock_insert_includes.return_value = _make_insert_includes_return()

    auto_deps_main(
        ctx=mock_ctx,
        prompt_file="prompt.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
        concurrency=8,
    )

    call_kwargs = mock_insert_includes.call_args[1]
    assert call_kwargs["max_workers"] == 8


# ---------------------------------------------------------------------------
# 9. Quiet mode sets verbose=False
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_quiet_mode(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_dir,
):
    """When quiet=True, verbose should be False in insert_includes."""
    mock_ctx.obj["quiet"] = True
    output_path = os.path.join(tmp_dir, "output.prompt")
    csv_path = os.path.join(tmp_dir, "deps.csv")
    mock_construct_paths.return_value = _make_construct_paths_return(output_path, csv_path)
    mock_insert_includes.return_value = _make_insert_includes_return()

    auto_deps_main(
        ctx=mock_ctx,
        prompt_file="prompt.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
    )

    call_kwargs = mock_insert_includes.call_args[1]
    assert call_kwargs["verbose"] is False


# ---------------------------------------------------------------------------
# 10. Empty csv_output is not written to file
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_empty_csv_not_written(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_dir,
):
    """When csv_output is empty, CSV file should not be written."""
    output_path = os.path.join(tmp_dir, "output.prompt")
    csv_path = os.path.join(tmp_dir, "deps.csv")
    mock_construct_paths.return_value = _make_construct_paths_return(output_path, csv_path)
    mock_insert_includes.return_value = _make_insert_includes_return(csv_output="")

    auto_deps_main(
        ctx=mock_ctx,
        prompt_file="prompt.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
    )

    # Output prompt should exist but CSV should not (empty csv_output)
    assert os.path.exists(output_path)
    assert not os.path.exists(csv_path)


# ---------------------------------------------------------------------------
# 11. construct_paths receives correct arguments
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_construct_paths_args(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_dir,
):
    """Verify construct_paths is called with the right input_file_paths, command, etc."""
    mock_ctx.obj["force"] = True
    mock_ctx.obj["context"] = "backend"
    callback = lambda msg: True
    mock_ctx.obj["confirm_callback"] = callback

    output_path = os.path.join(tmp_dir, "output.prompt")
    csv_path = os.path.join(tmp_dir, "deps.csv")
    mock_construct_paths.return_value = _make_construct_paths_return(output_path, csv_path)
    mock_insert_includes.return_value = _make_insert_includes_return()

    auto_deps_main(
        ctx=mock_ctx,
        prompt_file="prompts/my_module_python.prompt",
        directory_path="context/",
        auto_deps_csv_path="my_deps.csv",
        output="output/modified.prompt",
        force_scan=False,
    )

    mock_construct_paths.assert_called_once_with(
        input_file_paths={"prompt_file": "prompts/my_module_python.prompt"},
        force=True,
        quiet=False,
        command="auto-deps",
        command_options={"output": "output/modified.prompt", "csv": "my_deps.csv"},
        context_override="backend",
        confirm_callback=callback,
    )


# ---------------------------------------------------------------------------
# 12. Default csv_path fallback
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_default_csv_path_fallback(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_dir,
):
    """When output_file_paths has no 'csv' key, default to 'project_dependencies.csv'."""
    output_path = os.path.join(tmp_dir, "output.prompt")
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "Prompt content"},
        {"output": output_path},  # No "csv" key
        None,
    )
    mock_insert_includes.return_value = _make_insert_includes_return()

    auto_deps_main(
        ctx=mock_ctx,
        prompt_file="prompt.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
    )

    call_kwargs = mock_insert_includes.call_args[1]
    assert call_kwargs["csv_filename"] == "project_dependencies.csv"


# ---------------------------------------------------------------------------
# 13. LLM parameters from context with defaults
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_llm_params_from_context(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_dir,
):
    """Verify strength, temperature, time are read from ctx.obj."""
    mock_ctx.obj["strength"] = 0.7
    mock_ctx.obj["temperature"] = 0.3
    mock_ctx.obj["time"] = 0.5

    output_path = os.path.join(tmp_dir, "output.prompt")
    csv_path = os.path.join(tmp_dir, "deps.csv")
    mock_construct_paths.return_value = _make_construct_paths_return(output_path, csv_path)
    mock_insert_includes.return_value = _make_insert_includes_return()

    auto_deps_main(
        ctx=mock_ctx,
        prompt_file="prompt.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
    )

    call_kwargs = mock_insert_includes.call_args[1]
    assert call_kwargs["strength"] == 0.7
    assert call_kwargs["temperature"] == 0.3
    assert call_kwargs["time"] == 0.5


# ---------------------------------------------------------------------------
# 14. Return tuple shape
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_return_tuple_shape(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_dir,
):
    """Return value must be a 3-tuple of (str, float, str)."""
    output_path = os.path.join(tmp_dir, "output.prompt")
    csv_path = os.path.join(tmp_dir, "deps.csv")
    mock_construct_paths.return_value = _make_construct_paths_return(output_path, csv_path)
    mock_insert_includes.return_value = _make_insert_includes_return()

    result = auto_deps_main(
        ctx=mock_ctx,
        prompt_file="prompt.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
    )

    assert isinstance(result, tuple)
    assert len(result) == 3
    modified_prompt, total_cost, model_name = result
    assert isinstance(modified_prompt, str)
    assert isinstance(total_cost, float)
    assert isinstance(model_name, str)


# ---------------------------------------------------------------------------
# 15. Force scan with nonexistent CSV does not error
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_force_scan_no_existing_csv(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_dir,
):
    """force_scan=True when CSV does not exist should not raise."""
    output_path = os.path.join(tmp_dir, "output.prompt")
    csv_path = os.path.join(tmp_dir, "nonexistent.csv")
    mock_construct_paths.return_value = _make_construct_paths_return(output_path, csv_path)
    mock_insert_includes.return_value = _make_insert_includes_return()

    modified_prompt, total_cost, model_name = auto_deps_main(
        ctx=mock_ctx,
        prompt_file="prompt.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=True,
    )

    assert modified_prompt == "Modified prompt with includes"
    assert total_cost == 0.123456


# ---------------------------------------------------------------------------
# 16. File lock is used (csv_path.lock)
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_uses_file_lock(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_dir,
):
    """The function should acquire a file lock using {csv_path}.lock."""
    output_path = os.path.join(tmp_dir, "output.prompt")
    csv_path = os.path.join(tmp_dir, "deps.csv")
    mock_construct_paths.return_value = _make_construct_paths_return(output_path, csv_path)
    mock_insert_includes.return_value = _make_insert_includes_return()

    with patch("filelock.FileLock") as mock_filelock_cls:
        mock_lock = MagicMock()
        mock_filelock_cls.return_value = mock_lock

        auto_deps_main(
            ctx=mock_ctx,
            prompt_file="prompt.prompt",
            directory_path="context/",
            auto_deps_csv_path=None,
            output=None,
            force_scan=False,
        )

        mock_filelock_cls.assert_called_once_with(f"{csv_path}.lock")
        mock_lock.__enter__.assert_called_once()
