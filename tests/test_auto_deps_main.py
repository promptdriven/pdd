"""Tests for the auto_deps_main function."""
import json
import os
import tempfile
import shutil
from pathlib import Path
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


@pytest.fixture(autouse=True)
def _isolate_metadata_finalization():
    """
    Prevent tests in this module from writing real fingerprint/run-report
    files into the repository's ``.pdd/meta`` directory. Tests that need to
    assert on these calls explicitly patch them at the test scope, which
    overrides this fixture's stubs for the duration of that test.
    """
    with patch("pdd.auto_deps_main.save_fingerprint"), \
         patch("pdd.auto_deps_main.clear_run_report"):
        yield


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


@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_sanitizes_invalid_prompt_includes_before_writing(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_path,
):
    """Auto-deps prompt output should not persist selectors that sync will warn on."""
    mock_ctx.obj["quiet"] = True
    (tmp_path / "context").mkdir()
    (tmp_path / "context" / "llm_invoke_example.py").write_text(
        "def run_llm_invoke_examples():\n    pass\n",
        encoding="utf-8",
    )
    output_path = tmp_path / "output.prompt"
    csv_path = tmp_path / "deps.csv"
    bad_prompt = (
        '<include select="class:TokenMatch,def:detect_control_token">'
        "context/llm_invoke_example.py</include>"
    )

    mock_construct_paths.return_value = _make_construct_paths_return(
        str(output_path),
        str(csv_path),
    )
    mock_insert_includes.return_value = _make_insert_includes_return(
        modified_prompt=bad_prompt,
    )

    modified_prompt, total_cost, model_name = auto_deps_main(
        ctx=mock_ctx,
        prompt_file="sample_prompt_python.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
    )

    saved = output_path.read_text(encoding="utf-8")
    assert "Invalid selector" in saved
    assert "class:TokenMatch" not in saved
    assert modified_prompt == saved
    assert total_cost == pytest.approx(0.123456)
    assert model_name == "test-model"


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
    monkeypatch,
):
    """When output_file_paths has no 'csv' key, default to 'project_dependencies.csv'."""
    # Run inside tmp_dir so the relative-default CSV write doesn't clobber the
    # repository's real ``project_dependencies.csv`` cache.
    monkeypatch.chdir(tmp_dir)
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


# ---------------------------------------------------------------------------
# 17. Wiring: auto_deps_main → merge into architecture.json
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_main_updates_architecture_json_after_write(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_path: Path,
) -> None:
    """End-to-end through auto_deps_main: written prompt triggers arch merge (real files)."""
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    child = prompts / "child_Python.prompt"
    parent = prompts / "parent_Python.prompt"
    child.write_text("%\n", encoding="utf-8")
    parent.write_text("%\n", encoding="utf-8")
    arch = [
        {"filename": "child_Python.prompt", "dependencies": []},
        {"filename": "parent_Python.prompt", "dependencies": []},
    ]
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch), encoding="utf-8")

    output_path = str(child.resolve())
    csv_path = str(tmp_path / "project_dependencies.csv")
    mock_construct_paths.return_value = _make_construct_paths_return(
        output_path, csv_path, prompt_content="%\n"
    )
    new_text = "%\n<include>parent_python.prompt</include>\n"
    mock_insert_includes.return_value = _make_insert_includes_return(
        modified_prompt=new_text,
        csv_output="",
        cost=0.01,
        model="test-model",
    )

    modified_prompt, total_cost, model_name = auto_deps_main(
        ctx=mock_ctx,
        prompt_file=str(child),
        directory_path=str(tmp_path),
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
    )

    assert modified_prompt == new_text
    data = json.loads(arch_path.read_text(encoding="utf-8"))
    row = next(e for e in data if e["filename"] == "child_Python.prompt")
    assert row["dependencies"] == ["parent_Python.prompt"]
    assert total_cost == 0.01
    assert model_name == "test-model"


# ---------------------------------------------------------------------------
# 18. Metadata finalization: identity is derived from the *original* prompt,
#     not the default ``*_with_deps.prompt`` output path.
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.save_fingerprint")
@patch("pdd.auto_deps_main.clear_run_report")
@patch("pdd.auto_deps_main.infer_module_identity")
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_metadata_uses_original_prompt_identity(
    mock_insert_includes,
    mock_construct_paths,
    mock_infer_identity,
    mock_clear_run_report,
    mock_save_fingerprint,
    mock_ctx,
    tmp_path: Path,
):
    """
    With the default output (``<basename>_<language>_with_deps.prompt``),
    identity must come from the original ``prompt_file`` so we get
    ``("child", "python")`` — not ``("child_python_with", "deps")``.
    """
    prompt_file = "prompts/child_python.prompt"
    output_path = str(tmp_path / "child_python_with_deps.prompt")
    csv_path = str(tmp_path / "deps.csv")

    mock_construct_paths.return_value = _make_construct_paths_return(
        output_path, csv_path
    )
    mock_insert_includes.return_value = _make_insert_includes_return()
    mock_infer_identity.return_value = ("child", "python")

    auto_deps_main(
        ctx=mock_ctx,
        prompt_file=prompt_file,
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
    )

    # Identity must be inferred from the *input* prompt, not the output.
    mock_infer_identity.assert_called_once_with(Path(prompt_file))

    # Stale per-module run report cleared with the canonical identity.
    mock_clear_run_report.assert_called_once_with("child", "python")

    # Fingerprint persisted with the canonical identity and the cleaned
    # output prompt path.
    mock_save_fingerprint.assert_called_once()
    fp_kwargs = mock_save_fingerprint.call_args.kwargs
    assert fp_kwargs["basename"] == "child"
    assert fp_kwargs["language"] == "python"
    assert fp_kwargs["operation"] == "auto-deps"
    assert fp_kwargs["paths"] == {"prompt": Path(output_path)}
    assert fp_kwargs["model"] == "test-model"
    assert fp_kwargs["cost"] == pytest.approx(0.123456)


# ---------------------------------------------------------------------------
# 19. Metadata finalization is skipped when identity cannot be inferred,
#     i.e. ``infer_module_identity`` returns ``(None, None)``.
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.save_fingerprint")
@patch("pdd.auto_deps_main.clear_run_report")
@patch("pdd.auto_deps_main.infer_module_identity")
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_metadata_skipped_on_unknown_identity(
    mock_insert_includes,
    mock_construct_paths,
    mock_infer_identity,
    mock_clear_run_report,
    mock_save_fingerprint,
    mock_ctx,
    tmp_path: Path,
):
    """
    ``infer_module_identity`` returns ``(None, None)`` (a tuple, not None)
    for unrecognized prompt names. The finalization block must handle that
    explicitly and skip both ``clear_run_report`` and ``save_fingerprint``
    rather than crash.
    """
    output_path = str(tmp_path / "out.prompt")
    csv_path = str(tmp_path / "deps.csv")

    mock_construct_paths.return_value = _make_construct_paths_return(
        output_path, csv_path
    )
    mock_insert_includes.return_value = _make_insert_includes_return()
    mock_infer_identity.return_value = (None, None)

    modified_prompt, total_cost, model_name = auto_deps_main(
        ctx=mock_ctx,
        prompt_file="weird_name_no_language.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
    )

    mock_clear_run_report.assert_not_called()
    mock_save_fingerprint.assert_not_called()
    # Auto-deps still returns its successful result.
    assert modified_prompt == "Modified prompt with includes"
    assert total_cost == pytest.approx(0.123456)
    assert model_name == "test-model"


# ---------------------------------------------------------------------------
# 20. Metadata finalization: clear_run_report failure must not abort the
#     subsequent fingerprint save.
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.save_fingerprint")
@patch("pdd.auto_deps_main.clear_run_report")
@patch("pdd.auto_deps_main.infer_module_identity")
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_clear_run_report_error_does_not_block_fingerprint(
    mock_insert_includes,
    mock_construct_paths,
    mock_infer_identity,
    mock_clear_run_report,
    mock_save_fingerprint,
    mock_ctx,
    tmp_path: Path,
):
    """If clearing the stale run report fails, the fingerprint must still be saved."""
    output_path = str(tmp_path / "child_python_with_deps.prompt")
    csv_path = str(tmp_path / "deps.csv")
    mock_construct_paths.return_value = _make_construct_paths_return(
        output_path, csv_path
    )
    mock_insert_includes.return_value = _make_insert_includes_return()
    mock_infer_identity.return_value = ("child", "python")
    mock_clear_run_report.side_effect = OSError("permission denied")

    auto_deps_main(
        ctx=mock_ctx,
        prompt_file="prompts/child_python.prompt",
        directory_path="context/",
        auto_deps_csv_path=None,
        output=None,
        force_scan=False,
    )

    mock_clear_run_report.assert_called_once_with("child", "python")
    mock_save_fingerprint.assert_called_once()
    fp_kwargs = mock_save_fingerprint.call_args.kwargs
    assert fp_kwargs["basename"] == "child"
    assert fp_kwargs["language"] == "python"
