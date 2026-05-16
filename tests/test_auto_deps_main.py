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
def _isolate_metadata_finalization(request):
    """
    Prevent tests in this module from writing real fingerprint/run-report
    files into the repository's ``.pdd/meta`` directory. Tests that need to
    assert on these calls explicitly patch them at the test scope, which
    overrides this fixture's stubs for the duration of that test.

    A test that needs to exercise the *real* ``save_fingerprint`` and
    ``clear_run_report`` helpers (e.g. an integration-style readback of the
    on-disk fingerprint JSON) opts out by requesting the
    ``use_real_finalization`` fixture, which redirects ``META_DIR`` to a
    temp location.
    """
    if "use_real_finalization" in request.fixturenames:
        yield
        return
    with patch("pdd.auto_deps_main.save_fingerprint"), \
         patch("pdd.auto_deps_main.clear_run_report"):
        yield


@pytest.fixture
def use_real_finalization(tmp_path, monkeypatch):
    """
    Opt-in fixture for tests that want to exercise the *real* metadata
    finalization helpers. Redirects ``pdd.operation_log.META_DIR`` to a
    temporary directory so the repository's ``.pdd/meta`` is never touched,
    and signals the autouse fixture to skip its protective mocks.

    Yields the temp META_DIR as a ``Path``.
    """
    meta_dir = tmp_path / ".pdd" / "meta"
    meta_dir.mkdir(parents=True, exist_ok=True)
    monkeypatch.setattr("pdd.operation_log.META_DIR", str(meta_dir))
    yield meta_dir


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
# 18a. Metadata finalization: when the default output is a separate
#      ``*_with_deps.prompt`` file, the canonical prompt is untouched and
#      finalization must be SKIPPED — otherwise ``.pdd/meta/<module>.json``
#      would record the hash of a non-canonical file under the canonical
#      module identity.
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.save_fingerprint")
@patch("pdd.auto_deps_main.clear_run_report")
@patch("pdd.auto_deps_main.infer_module_identity")
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_metadata_skipped_when_output_differs_from_prompt(
    mock_insert_includes,
    mock_construct_paths,
    mock_infer_identity,
    mock_clear_run_report,
    mock_save_fingerprint,
    mock_ctx,
    tmp_path: Path,
):
    """
    Default CLI auto-deps writes to ``<basename>_<language>_with_deps.prompt``.
    The original canonical prompt is unchanged, so neither the fingerprint
    nor the run report must be touched.
    """
    prompt_file = str(tmp_path / "child_python.prompt")
    output_path = str(tmp_path / "child_python_with_deps.prompt")
    csv_path = str(tmp_path / "deps.csv")
    Path(prompt_file).write_text("orig", encoding="utf-8")

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

    # Output is a different file than the input prompt → finalization is
    # skipped entirely; identity inference is also unnecessary.
    mock_infer_identity.assert_not_called()
    mock_clear_run_report.assert_not_called()
    mock_save_fingerprint.assert_not_called()


# ---------------------------------------------------------------------------
# 18b. Metadata finalization: when the output path resolves to the *same*
#      file as the input prompt (the in-place ``pdd sync`` write-back case),
#      identity must come from the original ``prompt_file`` and both
#      ``clear_run_report`` and ``save_fingerprint`` must run with the
#      canonical identity and the output path.
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.save_fingerprint")
@patch("pdd.auto_deps_main.clear_run_report")
@patch("pdd.auto_deps_main.infer_module_identity")
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_metadata_uses_original_prompt_identity_inplace(
    mock_insert_includes,
    mock_construct_paths,
    mock_infer_identity,
    mock_clear_run_report,
    mock_save_fingerprint,
    mock_ctx,
    tmp_path: Path,
):
    """
    In-place overwrite (``output == prompt_file``): identity is inferred
    from the original prompt and the fingerprint is saved with that
    canonical identity.
    """
    prompt_file = str(tmp_path / "child_python.prompt")
    Path(prompt_file).write_text("orig", encoding="utf-8")
    output_path = prompt_file  # in-place overwrite (sync mode)
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
    # output prompt path (which equals the original prompt in this case).
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
    rather than crash. Use an in-place overwrite so finalization is actually
    attempted (otherwise the differing-output guard would short-circuit it).
    """
    prompt_file = str(tmp_path / "weird_name_no_language.prompt")
    Path(prompt_file).write_text("orig", encoding="utf-8")
    output_path = prompt_file  # in-place overwrite
    csv_path = str(tmp_path / "deps.csv")

    mock_construct_paths.return_value = _make_construct_paths_return(
        output_path, csv_path
    )
    mock_insert_includes.return_value = _make_insert_includes_return()
    mock_infer_identity.return_value = (None, None)

    modified_prompt, total_cost, model_name = auto_deps_main(
        ctx=mock_ctx,
        prompt_file=prompt_file,
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
    """If clearing the stale run report fails, the fingerprint must still be saved.

    Uses an in-place overwrite (``output == prompt_file``) so finalization
    is actually attempted — the differing-output guard would otherwise skip
    both calls regardless of ``clear_run_report``'s behavior.
    """
    prompt_file = str(tmp_path / "child_python.prompt")
    Path(prompt_file).write_text("orig", encoding="utf-8")
    output_path = prompt_file  # in-place overwrite
    csv_path = str(tmp_path / "deps.csv")
    mock_construct_paths.return_value = _make_construct_paths_return(
        output_path, csv_path
    )
    mock_insert_includes.return_value = _make_insert_includes_return()
    mock_infer_identity.return_value = ("child", "python")
    mock_clear_run_report.side_effect = OSError("permission denied")

    auto_deps_main(
        ctx=mock_ctx,
        prompt_file=prompt_file,
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


# ---------------------------------------------------------------------------
# 21. Integration: with the REAL ``save_fingerprint``/``clear_run_report``
#     helpers (autouse mocks bypassed via ``use_real_finalization``), an
#     in-place ``auto-deps`` run on a prompt containing ``<include>`` must
#     produce a fingerprint JSON on disk whose ``include_deps`` reflects
#     the included file *and* must remove any pre-existing ``_run.json``.
#     This verifies the end-to-end on-disk contract instead of merely
#     proving the helper was called.
# ---------------------------------------------------------------------------
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_finalization_writes_include_deps_and_clears_run_report(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_path: Path,
    monkeypatch,
    use_real_finalization,
):
    meta_dir = use_real_finalization

    # Resolve tmp_path so symlinked /tmp prefixes (e.g. /var → /private/var on
    # macOS) don't break the cwd-relative include path computed by
    # ``extract_include_deps``.
    work_dir = tmp_path.resolve()
    monkeypatch.chdir(work_dir)

    # Original prompt with naming that yields identity ("child", "python").
    prompt_file = work_dir / "child_python.prompt"
    prompt_file.write_text("original prompt body\n", encoding="utf-8")

    # Real dependency file referenced by an ``<include>`` directive in the
    # modified prompt below. ``extract_include_deps`` resolves the reference
    # against the prompt's directory and hashes the file's contents.
    dep_file = work_dir / "parent.py"
    dep_file.write_text("# parent helper\n", encoding="utf-8")

    modified_prompt = (
        "original prompt body\n<include>parent.py</include>\n"
    )
    csv_path = work_dir / "deps.csv"

    mock_construct_paths.return_value = (
        {},
        {"prompt_file": prompt_file.read_text(encoding="utf-8")},
        # In-place overwrite (``pdd sync`` write-back semantics) so the
        # finalization branch actually runs.
        {"output": str(prompt_file), "csv": str(csv_path)},
        None,
    )
    mock_insert_includes.return_value = (
        modified_prompt,
        "",      # no CSV output
        0.01,    # cost
        "test-model",
    )

    # Pre-existing stale run report that finalization must remove.
    run_report = meta_dir / "child_python_run.json"
    run_report.write_text(json.dumps({"stale": True}), encoding="utf-8")
    assert run_report.exists()

    returned_prompt, total_cost, model_name = auto_deps_main(
        ctx=mock_ctx,
        prompt_file=str(prompt_file),
        directory_path=str(work_dir),
        auto_deps_csv_path=str(csv_path),
        output=str(prompt_file),  # explicit in-place overwrite
        force_scan=False,
    )

    assert returned_prompt == modified_prompt
    assert total_cost == 0.01
    assert model_name == "test-model"

    # Fingerprint JSON was actually written to disk under the canonical
    # ``<basename>_<language>.json`` identity.
    fingerprint_path = meta_dir / "child_python.json"
    assert fingerprint_path.exists(), (
        f"fingerprint JSON missing at {fingerprint_path}"
    )
    fp = json.loads(fingerprint_path.read_text(encoding="utf-8"))

    assert fp["command"] == "auto-deps"
    assert fp["prompt_hash"], "prompt_hash should be populated"

    # ``include_deps`` must reflect the real ``<include>`` dependency on
    # ``parent.py``: a non-empty mapping keyed by the cwd-relative path with
    # a 64-char SHA-256 hex hash as the value.
    include_deps = fp.get("include_deps")
    assert isinstance(include_deps, dict) and include_deps, (
        f"include_deps should be a non-empty dict, got {include_deps!r}"
    )
    assert "parent.py" in include_deps, (
        f"expected 'parent.py' key in include_deps, got {list(include_deps)}"
    )
    assert len(include_deps["parent.py"]) == 64, (
        "include_deps hash should be a SHA-256 hex digest"
    )

    # The stale per-module run report must have been cleared.
    assert not run_report.exists(), (
        "_run.json should have been removed by clear_run_report"
    )


# ---------------------------------------------------------------------------
# Regression: auto_include emits attributed ``<include select="...">`` and
# ``<include query="...">`` directives (pdd/auto_include.py:148). The
# finalization path persists include dep hashes via ``save_fingerprint``,
# which reads them through ``extract_include_deps``. If that extractor only
# matched bare ``<include>...</include>``, attributed deps would silently
# vanish from the fingerprint and downstream sync would miss real changes.
# ---------------------------------------------------------------------------
@pytest.mark.parametrize(
    "include_directive",
    [
        '<include select="def:parent_helper">parent.py</include>',
        '<include query="parent module helpers">parent.py</include>',
    ],
    ids=["select-attr", "query-attr"],
)
@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_finalization_captures_attributed_include_deps(
    mock_insert_includes,
    mock_construct_paths,
    mock_ctx,
    tmp_path: Path,
    monkeypatch,
    use_real_finalization,
    include_directive,
):
    meta_dir = use_real_finalization
    work_dir = tmp_path.resolve()
    monkeypatch.chdir(work_dir)

    prompt_file = work_dir / "child_python.prompt"
    prompt_file.write_text("original prompt body\n", encoding="utf-8")

    # ``parent.py`` must define ``parent_helper`` so the
    # ``select="def:parent_helper"`` variant's selector validator (run by
    # ``sanitize_prompt_output``) resolves successfully and the attributed
    # include survives to reach ``extract_include_deps``.
    dep_file = work_dir / "parent.py"
    dep_file.write_text("def parent_helper():\n    return 1\n", encoding="utf-8")

    modified_prompt = f"original prompt body\n{include_directive}\n"
    csv_path = work_dir / "deps.csv"

    mock_construct_paths.return_value = (
        {},
        {"prompt_file": prompt_file.read_text(encoding="utf-8")},
        {"output": str(prompt_file), "csv": str(csv_path)},
        None,
    )
    mock_insert_includes.return_value = (
        modified_prompt,
        "",
        0.01,
        "test-model",
    )

    auto_deps_main(
        ctx=mock_ctx,
        prompt_file=str(prompt_file),
        directory_path=str(work_dir),
        auto_deps_csv_path=str(csv_path),
        output=str(prompt_file),
        force_scan=False,
    )

    fingerprint_path = meta_dir / "child_python.json"
    assert fingerprint_path.exists(), (
        f"fingerprint JSON missing at {fingerprint_path}"
    )
    fp = json.loads(fingerprint_path.read_text(encoding="utf-8"))

    include_deps = fp.get("include_deps")
    assert isinstance(include_deps, dict) and include_deps, (
        f"include_deps should capture attributed includes, got {include_deps!r}"
    )
    assert "parent.py" in include_deps, (
        f"expected 'parent.py' key in include_deps, got {list(include_deps)}"
    )
    assert len(include_deps["parent.py"]) == 64, (
        "include_deps hash should be a SHA-256 hex digest"
    )
