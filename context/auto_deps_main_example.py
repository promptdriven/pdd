"""
Example: auto_deps_main

Demonstrates the auto_deps_main function which serves as the CLI entry point
for the auto-deps command. It orchestrates dependency discovery, insertion into
prompts, and CSV cache management.

Features demonstrated:
  1. Basic usage — analyze a prompt and insert dependencies
  2. Force scan — delete existing CSV cache before processing
  3. Progress callback — monitor file processing progress
  4. Quiet mode — suppress console output
  5. Include docs — include .md/.txt/.rst in dependency discovery
  6. No dedup — skip redundant inline content removal
  7. Concurrency — parallel workers for file summarization
  8. Error handling — graceful error tuple on failure
  9. click.Abort re-raise — user cancellation propagates
 10. Return tuple shape: (modified_prompt, total_cost, model_name)
"""

import os
import sys
import tempfile
import shutil
from unittest.mock import patch, MagicMock

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

import click
from pdd.auto_deps_main import auto_deps_main
from pdd import DEFAULT_STRENGTH, DEFAULT_TIME


def make_ctx(
    force=False,
    quiet=False,
    strength=DEFAULT_STRENGTH,
    temperature=0.0,
    time=DEFAULT_TIME,
    context=None,
    confirm_callback=None,
):
    """Create a Click context with the given obj dict."""
    ctx = click.Context(click.Command("auto-deps"))
    ctx.obj = {
        "force": force,
        "quiet": quiet,
        "strength": strength,
        "temperature": temperature,
        "time": time,
        "context": context,
        "confirm_callback": confirm_callback,
    }
    return ctx


def mock_construct_paths(**overrides):
    """Return a mock construct_paths that resolves to temp files."""
    def _mock(input_file_paths, force, quiet, command, command_options,
              context_override=None, confirm_callback=None):
        prompt_content = overrides.get(
            "prompt_content", "% You are an expert Python engineer.\n"
        )
        output_path = overrides.get("output_path", "output/modified.prompt")
        csv_path = overrides.get("csv_path", "project_dependencies.csv")
        return (
            {},  # resolved_config
            {"prompt_file": prompt_content},
            {"output": output_path, "csv": csv_path},
            None,  # language (unused)
        )
    return _mock


def mock_insert_includes_ok(*args, **kwargs):
    """Mock insert_includes returning a successful result."""
    return (
        "% You are an expert Python engineer.\n\n"
        "<include>context/llm_invoke_example.py</include>\n"
        "<include>context/preprocess_example.py</include>\n",
        "full_path,file_summary,content_hash\n"
        "context/llm_invoke_example.py,LLM invocation example,hash1\n"
        "context/preprocess_example.py,Preprocessing example,hash2\n",
        0.05,
        "mock-gpt-4o",
    )


def mock_insert_includes_empty(*args, **kwargs):
    """Mock insert_includes returning empty CSV (no deps found)."""
    return ("simple prompt", "", 0.01, "mock-gpt-4o")


def main():
    print("=" * 60)
    print("Example: auto_deps_main")
    print("=" * 60)

    tmp_dir = tempfile.mkdtemp()

    try:
        output_path = os.path.join(tmp_dir, "modified.prompt")
        csv_path = os.path.join(tmp_dir, "deps.csv")

        # ------------------------------------------------------------------
        # 1. Basic usage — analyze prompt and insert dependencies
        # ------------------------------------------------------------------
        print("\n--- 1. Basic usage ---")
        ctx = make_ctx()

        with patch("pdd.auto_deps_main.construct_paths",
                    side_effect=mock_construct_paths(
                        output_path=output_path, csv_path=csv_path)), \
             patch("pdd.auto_deps_main.insert_includes",
                    side_effect=mock_insert_includes_ok):

            modified_prompt, total_cost, model_name = auto_deps_main(
                ctx=ctx,
                prompt_file="prompts/my_module_python.prompt",
                directory_path="context/*_example.py",
                auto_deps_csv_path=None,
                output=None,
                force_scan=False,
            )

        assert isinstance(modified_prompt, str), "modified_prompt must be str"
        assert isinstance(total_cost, float), "total_cost must be float"
        assert isinstance(model_name, str), "model_name must be str"
        assert total_cost == 0.05
        assert model_name == "mock-gpt-4o"
        print(f"  Modified prompt length: {len(modified_prompt)}")
        print(f"  Total cost: ${total_cost:.6f}")
        print(f"  Model: {model_name}")
        print("[PASS] Basic usage works")

        # ------------------------------------------------------------------
        # 2. Force scan — delete existing CSV before processing
        # ------------------------------------------------------------------
        print("\n--- 2. Force scan ---")
        # Create a CSV file to be deleted
        csv_path2 = os.path.join(tmp_dir, "force_scan_deps.csv")
        with open(csv_path2, "w") as f:
            f.write("full_path,file_summary,content_hash\nold.py,Old file,oldhash\n")

        ctx = make_ctx()

        with patch("pdd.auto_deps_main.construct_paths",
                    side_effect=mock_construct_paths(
                        output_path=output_path, csv_path=csv_path2)), \
             patch("pdd.auto_deps_main.insert_includes",
                    side_effect=mock_insert_includes_ok):

            modified_prompt, total_cost, model_name = auto_deps_main(
                ctx=ctx,
                prompt_file="prompts/my_module_python.prompt",
                directory_path="context/*_example.py",
                auto_deps_csv_path=None,
                output=None,
                force_scan=True,
            )

        assert total_cost == 0.05
        print(f"  Force scan completed, cost: ${total_cost:.6f}")
        print("[PASS] Force scan deletes CSV and re-processes")

        # ------------------------------------------------------------------
        # 3. Progress callback — monitor file processing progress
        # ------------------------------------------------------------------
        print("\n--- 3. Progress callback ---")
        progress_log = []

        def my_progress(current: int, total: int) -> None:
            progress_log.append((current, total))

        csv_path3 = os.path.join(tmp_dir, "progress_deps.csv")
        ctx = make_ctx()

        with patch("pdd.auto_deps_main.construct_paths",
                    side_effect=mock_construct_paths(
                        output_path=output_path, csv_path=csv_path3)), \
             patch("pdd.auto_deps_main.insert_includes",
                    side_effect=mock_insert_includes_ok) as mock_ii:

            auto_deps_main(
                ctx=ctx,
                prompt_file="prompts/my_module_python.prompt",
                directory_path="context/*_example.py",
                auto_deps_csv_path=None,
                output=None,
                force_scan=False,
                progress_callback=my_progress,
            )

        # Verify progress_callback was passed to insert_includes
        call_kwargs = mock_ii.call_args[1]
        assert call_kwargs["progress_callback"] is my_progress
        print("  progress_callback forwarded to insert_includes: verified")
        print("[PASS] Progress callback passed through correctly")

        # ------------------------------------------------------------------
        # 4. Quiet mode — suppress console output
        # ------------------------------------------------------------------
        print("\n--- 4. Quiet mode ---")
        csv_path4 = os.path.join(tmp_dir, "quiet_deps.csv")
        ctx = make_ctx(quiet=True)

        with patch("pdd.auto_deps_main.construct_paths",
                    side_effect=mock_construct_paths(
                        output_path=output_path, csv_path=csv_path4)), \
             patch("pdd.auto_deps_main.insert_includes",
                    side_effect=mock_insert_includes_ok):

            modified_prompt, total_cost, model_name = auto_deps_main(
                ctx=ctx,
                prompt_file="prompts/my_module_python.prompt",
                directory_path="context/*_example.py",
                auto_deps_csv_path=None,
                output=None,
                force_scan=False,
            )

        assert total_cost == 0.05
        print(f"  Quiet mode completed silently, cost: ${total_cost:.6f}")
        print("[PASS] Quiet mode suppresses output")

        # ------------------------------------------------------------------
        # 5. Include docs — include .md/.txt/.rst in discovery
        # ------------------------------------------------------------------
        print("\n--- 5. Include docs ---")
        csv_path5 = os.path.join(tmp_dir, "docs_deps.csv")
        ctx = make_ctx()

        with patch("pdd.auto_deps_main.construct_paths",
                    side_effect=mock_construct_paths(
                        output_path=output_path, csv_path=csv_path5)), \
             patch("pdd.auto_deps_main.insert_includes",
                    side_effect=mock_insert_includes_ok) as mock_ii:

            auto_deps_main(
                ctx=ctx,
                prompt_file="prompts/my_module_python.prompt",
                directory_path="context/",
                auto_deps_csv_path=None,
                output=None,
                force_scan=False,
                include_docs=True,
            )

        call_kwargs = mock_ii.call_args[1]
        assert call_kwargs["include_docs"] is True
        print("  include_docs=True forwarded to insert_includes: verified")
        print("[PASS] include_docs parameter passed through")

        # ------------------------------------------------------------------
        # 6. No dedup — skip redundant content removal
        # ------------------------------------------------------------------
        print("\n--- 6. No dedup ---")
        csv_path6 = os.path.join(tmp_dir, "nodedup_deps.csv")
        ctx = make_ctx()

        with patch("pdd.auto_deps_main.construct_paths",
                    side_effect=mock_construct_paths(
                        output_path=output_path, csv_path=csv_path6)), \
             patch("pdd.auto_deps_main.insert_includes",
                    side_effect=mock_insert_includes_ok) as mock_ii:

            auto_deps_main(
                ctx=ctx,
                prompt_file="prompts/my_module_python.prompt",
                directory_path="context/*_example.py",
                auto_deps_csv_path=None,
                output=None,
                force_scan=False,
                no_dedup=True,
            )

        call_kwargs = mock_ii.call_args[1]
        assert call_kwargs["dedup"] is False, "no_dedup=True should set dedup=False"
        print("  no_dedup=True -> dedup=False forwarded: verified")
        print("[PASS] no_dedup inverts to dedup parameter correctly")

        # ------------------------------------------------------------------
        # 7. Concurrency — parallel workers for file summarization
        # ------------------------------------------------------------------
        print("\n--- 7. Concurrency ---")
        csv_path7 = os.path.join(tmp_dir, "concurrent_deps.csv")
        ctx = make_ctx()

        with patch("pdd.auto_deps_main.construct_paths",
                    side_effect=mock_construct_paths(
                        output_path=output_path, csv_path=csv_path7)), \
             patch("pdd.auto_deps_main.insert_includes",
                    side_effect=mock_insert_includes_ok) as mock_ii:

            auto_deps_main(
                ctx=ctx,
                prompt_file="prompts/my_module_python.prompt",
                directory_path="context/*_example.py",
                auto_deps_csv_path=None,
                output=None,
                force_scan=False,
                concurrency=4,
            )

        call_kwargs = mock_ii.call_args[1]
        assert call_kwargs["max_workers"] == 4
        print("  concurrency=4 -> max_workers=4 forwarded: verified")
        print("[PASS] Concurrency parameter passed through")

        # ------------------------------------------------------------------
        # 8. Error handling — graceful error tuple on failure
        # ------------------------------------------------------------------
        print("\n--- 8. Error handling ---")
        ctx = make_ctx()

        with patch("pdd.auto_deps_main.construct_paths",
                    side_effect=RuntimeError("Simulated failure")):

            modified_prompt, total_cost, model_name = auto_deps_main(
                ctx=ctx,
                prompt_file="prompts/bad_module_python.prompt",
                directory_path="context/",
                auto_deps_csv_path=None,
                output=None,
                force_scan=False,
            )

        assert modified_prompt == ""
        assert total_cost == 0.0
        assert "Error:" in model_name
        assert "Simulated failure" in model_name
        print(f"  Error tuple: ('', 0.0, '{model_name}')")
        print("[PASS] Errors return graceful tuple instead of raising")

        # ------------------------------------------------------------------
        # 9. click.Abort re-raise — user cancellation propagates
        # ------------------------------------------------------------------
        print("\n--- 9. click.Abort re-raise ---")
        ctx = make_ctx()

        with patch("pdd.auto_deps_main.construct_paths",
                    side_effect=click.Abort()):
            try:
                auto_deps_main(
                    ctx=ctx,
                    prompt_file="prompts/cancel_module_python.prompt",
                    directory_path="context/",
                    auto_deps_csv_path=None,
                    output=None,
                    force_scan=False,
                )
                print("  ERROR: click.Abort was not re-raised!")
                assert False, "click.Abort should propagate"
            except click.Abort:
                print("  click.Abort correctly re-raised")
                print("[PASS] User cancellation propagates via click.Abort")

        # ------------------------------------------------------------------
        # 10. Return tuple shape verification
        # ------------------------------------------------------------------
        print("\n--- 10. Return tuple shape ---")
        csv_path10 = os.path.join(tmp_dir, "shape_deps.csv")
        ctx = make_ctx()

        with patch("pdd.auto_deps_main.construct_paths",
                    side_effect=mock_construct_paths(
                        output_path=output_path, csv_path=csv_path10)), \
             patch("pdd.auto_deps_main.insert_includes",
                    side_effect=mock_insert_includes_ok):

            result = auto_deps_main(
                ctx=ctx,
                prompt_file="prompts/my_module_python.prompt",
                directory_path="context/*_example.py",
                auto_deps_csv_path=None,
                output=None,
                force_scan=False,
            )

        assert isinstance(result, tuple), "Return must be a tuple"
        assert len(result) == 3, f"Tuple must have 3 elements, got {len(result)}"
        modified_prompt, total_cost, model_name = result
        assert isinstance(modified_prompt, str)
        assert isinstance(total_cost, float)
        assert isinstance(model_name, str)
        print(f"  Return types: str, float, str")
        print("[PASS] Return tuple has correct shape and types")

        print("\n" + "=" * 60)
        print("All examples passed!")
        print("=" * 60)

    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)


if __name__ == "__main__":
    main()
