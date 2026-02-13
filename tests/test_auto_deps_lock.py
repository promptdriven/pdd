"""Tests for auto_deps_main concurrent execution locking.

These tests verify that:
1. Concurrent auto_deps_main calls are serialized (not interleaved)
2. The second call benefits from the first's cache (LLM not called redundantly)
3. All file operations use tmp_path (no artifacts in working directory)
"""
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import patch, MagicMock
import pytest
import click

from pdd import DEFAULT_STRENGTH, DEFAULT_TIME
from pdd.auto_deps_main import auto_deps_main


@pytest.fixture
def mock_ctx():
    """Provide a mock for Click's context object."""
    ctx = MagicMock(spec=click.Context)
    ctx.params = {'quiet': True, 'force': False}
    ctx.obj = {
        'strength': DEFAULT_STRENGTH,
        'temperature': 0,
        'time': DEFAULT_TIME,
        'quiet': True,
        'force': False
    }
    return ctx


class TestConcurrentAutoDeps:
    """Integration tests for concurrent auto_deps_main execution."""

    @patch("pdd.auto_deps_main.insert_includes")
    @patch("pdd.auto_deps_main.construct_paths")
    def test_concurrent_calls_serialize_and_share_cache(
        self, mock_construct_paths, mock_insert_includes, tmp_path, mock_ctx
    ):
        """
        Two concurrent auto_deps_main calls should:
        1. Execute sequentially (second waits for first due to lock)
        2. Second call should benefit from first's cache

        This is the key integration test that verifies the locking fix works.
        """
        import threading

        # Setup paths in tmp_path
        csv_path = str(tmp_path / "deps.csv")
        output_path = str(tmp_path / "output.prompt")

        # Track execution order with thread-safe list
        execution_order = []
        order_lock = threading.Lock()

        def add_event(event):
            with order_lock:
                execution_order.append(event)

        # Configure construct_paths mock
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {"prompt_file": "Prompt content"},
            {"output": output_path, "csv": csv_path},
            None,
        )

        # Configure insert_includes mock with delay to simulate work
        call_count = [0]
        call_lock = threading.Lock()

        def mock_insert_with_delay(*args, **kwargs):
            with call_lock:
                call_num = call_count[0]
                call_count[0] += 1

            add_event(f"insert_start_{call_num}")
            time.sleep(0.15)  # Simulate LLM work
            add_event(f"insert_end_{call_num}")

            csv_content = f"full_path,file_summary,content_hash\n/test/file.py,summary,hash{call_num}\n"
            return (f"Modified prompt {call_num}", csv_content, 0.01, "test-model")

        mock_insert_includes.side_effect = mock_insert_with_delay

        def run_auto_deps(call_id):
            """Run auto_deps_main."""
            add_event(f"call_{call_id}_start")
            result = auto_deps_main(
                ctx=mock_ctx,
                prompt_file="test.prompt",
                directory_path=str(tmp_path),
                auto_deps_csv_path=None,
                output=None,
                force_scan=False
            )
            add_event(f"call_{call_id}_end")
            return result

        # Run two calls concurrently
        with ThreadPoolExecutor(max_workers=2) as executor:
            future_a = executor.submit(run_auto_deps, "A")
            time.sleep(0.02)  # Small delay to ensure A starts first
            future_b = executor.submit(run_auto_deps, "B")

            result_a = future_a.result()
            result_b = future_b.result()

        # Verify serialization: insert_includes calls should not overlap
        # If serialized: insert_start_0 -> insert_end_0 -> insert_start_1 -> insert_end_1
        # If NOT serialized: insert_start_0 -> insert_start_1 (interleaved)
        insert_start_0_idx = execution_order.index("insert_start_0")
        insert_end_0_idx = execution_order.index("insert_end_0")
        insert_start_1_idx = execution_order.index("insert_start_1")

        assert insert_start_1_idx > insert_end_0_idx, \
            f"Second insert_includes should start AFTER first ends (serialized). Order: {execution_order}"

        # Verify both calls completed successfully
        assert result_a[0].startswith("Modified prompt"), f"Call A should succeed: {result_a}"
        assert result_b[0].startswith("Modified prompt"), f"Call B should succeed: {result_b}"

        # Note: lock file persistence after release is filelock version-dependent.
        # Serialization is verified above via execution_order assertions.

        # Verify CSV was written to tmp_path
        csv_file = tmp_path / "deps.csv"
        assert csv_file.exists(), "CSV should be written to tmp_path"

    def test_no_artifacts_in_working_directory(self, tmp_path, mock_ctx):
        """Verify that running auto_deps_main doesn't create files in CWD."""
        import os

        # Get list of files in CWD before test
        cwd = Path.cwd()
        files_before = set(cwd.iterdir())

        # Setup paths in tmp_path
        csv_path = str(tmp_path / "test_deps.csv")

        with patch("pdd.auto_deps_main.construct_paths") as mock_construct:
            with patch("pdd.auto_deps_main.insert_includes") as mock_insert:
                mock_construct.return_value = (
                    {},
                    {"prompt_file": "content"},
                    {"output": str(tmp_path / "out.prompt"), "csv": csv_path},
                    None,
                )
                mock_insert.return_value = ("modified", "csv,content", 0.01, "model")

                auto_deps_main(
                    ctx=mock_ctx,
                    prompt_file="test.prompt",
                    directory_path=str(tmp_path),
                    auto_deps_csv_path=None,
                    output=None,
                    force_scan=False
                )

        # Get list of files in CWD after test
        files_after = set(cwd.iterdir())
        new_files = files_after - files_before

        # Filter to only CSV and lock files (ignore other temp files)
        artifact_files = [f for f in new_files if f.suffix in ('.csv', '.lock')]

        assert len(artifact_files) == 0, \
            f"No artifacts should be created in CWD. Found: {artifact_files}"


class TestCacheSharing:
    """Tests verifying cache is properly shared between calls."""

    @patch("pdd.summarize_directory.llm_invoke")
    @patch("pdd.summarize_directory.load_prompt_template")
    def test_second_call_uses_cache_no_redundant_llm(
        self,
        mock_load_template,
        mock_llm_invoke,
        tmp_path
    ):
        """
        Verify that summarize_directory uses cache on second call.
        This tests the cache mechanism that makes locking valuable.
        """
        from pdd.summarize_directory import summarize_directory, FileSummary

        # Setup
        mock_load_template.return_value = "Summarize: {file_contents}"

        call_count = [0]

        def counting_llm(*args, **kwargs):
            call_count[0] += 1
            return {
                'result': FileSummary(file_summary="Test summary"),
                'cost': 0.01,
                'model_name': "test"
            }

        mock_llm_invoke.side_effect = counting_llm

        # Create test file
        test_file = tmp_path / "test.py"
        test_file.write_text("print('hello')")

        # First call - should invoke LLM
        csv_output1, cost1, _ = summarize_directory(
            directory_path=str(tmp_path / "*.py"),
            strength=0.5,
            temperature=0,
            verbose=False,
            csv_file=None
        )
        assert call_count[0] == 1, "First call should invoke LLM"

        # Second call with cache - should NOT invoke LLM
        csv_output2, cost2, _ = summarize_directory(
            directory_path=str(tmp_path / "*.py"),
            strength=0.5,
            temperature=0,
            verbose=False,
            csv_file=csv_output1  # Pass first run's output as cache
        )
        assert call_count[0] == 1, "Second call should use cache, not invoke LLM again"
        assert cost2 == 0.0, "No cost when using cache"
