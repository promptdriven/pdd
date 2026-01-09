"""Tests for auto_deps_main concurrent execution locking."""
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import patch, MagicMock
import pytest
import click
from filelock import FileLock

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


class TestAutoDepsLocking:
    """Tests for concurrent execution locking in auto_deps_main."""

    def test_filelock_serializes_execution(self, tmp_path):
        """Second process should wait for first to complete.

        This test verifies that when two operations use the same FileLock,
        they execute sequentially (not interleaved).
        """
        csv_path = tmp_path / "deps.csv"
        lock_path = f"{csv_path}.lock"
        execution_order = []

        def run_with_lock(process_id, delay):
            lock = FileLock(lock_path)
            with lock:
                execution_order.append(f"{process_id}_start")
                time.sleep(delay)
                execution_order.append(f"{process_id}_end")

        # Start process A (slow), then B (fast)
        with ThreadPoolExecutor(max_workers=2) as executor:
            future_a = executor.submit(run_with_lock, "A", 0.2)
            time.sleep(0.05)  # Ensure A starts first
            future_b = executor.submit(run_with_lock, "B", 0.1)
            future_a.result()
            future_b.result()

        # B should wait for A to finish (serialized, not interleaved)
        assert execution_order == ["A_start", "A_end", "B_start", "B_end"], \
            f"Expected serialized execution, got: {execution_order}"

    def test_lock_file_created_with_lock_suffix(self, tmp_path):
        """Lock file should be created with .lock suffix."""
        csv_path = tmp_path / "deps.csv"
        lock_path = tmp_path / "deps.csv.lock"

        lock = FileLock(str(lock_path))
        with lock:
            assert lock_path.exists(), "Lock file should be created"

    @patch("pdd.auto_deps_main.construct_paths")
    @patch("pdd.auto_deps_main.insert_includes")
    def test_auto_deps_main_uses_lock(
        self,
        mock_insert_includes,
        mock_construct_paths,
        mock_ctx,
        tmp_path
    ):
        """auto_deps_main should acquire lock during execution."""
        # Setup mocks
        csv_path = str(tmp_path / "deps.csv")
        mock_construct_paths.return_value = (
            {},
            {"prompt_file": "Contents of prompt file"},
            {"output": str(tmp_path / "output.prompt"), "csv": csv_path},
            None,
        )
        mock_insert_includes.return_value = (
            "Modified prompt",
            "csv content",
            0.01,
            "test-model",
        )

        lock_acquired = [False]
        original_filelock = FileLock

        class TrackingFileLock(FileLock):
            def __enter__(self):
                lock_acquired[0] = True
                return super().__enter__()

        with patch("pdd.auto_deps_main.FileLock", TrackingFileLock):
            auto_deps_main(
                ctx=mock_ctx,
                prompt_file="test.prompt",
                directory_path="context/",
                auto_deps_csv_path=None,
                output=None,
                force_scan=False
            )

        # Verify lock was used
        assert lock_acquired[0], "FileLock should have been acquired"


class TestSecondProcessUsesCache:
    """Tests that verify the second process benefits from the first's cache."""

    @patch("pdd.summarize_directory.llm_invoke")
    @patch("pdd.summarize_directory.load_prompt_template")
    def test_second_call_uses_cache_no_redundant_llm(
        self,
        mock_load_template,
        mock_llm_invoke,
        tmp_path
    ):
        """Second auto-deps call should use cache, avoiding redundant LLM calls.

        This test creates a file, runs auto-deps twice, and verifies that
        the LLM is only called once (the second run uses the cache).
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
