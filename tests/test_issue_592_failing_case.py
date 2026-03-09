
import pytest
import os
import subprocess
from pdd.preprocess import preprocess
from unittest.mock import patch, MagicMock

# Define a temporary prompt file for testing
TEST_PROMPT_FILE = "test_issue_592_timeout_prompt.prompt"

@pytest.fixture
def create_test_prompt_file(tmp_path):
    """Fixture to create a temporary prompt file and clean up afterwards."""
    file_path = tmp_path / TEST_PROMPT_FILE
    yield file_path
    if file_path.exists():
        file_path.unlink()

def test_shell_command_timeout_bug_replication(create_test_prompt_file, monkeypatch):
    """
    This test replicates the original bug condition where a shell command without a timeout
    would cause `pdd preprocess` to hang indefinitely.
    
    Before the fix for issue #592, this test would hang indefinitely.
    With the fix, it should correctly terminate with a timeout error message.
    """
    prompt_content = """Test prompt
<shell>sleep 5</shell>"""
    create_test_prompt_file.write_text(prompt_content)

    # Set a very short timeout to ensure the command times out quickly
    monkeypatch.setenv("PDD_SHELL_TIMEOUT", "1")

    # Call preprocess, expecting it to handle the timeout gracefully
    result = preprocess(create_test_prompt_file.read_text())

    # Assert that the output contains the timeout error message, indicating the bug is fixed
    assert "Command 'sleep 5' timed out after 1 seconds." in result
    
    # Also assert that the process did not hang (implicitly verified by reaching this line and assertion)
    # If the bug were present, this line would not be reached within a reasonable time.
