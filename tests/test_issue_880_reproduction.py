import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

from pdd.agentic_update import run_agentic_update

def test_issue_880_reproduction(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    """
    Reproduction test for Issue #880: agentic update scope guard reverts
    included-doc edits and new shared includes.
    """
    # 1. Set up a git repo so _revert_out_of_scope_changes will run
    subprocess.run(["git", "init"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=tmp_path, check=True)

    # 2. Create initial files
    prompt_file = tmp_path / "my.prompt"
    code_file = tmp_path / "my_code.py"
    included_doc = tmp_path / "doc.md"
    context_dir = tmp_path / "context"
    context_dir.mkdir()
    shared_file = context_dir / "shared.md"
    unrelated_file = tmp_path / "unrelated.py"

    prompt_content = "<include doc.md>\n<include context/shared.md>\nPrompt contents here."
    prompt_file.write_text(prompt_content)
    code_file.write_text("print('hello')")
    included_doc.write_text("original doc content")
    shared_file.write_text("original shared content")
    unrelated_file.write_text("original unrelated")

    # Commit the initial files
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial"], cwd=tmp_path, check=True)

    # 3. Mock dependencies
    monkeypatch.setattr("pdd.agentic_update.PROJECT_ROOT", tmp_path)
    monkeypatch.setattr("pdd.agentic_update.get_available_agents", lambda: ["mock_agent"])

    mock_template = MagicMock()
    mock_template.format.return_value = "Instruction"
    monkeypatch.setattr("pdd.agentic_update.load_prompt_template", lambda name: mock_template)

    def mock_run_task(*args, **kwargs):
        # Simulate agent modifying the prompt file
        prompt_file.write_text(prompt_content + "\nAgent edit")
        # Simulate agent modifying an included document
        included_doc.write_text("original doc content\nAgent edit to included doc")
        # Simulate agent modifying a shared context file
        shared_file.write_text("original shared content\nAgent edit to shared file")
        # Simulate agent modifying an unrelated file (should be reverted)
        unrelated_file.write_text("original unrelated\nAgent edit to unrelated file")
        
        # Simulate agent creating a NEW shared context file
        new_shared = context_dir / "new_shared.md"
        new_shared.write_text("New shared context file")
        
        return True, "Task complete", 0.0, "mock_agent"

    monkeypatch.setattr("pdd.agentic_update.run_agentic_task", mock_run_task)

    # 4. Run the update
    success, msg, _, _, _ = run_agentic_update(
        str(prompt_file),
        str(code_file),
        test_files=[],
        quiet=True
    )

    assert success is True

    # 5. Assert EXPECTED behavior
    # Unrelated files should be reverted
    assert unrelated_file.read_text() == "original unrelated", "Unrelated file edit was not reverted"

    # Included docs should be preserved (currently fails because _allowed doesn't include them)
    assert included_doc.read_text() == "original doc content\nAgent edit to included doc", \
        "Included doc edit was incorrectly reverted"
    
    assert shared_file.read_text() == "original shared content\nAgent edit to shared file", \
        "Shared context edit was incorrectly reverted"
        
    new_shared = context_dir / "new_shared.md"
    assert new_shared.exists(), "New shared file was incorrectly removed/reverted"

