import subprocess
from pathlib import Path

test_file = Path("tests/test_agentic_update.py")
content = """

# --- Reproduction test from Step 5 ---
import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

from pdd.agentic_update import run_agentic_update

def test_issue_880_reproduction(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    \"\"\"
    Reproduction test for Issue #880: agentic update scope guard reverts
    included-doc edits and new shared includes.
    \"\"\"
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

    prompt_content = "<include doc.md>\\n<include context/shared.md>\\nPrompt contents here."
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
        prompt_file.write_text(prompt_content + "\\nAgent edit")
        # Simulate agent modifying an included document
        included_doc.write_text("original doc content\\nAgent edit to included doc")
        # Simulate agent modifying a shared context file
        shared_file.write_text("original shared content\\nAgent edit to shared file")
        # Simulate agent modifying an unrelated file (should be reverted)
        unrelated_file.write_text("original unrelated\\nAgent edit to unrelated file")
        
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
    assert included_doc.read_text() == "original doc content\\nAgent edit to included doc", \\
        "Included doc edit was incorrectly reverted"
    
    assert shared_file.read_text() == "original shared content\\nAgent edit to shared file", \\
        "Shared context edit was incorrectly reverted"
        
    new_shared = context_dir / "new_shared.md"
    assert new_shared.exists(), "New shared file was incorrectly removed/reverted"


def test_agentic_update_preserves_included_docs(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    \"\"\"Test 1: Agentic update preserves explicitly included docs\"\"\"
    subprocess.run(["git", "init"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=tmp_path, check=True)
    
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    docs_dir = tmp_path / "docs"
    docs_dir.mkdir()
    doc_file = docs_dir / "my_doc.md"
    
    prompt_file.write_text("<include docs/my_doc.md>\\nPrompt")
    code_file.write_text("code")
    doc_file.write_text("original")
    
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial"], cwd=tmp_path, check=True)
    
    monkeypatch.setattr("pdd.agentic_update.PROJECT_ROOT", tmp_path)
    monkeypatch.setattr("pdd.agentic_update.get_available_agents", lambda: ["mock_agent"])
    
    mock_template = MagicMock()
    mock_template.format.return_value = "Instruction"
    monkeypatch.setattr("pdd.agentic_update.load_prompt_template", lambda name: mock_template)
    
    def mock_run_task(*args, **kwargs):
        doc_file.write_text("modified")
        prompt_file.write_text("<include docs/my_doc.md>\\nModified Prompt")
        return True, "Task complete", 0.0, "mock_agent"
        
    monkeypatch.setattr("pdd.agentic_update.run_agentic_task", mock_run_task)
    
    success, msg, _, _, _ = run_agentic_update(str(prompt_file), str(code_file), test_files=[], quiet=True)
    assert success is True
    assert doc_file.read_text() == "modified", "Included doc edit was reverted"


def test_agentic_update_preserves_new_shared_context(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    \"\"\"Test 2: Agentic update preserves new shared context files\"\"\"
    subprocess.run(["git", "init"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=tmp_path, check=True)
    
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    context_dir = tmp_path / "context"
    context_dir.mkdir()
    
    prompt_file.write_text("Prompt")
    code_file.write_text("code")
    
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial"], cwd=tmp_path, check=True)
    
    monkeypatch.setattr("pdd.agentic_update.PROJECT_ROOT", tmp_path)
    monkeypatch.setattr("pdd.agentic_update.get_available_agents", lambda: ["mock_agent"])
    
    mock_template = MagicMock()
    mock_template.format.return_value = "Instruction"
    monkeypatch.setattr("pdd.agentic_update.load_prompt_template", lambda name: mock_template)
    
    new_shared = context_dir / "shared_state.md"
    def mock_run_task(*args, **kwargs):
        new_shared.write_text("new content")
        prompt_file.write_text("Modified Prompt")
        return True, "Task complete", 0.0, "mock_agent"
        
    monkeypatch.setattr("pdd.agentic_update.run_agentic_task", mock_run_task)
    
    success, msg, _, _, changed_files = run_agentic_update(str(prompt_file), str(code_file), test_files=[], quiet=True)
    assert success is True
    assert new_shared.exists(), "New shared context file was reverted"


def test_unrelated_file_mutations_reverted(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    \"\"\"Test 3: Unrelated file mutations are reverted\"\"\"
    subprocess.run(["git", "init"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=tmp_path, check=True)
    
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    src_dir = tmp_path / "src"
    src_dir.mkdir()
    unrelated_file = src_dir / "unrelated_file.py"
    
    prompt_file.write_text("Prompt")
    code_file.write_text("code")
    unrelated_file.write_text("original")
    
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial"], cwd=tmp_path, check=True)
    
    monkeypatch.setattr("pdd.agentic_update.PROJECT_ROOT", tmp_path)
    monkeypatch.setattr("pdd.agentic_update.get_available_agents", lambda: ["mock_agent"])
    
    mock_template = MagicMock()
    mock_template.format.return_value = "Instruction"
    monkeypatch.setattr("pdd.agentic_update.load_prompt_template", lambda name: mock_template)
    
    def mock_run_task(*args, **kwargs):
        unrelated_file.write_text("modified")
        prompt_file.write_text("Modified Prompt")
        return True, "Task complete", 0.0, "mock_agent"
        
    monkeypatch.setattr("pdd.agentic_update.run_agentic_task", mock_run_task)
    
    success, msg, _, _, _ = run_agentic_update(str(prompt_file), str(code_file), test_files=[], quiet=True)
    assert success is True
    assert unrelated_file.read_text() == "original", "Unrelated file mutation was not reverted"


# Scope addition: covers expansion item "before_paths initialization" identified by Step 6 but absent from Step 8's plan
def test_before_paths_captures_included_docs(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    \"\"\"Test 4: Tracking state before_paths initialization captures included docs\"\"\"
    subprocess.run(["git", "init"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=tmp_path, check=True)
    
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    docs_dir = tmp_path / "docs"
    docs_dir.mkdir()
    doc_file = docs_dir / "my_doc.md"
    
    prompt_file.write_text("<include docs/my_doc.md>\\nPrompt")
    code_file.write_text("code")
    doc_file.write_text("doc")
    
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial"], cwd=tmp_path, check=True)
    
    monkeypatch.setattr("pdd.agentic_update.PROJECT_ROOT", tmp_path)
    monkeypatch.setattr("pdd.agentic_update.get_available_agents", lambda: ["mock_agent"])
    
    mock_template = MagicMock()
    mock_template.format.return_value = "Instruction"
    monkeypatch.setattr("pdd.agentic_update.load_prompt_template", lambda name: mock_template)
    
    def mock_run_task(*args, **kwargs):
        doc_file.write_text("doc modified")
        prompt_file.write_text("<include docs/my_doc.md>\\nModified Prompt")
        return True, "Task complete", 0.0, "mock_agent"
        
    monkeypatch.setattr("pdd.agentic_update.run_agentic_task", mock_run_task)
    
    success, msg, _, _, changed_files = run_agentic_update(str(prompt_file), str(code_file), test_files=[], quiet=True)
    assert success is True
    assert str(doc_file.resolve()) in changed_files, "Included doc not found in changed_files"


# Scope addition: covers expansion item "after_paths initialization" identified by Step 6 but absent from Step 8's plan
def test_after_paths_captures_new_context(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    \"\"\"Test 5: Tracking state after_paths initialization captures new context files\"\"\"
    subprocess.run(["git", "init"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test User"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=tmp_path, check=True)
    
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    context_dir = tmp_path / "context"
    context_dir.mkdir()
    
    prompt_file.write_text("Prompt")
    code_file.write_text("code")
    
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-m", "Initial"], cwd=tmp_path, check=True)
    
    monkeypatch.setattr("pdd.agentic_update.PROJECT_ROOT", tmp_path)
    monkeypatch.setattr("pdd.agentic_update.get_available_agents", lambda: ["mock_agent"])
    
    mock_template = MagicMock()
    mock_template.format.return_value = "Instruction"
    monkeypatch.setattr("pdd.agentic_update.load_prompt_template", lambda name: mock_template)
    
    new_shared = context_dir / "new_shared.md"
    def mock_run_task(*args, **kwargs):
        new_shared.write_text("new shared")
        prompt_file.write_text("Modified Prompt")
        return True, "Task complete", 0.0, "mock_agent"
        
    monkeypatch.setattr("pdd.agentic_update.run_agentic_task", mock_run_task)
    
    success, msg, _, _, changed_files = run_agentic_update(str(prompt_file), str(code_file), test_files=[], quiet=True)
    assert success is True
    assert str(new_shared.resolve()) in changed_files, "New shared context file not found in changed_files"

"""

with open(test_file, "a") as f:
    f.write(content)
