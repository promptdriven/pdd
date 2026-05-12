import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path
import click

from pdd.update_main import update_main

class DummyArchStage:
    status = "ok"
    detail = "updated fields: ['foo']"

@patch('pdd.update_main.update_file_pair')
@patch('pdd.update_main.is_code_changed', return_value=(True, ""))
@patch('pdd.update_main.get_git_changed_files', return_value=set())
@patch('pdd.update_main._find_prd_file')
@patch('pdd.agentic_common.run_agentic_task')
def test_dummy(mock_agentic, mock_find_prd, mock_git, mock_changed, mock_update, tmp_path, capsys):
    mock_update.return_value = {
        "prompt_file": "prompts/src/module1_python.prompt", 
        "status": "✅ Success", 
        "cost": 0.05, 
        "model": "mock_model", 
        "error": "",
        "arch_stage": DummyArchStage()
    }
    
    mock_agentic.return_value = (True, "<updated-prd>new PRD content</updated-prd>", 0.12, "agent_model")
    
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    arch_file = repo_root / "architecture.json"
    arch_file.write_text("{}")
    
    prd_file = repo_root / "PRD.md"
    prd_file.write_text("old PRD content")
    
    prompts_dir = repo_root / "prompts"
    prompts_dir.mkdir()
    
    mock_find_prd.return_value = prd_file

    ctx = click.Context(click.Command('update'))
    ctx.obj = {"verbose": False}

    with patch('pdd.update_main.find_and_resolve_all_pairs', return_value=[("prompts/src/module1_python.prompt", "src/module1.py")]):
        with patch('pdd.update_main.git.Repo'):
            with patch('pdd.update_main.os.getcwd', return_value=str(repo_root)):
                result = update_main(
                    ctx=ctx, 
                    use_git=False, 
                    repo=True, 
                    input_prompt_file=None, 
                    modified_code_file=None, 
                    input_code_file=None, 
                    output=None,
                    dry_run=False,
                    sync_metadata=False
                )

    out = capsys.readouterr().out

if __name__ == "__main__":
    pytest.main(["-v", "-s", "test_dummy_prd_sync.py"])
