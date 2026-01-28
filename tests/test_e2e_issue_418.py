"""E2E tests for Issue #418: Temp directory cleanup on git clone failure."""

import glob
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path


def get_project_root() -> Path:
    return Path(__file__).parent.parent


def test_temp_dir_cleaned_up_on_clone_failure(tmp_path: Path):
    """E2E: Temp directory cleaned up when clone fails."""
    project_root = get_project_root()

    test_script = f'''
import sys, json, glob, tempfile, os
sys.path.insert(0, "{project_root}")
from pdd.agentic_change import _setup_repository

temp_root = tempfile.gettempdir()
before = len(glob.glob(os.path.join(temp_root, "pdd_*")))

try:
    _setup_repository("nonexistent-user", "nonexistent-repo", quiet=True)
except RuntimeError:
    pass

after = len(glob.glob(os.path.join(temp_root, "pdd_*")))
print(json.dumps({{"leaked": after > before}}))
'''

    script_file = tmp_path / "test_leak.py"
    script_file.write_text(test_script)

    env = os.environ.copy()
    env['PYTHONPATH'] = str(project_root)

    result = subprocess.run(
        [sys.executable, str(script_file)],
        capture_output=True, text=True, timeout=30, env=env
    )

    assert result.returncode == 0, f"Script failed: {result.stderr}"
    output = json.loads(result.stdout.strip())
    assert not output['leaked'], "Temp directory leaked after clone failure"


def test_temp_dir_kept_on_success(tmp_path: Path):
    """E2E: Successful clone keeps temp directory."""
    project_root = get_project_root()

    test_script = f'''
import sys, json, os
from pathlib import Path
from unittest.mock import patch, MagicMock
sys.path.insert(0, "{project_root}")
from pdd.agentic_change import _setup_repository

with patch('pdd.agentic_change.subprocess.run') as mock_run:
    mock_run.return_value = MagicMock(returncode=0, stderr="")
    try:
        result_dir = _setup_repository("test-owner", "test-repo", quiet=True)
        exists = result_dir.exists()
    except:
        exists = False

print(json.dumps({{"exists": exists}}))
'''

    script_file = tmp_path / "test_success.py"
    script_file.write_text(test_script)

    env = os.environ.copy()
    env['PYTHONPATH'] = str(project_root)

    result = subprocess.run(
        [sys.executable, str(script_file)],
        capture_output=True, text=True, timeout=30, env=env
    )

    assert result.returncode == 0, f"Script failed: {result.stderr}"
    output = json.loads(result.stdout.strip())
    assert output['exists'], "Successful clone should keep temp directory"
