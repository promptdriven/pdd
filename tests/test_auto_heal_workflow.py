import os
import subprocess
import yaml
import tempfile
import pytest

def get_auth_script():
    workflow_path = ".github/workflows/auto-heal.yml"
    with open(workflow_path, "r") as f:
        workflow = yaml.safe_load(f)
        
    steps = workflow['jobs']['heal']['steps']
    auth_step = None
    for step in steps:
        if step.get('name') == "Authorize requester (must be pdd_cloud collaborator)":
            auth_step = step
            break
            
    assert auth_step is not None, "Could not find 'Authorize requester' step"
    return auth_step['run']

def run_script_with_mock_gh(run_script, requester, gh_mock_output):
    with tempfile.TemporaryDirectory() as tmpdir:
        mock_gh_path = os.path.join(tmpdir, "gh")
        with open(mock_gh_path, "w") as f:
            f.write("#!/bin/bash\n")
            f.write(f"echo '{gh_mock_output}'\n")
        os.chmod(mock_gh_path, 0o755)
        
        env = os.environ.copy()
        env['PATH'] = tmpdir + os.pathsep + env.get('PATH', '')
        env['REQUESTER'] = requester
        env['GH_TOKEN'] = "fake-token"
        
        result = subprocess.run(["bash", "-c", run_script], env=env, capture_output=True, text=True)
        return result

# --- Step 5 Reproduction Test ---
def test_issue_921_reproduction():
    """
    Test that the 'Authorize requester' step in auto-heal.yml correctly
    authorizes the bot account without failing.
    """
    run_script = get_auth_script()
    
    # We will run this script with a mocked `gh` command that returns 404
    # to simulate that the bot is not a collaborator.
    with tempfile.TemporaryDirectory() as tmpdir:
        mock_gh_path = os.path.join(tmpdir, "gh")
        with open(mock_gh_path, "w") as f:
            f.write("#!/bin/bash\n")
            f.write("echo 'HTTP/2.0 404'\n")
        os.chmod(mock_gh_path, 0o755)
        
        env = os.environ.copy()
        env['PATH'] = tmpdir + os.pathsep + env.get('PATH', '')
        env['REQUESTER'] = "prompt-driven-github[bot]"
        env['GH_TOKEN'] = "fake-token"
        
        # Run the script
        result = subprocess.run(["bash", "-c", run_script], env=env, capture_output=True, text=True)
        
        # We assert that the script succeeded (which means it bypassed the gh check or otherwise succeeded)
        assert result.returncode == 0, f"Script failed with code {result.returncode}\nstdout: {result.stdout}\nstderr: {result.stderr}"
        assert "authorized:" in result.stdout, f"Missing authorized message in stdout: {result.stdout}"

# --- Step 8 Proposed Tests ---

def test_bot_app_identity_authorization():
    """Test 1: Bot App Identity Authorization (Primary Bug)"""
    run_script = get_auth_script()
    result = run_script_with_mock_gh(run_script, "prompt-driven-github[bot]", "HTTP/2.0 404")
    
    # We expect this test to fail when run against the unmodified auto-heal.yml,
    # because the fix hasn't been applied yet. When the fix is applied, it will pass.
    assert result.returncode == 0, f"Script failed with code {result.returncode}\nstdout: {result.stdout}\nstderr: {result.stderr}"
    assert "authorized: prompt-driven-github[bot]" in result.stdout

def test_human_collaborator_authorization():
    """Test 2: Human Collaborator Authorization"""
    run_script = get_auth_script()
    result = run_script_with_mock_gh(run_script, "valid-human", "HTTP/2.0 204")
    
    assert result.returncode == 0, f"Script failed with code {result.returncode}\nstdout: {result.stdout}\nstderr: {result.stderr}"
    assert "authorized: valid-human is a pdd_cloud collaborator" in result.stdout

def test_human_non_collaborator_rejection():
    """Test 3: Human Non-Collaborator Rejection"""
    run_script = get_auth_script()
    result = run_script_with_mock_gh(run_script, "invalid-human", "HTTP/2.0 404")
    
    assert result.returncode == 1, f"Expected script to fail, but it exited with 0"
    assert "invalid-human is not a pdd_cloud collaborator" in result.stdout or "invalid-human is not a pdd_cloud collaborator" in result.stderr

def test_api_transient_error_handling():
    """Test 4: API Transient Error Handling"""
    run_script = get_auth_script()
    result = run_script_with_mock_gh(run_script, "some-user", "HTTP/2.0 500")
    
    assert result.returncode == 1, f"Expected script to fail, but it exited with 0"
    assert "returned HTTP '500'; refusing to authorize" in result.stdout or "returned HTTP '500'; refusing to authorize" in result.stderr

def test_missing_requester_edge_case():
    """Test 5: Missing Requester Edge Case"""
    run_script = get_auth_script()
    result = run_script_with_mock_gh(run_script, "", "HTTP/2.0 404")
    
    assert result.returncode == 1, f"Expected script to fail, but it exited with 0"
    assert "requester unresolved" in result.stdout or "requester unresolved" in result.stderr
