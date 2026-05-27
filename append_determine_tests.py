import os

code = """
from unittest.mock import patch

def test_issue1200_stale_state_skip_flags_exhausts_consecutive_fix_breaker(pdd_test_environment):
    from pdd.sync_determine_operation import sync_determine_operation
    from tests.test_sync_determine_operation import create_file, create_run_report_file, create_fingerprint_file, get_meta_dir, BASENAME, LANGUAGE

    tmp_path = pdd_test_environment
    (tmp_path / "src").mkdir(exist_ok=True)
    (tmp_path / "tests").mkdir(exist_ok=True)

    prompt_path = tmp_path / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt"
    prompt_hash = create_file(prompt_path, "# prompt")
    
    code_path = tmp_path / "src" / f"{BASENAME}.py"
    code_hash = create_file(code_path, "def foo(): pass")
    
    test_path = tmp_path / "tests" / f"test_{BASENAME}.py"
    test_hash = create_file(test_path, "def test_fail(): assert False\\n# changed")

    create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
        "timestamp": "2025-12-10T08:33:52.589258+00:00",
        "exit_code": 1,
        "tests_passed": 1,
        "tests_failed": 2,
        "coverage": 95.0,
        "test_hash": "old_stale_hash"
    })

    create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
        "pdd_version": "0.0.81",
        "timestamp": "2025-12-10T08:30:00.000000+00:00",
        "command": "verify",
        "prompt_hash": prompt_hash,
        "code_hash": code_hash,
        "test_hash": test_hash, # Current hash in fingerprint
    })

    mock_paths = {
        'prompt': prompt_path,
        'code': code_path,
        'test': test_path,
        'example': None
    }

    with patch('pdd.sync_determine_operation.get_pdd_file_paths', return_value=mock_paths):
        decision = sync_determine_operation(BASENAME, LANGUAGE, "prompts", "src", "examples", "tests", False, False)
    
    assert decision.operation != 'fix', "Should not recommend fix based on stale tests_failed > 0"

def test_issue1200_stale_run_report_crash_validation(pdd_test_environment):
    # Scope addition: covers expansion item "sync_determine_operation.py must validate run_report staleness before recommending crash based on exit_code != 0"
    from pdd.sync_determine_operation import sync_determine_operation
    from tests.test_sync_determine_operation import create_file, create_run_report_file, create_fingerprint_file, get_meta_dir, BASENAME, LANGUAGE

    tmp_path = pdd_test_environment
    (tmp_path / "src").mkdir(exist_ok=True)
    (tmp_path / "tests").mkdir(exist_ok=True)

    prompt_path = tmp_path / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt"
    prompt_hash = create_file(prompt_path, "# prompt")
    
    code_path = tmp_path / "src" / f"{BASENAME}.py"
    code_hash = create_file(code_path, "def foo(): pass\\n# changed")
    
    test_path = tmp_path / "tests" / f"test_{BASENAME}.py"
    test_hash = create_file(test_path, "def test_fail(): pass")

    create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
        "timestamp": "2025-12-10T08:33:52.589258+00:00",
        "exit_code": 1,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 95.0,
        "test_hash": "old_stale_hash" 
    })

    create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
        "pdd_version": "0.0.81",
        "timestamp": "2025-12-10T08:30:00.000000+00:00",
        "command": "verify",
        "prompt_hash": prompt_hash,
        "code_hash": code_hash,
        "test_hash": test_hash, # Current hash in fingerprint
    })

    mock_paths = {
        'prompt': prompt_path,
        'code': code_path,
        'test': test_path,
        'example': None
    }

    with patch('pdd.sync_determine_operation.get_pdd_file_paths', return_value=mock_paths):
        decision = sync_determine_operation(BASENAME, LANGUAGE, "prompts", "src", "examples", "tests", False, False)
    
    assert decision.operation != 'crash', "Should not recommend crash based on stale exit_code != 0"

def test_issue1200_fresh_run_report_fix_and_crash_validation(pdd_test_environment):
    # Regression prevention for Expansion items
    from pdd.sync_determine_operation import sync_determine_operation
    from tests.test_sync_determine_operation import create_file, create_run_report_file, create_fingerprint_file, get_meta_dir, BASENAME, LANGUAGE

    tmp_path = pdd_test_environment
    (tmp_path / "src").mkdir(exist_ok=True)
    (tmp_path / "tests").mkdir(exist_ok=True)

    prompt_path = tmp_path / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt"
    prompt_hash = create_file(prompt_path, "# prompt")
    
    code_path = tmp_path / "src" / f"{BASENAME}.py"
    code_hash = create_file(code_path, "def foo(): pass")
    
    test_path = tmp_path / "tests" / f"test_{BASENAME}.py"
    test_hash = create_file(test_path, "def test_fail(): pass")

    create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
        "timestamp": "2025-12-10T08:33:52.589258+00:00",
        "exit_code": 0,
        "tests_passed": 0,
        "tests_failed": 2,
        "coverage": 95.0,
        "test_hash": test_hash
    })

    create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
        "pdd_version": "0.0.81",
        "timestamp": "2025-12-10T08:30:00.000000+00:00",
        "command": "verify",
        "prompt_hash": prompt_hash,
        "code_hash": code_hash,
        "test_hash": test_hash, # Current hash in fingerprint
    })

    mock_paths = {
        'prompt': prompt_path,
        'code': code_path,
        'test': test_path,
        'example': None
    }

    with patch('pdd.sync_determine_operation.get_pdd_file_paths', return_value=mock_paths):
        decision = sync_determine_operation(BASENAME, LANGUAGE, "prompts", "src", "examples", "tests", False, False)
    
    assert decision.operation == 'fix', "Should recommend fix since tests_failed > 0 and report is fresh"
"""

with open("tests/test_sync_determine_operation.py", "a") as f:
    f.write("\n" + code)
