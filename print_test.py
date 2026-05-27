from unittest.mock import patch
def test_print(pdd_test_environment):
    from pdd.sync_determine_operation import sync_determine_operation
    from tests.test_sync_determine_operation import create_file, create_run_report_file, create_fingerprint_file, get_meta_dir, BASENAME, LANGUAGE

    tmp_path = pdd_test_environment
    (tmp_path / "src").mkdir(exist_ok=True)
    (tmp_path / "tests").mkdir(exist_ok=True)
    prompt_hash = create_file(tmp_path / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt", "# prompt")
    code_hash = create_file(tmp_path / "src" / f"{BASENAME}.py", "def foo(): pass\\n# changed")
    test_hash = create_file(tmp_path / "tests" / f"test_{BASENAME}.py", "def test_fail(): pass")

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
        "test_hash": test_hash,
    })

    mock_paths = {
        'prompt': tmp_path / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt",
        'code': tmp_path / "src" / f"{BASENAME}.py",
        'test': tmp_path / "tests" / f"test_{BASENAME}.py",
        'example': tmp_path / "examples" / f"{BASENAME}_example.py"
    }

    with patch('pdd.sync_determine_operation.get_pdd_file_paths', return_value=mock_paths):
        decision = sync_determine_operation(BASENAME, LANGUAGE, 90.0, 5.0, prompts_dir="prompts", skip_tests=False, skip_verify=False)
    print("DECISION:", decision)
