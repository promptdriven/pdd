from pathlib import Path
from pdd.agentic_verify import verify_and_log

def test_verify_disabled_returns_true(tmp_path):
    ok = verify_and_log("tests/test_dummy.py", tmp_path, verify_cmd=None, enabled=False)
    assert ok is True

def test_verify_cmd_success(tmp_path):
    testfile = tmp_path / "unit.test"
    testfile.write_text("ok")
    cmd = 'test -f "{test}" && exit 0 || exit 1'
    ok = verify_and_log(str(testfile), tmp_path, verify_cmd=cmd, enabled=True)
    assert ok is True

def test_verify_cmd_failure(tmp_path):
    missing = tmp_path / "missing.test"
    cmd = 'test -f "{test}" && exit 0 || exit 1'
    ok = verify_and_log(str(missing), tmp_path, verify_cmd=cmd, enabled=True)
    assert ok is False
