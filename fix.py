with open('/tmp/pdd_job_N6ExQV0wIuaYNBNAR0GK_tko3lgvf/tests/test_checkup_review_loop.py', 'r') as f:
    content = f.read()

# Fix the mess I made in test_full_loop_success
content = content.replace("""    mock_invoke.side_effect = [
        (True, '{"status": "failed", "findings": []}', 0.1, "test-model"),
        (True, '{"status": "findings", "findings": [{"severity": "critical", "location": "file.py:1", "finding": "bug", "required_fix": "fix it"}]}', 0.1, "test-model"),""", """    mock_invoke.side_effect = [
        (True, '{"status": "findings", "findings": [{"severity": "critical", "location": "file.py:1", "finding": "bug", "required_fix": "fix it"}]}', 0.1, "test-model"),""")

# Fix the fallback test to have 3 side effects properly
old_fallback = """    mock_invoke.side_effect = [
        (True, '{"status": "failed", "findings": []}', 0.1, "test-model"),
        (True, '{"status": "failed", "findings": []}', 0.1, "test-model"),
        (True, '{"status": "clean", "findings": []}', 0.1, "test-model"),
    ]"""

# Because of the sed, it looks like this now:
curr_fallback = """    mock_invoke.side_effect = [
        (True, '{"status": "failed", "findings": []}', 0.1, "test-model"),
        (True, '{"status": "failed", "findings": []}', 0.1, "test-model"),
        (True, '{"status": "clean", "findings": []}', 0.1, "test-model"),
    ]"""

with open('/tmp/pdd_job_N6ExQV0wIuaYNBNAR0GK_tko3lgvf/tests/test_checkup_review_loop.py', 'w') as f:
    f.write(content)
