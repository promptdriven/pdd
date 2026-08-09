"""
E2E regression test for Issue #522: Sync fingerprint ignores <include> dependencies.

When an included file changes but the top-level .prompt file doesn't, sync should
detect the change and regenerate code. The bug is that calculate_sha256 only hashes
the raw .prompt file, so included file changes are invisible to the fingerprint system.

Approach 2 fix: Store include dependency paths + hashes in the fingerprint JSON so
they persist even after auto-deps strips <include> tags from the prompt.
"""

import hashlib
import json
from pathlib import Path
from unittest.mock import patch

from pdd.sync_determine_operation import (
    sync_determine_operation,
    calculate_prompt_hash,
    extract_include_deps,
    calculate_sha256,
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _setup_sync_env(tmp_path, prompt_content, included_files):
    """
    Set up a realistic sync environment simulating a completed prior sync.
    """
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    src_dir = tmp_path / "src"
    src_dir.mkdir()
    tests_dir = tmp_path / "tests"
    tests_dir.mkdir()
    pdd_dir = tmp_path / ".pdd"
    meta_dir = pdd_dir / "meta"
    locks_dir = pdd_dir / "locks"
    meta_dir.mkdir(parents=True)
    locks_dir.mkdir(parents=True)

    prompt_file = prompts_dir / "helper_python.prompt"
    prompt_file.write_text(prompt_content)

    for name, content in included_files.items():
        (tmp_path / name).write_text(content)

    code_file = src_dir / "helper.py"
    code_file.write_text("# generated\ndef helper(): pass\n")

    example_file = src_dir / "helper_example.py"
    example_file.write_text("# example\n")

    test_file = tests_dir / "test_helper.py"
    test_file.write_text("def test_helper(): assert True\n")

    prompt_hash = calculate_prompt_hash(prompt_file)
    include_deps = extract_include_deps(prompt_file)
    code_hash = _sha256(code_file)
    example_hash = _sha256(example_file)
    test_hash = _sha256(test_file)

    fp_file = meta_dir / "helper_python.json"
    fp_file.write_text(json.dumps({
        "pdd_version": "0.0.156",
        "prompt_hash": prompt_hash,
        "code_hash": code_hash,
        "example_hash": example_hash,
        "test_hash": test_hash,
        "command": "test",
        "timestamp": "2026-02-14T00:00:00+00:00",
        "include_deps": include_deps,
    }))

    rr_file = meta_dir / "helper_python_run.json"
    rr_file.write_text(json.dumps({
        "timestamp": "2026-02-14T00:00:00+00:00",
        "exit_code": 0,
        "tests_passed": 5,
        "tests_failed": 0,
        "coverage": 95.0,
        "test_hash": test_hash,
    }))

    paths = {
        "prompt": prompt_file,
        "code": code_file,
        "example": example_file,
        "test": test_file,
        "test_files": [test_file],
    }

    return {
        "paths": paths,
        "prompts_dir": prompts_dir,
    }


class TestIssue522IncludeFingerprintE2E:
    """
    E2E: Full sync_determine_operation with real filesystem state to verify
    that changes to <include>d files trigger regeneration.
    """

    def test_included_file_change_triggers_regeneration(self, tmp_path, monkeypatch):
        """
        BUG: After a successful sync, modifying an <include>d file without touching
        the prompt should trigger regeneration.
        """
        monkeypatch.chdir(tmp_path)

        prompt_content = (
            "Create a helper function.\n"
            "<include>shared_types.py</include>\n"
            "Generate a function that creates a User object.\n"
        )
        env = _setup_sync_env(tmp_path, prompt_content, {
            "shared_types.py": "class User:\n    def __init__(self, name): self.name = name\n",
        })

        # Modify the included file — this is the bug trigger
        (tmp_path / "shared_types.py").write_text(
            "class User:\n    def __init__(self, name, age, email): pass\n"
        )

        with patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=env["paths"]):
            decision = sync_determine_operation(
                basename="helper",
                language="python",
                target_coverage=90.0,
                prompts_dir=str(env["prompts_dir"]),
            )

        assert decision.operation in ("generate", "auto-deps"), (
            f"Expected 'generate' or 'auto-deps' because <include>d file changed, "
            f"but got '{decision.operation}'. "
            f"Fingerprint must account for included file content."
        )

    def test_tags_stripped_dep_change_still_detected(self, tmp_path, monkeypatch):
        """
        Greg's exact scenario: auto-deps strips <include> tags, then dep changes.
        Stored include_deps in fingerprint must catch it.
        """
        monkeypatch.chdir(tmp_path)

        # Step 1: First sync with include tags
        prompt_content_with_tags = (
            "Create a helper function.\n"
            "<include>shared_types.py</include>\n"
        )
        env = _setup_sync_env(tmp_path, prompt_content_with_tags, {
            "shared_types.py": "class User:\n    def __init__(self, name): self.name = name\n",
        })

        # Step 2: Simulate auto-deps stripping tags (rewrites prompt)
        prompt_file = env["paths"]["prompt"]
        stripped_content = (
            "Create a helper function.\n"
            "class User:\n    def __init__(self, name): self.name = name\n"
        )
        prompt_file.write_text(stripped_content)

        # Step 3: Change the dependency file
        (tmp_path / "shared_types.py").write_text(
            "class User:\n    def __init__(self, name, age): pass\n"
        )

        with patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=env["paths"]):
            decision = sync_determine_operation(
                basename="helper",
                language="python",
                target_coverage=90.0,
                prompts_dir=str(env["prompts_dir"]),
            )

        assert decision.operation in ("generate", "auto-deps"), (
            f"Expected regeneration because stored include dep changed, "
            f"but got '{decision.operation}'. "
            f"Stored include_deps must persist across tag stripping."
        )

    def test_no_change_returns_nothing(self, tmp_path, monkeypatch):
        """
        Baseline: When nothing changes, sync should not regenerate.
        """
        monkeypatch.chdir(tmp_path)

        prompt_content = (
            "Create a helper function.\n"
            "<include>shared_types.py</include>\n"
        )
        env = _setup_sync_env(tmp_path, prompt_content, {
            "shared_types.py": "class User:\n    pass\n",
        })

        with patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=env["paths"]):
            decision = sync_determine_operation(
                basename="helper",
                language="python",
                target_coverage=90.0,
                prompts_dir=str(env["prompts_dir"]),
            )

        assert decision.operation in ("nothing", "all_synced", "verify"), (
            f"Expected 'nothing'/'all_synced'/'verify' when nothing changed, "
            f"got '{decision.operation}'. Fix must not cause false positives."
        )
