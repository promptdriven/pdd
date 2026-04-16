"""
End-to-end integration test for the full auto-deps pipeline.

This file contains one large integrative test that exercises the full pipeline
(auto_deps_main -> insert_includes -> auto_include -> summarize_directory)
across multiple directories and multiple runs with real LLM calls, catching
interaction bugs like those in PR #763 (CSV wipeout, path inconsistency,
path corruption).

Requires API key:
    PDD_RUN_REAL_LLM_TESTS=1 pytest tests/test_e2e_auto_deps_pipeline.py -v
"""

from __future__ import annotations

import csv
import json
import os
import re
import subprocess
import textwrap
from io import StringIO
from pathlib import Path
from typing import Dict, List

import click
import pytest

from pdd import DEFAULT_STRENGTH, DEFAULT_TIME
from pdd.auto_deps_main import auto_deps_main


# ---------------------------------------------------------------------------
# Skip logic
# ---------------------------------------------------------------------------

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"


def _skip_unless_llm():
    if not (os.getenv("PDD_RUN_REAL_LLM_TESTS") or RUN_ALL_TESTS_ENABLED):
        pytest.skip(
            "Real LLM integration tests require network/API access; set "
            "PDD_RUN_REAL_LLM_TESTS=1 or PDD_RUN_ALL_TESTS=1."
        )


# ---------------------------------------------------------------------------
# Shared fixtures and helpers
# ---------------------------------------------------------------------------

@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH so language_format.csv and prompt templates are found."""
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


def _init_git_repo(path: Path) -> None:
    """Initialize a git repo at *path* with all files committed."""
    subprocess.run(
        ["git", "init"], cwd=str(path), capture_output=True, check=True
    )
    subprocess.run(
        ["git", "add", "."], cwd=str(path), capture_output=True, check=True
    )
    subprocess.run(
        ["git", "commit", "-m", "init", "--allow-empty"],
        cwd=str(path),
        capture_output=True,
        check=True,
        env={**os.environ, "GIT_AUTHOR_NAME": "test", "GIT_AUTHOR_EMAIL": "t@t",
             "GIT_COMMITTER_NAME": "test", "GIT_COMMITTER_EMAIL": "t@t"},
    )


def _parse_csv(csv_str: str) -> List[Dict[str, str]]:
    return list(csv.DictReader(StringIO(csv_str)))


# Large source file (>100 lines) used in the test project
MODELS_PY = textwrap.dedent('''\
    """User and Admin models for the application."""

    from __future__ import annotations

    import re
    from dataclasses import dataclass, field
    from typing import Optional, List


    @dataclass
    class UserModel:
        """Represents a user in the system."""

        name: str
        email: str
        role: str = "user"
        active: bool = True
        tags: List[str] = field(default_factory=list)

        def validate(self) -> bool:
            """Validate user fields."""
            if not self.name or not self.name.strip():
                return False
            if not self.email or "@" not in self.email:
                return False
            if not re.match(r"^[^@]+@[^@]+\\\\.[^@]+$", self.email):
                return False
            return True

        def display_name(self) -> str:
            """Return formatted display name."""
            return f"{self.name} <{self.email}>"

        def has_tag(self, tag: str) -> bool:
            """Check if user has a specific tag."""
            return tag in self.tags

        def add_tag(self, tag: str) -> None:
            """Add a tag to the user."""
            if tag not in self.tags:
                self.tags.append(tag)

        def remove_tag(self, tag: str) -> None:
            """Remove a tag from the user."""
            if tag in self.tags:
                self.tags.remove(tag)

        def to_dict(self) -> dict:
            """Serialize user to dictionary."""
            return {
                "name": self.name,
                "email": self.email,
                "role": self.role,
                "active": self.active,
                "tags": self.tags,
            }

        @classmethod
        def from_dict(cls, data: dict) -> "UserModel":
            """Create user from dictionary."""
            return cls(
                name=data["name"],
                email=data["email"],
                role=data.get("role", "user"),
                active=data.get("active", True),
                tags=data.get("tags", []),
            )


    @dataclass
    class AdminModel(UserModel):
        """Represents an admin user with additional permissions."""

        permissions: List[str] = field(default_factory=list)

        def has_permission(self, perm: str) -> bool:
            """Check if admin has a specific permission."""
            return perm in self.permissions or "admin:*" in self.permissions

        def grant_permission(self, perm: str) -> None:
            """Grant a permission to the admin."""
            if perm not in self.permissions:
                self.permissions.append(perm)

        def revoke_permission(self, perm: str) -> None:
            """Revoke a permission from the admin."""
            if perm in self.permissions:
                self.permissions.remove(perm)

        def to_dict(self) -> dict:
            """Serialize admin to dictionary."""
            base = super().to_dict()
            base["permissions"] = self.permissions
            return base


    def create_user(name: str, email: str, **kwargs) -> UserModel:
        """Factory function to create a UserModel."""
        return UserModel(name=name, email=email, **kwargs)


    def create_admin(name: str, email: str, permissions: Optional[List[str]] = None) -> AdminModel:
        """Factory function to create an AdminModel."""
        return AdminModel(
            name=name,
            email=email,
            role="admin",
            permissions=permissions or [],
        )


    # Module-level constants
    DEFAULT_ROLE = "user"
    ADMIN_ROLE = "admin"
    MAX_TAGS = 50
''')


class TestMultiDirectoryMultiRunPipeline:
    """Full auto-deps pipeline across multiple directories and multiple runs.

    Simulates a real-world auto-deps lifecycle using the real entry point
    (auto_deps_main) with real LLM calls:

    1. Write a prompt file to disk
    2. Run auto-deps scanning context/ — CSV written, output file written
    3. Run auto-deps scanning pdd/ — CSV accumulates entries from both dirs
    4. Run auto-deps re-scanning context/ — all cache hits, CSV preserved
    5. Modify a file, re-run — only modified file re-summarized
    6. Verify file I/O: output files and CSV on disk are correct

    Catches Bugs #1 (CSV wipeout), #2 (cache miss), #3 (path corruption).
    """

    @pytest.fixture
    def project(self, tmp_path):
        """Create a realistic multi-directory project with git repo."""
        # context/ directory — small example files
        context_dir = tmp_path / "context"
        context_dir.mkdir()
        (context_dir / "example.py").write_text(
            'def example_helper():\n    """Example helper function."""\n    return 42\n'
        )
        (context_dir / "helper.py").write_text(
            'def format_output(data):\n    """Format data for display."""\n    return str(data)\n'
        )

        # pdd/ directory — larger source files
        pdd_dir = tmp_path / "pdd"
        pdd_dir.mkdir()
        (pdd_dir / "cli.py").write_text(
            'import click\n\n@click.command()\ndef main():\n    """CLI entry point."""\n    pass\n'
        )
        (pdd_dir / "models.py").write_text(MODELS_PY)

        # Write the prompt file to disk (auto_deps_main reads it via construct_paths)
        prompt_content = textwrap.dedent("""\
            Generate a Python function that:
            - Uses the UserModel to validate users
            - Calls example_helper for demo output
        """)
        prompt_file = tmp_path / "test_module_python.prompt"
        prompt_file.write_text(prompt_content)

        _init_git_repo(tmp_path)
        return tmp_path, prompt_file

    def _make_ctx(self):
        """Create a Click context for auto_deps_main."""
        ctx = click.Context(click.Command("auto-deps"))
        ctx.obj = {
            "force": False,
            "quiet": True,
            "strength": DEFAULT_STRENGTH,
            "temperature": 0,
            "time": DEFAULT_TIME,
        }
        return ctx

    def _make_construct_paths(self, prompt_file, output_path, csv_path):
        """Create a construct_paths mock that returns our temp paths."""
        def mock_construct_paths(**kwargs):
            return (
                {},  # resolved_config
                {"prompt_file": prompt_file.read_text()},
                {"output": str(output_path), "csv": str(csv_path)},
                None,
            )
        return mock_construct_paths

    def test_multi_directory_multi_run_full_pipeline(self, project, monkeypatch):
        """Full lifecycle through auto_deps_main with real LLM calls:
        scan context/ → scan pdd/ → rescan context/ → modify + rescan.
        Verifies file I/O, CSV accumulation, path consistency, and caching."""
        _skip_unless_llm()
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

        tmp_path, prompt_file = project
        monkeypatch.chdir(tmp_path)

        output_path = tmp_path / "output.prompt"
        csv_path = tmp_path / "project_dependencies.csv"

        # Only mock construct_paths (project-config dependent) — everything else is real
        monkeypatch.setattr("pdd.auto_deps_main.construct_paths",
                            self._make_construct_paths(prompt_file, output_path, csv_path))

        # Wrap the real summarize llm_invoke to count calls
        from pdd.summarize_directory import llm_invoke as real_summarize_llm
        summarize_call_count = [0]
        def counting_summarize_llm(**kwargs):
            summarize_call_count[0] += 1
            return real_summarize_llm(**kwargs)
        monkeypatch.setattr("pdd.summarize_directory.llm_invoke", counting_summarize_llm)

        ctx = self._make_ctx()

        # ---- RUN 1: scan context/ via auto_deps_main ----
        print("\n  ---- RUN 1: scan context/ ----")
        modified_1, cost_1, model_1 = auto_deps_main(
            ctx=ctx,
            prompt_file=str(prompt_file),
            directory_path="context/",
            auto_deps_csv_path=None,
            output=str(output_path),
        )
        print(f"  Cost: ${cost_1:.4f}, Model: {model_1}")
        print(f"  Output: {modified_1[:200]}")

        # Verify file I/O
        assert output_path.exists(), "Output file should be written"
        assert csv_path.exists(), "CSV file should be written"

        # Verify CSV on disk has context/ entries
        csv_rows_1 = _parse_csv(csv_path.read_text())
        csv_paths_1 = {r["full_path"] for r in csv_rows_1}
        print(f"  CSV entries: {len(csv_rows_1)}, paths: {csv_paths_1}")
        assert any("example" in p for p in csv_paths_1), f"CSV should have example.py: {csv_paths_1}"
        assert any("helper" in p for p in csv_paths_1), f"CSV should have helper.py: {csv_paths_1}"

        # Should have summarized exactly 2 files
        assert summarize_call_count[0] == 2, (
            f"Run 1 should summarize 2 context/ files, got {summarize_call_count[0]}"
        )

        # Every entry should have non-empty file_summary and key_exports
        for row in csv_rows_1:
            assert row.get("file_summary", "").strip(), (
                f"Entry {row['full_path']} has empty file_summary"
            )

        # Every CSV entry should have valid content_hash and key_exports
        for row in csv_rows_1:
            assert row.get("content_hash", "").strip(), (
                f"Entry {row['full_path']} has empty content_hash"
            )
            # key_exports should be parseable JSON
            try:
                exports = json.loads(row.get("key_exports", "[]"))
                assert isinstance(exports, list), (
                    f"key_exports for {row['full_path']} is not a list: {row['key_exports']}"
                )
            except json.JSONDecodeError:
                pytest.fail(f"key_exports for {row['full_path']} is not valid JSON: {row['key_exports']}")

        # No duplicate entries in CSV
        assert len(csv_paths_1) == len(csv_rows_1), (
            f"CSV has duplicate entries: {len(csv_rows_1)} rows but {len(csv_paths_1)} unique paths"
        )

        # Output should have at least one <include> tag (LLM decided what to include)
        assert "<include" in modified_1, (
            f"Run 1 output should have at least one include tag. Got:\n{modified_1}"
        )

        # The original prompt text should be preserved in the output
        assert "UserModel" in modified_1, "Original prompt content should be preserved in output"

        # Include tags should reference files that actually exist
        include_paths_1 = re.findall(r'<include[^>]*>([^<]+)</include>', modified_1)
        for p in include_paths_1:
            p = p.strip()
            assert (tmp_path / p).exists(), (
                f"Include tag references non-existent file: {p}"
            )
            # Paths should be repo-root-relative, not absolute
            assert not os.path.isabs(p), f"Include path should be relative: {p}"

        # ---- RUN 2: scan pdd/ — CSV should accumulate both directories ----
        print("\n  ---- RUN 2: scan pdd/ ----")
        summarize_call_count[0] = 0
        prompt_file.write_text(modified_1)

        modified_2, cost_2, _ = auto_deps_main(
            ctx=ctx,
            prompt_file=str(prompt_file),
            directory_path="pdd/",
            auto_deps_csv_path=None,
            output=str(output_path),
        )
        print(f"  Cost: ${cost_2:.4f}")

        # BUG #1 check: CSV on disk should have entries from BOTH context/ and pdd/
        csv_rows_2 = _parse_csv(csv_path.read_text())
        all_paths_2 = {r["full_path"] for r in csv_rows_2}
        print(f"  CSV entries: {len(csv_rows_2)}, paths: {all_paths_2}")
        assert len(csv_rows_2) >= 4, (
            f"CSV should have >= 4 entries (2 context + 2 pdd), got {len(csv_rows_2)}. "
            f"Paths: {all_paths_2}. BUG #1: context/ entries were wiped."
        )
        assert any("example" in p for p in all_paths_2), (
            f"context/example.py missing from CSV after pdd/ scan. BUG #1 wipeout. Paths: {all_paths_2}"
        )

        # BUG #3 check: paths should be repo-root-relative, not double-prefixed
        for p in all_paths_2:
            assert not p.startswith("pdd/pdd/"), (
                f"Double-prefixed path found: {p}. BUG #3: path corruption."
            )
            assert not os.path.isabs(p), (
                f"Absolute path found in CSV: {p}. Paths should be repo-root-relative."
            )

        # Should have summarized exactly 2 new pdd/ files
        assert summarize_call_count[0] == 2, (
            f"Run 2 should summarize 2 pdd/ files, got {summarize_call_count[0]}"
        )

        # Verify output file on disk matches return value
        assert output_path.read_text() == modified_2

        # Include tags from run 1 should survive into run 2's output
        assert "<include" in modified_2, "Run 2 output should still have include tags"

        # Include tags should reference files that exist
        include_paths_2 = re.findall(r'<include[^>]*>([^<]+)</include>', modified_2)
        for p in include_paths_2:
            p = p.strip()
            assert (tmp_path / p).exists(), f"Include references non-existent file: {p}"
            assert not os.path.isabs(p), f"Include path should be relative: {p}"

        # No duplicate CSV entries
        assert len(all_paths_2) == len(csv_rows_2), (
            f"CSV has duplicates: {len(csv_rows_2)} rows, {len(all_paths_2)} unique paths"
        )

        # CSV entry count should not decrease from run 1
        assert len(csv_rows_2) >= len(csv_rows_1), (
            f"CSV shrank from {len(csv_rows_1)} to {len(csv_rows_2)} entries between runs"
        )

        # ---- RUN 3: rescan context/ — should be all cache hits ----
        print("\n  ---- RUN 3: rescan context/ (expect cache hits) ----")
        summarize_call_count[0] = 0
        prompt_file.write_text(modified_2)

        modified_3, _, _ = auto_deps_main(
            ctx=ctx,
            prompt_file=str(prompt_file),
            directory_path="context/",
            auto_deps_csv_path=None,
            output=str(output_path),
        )

        # BUG #2 check: summarize should NOT re-call LLM (all cache hits)
        assert summarize_call_count[0] == 0, (
            f"Run 3 should be all cache hits (0 summarize LLM calls), got {summarize_call_count[0]}. "
            "BUG #2: cache miss due to path inconsistency."
        )

        # BUG #1 check (reverse): pdd/ entries should still be in CSV on disk
        csv_rows_3 = _parse_csv(csv_path.read_text())
        all_paths_3 = {r["full_path"] for r in csv_rows_3}
        print(f"  CSV entries: {len(csv_rows_3)}, paths: {all_paths_3}")
        assert len(csv_rows_3) >= 4, (
            f"CSV should still have >= 4 entries after context/ rescan, got {len(csv_rows_3)}. "
            f"Paths: {all_paths_3}. BUG #1: pdd/ entries were wiped on context/ rescan."
        )

        # ---- RUN 4: modify a file and rescan — selective cache invalidation ----
        print("\n  ---- RUN 4: modify example.py, rescan context/ ----")
        modified_content = 'def example_helper():\n    """Modified helper."""\n    return 99\n'
        (tmp_path / "context" / "example.py").write_text(modified_content)
        subprocess.run(
            ["git", "add", "."], cwd=str(tmp_path), capture_output=True, check=True
        )
        subprocess.run(
            ["git", "commit", "-m", "modify example"],
            cwd=str(tmp_path), capture_output=True, check=True,
            env={**os.environ, "GIT_AUTHOR_NAME": "test", "GIT_AUTHOR_EMAIL": "t@t",
                 "GIT_COMMITTER_NAME": "test", "GIT_COMMITTER_EMAIL": "t@t"},
        )

        summarize_call_count[0] = 0
        prompt_file.write_text(modified_3)

        modified_4, _, _ = auto_deps_main(
            ctx=ctx,
            prompt_file=str(prompt_file),
            directory_path="context/",
            auto_deps_csv_path=None,
            output=str(output_path),
        )

        # Only the modified file should be re-summarized
        assert summarize_call_count[0] == 1, (
            f"Run 4 should re-summarize only 1 modified file, got {summarize_call_count[0]}."
        )

        # CSV on disk should still have all entries
        csv_rows_4 = _parse_csv(csv_path.read_text())
        print(f"  CSV entries: {len(csv_rows_4)}")
        assert len(csv_rows_4) >= 4, (
            f"CSV should still have >= 4 entries after modification, got {len(csv_rows_4)}."
        )

        # The modified file's content_hash should have changed
        example_row_before = next(
            (r for r in csv_rows_3 if "example" in r["full_path"]), None
        )
        example_row_after = next(
            (r for r in csv_rows_4 if "example" in r["full_path"]), None
        )
        assert example_row_before and example_row_after, (
            "example.py should be in CSV before and after modification"
        )
        assert example_row_before["content_hash"] != example_row_after["content_hash"], (
            "Modified file's content_hash should change in CSV"
        )

        # The un-modified file's content_hash should be unchanged
        helper_row_before = next(
            (r for r in csv_rows_3 if "helper" in r["full_path"]), None
        )
        helper_row_after = next(
            (r for r in csv_rows_4 if "helper" in r["full_path"]), None
        )
        assert helper_row_before and helper_row_after, (
            "helper.py should be in CSV before and after modification"
        )
        assert helper_row_before["content_hash"] == helper_row_after["content_hash"], (
            "Unmodified file's content_hash should NOT change"
        )

        # CSV entry count should never decrease
        assert len(csv_rows_4) >= len(csv_rows_3), (
            f"CSV shrank from {len(csv_rows_3)} to {len(csv_rows_4)} entries"
        )

        # Output file on disk should be updated
        assert output_path.read_text() == modified_4

        print("\n  All 4 runs passed.")
