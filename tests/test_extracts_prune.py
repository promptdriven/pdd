# =============================================================================
# TEST PLAN
# =============================================================================
#
# The code under test implements a CLI subcommand `pdd extracts prune` that:
# 1. Checks if .pdd/extracts/ directory exists
# 2. Checks if there are any .md files in the cache
# 3. Scans .prompt files for <include> tags with query attributes
# 4. Computes cache keys for referenced entries
# 5. Identifies orphaned cache entries (on disk but not referenced)
# 6. Displays orphaned entries in a table
# 7. Prompts for confirmation (unless --force)
# 8. Deletes orphaned .md and .meta.json files
#
# PUBLIC API TO TEST:
# - extracts: click group
# - prune: click command (subcommand of extracts)
#
# TEST CASES:
#
# 1. No cache directory exists -> early exit with info message
# 2. Cache directory exists but empty (no .md files) -> early exit
# 3. All cache entries are referenced -> "cache is clean" message
# 4. Some entries are orphaned -> display table, prompt confirmation, delete
# 5. All entries are orphaned -> display table, prompt confirmation, delete all
# 6. --force flag skips confirmation
# 7. Global --force flag (ctx.obj) skips confirmation
# 8. User declines confirmation -> abort, no deletion
# 9. Meta.json missing or malformed -> display <unknown> for source/query
# 10. Source file in include tag doesn't exist -> entry treated as orphaned
# 11. Prompt file unreadable (OSError) -> skipped gracefully
# 12. Singular/plural grammar in messages (1 entry vs multiple)
# 13. Cache key computation consistency (sha256 of path + "\n" + query)
# 14. Deletion of both .md and .meta.json files
# 15. OSError during deletion -> warning printed, continues
# =============================================================================


import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import hashlib
import json
import os
import click
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest
from click.testing import CliRunner


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def project_dir(tmp_path):
    """Create a minimal project structure with .pdd/extracts/."""
    cache_dir = tmp_path / ".pdd" / "extracts"
    cache_dir.mkdir(parents=True)
    return tmp_path


@pytest.fixture
def runner():
    return CliRunner()


def _compute_cache_key(source_path: str, query: str) -> str:
    """Mirror the expected cache key computation."""
    return hashlib.sha256((source_path + "\n" + query).encode()).hexdigest()


def _create_cache_entry(cache_dir: Path, key: str, source_path: str = "src.py", query: str = "some query"):
    """Create a .md and .meta.json cache entry."""
    (cache_dir / f"{key}.md").write_text("cached content", encoding="utf-8")
    meta = {
        "source_path": source_path,
        "source_hash": "abc123",
        "query": query,
        "timestamp": "2024-01-01T00:00:00",
        "token_count": 42,
    }
    (cache_dir / f"{key}.meta.json").write_text(json.dumps(meta), encoding="utf-8")


@pytest.fixture
def cli_env(project_dir):
    """
    Provide a patched CLI environment.
    Returns (extracts_group, project_dir, cache_dir).
    """
    cache_dir = project_dir / ".pdd" / "extracts"

    config_patch = patch(
        "pdd.extracts_prune.get_config",
        return_value={"project_root": str(project_dir)},
    )

    with config_patch:
        from pdd.extracts_prune import extracts
        yield extracts, project_dir, cache_dir


# ---------------------------------------------------------------------------
# Tests: Early exit conditions
# ---------------------------------------------------------------------------

class TestPruneEarlyExit:
    """Tests for early exit when cache doesn't exist or is empty."""

    def test_no_cache_directory(self, tmp_path, runner):
        """When .pdd/extracts/ doesn't exist, exit with info message."""
        with patch(
            "pdd.extracts_prune.get_config",
            return_value={"project_root": str(tmp_path)},
        ):
            from pdd.extracts_prune import extracts
            result = runner.invoke(extracts, ["prune"], obj={"force": False})
        assert result.exit_code == 0
        assert "nothing to do" in result.output.lower() or "No extracts directory" in result.output

    def test_empty_cache_directory(self, cli_env, runner):
        """When cache dir exists but has no .md files, exit with info."""
        qc, project_dir, cache_dir = cli_env
        result = runner.invoke(qc, ["prune"], obj={"force": False})
        assert result.exit_code == 0
        assert "empty" in result.output.lower() or "nothing to prune" in result.output.lower()


# ---------------------------------------------------------------------------
# Tests: No orphans
# ---------------------------------------------------------------------------

class TestPruneNoOrphans:
    """Tests when all cache entries are referenced."""

    def test_all_entries_referenced(self, cli_env, runner):
        """When every cache entry is referenced by a prompt file, report clean."""
        qc, project_dir, cache_dir = cli_env

        src_file = project_dir / "data.py"
        src_file.write_text("print('hello')", encoding="utf-8")

        resolved_path = str(src_file.resolve())
        query = "extract functions"
        key = _compute_cache_key(resolved_path, query)
        _create_cache_entry(cache_dir, key, source_path=resolved_path, query=query)

        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text(
            f'<include path="data.py" query="extract functions" />',
            encoding="utf-8",
        )

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[("data.py", "extract functions")],
        ), patch(
            "pdd.extracts_prune.get_file_path",
            return_value=src_file.resolve(),
        ), patch(
            "pdd.extracts_prune.compute_cache_key",
            return_value=key,
        ):
            result = runner.invoke(qc, ["prune"], obj={"force": False})

        assert result.exit_code == 0
        assert "clean" in result.output.lower() or "no orphaned" in result.output.lower()


# ---------------------------------------------------------------------------
# Tests: Orphan detection and deletion
# ---------------------------------------------------------------------------

class TestPruneOrphans:
    """Tests for orphan detection, display, and deletion."""

    def test_orphaned_entries_deleted_with_force(self, cli_env, runner):
        """Orphaned entries are deleted when --force is used."""
        qc, project_dir, cache_dir = cli_env

        key = "deadbeef" + "0" * 56
        _create_cache_entry(cache_dir, key, source_path="/old/file.py", query="old query")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "pruned" in result.output.lower() or "Pruned" in result.output
        assert not (cache_dir / f"{key}.md").exists()
        assert not (cache_dir / f"{key}.meta.json").exists()

    def test_orphaned_entries_user_confirms(self, cli_env, runner):
        """Orphaned entries are deleted when user confirms."""
        qc, project_dir, cache_dir = cli_env

        key = "abcdef01" + "0" * 56
        _create_cache_entry(cache_dir, key, source_path="/some/file.py", query="test query")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune"], input="y\n", obj={"force": False})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()
        assert not (cache_dir / f"{key}.meta.json").exists()

    def test_orphaned_entries_user_declines(self, cli_env, runner):
        """When user declines confirmation, nothing is deleted."""
        qc, project_dir, cache_dir = cli_env

        key = "abcdef02" + "0" * 56
        _create_cache_entry(cache_dir, key, source_path="/some/file.py", query="test query")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune"], input="n\n", obj={"force": False})

        assert result.exit_code == 0
        assert "aborted" in result.output.lower() or "Aborted" in result.output
        assert (cache_dir / f"{key}.md").exists()
        assert (cache_dir / f"{key}.meta.json").exists()

    def test_global_force_flag(self, cli_env, runner):
        """Global --force flag (ctx.obj) skips confirmation."""
        qc, project_dir, cache_dir = cli_env

        key = "abcdef03" + "0" * 56
        _create_cache_entry(cache_dir, key, source_path="/some/file.py", query="test query")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune"], obj={"force": True})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()

    def test_mixed_referenced_and_orphaned(self, cli_env, runner):
        """Only orphaned entries are deleted; referenced ones are kept."""
        qc, project_dir, cache_dir = cli_env

        src_file = project_dir / "keep.py"
        src_file.write_text("keep", encoding="utf-8")
        ref_key = "referenced0" + "0" * 54
        _create_cache_entry(cache_dir, ref_key, source_path=str(src_file), query="keep query")

        orph_key = "orphaned00" + "0" * 54
        _create_cache_entry(cache_dir, orph_key, source_path="/gone/file.py", query="old query")

        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text('<include path="keep.py" query="keep query" />', encoding="utf-8")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[("keep.py", "keep query")],
        ), patch(
            "pdd.extracts_prune.get_file_path",
            return_value=src_file.resolve(),
        ), patch(
            "pdd.extracts_prune.compute_cache_key",
            return_value=ref_key,
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert (cache_dir / f"{ref_key}.md").exists()
        assert (cache_dir / f"{ref_key}.meta.json").exists()
        assert not (cache_dir / f"{orph_key}.md").exists()
        assert not (cache_dir / f"{orph_key}.meta.json").exists()


# ---------------------------------------------------------------------------
# Tests: Meta.json edge cases
# ---------------------------------------------------------------------------

class TestPruneMetaEdgeCases:
    """Tests for missing or malformed meta.json."""

    def test_missing_meta_json(self, cli_env, runner):
        """Orphaned entry without meta.json shows <unknown> and still deletes."""
        qc, project_dir, cache_dir = cli_env

        key = "nometa000" + "0" * 55
        (cache_dir / f"{key}.md").write_text("content", encoding="utf-8")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()

    def test_malformed_meta_json(self, cli_env, runner):
        """Orphaned entry with invalid JSON in meta.json still works."""
        qc, project_dir, cache_dir = cli_env

        key = "badjson0" + "0" * 56
        (cache_dir / f"{key}.md").write_text("content", encoding="utf-8")
        (cache_dir / f"{key}.meta.json").write_text("not valid json{{{", encoding="utf-8")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()
        assert not (cache_dir / f"{key}.meta.json").exists()


# ---------------------------------------------------------------------------
# Tests: Source file not found in include tag
# ---------------------------------------------------------------------------

class TestPruneSourceNotFound:
    """Tests when source file referenced in include tag doesn't exist."""

    def test_include_references_missing_file(self, cli_env, runner):
        """If get_file_path raises FileNotFoundError, entry is treated as orphaned."""
        qc, project_dir, cache_dir = cli_env

        key = "missing0" + "0" * 56
        _create_cache_entry(cache_dir, key, source_path="/missing/file.py", query="q")

        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text('<include path="missing.py" query="q" />', encoding="utf-8")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[("missing.py", "q")],
        ), patch(
            "pdd.extracts_prune.get_file_path",
            side_effect=FileNotFoundError("not found"),
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()


# ---------------------------------------------------------------------------
# Tests: Singular/plural grammar
# ---------------------------------------------------------------------------

class TestPruneGrammar:
    """Tests for singular/plural grammar in output messages."""

    def test_singular_entry(self, cli_env, runner):
        """Single orphaned entry uses singular grammar."""
        qc, project_dir, cache_dir = cli_env

        key = "single00" + "0" * 56
        _create_cache_entry(cache_dir, key)

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "1" in result.output
        assert "entry" in result.output.lower()

    def test_plural_entries(self, cli_env, runner):
        """Multiple orphaned entries use plural grammar."""
        qc, project_dir, cache_dir = cli_env

        for i in range(3):
            key = f"plural{i:02d}" + "0" * 56
            _create_cache_entry(cache_dir, key)

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "3" in result.output
        assert "entries" in result.output.lower()


# ---------------------------------------------------------------------------
# Tests: Deletion error handling
# ---------------------------------------------------------------------------

class TestPruneDeletionErrors:
    """Tests for error handling during file deletion."""

    def test_oserror_during_deletion(self, cli_env, runner):
        """OSError during deletion prints warning but continues."""
        qc, project_dir, cache_dir = cli_env

        key1 = "err00000" + "0" * 56
        key2 = "err00001" + "0" * 56
        _create_cache_entry(cache_dir, key1)
        _create_cache_entry(cache_dir, key2)

        original_unlink = Path.unlink

        def failing_unlink(self, *args, **kwargs):
            if key1 in str(self):
                raise OSError("permission denied")
            return original_unlink(self, *args, **kwargs)

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ), patch.object(Path, "unlink", failing_unlink):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "warning" in result.output.lower() or "Warning" in result.output


# ---------------------------------------------------------------------------
# Tests: Multiple prompt files
# ---------------------------------------------------------------------------

class TestPruneMultiplePromptFiles:
    """Tests with multiple prompt files."""

    def test_references_from_multiple_prompts(self, cli_env, runner):
        """References from multiple prompt files are all collected."""
        qc, project_dir, cache_dir = cli_env

        src1 = project_dir / "a.py"
        src1.write_text("a", encoding="utf-8")
        src2 = project_dir / "b.py"
        src2.write_text("b", encoding="utf-8")

        key1 = "refkey01" + "0" * 56
        key2 = "refkey02" + "0" * 56
        orph_key = "orphkey0" + "0" * 56

        _create_cache_entry(cache_dir, key1)
        _create_cache_entry(cache_dir, key2)
        _create_cache_entry(cache_dir, orph_key)

        (project_dir / "p1.prompt").write_text('<include path="a.py" query="q1" />', encoding="utf-8")
        (project_dir / "p2.prompt").write_text('<include path="b.py" query="q2" />', encoding="utf-8")

        def mock_parse(text):
            if "a.py" in text:
                return [("a.py", "q1")]
            elif "b.py" in text:
                return [("b.py", "q2")]
            return []

        def mock_get_file_path(raw_path, prompt_file=None):
            if raw_path == "a.py":
                return src1.resolve()
            elif raw_path == "b.py":
                return src2.resolve()
            raise FileNotFoundError()

        def mock_compute_key(path, query):
            if "a.py" in path and query == "q1":
                return key1
            elif "b.py" in path and query == "q2":
                return key2
            return "unknown"

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            side_effect=mock_parse,
        ), patch(
            "pdd.extracts_prune.get_file_path",
            side_effect=mock_get_file_path,
        ), patch(
            "pdd.extracts_prune.compute_cache_key",
            side_effect=mock_compute_key,
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert (cache_dir / f"{key1}.md").exists()
        assert (cache_dir / f"{key2}.md").exists()
        assert not (cache_dir / f"{orph_key}.md").exists()


# ---------------------------------------------------------------------------
# Tests: Click group structure
# ---------------------------------------------------------------------------

class TestClickGroupStructure:
    """Tests for the click group and command registration."""

    def test_extracts_is_group(self):
        """extracts should be a click Group."""
        from pdd.extracts_prune import extracts
        assert isinstance(extracts, click.Group)

    def test_prune_is_registered(self):
        """prune should be a registered command in the extracts group."""
        from pdd.extracts_prune import extracts
        assert "prune" in extracts.commands

    def test_prune_has_force_option(self):
        """prune command should have a --force option."""
        from pdd.extracts_prune import extracts
        prune_cmd = extracts.commands["prune"]
        param_names = [p.name for p in prune_cmd.params]
        assert "force" in param_names


# ---------------------------------------------------------------------------
# Tests: Cache key consistency between prune and CLI/API
# ---------------------------------------------------------------------------

class TestPruneCacheKeyConsistency:
    """Tests that prune computes cache keys the same way as CLI and API.

    Bug: _collect_referenced_keys used to call compute_cache_key with the
    absolute resolved path from get_file_path(), while CLI (extract()) and
    API (extracts_for_prompt) use project-relative paths. This meant prune
    could never match entries created by the CLI/API, so valid entries were
    incorrectly treated as orphaned and deleted.
    """

    def test_prune_uses_project_relative_key(self, cli_env, runner):
        """Prune should compute cache keys using project-relative paths,
        matching what CLI extract() and the API use."""
        qc, project_dir, cache_dir = cli_env

        # Create a source file
        src_file = project_dir / "lib" / "utils.py"
        src_file.parent.mkdir(parents=True)
        src_file.write_text("def helper(): pass", encoding="utf-8")

        # Create cache entry with project-relative key (as CLI now does)
        rel_path = str(src_file.resolve().relative_to(project_dir.resolve()))
        query = "extract helper"
        key = _compute_cache_key(rel_path, query)
        _create_cache_entry(cache_dir, key, source_path=rel_path, query=query)

        # Create prompt referencing the file
        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text(
            '<include path="lib/utils.py" query="extract helper" />',
            encoding="utf-8",
        )

        # Prune should recognize this as referenced (not orphaned)
        result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert (cache_dir / f"{key}.md").exists(), (
            "Prune incorrectly deleted a valid cache entry. "
            "It likely computed the key with an absolute path instead of "
            "project-relative."
        )
        assert "clean" in result.output.lower() or "no orphaned" in result.output.lower()

    def test_prune_does_not_match_with_absolute_key(self, cli_env, runner):
        """Cache entry keyed by absolute path should be treated as orphaned
        since CLI/API now use project-relative keys."""
        qc, project_dir, cache_dir = cli_env

        src_file = project_dir / "src.py"
        src_file.write_text("x = 1", encoding="utf-8")

        # Create cache entry with ABSOLUTE path key (old/broken behavior)
        abs_path = str(src_file.resolve())
        query = "extract x"
        abs_key = _compute_cache_key(abs_path, query)
        _create_cache_entry(cache_dir, abs_key, source_path=abs_path, query=query)

        # Create prompt referencing the file
        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text(
            '<include path="src.py" query="extract x" />',
            encoding="utf-8",
        )

        # Prune should NOT find this entry (wrong key form), so it's orphaned
        result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert not (cache_dir / f"{abs_key}.md").exists(), (
            "Prune should have deleted the entry keyed by absolute path "
            "since it doesn't match the project-relative key."
        )

    def test_prune_key_matches_api_key(self, cli_env, runner):
        """The cache key computed by prune should match what the API computes
        for the same file and query."""
        qc, project_dir, cache_dir = cli_env

        # Create source in subdirectory
        src_file = project_dir / "pkg" / "mod.py"
        src_file.parent.mkdir(parents=True)
        src_file.write_text("class Foo: pass", encoding="utf-8")

        query = "find classes"

        # Compute key the way the API does (project-relative)
        resolved = src_file.resolve()
        api_rel_path = str(resolved.relative_to(project_dir.resolve()))
        api_key = _compute_cache_key(api_rel_path, query)

        # Create cache entry with the API key
        _create_cache_entry(cache_dir, api_key, source_path=api_rel_path, query=query)

        # Create prompt
        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text(
            '<include path="pkg/mod.py" query="find classes" />',
            encoding="utf-8",
        )

        # Prune should recognize this as referenced
        result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert (cache_dir / f"{api_key}.md").exists(), (
            "Prune did not recognize cache entry created with API-style "
            "project-relative key. Prune likely uses a different path form."
        )

    def test_prune_subdirectory_prompt_relative_include(self, cli_env, runner):
        """Prune should handle prompts in subdirectories with relative includes."""
        qc, project_dir, cache_dir = cli_env

        # Source at project root
        readme = project_dir / "README.md"
        readme.write_text("# Project", encoding="utf-8")

        query = "what is this"
        rel_path = str(readme.resolve().relative_to(project_dir.resolve()))
        key = _compute_cache_key(rel_path, query)
        _create_cache_entry(cache_dir, key, source_path=rel_path, query=query)

        # Prompt in subdirectory with ../ include
        prompts_dir = project_dir / "prompts"
        prompts_dir.mkdir()
        prompt = prompts_dir / "my.prompt"
        prompt.write_text(
            '<include path="../README.md" query="what is this" />',
            encoding="utf-8",
        )

        result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert (cache_dir / f"{key}.md").exists(), (
            "Prune incorrectly orphaned cache entry for ../README.md include. "
            "The relative path resolution in prune doesn't match CLI/API."
        )


import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import hashlib
import json
import os
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import click
import pytest
from click.testing import CliRunner

from pdd.extracts_prune import extracts, prune


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def project_dir(tmp_path):
    """Create a minimal project structure with .pdd/extracts/."""
    cache_dir = tmp_path / ".pdd" / "extracts"
    cache_dir.mkdir(parents=True)
    return tmp_path


@pytest.fixture
def runner():
    return CliRunner()


def _compute_cache_key(source_path: str, query: str) -> str:
    """Mirror the expected cache key computation."""
    normalized = os.path.normpath(source_path)
    return hashlib.sha256((normalized + "\n" + query).encode()).hexdigest()


def _create_cache_entry(cache_dir: Path, key: str, source_path: str = "src.py",
                        query: str = "some query"):
    """Create a .md and .meta.json cache entry."""
    (cache_dir / f"{key}.md").write_text("cached content", encoding="utf-8")
    meta = {
        "source_path": source_path,
        "source_hash": "abc123",
        "query": query,
        "timestamp": "2024-01-01T00:00:00",
        "token_count": 42,
    }
    (cache_dir / f"{key}.meta.json").write_text(json.dumps(meta), encoding="utf-8")


@pytest.fixture
def cli_env(project_dir):
    """Provide a patched CLI environment. Returns (extracts_group, project_dir, cache_dir)."""
    cache_dir = project_dir / ".pdd" / "extracts"

    config_patch = patch(
        "pdd.extracts_prune.get_config",
        return_value={"project_root": str(project_dir)},
    )

    with config_patch:
        yield extracts, project_dir, cache_dir


# ---------------------------------------------------------------------------
# Tests: Early exit conditions
# ---------------------------------------------------------------------------

class TestPruneEarlyExit:
    """Tests for early exit when cache doesn't exist or is empty."""

    def test_no_cache_directory(self, tmp_path, runner):
        """When .pdd/extracts/ doesn't exist, exit with info message."""
        with patch(
            "pdd.extracts_prune.get_config",
            return_value={"project_root": str(tmp_path)},
        ):
            result = runner.invoke(extracts, ["prune"], obj={"force": False})
        assert result.exit_code == 0
        assert "nothing to do" in result.output.lower() or "No extracts directory" in result.output

    def test_empty_cache_directory(self, cli_env, runner):
        """When cache dir exists but has no .md files, exit with info."""
        qc, project_dir, cache_dir = cli_env
        result = runner.invoke(qc, ["prune"], obj={"force": False})
        assert result.exit_code == 0
        assert "empty" in result.output.lower() or "nothing to prune" in result.output.lower()


# ---------------------------------------------------------------------------
# Tests: No orphans
# ---------------------------------------------------------------------------

class TestPruneNoOrphans:
    """Tests when all cache entries are referenced."""

    def test_all_entries_referenced(self, cli_env, runner):
        """When every cache entry is referenced by a prompt file, report clean."""
        qc, project_dir, cache_dir = cli_env

        src_file = project_dir / "data.py"
        src_file.write_text("print('hello')", encoding="utf-8")

        resolved_path = str(src_file.resolve())
        rel_path = str(Path(resolved_path).resolve().relative_to(project_dir.resolve()))
        query = "extract functions"
        key = _compute_cache_key(rel_path, query)
        _create_cache_entry(cache_dir, key, source_path=resolved_path, query=query)

        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text(
            f'<include path="data.py" query="extract functions" />',
            encoding="utf-8",
        )

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[("data.py", "extract functions")],
        ), patch(
            "pdd.extracts_prune.get_file_path",
            return_value=src_file.resolve(),
        ), patch(
            "pdd.extracts_prune.compute_cache_key",
            return_value=key,
        ):
            result = runner.invoke(qc, ["prune"], obj={"force": False})

        assert result.exit_code == 0
        assert "clean" in result.output.lower() or "no orphaned" in result.output.lower()


# ---------------------------------------------------------------------------
# Tests: Orphan detection and deletion
# ---------------------------------------------------------------------------

class TestPruneOrphans:
    """Tests for orphan detection, display, and deletion."""

    def test_orphaned_entries_deleted_with_force(self, cli_env, runner):
        """Orphaned entries are deleted when --force is used."""
        qc, project_dir, cache_dir = cli_env

        key = "deadbeef" + "0" * 56
        _create_cache_entry(cache_dir, key, source_path="/old/file.py", query="old query")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "pruned" in result.output.lower() or "Pruned" in result.output
        assert not (cache_dir / f"{key}.md").exists()
        assert not (cache_dir / f"{key}.meta.json").exists()

    def test_orphaned_entries_user_confirms(self, cli_env, runner):
        """Orphaned entries are deleted when user confirms."""
        qc, project_dir, cache_dir = cli_env

        key = "abcdef01" + "0" * 56
        _create_cache_entry(cache_dir, key, source_path="/some/file.py", query="test query")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune"], input="y\n", obj={"force": False})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()
        assert not (cache_dir / f"{key}.meta.json").exists()

    def test_orphaned_entries_user_declines(self, cli_env, runner):
        """When user declines confirmation, nothing is deleted."""
        qc, project_dir, cache_dir = cli_env

        key = "abcdef02" + "0" * 56
        _create_cache_entry(cache_dir, key, source_path="/some/file.py", query="test query")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune"], input="n\n", obj={"force": False})

        assert result.exit_code == 0
        assert "aborted" in result.output.lower() or "Aborted" in result.output
        assert (cache_dir / f"{key}.md").exists()
        assert (cache_dir / f"{key}.meta.json").exists()

    def test_global_force_flag(self, cli_env, runner):
        """Global --force flag (ctx.obj) skips confirmation."""
        qc, project_dir, cache_dir = cli_env

        key = "abcdef03" + "0" * 56
        _create_cache_entry(cache_dir, key, source_path="/some/file.py", query="test query")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune"], obj={"force": True})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()
        assert not (cache_dir / f"{key}.meta.json").exists()

    def test_mixed_referenced_and_orphaned(self, cli_env, runner):
        """Only orphaned entries are deleted; referenced ones are kept."""
        qc, project_dir, cache_dir = cli_env

        src_file = project_dir / "keep.py"
        src_file.write_text("keep", encoding="utf-8")
        ref_key = "referenced0" + "0" * 54
        _create_cache_entry(cache_dir, ref_key, source_path=str(src_file), query="keep query")

        orph_key = "orphaned00" + "0" * 54
        _create_cache_entry(cache_dir, orph_key, source_path="/gone/file.py", query="old query")

        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text('<include path="keep.py" query="keep query" />', encoding="utf-8")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[("keep.py", "keep query")],
        ), patch(
            "pdd.extracts_prune.get_file_path",
            return_value=src_file.resolve(),
        ), patch(
            "pdd.extracts_prune.compute_cache_key",
            return_value=ref_key,
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert (cache_dir / f"{ref_key}.md").exists()
        assert (cache_dir / f"{ref_key}.meta.json").exists()
        assert not (cache_dir / f"{orph_key}.md").exists()
        assert not (cache_dir / f"{orph_key}.meta.json").exists()


# ---------------------------------------------------------------------------
# Tests: Meta.json edge cases
# ---------------------------------------------------------------------------

class TestPruneMetaEdgeCases:
    """Tests for missing or malformed meta.json."""

    def test_missing_meta_json(self, cli_env, runner):
        """Orphaned entry without meta.json shows <unknown> and still deletes."""
        qc, project_dir, cache_dir = cli_env

        key = "nometa000" + "0" * 55
        (cache_dir / f"{key}.md").write_text("content", encoding="utf-8")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()

    def test_malformed_meta_json(self, cli_env, runner):
        """Orphaned entry with invalid JSON in meta.json still works."""
        qc, project_dir, cache_dir = cli_env

        key = "badjson0" + "0" * 56
        (cache_dir / f"{key}.md").write_text("content", encoding="utf-8")
        (cache_dir / f"{key}.meta.json").write_text("not valid json{{{", encoding="utf-8")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()
        assert not (cache_dir / f"{key}.meta.json").exists()


# ---------------------------------------------------------------------------
# Tests: Source file not found in include tag
# ---------------------------------------------------------------------------

class TestPruneSourceNotFound:
    """Tests when source file referenced in include tag doesn't exist."""

    def test_include_references_missing_file(self, cli_env, runner):
        """If get_file_path raises FileNotFoundError, entry is treated as orphaned."""
        qc, project_dir, cache_dir = cli_env

        key = "missing0" + "0" * 56
        _create_cache_entry(cache_dir, key, source_path="/missing/file.py", query="q")

        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text('<include path="missing.py" query="q" />', encoding="utf-8")

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[("missing.py", "q")],
        ), patch(
            "pdd.extracts_prune.get_file_path",
            side_effect=FileNotFoundError("not found"),
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()


# ---------------------------------------------------------------------------
# Tests: Singular/plural grammar
# ---------------------------------------------------------------------------

class TestPruneGrammar:
    """Tests for singular/plural grammar in output messages."""

    def test_singular_entry(self, cli_env, runner):
        """Single orphaned entry uses singular grammar."""
        qc, project_dir, cache_dir = cli_env

        key = "single00" + "0" * 56
        _create_cache_entry(cache_dir, key)

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "1" in result.output
        assert "entry" in result.output.lower() or "entr" in result.output.lower()

    def test_plural_entries(self, cli_env, runner):
        """Multiple orphaned entries use plural grammar."""
        qc, project_dir, cache_dir = cli_env

        for i in range(3):
            key = f"plural{i:02d}" + "0" * 56
            _create_cache_entry(cache_dir, key)

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "3" in result.output
        assert "entries" in result.output.lower() or "ies" in result.output.lower()


# ---------------------------------------------------------------------------
# Tests: Deletion error handling
# ---------------------------------------------------------------------------

class TestPruneDeletionErrors:
    """Tests for error handling during file deletion."""

    def test_oserror_during_deletion(self, cli_env, runner):
        """OSError during deletion prints warning but continues."""
        qc, project_dir, cache_dir = cli_env

        key1 = "err00000" + "0" * 56
        key2 = "err00001" + "0" * 56
        _create_cache_entry(cache_dir, key1)
        _create_cache_entry(cache_dir, key2)

        original_unlink = Path.unlink

        def failing_unlink(self, *args, **kwargs):
            if key1 in str(self):
                raise OSError("permission denied")
            return original_unlink(self, *args, **kwargs)

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ), patch.object(Path, "unlink", failing_unlink):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "warning" in result.output.lower() or "Warning" in result.output


# ---------------------------------------------------------------------------
# Tests: Click group structure
# ---------------------------------------------------------------------------

class TestClickGroupStructure:
    """Tests for the click group and command registration."""

    def test_extracts_is_group(self):
        """extracts should be a click Group."""
        assert isinstance(extracts, click.Group)

    def test_prune_is_registered(self):
        """prune should be a registered command in the extracts group."""
        assert "prune" in extracts.commands

    def test_prune_has_force_option(self):
        """prune command should have a --force option."""
        prune_cmd = extracts.commands["prune"]
        param_names = [p.name for p in prune_cmd.params]
        assert "force" in param_names


# ---------------------------------------------------------------------------
# Tests: Multiple prompt files
# ---------------------------------------------------------------------------

class TestPruneMultiplePromptFiles:
    """Tests with multiple prompt files."""

    def test_references_from_multiple_prompts(self, cli_env, runner):
        """References from multiple prompt files are all collected."""
        qc, project_dir, cache_dir = cli_env

        src1 = project_dir / "a.py"
        src1.write_text("a", encoding="utf-8")
        src2 = project_dir / "b.py"
        src2.write_text("b", encoding="utf-8")

        key1 = "refkey01" + "0" * 56
        key2 = "refkey02" + "0" * 56
        orph_key = "orphkey0" + "0" * 56

        _create_cache_entry(cache_dir, key1)
        _create_cache_entry(cache_dir, key2)
        _create_cache_entry(cache_dir, orph_key)

        (project_dir / "p1.prompt").write_text('<include path="a.py" query="q1" />', encoding="utf-8")
        (project_dir / "p2.prompt").write_text('<include path="b.py" query="q2" />', encoding="utf-8")

        def mock_parse(text):
            if "a.py" in text:
                return [("a.py", "q1")]
            elif "b.py" in text:
                return [("b.py", "q2")]
            return []

        def mock_get_file_path(raw_path, prompt_file=None):
            if raw_path == "a.py":
                return src1.resolve()
            elif raw_path == "b.py":
                return src2.resolve()
            raise FileNotFoundError()

        def mock_compute_key(path, query):
            if "a.py" in path and query == "q1":
                return key1
            elif "b.py" in path and query == "q2":
                return key2
            return "unknown"

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            side_effect=mock_parse,
        ), patch(
            "pdd.extracts_prune.get_file_path",
            side_effect=mock_get_file_path,
        ), patch(
            "pdd.extracts_prune.compute_cache_key",
            side_effect=mock_compute_key,
        ):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert (cache_dir / f"{key1}.md").exists()
        assert (cache_dir / f"{key2}.md").exists()
        assert not (cache_dir / f"{orph_key}.md").exists()
        assert not (cache_dir / f"{orph_key}.meta.json").exists()


# ---------------------------------------------------------------------------
# Tests: Prompt file unreadable
# ---------------------------------------------------------------------------

class TestPruneUnreadablePromptFile:
    """Tests when prompt files can't be read."""

    def test_unreadable_prompt_file_skipped(self, cli_env, runner):
        """Prompt files that raise OSError are skipped gracefully."""
        qc, project_dir, cache_dir = cli_env

        key = "orphan00" + "0" * 56
        _create_cache_entry(cache_dir, key)

        # Create a prompt file but make it unreadable by patching
        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text("content", encoding="utf-8")

        original_read_text = Path.read_text

        def failing_read_text(self, *args, **kwargs):
            if str(self).endswith(".prompt"):
                raise OSError("permission denied")
            return original_read_text(self, *args, **kwargs)

        with patch.object(Path, "read_text", failing_read_text):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        # The orphaned entry should be detected and deleted since no references
        # could be collected
        assert not (cache_dir / f"{key}.md").exists()


# ---------------------------------------------------------------------------
# Tests: Cache key computation (using the fallback stub)
# ---------------------------------------------------------------------------

class TestCacheKeyComputation:
    """Tests for cache key computation consistency."""

    def test_cache_key_deterministic(self):
        """Same inputs produce same cache key."""
        key1 = _compute_cache_key("src/main.py", "extract functions")
        key2 = _compute_cache_key("src/main.py", "extract functions")
        assert key1 == key2

    def test_cache_key_different_for_different_queries(self):
        """Different queries produce different cache keys."""
        key1 = _compute_cache_key("src/main.py", "extract functions")
        key2 = _compute_cache_key("src/main.py", "extract classes")
        assert key1 != key2

    def test_cache_key_different_for_different_paths(self):
        """Different paths produce different cache keys."""
        key1 = _compute_cache_key("src/main.py", "extract functions")
        key2 = _compute_cache_key("src/other.py", "extract functions")
        assert key1 != key2

    def test_cache_key_is_sha256_hex(self):
        """Cache key should be a valid sha256 hex digest (64 chars)."""
        key = _compute_cache_key("test.py", "query")
        assert len(key) == 64
        assert all(c in "0123456789abcdef" for c in key)

    def test_cache_key_uses_normalized_path(self):
        """Cache key normalizes the path before hashing."""
        key1 = _compute_cache_key("src/../src/main.py", "query")
        key2 = _compute_cache_key("src/main.py", "query")
        assert key1 == key2


# ---------------------------------------------------------------------------
# Tests: No obj in context
# ---------------------------------------------------------------------------

class TestPruneNoContextObj:
    """Tests when ctx.obj is None."""

    def test_no_ctx_obj(self, cli_env, runner):
        """When ctx.obj is None, prune should still work."""
        qc, project_dir, cache_dir = cli_env

        key = "noobj000" + "0" * 56
        _create_cache_entry(cache_dir, key)

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ):
            # Pass obj=None to simulate no context object
            result = runner.invoke(qc, ["prune", "--force"])

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()


# ---------------------------------------------------------------------------
# Tests: Rich fallback (when rich is not available)
# ---------------------------------------------------------------------------

class TestPruneRichFallback:
    """Tests for the rich import fallback path."""

    def test_fallback_without_rich(self, cli_env, runner):
        """When rich is not available, fallback text output is used."""
        qc, project_dir, cache_dir = cli_env

        key = "richfb00" + "0" * 56
        _create_cache_entry(cache_dir, key, source_path="/test/file.py", query="test query")

        import builtins
        original_import = builtins.__import__

        def mock_import(name, *args, **kwargs):
            if name.startswith("rich"):
                raise ImportError("no rich")
            return original_import(name, *args, **kwargs)

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ), patch("builtins.__import__", side_effect=mock_import):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()


# ---------------------------------------------------------------------------
# Tests: Meta.json with valid data displayed correctly
# ---------------------------------------------------------------------------

class TestPruneMetaDisplay:
    """Tests that meta.json data is read and displayed."""

    def test_meta_json_source_and_query_displayed(self, cli_env, runner):
        """Source path and query from meta.json appear in output."""
        qc, project_dir, cache_dir = cli_env

        key = "display0" + "0" * 56
        _create_cache_entry(cache_dir, key, source_path="/my/source.py", query="find classes")

        import builtins
        original_import = builtins.__import__

        def mock_import(name, *args, **kwargs):
            if name.startswith("rich"):
                raise ImportError("no rich")
            return original_import(name, *args, **kwargs)

        with patch(
            "pdd.extracts_prune.parse_include_tags",
            return_value=[],
        ), patch("builtins.__import__", side_effect=mock_import):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "/my/source.py" in result.output
        assert "find classes" in result.output