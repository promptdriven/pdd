# =============================================================================
# TEST PLAN – pdd extracts prune
# =============================================================================
#
# Tests the `pdd extracts prune` CLI subcommand against prompt requirements:
#
# 1. Structure: `extracts` is a click.Group, `prune` is a subcommand with --force
# 2. Scanning: Scans .prompt files for include tags with queries
# 3. Cache Keys: Computes expected cache key using project-relative path + query
# 4. Orphans: Identifies .md files in .pdd/extracts/ not in the referenced set
# 5. Display: Shows orphaned entries (Key, Source Path, Query) in a table
# 6. Safety: Prompts for confirmation; skip with --force or ctx.obj["force"]
# 7. Deletion: Deletes both .md and .meta.json for each orphan
# 8. Testing Support: try/except ImportError stubs for pdd imports
#
# MOCKING STRATEGY:
# - Mock `pdd.extracts_prune.get_config` (external dependency)
# - Mock `pdd.extracts_prune.compute_cache_key` (external dependency from pdd.preprocess)
# - Mock `pdd.extracts_prune.parse_include_tags` (external dependency from pdd.preprocess)
# - Do NOT mock internal functions like _collect_referenced_keys, _cache_dir, etc.
# =============================================================================

import sys
from pathlib import Path

project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import hashlib
import json

import click
import pytest
from click.testing import CliRunner
from unittest.mock import patch


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _compute_cache_key(source_path: str, query: str) -> str:
    """Mirror the expected cache key formula: sha256(normpath(path) + '\\n' + query)."""
    import os
    normalized = os.path.normpath(source_path)
    return hashlib.sha256((normalized + "\n" + query).encode()).hexdigest()


def _create_cache_entry(
    cache_dir: Path, key: str, source_path: str = "src.py", query: str = "some query"
):
    """Create a .md and .meta.json cache entry pair."""
    (cache_dir / f"{key}.md").write_text("cached content", encoding="utf-8")
    meta = {
        "source_path": source_path,
        "source_hash": "abc123",
        "query": query,
        "timestamp": "2024-01-01T00:00:00",
        "token_count": 42,
    }
    (cache_dir / f"{key}.meta.json").write_text(
        json.dumps(meta), encoding="utf-8"
    )


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def runner():
    return CliRunner()


@pytest.fixture
def project_dir(tmp_path):
    """Create a minimal project with .pdd/extracts/."""
    cache_dir = tmp_path / ".pdd" / "extracts"
    cache_dir.mkdir(parents=True)
    return tmp_path


@pytest.fixture
def cli_env(project_dir):
    """Provide a patched CLI environment.

    Yields (extracts_group, project_dir, cache_dir).
    """
    cache_dir = project_dir / ".pdd" / "extracts"
    with patch(
        "pdd.extracts_prune.get_config",
        return_value={"project_root": str(project_dir)},
    ):
        from pdd.extracts_prune import extracts
        yield extracts, project_dir, cache_dir


# ===========================================================================
# 1. Structure – click group & command registration
# ===========================================================================

class TestClickGroupStructure:
    def test_extracts_is_group(self):
        from pdd.extracts_prune import extracts
        assert isinstance(extracts, click.Group)

    def test_prune_is_registered(self):
        from pdd.extracts_prune import extracts
        assert "prune" in extracts.commands

    def test_prune_has_force_option(self):
        from pdd.extracts_prune import extracts
        prune_cmd = extracts.commands["prune"]
        param_names = [p.name for p in prune_cmd.params]
        assert "force" in param_names


# ===========================================================================
# 2 & 3. Scanning + Cache Keys – project-relative path hashing
# ===========================================================================

class TestPruneCacheKeyConsistency:
    """Prune must compute keys using project-relative paths, matching CLI/API."""

    def test_prune_uses_project_relative_key(self, cli_env, runner):
        qc, project_dir, cache_dir = cli_env

        src_file = project_dir / "lib" / "utils.py"
        src_file.parent.mkdir(parents=True)
        src_file.write_text("def helper(): pass", encoding="utf-8")

        rel_path = str(src_file.resolve().relative_to(project_dir.resolve()))
        query = "extract helper"
        key = _compute_cache_key(rel_path, query)
        _create_cache_entry(cache_dir, key, source_path=rel_path, query=query)

        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text(
            '<include query="extract helper">lib/utils.py</include>',
            encoding="utf-8",
        )

        result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})
        assert result.exit_code == 0
        assert (cache_dir / f"{key}.md").exists(), (
            "Prune incorrectly deleted a valid cache entry – "
            "likely computed the key with an absolute path."
        )

    def test_absolute_keyed_entry_is_orphaned(self, cli_env, runner):
        """Entry keyed by absolute path should be treated as orphaned."""
        qc, project_dir, cache_dir = cli_env

        src_file = project_dir / "src.py"
        src_file.write_text("x = 1", encoding="utf-8")

        abs_path = str(src_file.resolve())
        query = "extract x"
        abs_key = _compute_cache_key(abs_path, query)
        _create_cache_entry(cache_dir, abs_key, source_path=abs_path, query=query)

        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text(
            '<include query="extract x">src.py</include>',
            encoding="utf-8",
        )

        result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})
        assert result.exit_code == 0
        assert not (cache_dir / f"{abs_key}.md").exists()

    def test_subdirectory_prompt_relative_include(self, cli_env, runner):
        """Prompt in subdirectory with ../ include resolves correctly."""
        qc, project_dir, cache_dir = cli_env

        readme = project_dir / "README.md"
        readme.write_text("# Project", encoding="utf-8")

        query = "what is this"
        rel_path = str(readme.resolve().relative_to(project_dir.resolve()))
        key = _compute_cache_key(rel_path, query)
        _create_cache_entry(cache_dir, key, source_path=rel_path, query=query)

        prompts_dir = project_dir / "prompts"
        prompts_dir.mkdir()
        prompt = prompts_dir / "my.prompt"
        prompt.write_text(
            '<include query="what is this">../README.md</include>',
            encoding="utf-8",
        )

        result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})
        assert result.exit_code == 0
        assert (cache_dir / f"{key}.md").exists()

    def test_subdirectory_prompt_with_project_root_relative_path(self, cli_env, runner):
        """Prompt in a subdirectory using project-root-relative paths in include tags.

        Reproduces the bug where auto-deps inserts paths like
        <include query="...">subdir/file.py</include> into a prompt that
        itself lives inside subdir/. The path is project-root-relative (as
        created by include_query_extractor via get_file_path / PathResolver),
        but prune was only trying prompt-parent-relative resolution, producing
        subdir/subdir/file.py which doesn't exist.
        """
        qc, project_dir, cache_dir = cli_env

        # Create source files in a subdirectory
        subdir = project_dir / "myapp"
        subdir.mkdir()
        src_file = subdir / "utils.py"
        src_file.write_text("def helper(): pass", encoding="utf-8")

        # Cache key uses project-relative path (how include_query_extractor creates it)
        rel_path = str(src_file.resolve().relative_to(project_dir.resolve()))
        assert rel_path == "myapp/utils.py"
        query = "extract helper function"
        key = _compute_cache_key(rel_path, query)
        _create_cache_entry(cache_dir, key, source_path=rel_path, query=query)

        # Prompt lives in the SAME subdirectory but uses project-root-relative path
        # (this is what auto-deps produces)
        prompt = subdir / "my.prompt"
        prompt.write_text(
            '<include query="extract helper function">myapp/utils.py</include>',
            encoding="utf-8",
        )

        result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})
        assert result.exit_code == 0
        assert (cache_dir / f"{key}.md").exists(), (
            "Prune incorrectly deleted a referenced cache entry — "
            "failed to resolve project-root-relative path from subdirectory prompt."
        )


# ===========================================================================
# 4. Orphan detection – early exits, mixed states
# ===========================================================================

class TestPruneEarlyExit:
    def test_no_cache_directory(self, tmp_path, runner):
        """No .pdd/extracts/ → info message, exit 0."""
        with patch(
            "pdd.extracts_prune.get_config",
            return_value={"project_root": str(tmp_path)},
        ):
            from pdd.extracts_prune import extracts
            result = runner.invoke(extracts, ["prune"], obj={"force": False})
        assert result.exit_code == 0
        assert "nothing to do" in result.output.lower()

    def test_empty_cache_directory(self, cli_env, runner):
        """Cache dir exists but no .md files → info message."""
        qc, project_dir, cache_dir = cli_env
        result = runner.invoke(qc, ["prune"], obj={"force": False})
        assert result.exit_code == 0
        assert "nothing to prune" in result.output.lower()

    def test_all_entries_referenced(self, cli_env, runner):
        """All cache entries referenced → 'cache is clean'."""
        qc, project_dir, cache_dir = cli_env

        src_file = project_dir / "data.py"
        src_file.write_text("print('hello')", encoding="utf-8")

        rel_path = str(src_file.resolve().relative_to(project_dir.resolve()))
        query = "extract functions"
        key = _compute_cache_key(rel_path, query)
        _create_cache_entry(cache_dir, key, source_path=rel_path, query=query)

        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text(
            '<include query="extract functions">data.py</include>',
            encoding="utf-8",
        )

        result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})
        assert result.exit_code == 0
        assert "clean" in result.output.lower() or "no orphaned" in result.output.lower()


class TestPruneOrphans:
    def test_orphaned_entries_deleted_with_force(self, cli_env, runner):
        qc, project_dir, cache_dir = cli_env

        key = "deadbeef" + "0" * 56
        _create_cache_entry(cache_dir, key, source_path="/old/file.py", query="old query")

        with patch("pdd.extracts_prune.parse_include_tags", return_value=[]):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "pruned" in result.output.lower()
        assert not (cache_dir / f"{key}.md").exists()
        assert not (cache_dir / f"{key}.meta.json").exists()

    def test_mixed_referenced_and_orphaned(self, cli_env, runner):
        """Only orphaned entries are deleted; referenced ones kept."""
        qc, project_dir, cache_dir = cli_env

        src_file = project_dir / "keep.py"
        src_file.write_text("keep", encoding="utf-8")
        rel_path = str(src_file.resolve().relative_to(project_dir.resolve()))
        ref_key = _compute_cache_key(rel_path, "keep query")
        _create_cache_entry(cache_dir, ref_key, source_path=rel_path, query="keep query")

        orph_key = "orphaned00" + "0" * 54
        _create_cache_entry(cache_dir, orph_key, source_path="/gone/file.py", query="old query")

        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text(
            '<include query="keep query">keep.py</include>',
            encoding="utf-8",
        )

        result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})
        assert result.exit_code == 0
        assert (cache_dir / f"{ref_key}.md").exists()
        assert not (cache_dir / f"{orph_key}.md").exists()

    def test_include_references_missing_file(self, cli_env, runner):
        """Include referencing a non-existent file → entry treated as orphaned."""
        qc, project_dir, cache_dir = cli_env

        key = "missing0" + "0" * 56
        _create_cache_entry(cache_dir, key, source_path="/missing/file.py", query="q")

        prompt_file = project_dir / "test.prompt"
        prompt_file.write_text(
            '<include query="q">missing.py</include>',
            encoding="utf-8",
        )

        result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})
        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()

    def test_references_from_multiple_prompts(self, cli_env, runner):
        """References collected from multiple .prompt files."""
        qc, project_dir, cache_dir = cli_env

        src1 = project_dir / "a.py"
        src1.write_text("a", encoding="utf-8")
        src2 = project_dir / "b.py"
        src2.write_text("b", encoding="utf-8")

        rel1 = str(src1.resolve().relative_to(project_dir.resolve()))
        rel2 = str(src2.resolve().relative_to(project_dir.resolve()))
        key1 = _compute_cache_key(rel1, "q1")
        key2 = _compute_cache_key(rel2, "q2")
        orph_key = "orphkey0" + "0" * 56

        _create_cache_entry(cache_dir, key1, source_path=rel1, query="q1")
        _create_cache_entry(cache_dir, key2, source_path=rel2, query="q2")
        _create_cache_entry(cache_dir, orph_key, source_path="gone.py", query="old")

        (project_dir / "p1.prompt").write_text(
            '<include query="q1">a.py</include>', encoding="utf-8"
        )
        (project_dir / "p2.prompt").write_text(
            '<include query="q2">b.py</include>', encoding="utf-8"
        )

        result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})
        assert result.exit_code == 0
        assert (cache_dir / f"{key1}.md").exists()
        assert (cache_dir / f"{key2}.md").exists()
        assert not (cache_dir / f"{orph_key}.md").exists()


# ===========================================================================
# 5. Display – table with Key, Source Path, Query from .meta.json
# ===========================================================================

class TestPruneDisplay:
    def test_meta_json_source_and_query_displayed(self, cli_env, runner):
        """Source path and query from meta.json appear in output."""
        qc, project_dir, cache_dir = cli_env

        key = "display0" + "0" * 56
        _create_cache_entry(
            cache_dir, key, source_path="/my/source.py", query="find classes"
        )

        import builtins
        original_import = builtins.__import__

        def mock_import(name, *args, **kwargs):
            if name.startswith("rich"):
                raise ImportError("no rich")
            return original_import(name, *args, **kwargs)

        with patch("pdd.extracts_prune.parse_include_tags", return_value=[]), \
             patch("builtins.__import__", side_effect=mock_import):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "/my/source.py" in result.output
        assert "find classes" in result.output

    def test_missing_meta_json_shows_unknown(self, cli_env, runner):
        """Orphan without meta.json shows <unknown> and still deletes."""
        qc, project_dir, cache_dir = cli_env

        key = "nometa000" + "0" * 55
        (cache_dir / f"{key}.md").write_text("content", encoding="utf-8")

        import builtins
        original_import = builtins.__import__

        def mock_import(name, *args, **kwargs):
            if name.startswith("rich"):
                raise ImportError("no rich")
            return original_import(name, *args, **kwargs)

        with patch("pdd.extracts_prune.parse_include_tags", return_value=[]), \
             patch("builtins.__import__", side_effect=mock_import):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "<unknown>" in result.output
        assert not (cache_dir / f"{key}.md").exists()

    def test_malformed_meta_json(self, cli_env, runner):
        """Invalid JSON in meta.json → graceful fallback, still deletes."""
        qc, project_dir, cache_dir = cli_env

        key = "badjson0" + "0" * 56
        (cache_dir / f"{key}.md").write_text("content", encoding="utf-8")
        (cache_dir / f"{key}.meta.json").write_text("not valid json{{{", encoding="utf-8")

        with patch("pdd.extracts_prune.parse_include_tags", return_value=[]):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()
        assert not (cache_dir / f"{key}.meta.json").exists()

    def test_fallback_without_rich(self, cli_env, runner):
        """When rich is unavailable, plain text output is used."""
        qc, project_dir, cache_dir = cli_env

        key = "richfb00" + "0" * 56
        _create_cache_entry(
            cache_dir, key, source_path="/test/file.py", query="test query"
        )

        import builtins
        original_import = builtins.__import__

        def mock_import(name, *args, **kwargs):
            if name.startswith("rich"):
                raise ImportError("no rich")
            return original_import(name, *args, **kwargs)

        with patch("pdd.extracts_prune.parse_include_tags", return_value=[]), \
             patch("builtins.__import__", side_effect=mock_import):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "Orphaned extracts cache entries:" in result.output
        assert not (cache_dir / f"{key}.md").exists()


# ===========================================================================
# 6. Safety – confirmation prompt, --force, ctx.obj["force"]
# ===========================================================================

class TestPruneSafety:
    def test_user_confirms_deletion(self, cli_env, runner):
        qc, project_dir, cache_dir = cli_env

        key = "confirm0" + "0" * 56
        _create_cache_entry(cache_dir, key)

        with patch("pdd.extracts_prune.parse_include_tags", return_value=[]):
            result = runner.invoke(qc, ["prune"], input="y\n", obj={"force": False})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()

    def test_user_declines_deletion(self, cli_env, runner):
        qc, project_dir, cache_dir = cli_env

        key = "decline0" + "0" * 56
        _create_cache_entry(cache_dir, key)

        with patch("pdd.extracts_prune.parse_include_tags", return_value=[]):
            result = runner.invoke(qc, ["prune"], input="n\n", obj={"force": False})

        assert result.exit_code == 0
        assert "aborted" in result.output.lower()
        assert (cache_dir / f"{key}.md").exists()
        assert (cache_dir / f"{key}.meta.json").exists()

    def test_force_flag_skips_confirmation(self, cli_env, runner):
        qc, project_dir, cache_dir = cli_env

        key = "forced00" + "0" * 56
        _create_cache_entry(cache_dir, key)

        with patch("pdd.extracts_prune.parse_include_tags", return_value=[]):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()

    def test_global_force_flag(self, cli_env, runner):
        """ctx.obj["force"] = True skips confirmation."""
        qc, project_dir, cache_dir = cli_env

        key = "gforce0" + "0" * 56
        _create_cache_entry(cache_dir, key)

        with patch("pdd.extracts_prune.parse_include_tags", return_value=[]):
            result = runner.invoke(qc, ["prune"], obj={"force": True})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()

    def test_no_ctx_obj(self, cli_env, runner):
        """ctx.obj=None doesn't crash."""
        qc, project_dir, cache_dir = cli_env

        key = "noobj000" + "0" * 56
        _create_cache_entry(cache_dir, key)

        with patch("pdd.extracts_prune.parse_include_tags", return_value=[]):
            result = runner.invoke(qc, ["prune", "--force"])

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()


# ===========================================================================
# 7. Deletion – both files, error handling
# ===========================================================================

class TestPruneDeletion:
    def test_deletes_both_md_and_meta(self, cli_env, runner):
        qc, project_dir, cache_dir = cli_env

        key = "bothfile" + "0" * 56
        _create_cache_entry(cache_dir, key)

        with patch("pdd.extracts_prune.parse_include_tags", return_value=[]):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert not (cache_dir / f"{key}.md").exists()
        assert not (cache_dir / f"{key}.meta.json").exists()

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

        with patch("pdd.extracts_prune.parse_include_tags", return_value=[]), \
             patch.object(Path, "unlink", failing_unlink):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "warning" in result.output.lower()


# ===========================================================================
# 8. Grammar – singular/plural
# ===========================================================================

class TestPruneGrammar:
    def test_singular_entry(self, cli_env, runner):
        qc, project_dir, cache_dir = cli_env

        key = "single00" + "0" * 56
        _create_cache_entry(cache_dir, key)

        with patch("pdd.extracts_prune.parse_include_tags", return_value=[]):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "1" in result.output
        assert "entry" in result.output.lower()

    def test_plural_entries(self, cli_env, runner):
        qc, project_dir, cache_dir = cli_env

        for i in range(3):
            key = f"plural{i:02d}" + "0" * 56
            _create_cache_entry(cache_dir, key)

        with patch("pdd.extracts_prune.parse_include_tags", return_value=[]):
            result = runner.invoke(qc, ["prune", "--force"], obj={"force": False})

        assert result.exit_code == 0
        assert "3" in result.output
        assert "entries" in result.output.lower()


# ===========================================================================
# Edge cases – unreadable prompt files, cache key computation
# ===========================================================================

class TestPruneUnreadablePromptFile:
    def test_unreadable_prompt_file_skipped(self, cli_env, runner):
        """Prompt files that raise OSError are skipped gracefully."""
        qc, project_dir, cache_dir = cli_env

        key = "orphan00" + "0" * 56
        _create_cache_entry(cache_dir, key)

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
        assert not (cache_dir / f"{key}.md").exists()


class TestCacheKeyComputation:
    """Cache key formula: sha256(normpath(path) + '\\n' + query)."""

    def test_deterministic(self):
        assert _compute_cache_key("src/main.py", "q") == _compute_cache_key("src/main.py", "q")

    def test_different_queries(self):
        assert _compute_cache_key("f.py", "a") != _compute_cache_key("f.py", "b")

    def test_different_paths(self):
        assert _compute_cache_key("a.py", "q") != _compute_cache_key("b.py", "q")

    def test_sha256_hex_format(self):
        key = _compute_cache_key("test.py", "query")
        assert len(key) == 64
        assert all(c in "0123456789abcdef" for c in key)

    def test_normpath_consistency(self):
        """src/../src/main.py and src/main.py produce the same key."""
        assert (
            _compute_cache_key("src/../src/main.py", "q")
            == _compute_cache_key("src/main.py", "q")
        )


# ===========================================================================
# Import source correctness
# ===========================================================================

class TestImportSources:
    """Verify extracts_prune imports from the canonical module, not stubs."""

    def test_compute_cache_key_matches_canonical(self):
        """extracts_prune.compute_cache_key must produce the same result
        as include_query_extractor.compute_cache_key for all inputs."""
        from pdd.extracts_prune import compute_cache_key as prune_key
        from pdd.include_query_extractor import compute_cache_key as canonical_key

        for path, query in [
            ("src.py", "q"),
            ("./src.py", "q"),
            ("a/b/../c.py", "find stuff"),
        ]:
            assert prune_key(path, query) == canonical_key(path, query), (
                f"Key mismatch for ({path!r}, {query!r}): prune uses a different "
                "implementation than include_query_extractor"
            )

    def test_compute_cache_key_imported_from_correct_module(self):
        """compute_cache_key should be imported from pdd.include_query_extractor,
        not from pdd.preprocess (where it doesn't exist)."""
        import pdd.extracts_prune as ep
        # The function should be the same object as the canonical one
        from pdd.include_query_extractor import compute_cache_key as canonical
        assert ep.compute_cache_key is canonical, (
            "extracts_prune.compute_cache_key is not imported from "
            "pdd.include_query_extractor — likely using a fallback stub"
        )
