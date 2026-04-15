"""Tests for _find_prompt_file — authoritative prompt resolution (#1169).

Covers: case-insensitive matching, nested subdirectories, architecture.json
hints, glob metacharacters, and temp directory execution.
"""
import json
import pytest
from pathlib import Path

from pdd.sync_determine_operation import _find_prompt_file


@pytest.fixture
def prompts_tree(tmp_path):
    """Create a nested prompts directory mimicking pdd_cloud's structure."""
    prompts = tmp_path / "prompts"
    # Flat file
    (prompts).mkdir(parents=True)
    (prompts / "config_Python.prompt").write_text("flat config")
    # Nested: prompts/src/clients/
    clients = prompts / "src" / "clients"
    clients.mkdir(parents=True)
    (clients / "firestore_client_Python.prompt").write_text("nested client")
    # Nested: prompts/src/routers/
    routers = prompts / "src" / "routers"
    routers.mkdir(parents=True)
    (routers / "board_config_Python.prompt").write_text("nested router")
    # Nested: prompts/frontend/components/
    frontend = prompts / "frontend" / "components"
    frontend.mkdir(parents=True)
    (frontend / "Dashboard_TypeScriptReact.prompt").write_text("frontend component")
    return prompts


@pytest.fixture
def arch_json(tmp_path):
    """Create an architecture.json with filename-only entries (no subdirectory)."""
    arch = [
        {"filename": "firestore_client_Python.prompt", "filepath": "src/clients/firestore_client.py"},
        {"filename": "board_config_Python.prompt", "filepath": "src/routers/board_config.py"},
        {"filename": "config_Python.prompt", "filepath": "src/config.py"},
        {"filename": "Dashboard_TypeScriptReact.prompt", "filepath": "frontend/components/Dashboard.tsx"},
    ]
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch))
    return arch_path


# === Step 1: Direct path match ===

class TestDirectPath:
    def test_flat_exact_match(self, prompts_tree):
        """File at prompts_root/name_language.prompt — fastest path."""
        result = _find_prompt_file("config", "Python", prompts_tree)
        assert result is not None
        assert result.name == "config_Python.prompt"
        assert result.exists()

    def test_returns_none_for_missing(self, prompts_tree):
        """Module that doesn't exist → None, not crash."""
        result = _find_prompt_file("nonexistent_module", "python", prompts_tree)
        assert result is None


# === Step 2: Case-insensitive match in same directory ===

class TestCaseInsensitive:
    def test_lowercase_language_finds_pascalcase_file(self, prompts_tree):
        """language='python' finds config_Python.prompt on case-sensitive FS."""
        result = _find_prompt_file("config", "python", prompts_tree)
        assert result is not None
        assert result.exists()
        # On case-insensitive FS (macOS), direct path works but may preserve
        # the search casing. On case-sensitive FS (Linux), step 2 returns
        # the actual filename. Either way the file must be found.
        assert result.name.lower() == "config_python.prompt"


# === Step 3: Architecture.json hint + recursive search ===

class TestArchitectureHint:
    def test_nested_subdir_found_via_architecture(self, prompts_tree, arch_json):
        """arch says 'firestore_client_Python.prompt', file in prompts/src/clients/."""
        result = _find_prompt_file("firestore_client", "python", prompts_tree, arch_json)
        assert result is not None
        assert result.name == "firestore_client_Python.prompt"
        assert "clients" in str(result)
        assert result.exists()

    def test_nested_router_found_via_architecture(self, prompts_tree, arch_json):
        """board_config in prompts/src/routers/."""
        result = _find_prompt_file("board_config", "python", prompts_tree, arch_json)
        assert result is not None
        assert result.name == "board_config_Python.prompt"
        assert "routers" in str(result)

    def test_frontend_component_found_via_architecture(self, prompts_tree, arch_json):
        """TypeScriptReact component in prompts/frontend/components/."""
        result = _find_prompt_file("Dashboard", "typescriptreact", prompts_tree, arch_json)
        assert result is not None
        assert result.name == "Dashboard_TypeScriptReact.prompt"
        assert "frontend" in str(result)


# === Step 4: Recursive glob fallback (no architecture.json) ===

class TestRecursiveFallback:
    def test_nested_found_without_architecture(self, prompts_tree):
        """No architecture.json — finds file via recursive glob."""
        result = _find_prompt_file("firestore_client", "python", prompts_tree)
        assert result is not None
        assert result.name == "firestore_client_Python.prompt"
        assert "clients" in str(result)

    def test_nested_frontend_without_architecture(self, prompts_tree):
        """No architecture.json — finds TypeScriptReact component recursively."""
        result = _find_prompt_file("Dashboard", "typescriptreact", prompts_tree)
        assert result is not None
        assert result.name == "Dashboard_TypeScriptReact.prompt"


# === Cross-cutting: all language casings ===

class TestAllLanguages:
    @pytest.mark.parametrize("search_lang,file_lang", [
        ("python", "Python"),
        ("typescript", "TypeScript"),
        ("typescriptreact", "TypeScriptReact"),
        ("javascript", "JavaScript"),
        ("go", "Go"),
        ("rust", "Rust"),
    ])
    def test_case_insensitive_language_suffix(self, tmp_path, search_lang, file_lang):
        """Searching with lowercase language finds PascalCase file for every language."""
        prompts = tmp_path / "prompts"
        prompts.mkdir()
        target = prompts / f"mymodule_{file_lang}.prompt"
        target.write_text("content")

        result = _find_prompt_file("mymodule", search_lang, prompts)
        assert result is not None
        assert result.exists()
        assert result.name.lower() == f"mymodule_{file_lang}.prompt".lower()


# === Edge cases ===

class TestEdgeCases:
    def test_glob_metacharacters_in_basename(self, tmp_path):
        """Basename with brackets (Next.js dynamic routes) doesn't crash."""
        prompts = tmp_path / "prompts" / "app" / "routes"
        prompts.mkdir(parents=True)
        (prompts / "[id]_TypeScript.prompt").write_text("dynamic route")

        result = _find_prompt_file("[id]", "typescript", tmp_path / "prompts")
        assert result is not None
        assert result.name == "[id]_TypeScript.prompt"

    def test_basename_with_subdirectory(self, prompts_tree):
        """basename='src/clients/firestore_client' extracts name part correctly."""
        result = _find_prompt_file("src/clients/firestore_client", "python", prompts_tree)
        assert result is not None
        assert result.name == "firestore_client_Python.prompt"

    def test_empty_prompts_dir(self, tmp_path):
        """Empty prompts directory → None."""
        prompts = tmp_path / "prompts"
        prompts.mkdir()
        result = _find_prompt_file("anything", "python", prompts)
        assert result is None

    def test_nonexistent_prompts_dir(self, tmp_path):
        """prompts_root doesn't exist → None, not crash."""
        result = _find_prompt_file("anything", "python", tmp_path / "nope")
        assert result is None

    def test_architecture_path_nonexistent(self, prompts_tree, tmp_path):
        """Nonexistent architecture.json path is handled gracefully."""
        fake_arch = tmp_path / "nope.json"
        result = _find_prompt_file("config", "python", prompts_tree, fake_arch)
        # Should still find via step 2 (case-insensitive) or step 4 (recursive)
        assert result is not None
        assert result.exists()
        assert result.name.lower() == "config_python.prompt"


# === Deterministic tie-break when multiple nested files share a basename ===


class TestDeterministicResolution:
    def test_step4_prefers_shallowest_match(self, tmp_path):
        """Two nested files sharing the basename — shallowest wins, not rglob order."""
        prompts = tmp_path / "prompts"
        (prompts / "src").mkdir(parents=True)
        (prompts / "zzz" / "deep" / "nested").mkdir(parents=True)
        shallow = prompts / "src" / "foo_Python.prompt"
        deep = prompts / "zzz" / "deep" / "nested" / "foo_Python.prompt"
        shallow.write_text("shallow")
        deep.write_text("deep")

        result = _find_prompt_file("foo", "python", prompts)
        assert result == shallow, (
            f"Expected shallowest match {shallow}, got {result}. "
            "Non-deterministic rglob order must be stabilised by depth+path sort."
        )

    def test_step4_lexicographic_tiebreak_at_same_depth(self, tmp_path):
        """Two files at the same depth — lexicographic order wins deterministically."""
        prompts = tmp_path / "prompts"
        (prompts / "alpha").mkdir(parents=True)
        (prompts / "beta").mkdir(parents=True)
        alpha = prompts / "alpha" / "foo_Python.prompt"
        beta = prompts / "beta" / "foo_Python.prompt"
        alpha.write_text("a")
        beta.write_text("b")

        result = _find_prompt_file("foo", "python", prompts)
        assert result == alpha, f"Expected lexicographic winner {alpha}, got {result}"

    def test_step3c_prefers_shallowest_match(self, tmp_path):
        """architecture.json hint + two nested matches — shallowest wins."""
        prompts = tmp_path / "prompts"
        (prompts / "src").mkdir(parents=True)
        (prompts / "legacy" / "backup").mkdir(parents=True)
        shallow = prompts / "src" / "foo_Python.prompt"
        deep = prompts / "legacy" / "backup" / "foo_Python.prompt"
        shallow.write_text("shallow")
        deep.write_text("deep")

        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(
            [{"filename": "foo_Python.prompt", "filepath": "src/foo.py"}]
        ))

        result = _find_prompt_file("foo", "python", prompts, arch_path)
        assert result == shallow, f"Expected shallowest arch match {shallow}, got {result}"

    def test_stale_flat_file_wins_over_nested(self, tmp_path):
        """Stale flat file at prompts_root takes precedence over nested — step 1 wins.

        This is documented behaviour: if a user has an old flat prompt AND a nested
        one, step 1 (direct path) returns the flat one. Users who moved prompts
        to a subdirectory must delete the old flat file.
        """
        prompts = tmp_path / "prompts"
        prompts.mkdir()
        (prompts / "src").mkdir()
        flat = prompts / "foo_Python.prompt"
        nested = prompts / "src" / "foo_Python.prompt"
        flat.write_text("flat-stale")
        nested.write_text("nested-current")

        result = _find_prompt_file("foo", "Python", prompts)
        assert result == flat, (
            "Step 1 (direct path) must short-circuit before recursion — "
            "flat file wins even when a nested version exists."
        )


# === Simulates the exact Cloud Run failure from #1169 ===

class TestCloudRunScenario:
    def test_exact_production_failure(self, tmp_path):
        """Reproduces: get_pdd_file_paths('firestore_client', 'python', 'prompts')
        where file is at prompts/src/clients/firestore_client_Python.prompt
        and architecture.json has filename without subdirectory path."""
        # Simulate the Cloud Run temp directory structure
        ext_dir = tmp_path / "extensions" / "github_pdd_app"
        prompts = ext_dir / "prompts" / "src" / "clients"
        prompts.mkdir(parents=True)
        (prompts / "firestore_client_Python.prompt").write_text("production prompt")

        # Architecture.json at extension root (filename only, no subdir path)
        arch = [{"filename": "firestore_client_Python.prompt", "filepath": "src/clients/firestore_client.py"}]
        arch_path = ext_dir / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        # Call with root prompts dir (not the specific subdirectory)
        prompts_root = ext_dir / "prompts"
        result = _find_prompt_file("firestore_client", "python", prompts_root, arch_path)

        assert result is not None
        assert result.exists()
        assert result.name == "firestore_client_Python.prompt"
        assert "clients" in str(result)


# === Greg review issue #1: basename directory hint disambiguation ===

class TestDirectoryHintDisambiguation:
    def test_two_subdirs_same_basename_no_arch_prefers_dir_hint(self, tmp_path):
        """basename='src/routers/foo' must NOT resolve to prompts/src/clients/foo_Python.prompt."""
        prompts = tmp_path / "prompts"
        (prompts / "src" / "clients").mkdir(parents=True)
        (prompts / "src" / "routers").mkdir(parents=True)
        clients = prompts / "src" / "clients" / "foo_Python.prompt"
        routers = prompts / "src" / "routers" / "foo_Python.prompt"
        clients.write_text("client")
        routers.write_text("router")

        result = _find_prompt_file("src/routers/foo", "python", prompts)
        assert result == routers, (
            f"basename='src/routers/foo' should prefer the routers match, got {result}"
        )

    def test_two_subdirs_same_basename_no_hint_picks_shallowest(self, tmp_path):
        """Without a dir hint in basename, shallowest/lex wins deterministically."""
        prompts = tmp_path / "prompts"
        (prompts / "alpha").mkdir(parents=True)
        (prompts / "beta").mkdir(parents=True)
        alpha = prompts / "alpha" / "foo_Python.prompt"
        beta = prompts / "beta" / "foo_Python.prompt"
        alpha.write_text("a")
        beta.write_text("b")

        result = _find_prompt_file("foo", "python", prompts)
        assert result == alpha, f"Expected lex winner {alpha}, got {result}"


# === Greg review issue #3: context_override scoping ===

class TestContextOverrideScoping:
    def test_context_override_prefers_correct_context_subdir(self, tmp_path, monkeypatch):
        """context_override='backend-utils' must pick prompts/backend/utils/ not prompts/frontend/."""
        monkeypatch.chdir(tmp_path)
        prompts = tmp_path / "prompts"
        (prompts / "frontend").mkdir(parents=True)
        (prompts / "backend" / "utils").mkdir(parents=True)
        frontend = prompts / "frontend" / "credit_helpers_Python.prompt"
        backend = prompts / "backend" / "utils" / "credit_helpers_Python.prompt"
        frontend.write_text("wrong context")
        backend.write_text("right context")

        # Create .pddrc with two contexts
        pddrc = {
            "contexts": {
                "frontend": {"defaults": {"prompts_dir": "prompts/frontend"}},
                "backend-utils": {"defaults": {"prompts_dir": "prompts/backend/utils"}}
            }
        }
        (tmp_path / ".pddrc").write_text(json.dumps(pddrc))

        result = _find_prompt_file(
            "credit_helpers", "python", prompts, context_override="backend-utils"
        )
        assert result == backend, (
            f"context_override='backend-utils' should prefer {backend}, got {result}"
        )

    def test_context_override_without_pddrc_still_works(self, tmp_path):
        """context_override without a .pddrc file degrades gracefully."""
        prompts = tmp_path / "prompts" / "src"
        prompts.mkdir(parents=True)
        target = prompts / "foo_Python.prompt"
        target.write_text("content")

        result = _find_prompt_file("foo", "python", tmp_path / "prompts", context_override="anything")
        assert result is not None
        assert result.exists()


# === Greg review issue #4: case-insensitive basename ===

class TestCaseInsensitiveBasename:
    def test_lowercase_basename_finds_pascalcase_file(self, tmp_path):
        """basename='dashboard' must find Dashboard_TypeScriptReact.prompt."""
        prompts = tmp_path / "prompts" / "frontend" / "components"
        prompts.mkdir(parents=True)
        target = prompts / "Dashboard_TypeScriptReact.prompt"
        target.write_text("component")

        result = _find_prompt_file("dashboard", "typescriptreact", tmp_path / "prompts")
        assert result is not None, (
            "Lowercase basename 'dashboard' should find PascalCase 'Dashboard_TypeScriptReact.prompt'"
        )
        assert result.exists()
        assert result.name == "Dashboard_TypeScriptReact.prompt"

    def test_uppercase_basename_finds_lowercase_file(self, tmp_path):
        """basename='MyModule' finds mymodule_python.prompt (all lowercase on disk)."""
        prompts = tmp_path / "prompts" / "src"
        prompts.mkdir(parents=True)
        target = prompts / "mymodule_Python.prompt"
        target.write_text("content")

        result = _find_prompt_file("MyModule", "python", tmp_path / "prompts")
        assert result is not None, "PascalCase basename should find lowercase file"
        assert result.exists()

    def test_case_insensitive_basename_in_flat_dir(self, tmp_path):
        """Case-insensitive basename works for flat (non-nested) prompts too."""
        prompts = tmp_path / "prompts"
        prompts.mkdir()
        target = prompts / "Config_Python.prompt"
        target.write_text("flat config")

        result = _find_prompt_file("config", "python", prompts)
        assert result is not None, "Lowercase 'config' should find 'Config_Python.prompt'"
        # On case-insensitive FS (macOS), Step 1 matches with original casing;
        # on case-sensitive FS (Linux), Step 2 returns the actual filename.
        # Either way the file must be found and names must match case-insensitively.
        assert result.name.lower() == "config_python.prompt"


# === Greg review issue #2: .pddrc prefix for prompt creation paths ===
# (Tested at the get_pdd_file_paths level since _find_prompt_file returns None
# for non-existent files — the prefix logic is in the caller.)

from pdd.sync_determine_operation import get_pdd_file_paths


class TestPddrcPrefixForNewModules:
    def test_new_module_respects_pddrc_prompts_dir_prefix(self, tmp_path, monkeypatch):
        """When prompt doesn't exist, the path must include the .pddrc context prefix."""
        monkeypatch.chdir(tmp_path)
        prompts = tmp_path / "prompts" / "backend" / "utils"
        prompts.mkdir(parents=True)

        # .pddrc with a context that maps to a prompts subdirectory
        pddrc = {
            "contexts": {
                "backend-utils": {
                    "defaults": {"prompts_dir": "prompts/backend/utils"},
                    "match": {"paths": ["backend/utils/"]}
                }
            }
        }
        (tmp_path / ".pddrc").write_text(json.dumps(pddrc))
        (tmp_path / ".pdd" / "meta").mkdir(parents=True)
        (tmp_path / ".pdd" / "locks").mkdir(parents=True)

        # No prompt file exists — this is a new module being created
        paths = get_pdd_file_paths("credit_helpers", "python", "prompts", context_override="backend-utils")

        # The prompt path should include the context prefix, not be flat
        prompt_str = str(paths['prompt'])
        assert "backend/utils" in prompt_str or "backend\\utils" in prompt_str, (
            f"New module prompt path should include .pddrc prefix 'backend/utils', got: {prompt_str}"
        )
