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
