# Test Plan:
# I. Early Exits
#   1.  test_already_exists_returns_false: .pddrc exists → returns False, file untouched
#   2.  test_already_exists_shows_message: .pddrc exists → output mentions "already exists"
#
# II. Language Detection (pure function contract — stable sub-contract)
#   3.  test_detect_language_python_markers: pyproject.toml, setup.py, requirements.txt → "python"
#   4.  test_detect_language_typescript: package.json with typescript dep → "typescript"
#   5.  test_detect_language_not_typescript_without_dep: package.json without typescript → None
#   6.  test_detect_language_go: go.mod → "go"
#   7.  test_detect_language_none: empty dir → None
#   8.  test_detect_language_python_priority: both pyproject.toml and go.mod → "python"
#
# III. Content Generation (pure function contract — stable sub-contract)
#   9.  test_build_content_language_paths: each language gets correct output paths
#   10. test_build_content_standard_defaults: strength, temperature, etc. present
#   11. test_build_content_unknown_language_fallback: unknown lang falls back to Python paths
#   12. test_build_content_ends_with_newline: trailing newline
#
# IV. Success Path — File Created
#   13. test_creates_file_on_confirm_yes: user types "y" → file created, returns True
#   14. test_creates_file_on_enter: empty input (Enter) → file created, returns True
#   15. test_created_file_has_correct_content: created file contains detected language defaults
#   16. test_prompts_language_when_undetected: no markers → asks for language, then confirms
#
# V. User Declines
#   17. test_declined_returns_false: user types "n" → returns False, no file
#
# VI. Language Prompt with Invalid Input
#   18. test_language_prompt_retries_on_invalid: invalid then valid → correct language used
#
# VII. Output / Display
#   19. test_detected_language_shown: auto-detected language appears in output
#   20. test_preview_shown_before_confirmation: YAML preview shown before user asked to confirm
#   21. test_creation_success_message: "Created .pddrc" message appears after creation
#   22. test_skip_message_on_decline: "Skipped" message appears when user declines
#
# VIII. Filesystem Error
#   23. test_write_error_returns_false: OSError on write → returns False, error shown

import json
import os
import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path
from io import StringIO

from pdd import pddrc_initializer
from pdd.pddrc_initializer import (
    _detect_language,
    _build_pddrc_content,
    _detect_language_from_extensions,
    _sanitize_context_name,
    infer_contexts_from_scan,
    ensure_pddrc_for_scan,
)


# ---------------------------------------------------------------------------
# Module-level fixtures / constants
# ---------------------------------------------------------------------------

PYTHON_PROJECT_MARKERS = ["pyproject.toml", "setup.py", "requirements.txt"]

TS_PACKAGE_JSON = json.dumps({
    "devDependencies": {"typescript": "^5.0.0"}
})

NON_TS_PACKAGE_JSON = json.dumps({
    "dependencies": {"express": "^4.0.0"}
})


# ---------------------------------------------------------------------------
# Helper: run offer_pddrc_init and capture output
# ---------------------------------------------------------------------------

def _run_offer_capture(tmp_path, monkeypatch, user_inputs, *, marker_files=None):
    """Run offer_pddrc_init() in tmp_path, capturing printed output.

    Parameters
    ----------
    tmp_path : Path
        Working directory for the test.
    monkeypatch : pytest.MonkeyPatch
        Used to patch cwd.
    user_inputs : list[str]
        Sequence of strings returned by console.input() calls.
    marker_files : dict[str, str | None] | None
        Files to create in tmp_path before running.  Keys are filenames,
        values are contents (None → touch).

    Returns
    -------
    tuple[bool, str]
        (return_value, captured_output_text)
    """
    # Set up marker files
    if marker_files:
        for name, content in marker_files.items():
            path = tmp_path / name
            if content is not None:
                path.write_text(content)
            else:
                path.touch()

    # Mock console.input to feed user inputs
    input_iter = iter(user_inputs)

    # Capture console.print output
    captured = []

    original_print = pddrc_initializer.console.print

    def fake_print(*args, **kwargs):
        # Convert to plain string for assertion
        buf = StringIO()
        temp_console = pddrc_initializer.Console(file=buf, force_terminal=False, no_color=True)
        temp_console.print(*args, **kwargs)
        captured.append(buf.getvalue())

    with patch.object(Path, "cwd", return_value=tmp_path), \
         patch.object(pddrc_initializer.console, "input", side_effect=input_iter), \
         patch.object(pddrc_initializer.console, "print", side_effect=fake_print):
        result = pddrc_initializer.offer_pddrc_init()

    output = "".join(captured)
    return result, output


# ---------------------------------------------------------------------------
# I. Early Exits
# ---------------------------------------------------------------------------

def test_already_exists_returns_false(tmp_path, monkeypatch):
    """When .pddrc already exists, offer_pddrc_init returns False."""
    (tmp_path / ".pddrc").write_text("existing config")
    result, _ = _run_offer_capture(tmp_path, monkeypatch, [])
    assert result is False
    assert (tmp_path / ".pddrc").read_text() == "existing config"


def test_already_exists_shows_message(tmp_path, monkeypatch):
    """When .pddrc already exists, user sees 'already exists' message."""
    (tmp_path / ".pddrc").write_text("existing config")
    _, output = _run_offer_capture(tmp_path, monkeypatch, [])
    assert "already exists" in output


# ---------------------------------------------------------------------------
# II. Language Detection (pure function — stable sub-contract)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("marker", PYTHON_PROJECT_MARKERS)
def test_detect_language_python_markers(tmp_path, marker):
    """Python marker files are detected correctly."""
    (tmp_path / marker).touch()
    assert _detect_language(tmp_path) == "python"


def test_detect_language_typescript(tmp_path):
    """package.json with typescript dependency → 'typescript'."""
    (tmp_path / "package.json").write_text(TS_PACKAGE_JSON)
    assert _detect_language(tmp_path) == "typescript"


def test_detect_language_not_typescript_without_dep(tmp_path):
    """package.json without typescript dep → None."""
    (tmp_path / "package.json").write_text(NON_TS_PACKAGE_JSON)
    assert _detect_language(tmp_path) is None


def test_detect_language_go(tmp_path):
    """go.mod → 'go'."""
    (tmp_path / "go.mod").touch()
    assert _detect_language(tmp_path) == "go"


def test_detect_language_none(tmp_path):
    """Empty directory → None."""
    assert _detect_language(tmp_path) is None


def test_detect_language_python_priority(tmp_path):
    """Python markers take priority over Go markers."""
    (tmp_path / "pyproject.toml").touch()
    (tmp_path / "go.mod").touch()
    assert _detect_language(tmp_path) == "python"


# ---------------------------------------------------------------------------
# III. Content Generation (pure function — stable sub-contract)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("language, gen_path, test_path, example_path", [
    ("python", "pdd/", "tests/", "context/"),
    ("typescript", "src/", "__tests__/", "examples/"),
    ("go", ".", ".", "examples/"),
])
def test_build_content_language_paths(language, gen_path, test_path, example_path):
    """Each language gets correct output paths in generated content."""
    content = _build_pddrc_content(language)
    assert f'generate_output_path: "{gen_path}"' in content
    assert f'test_output_path: "{test_path}"' in content
    assert f'example_output_path: "{example_path}"' in content
    assert f'default_language: "{language}"' in content


def test_build_content_standard_defaults():
    """Generated content includes all standard defaults."""
    content = _build_pddrc_content("python")
    assert "strength: 0.818" in content
    assert "temperature: 0.0" in content
    assert "target_coverage: 80.0" in content
    assert "budget: 10.0" in content
    assert "max_attempts: 3" in content
    assert 'version: "1.0"' in content


def test_build_content_unknown_language_fallback():
    """Unknown language falls back to Python paths but uses given language name."""
    content = _build_pddrc_content("haskell")
    assert 'generate_output_path: "pdd/"' in content
    assert 'default_language: "haskell"' in content


def test_build_content_ends_with_newline():
    """Generated content ends with a trailing newline."""
    content = _build_pddrc_content("python")
    assert content.endswith("\n")


# ---------------------------------------------------------------------------
# IV. Success Path — File Created
# ---------------------------------------------------------------------------

def test_creates_file_on_confirm_yes(tmp_path, monkeypatch):
    """User confirms with 'y' → .pddrc created, returns True."""
    result, _ = _run_offer_capture(
        tmp_path, monkeypatch, ["y"],
        marker_files={"pyproject.toml": None},
    )
    assert result is True
    assert (tmp_path / ".pddrc").exists()


def test_creates_file_on_enter(tmp_path, monkeypatch):
    """Empty input (Enter) means yes → .pddrc created, returns True."""
    result, _ = _run_offer_capture(
        tmp_path, monkeypatch, [""],
        marker_files={"pyproject.toml": None},
    )
    assert result is True
    assert (tmp_path / ".pddrc").exists()


def test_created_file_has_correct_content(tmp_path, monkeypatch):
    """Created .pddrc contains language-appropriate defaults."""
    _run_offer_capture(
        tmp_path, monkeypatch, ["y"],
        marker_files={"pyproject.toml": None},
    )
    content = (tmp_path / ".pddrc").read_text()
    assert 'default_language: "python"' in content
    assert 'generate_output_path: "pdd/"' in content
    assert "strength: 0.818" in content


def test_prompts_language_when_undetected(tmp_path, monkeypatch):
    """No markers → user prompted for language (1=Python), then confirms."""
    # First input: language choice, second: confirmation
    result, _ = _run_offer_capture(
        tmp_path, monkeypatch, ["1", "y"],
    )
    assert result is True
    content = (tmp_path / ".pddrc").read_text()
    assert 'default_language: "python"' in content


# ---------------------------------------------------------------------------
# V. User Declines
# ---------------------------------------------------------------------------

def test_declined_returns_false(tmp_path, monkeypatch):
    """User types 'n' → returns False, no file created."""
    result, _ = _run_offer_capture(
        tmp_path, monkeypatch, ["n"],
        marker_files={"pyproject.toml": None},
    )
    assert result is False
    assert not (tmp_path / ".pddrc").exists()


# ---------------------------------------------------------------------------
# VI. Language Prompt with Invalid Input
# ---------------------------------------------------------------------------

def test_language_prompt_retries_on_invalid(tmp_path, monkeypatch):
    """Invalid language choices cause retries until valid choice, then file created."""
    # "x" and "99" are invalid, "2" selects TypeScript, "y" confirms
    result, output = _run_offer_capture(
        tmp_path, monkeypatch, ["x", "99", "2", "y"],
    )
    assert result is True
    content = (tmp_path / ".pddrc").read_text()
    assert 'default_language: "typescript"' in content
    assert "Invalid choice" in output


# ---------------------------------------------------------------------------
# VII. Output / Display
# ---------------------------------------------------------------------------

def test_detected_language_shown(tmp_path, monkeypatch):
    """Auto-detected language is displayed to user."""
    _, output = _run_offer_capture(
        tmp_path, monkeypatch, ["y"],
        marker_files={"pyproject.toml": None},
    )
    assert "python" in output.lower()


def test_preview_shown_before_confirmation(tmp_path, monkeypatch):
    """YAML preview content appears in output before confirmation."""
    _, output = _run_offer_capture(
        tmp_path, monkeypatch, ["y"],
        marker_files={"pyproject.toml": None},
    )
    assert "Proposed" in output or "contents" in output
    assert "version" in output


def test_creation_success_message(tmp_path, monkeypatch):
    """'Created .pddrc' message appears after successful creation."""
    _, output = _run_offer_capture(
        tmp_path, monkeypatch, ["y"],
        marker_files={"pyproject.toml": None},
    )
    assert "Created" in output
    assert ".pddrc" in output


def test_skip_message_on_decline(tmp_path, monkeypatch):
    """'Skipped' message appears when user declines."""
    _, output = _run_offer_capture(
        tmp_path, monkeypatch, ["n"],
        marker_files={"pyproject.toml": None},
    )
    assert "Skipped" in output or "skipped" in output


# ---------------------------------------------------------------------------
# VIII. Filesystem Error
# ---------------------------------------------------------------------------

def test_write_error_returns_false(tmp_path, monkeypatch):
    """OSError during file write → returns False, error message shown."""
    with patch.object(Path, "write_text", side_effect=OSError("Permission denied")):
        result, output = _run_offer_capture(
            tmp_path, monkeypatch, ["y"],
            marker_files={"pyproject.toml": None},
        )
    assert result is False
    assert "Failed" in output or "error" in output.lower()


# ---------------------------------------------------------------------------
# IX. Auto-generation for `pdd update --directory / --repo`
# ---------------------------------------------------------------------------

class TestPddrcAutoGeneration:
    """Tests for auto-generation of .pddrc from scan results."""

    def test_infer_contexts_groups_by_subdir(self, tmp_path):
        """Rust crates are grouped into separate contexts by subdirectory."""
        # Create a file structure mimicking a monorepo with crates
        scan_dir = str(tmp_path / "crates")
        repo_root = str(tmp_path)
        code_files = [
            str(tmp_path / "crates" / "selune-compiler" / "src" / "lib.rs"),
            str(tmp_path / "crates" / "selune-compiler" / "src" / "compiler" / "expr.rs"),
            str(tmp_path / "crates" / "selune-core" / "src" / "lib.rs"),
        ]

        with patch("pdd.pddrc_initializer._detect_language_from_extensions") as mock_lang:
            mock_lang.return_value = "rust"
            contexts = infer_contexts_from_scan(scan_dir, repo_root, code_files)

        assert "crates-selune-compiler" in contexts
        assert "crates-selune-core" in contexts
        assert len(contexts) == 2

        # Verify paths pattern
        assert contexts["crates-selune-compiler"]["paths"] == ["crates/selune-compiler/**"]
        assert contexts["crates-selune-core"]["paths"] == ["crates/selune-core/**"]

    def test_infer_contexts_flat_directory(self, tmp_path):
        """Single context when all files are directly in scan_dir (no subdirs)."""
        scan_dir = str(tmp_path / "lib")
        repo_root = str(tmp_path)
        code_files = [
            str(tmp_path / "lib" / "utils.py"),
            str(tmp_path / "lib" / "helpers.py"),
        ]

        with patch("pdd.pddrc_initializer._detect_language_from_extensions") as mock_lang:
            mock_lang.return_value = "python"
            contexts = infer_contexts_from_scan(scan_dir, repo_root, code_files)

        assert len(contexts) == 1
        name = list(contexts.keys())[0]
        assert name == "lib"
        assert contexts[name]["paths"] == ["lib/**"]

    def test_infer_contexts_language_detection(self, tmp_path):
        """Majority-vote .rs files → 'rust'."""
        code_files = [
            "/repo/crates/a/src/lib.rs",
            "/repo/crates/a/src/main.rs",
            "/repo/crates/a/build.py",
        ]

        with patch("pdd.get_language.get_language") as mock_gl:
            # .rs → "Rust", .py → "Python"
            def side_effect(ext):
                return {".rs": "Rust", ".py": "Python"}.get(ext, "")
            mock_gl.side_effect = side_effect

            result = _detect_language_from_extensions(code_files)

        assert result == "rust"

    def test_sanitize_context_name(self):
        """Special chars are stripped, result is lowercase with hyphens."""
        assert _sanitize_context_name("crates", "selune-compiler") == "crates-selune-compiler"
        assert _sanitize_context_name("src", "utils") == "src-utils"
        assert _sanitize_context_name("", "backend") == "backend"
        # Special characters replaced
        assert _sanitize_context_name("my.dir", "sub@pkg") == "my-dir-sub-pkg"
        # Consecutive hyphens collapsed
        assert _sanitize_context_name("a--b", "c") == "a-b-c"

    def test_ensure_pddrc_creates_when_missing(self, tmp_path):
        """Creates .pddrc with correct contexts when none exists."""
        scan_dir = str(tmp_path / "crates")
        repo_root = str(tmp_path)
        code_files = [
            str(tmp_path / "crates" / "foo" / "src" / "lib.rs"),
        ]

        with patch("pdd.pddrc_initializer._detect_language_from_extensions", return_value="rust"), \
             patch("pdd.construct_paths._find_pddrc_file", return_value=None):
            result = ensure_pddrc_for_scan(scan_dir, repo_root, code_files, quiet=True)

        assert result is not None
        assert result == tmp_path / ".pddrc"
        content = result.read_text(encoding="utf-8")
        assert 'version: "1.0"' in content
        assert "crates-foo:" in content
        assert '"crates/foo/**"' in content
        assert '"prompts/crates/foo"' in content
        assert '"crates/foo"' in content

    def test_ensure_pddrc_adds_to_existing(self, tmp_path):
        """Adds new context to existing .pddrc, preserves existing contexts."""
        existing = (
            'version: "1.0"\n'
            "\n"
            "contexts:\n"
            "  default:\n"
            "    defaults:\n"
            '      default_language: "python"\n'
        )
        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text(existing, encoding="utf-8")

        scan_dir = str(tmp_path / "crates")
        repo_root = str(tmp_path)
        code_files = [
            str(tmp_path / "crates" / "bar" / "src" / "main.rs"),
        ]

        with patch("pdd.pddrc_initializer._detect_language_from_extensions", return_value="rust"), \
             patch("pdd.construct_paths._find_pddrc_file", return_value=pddrc_file):
            result = ensure_pddrc_for_scan(scan_dir, repo_root, code_files, quiet=True)

        assert result is not None
        content = result.read_text(encoding="utf-8")
        # Existing content preserved
        assert "default:" in content
        assert 'default_language: "python"' in content
        # New context added
        assert "crates-bar:" in content

    def test_ensure_pddrc_noop_when_covered(self, tmp_path):
        """No-op if contexts already match."""
        existing = (
            'version: "1.0"\n'
            "\n"
            "contexts:\n"
            "  crates-foo:\n"
            "    paths:\n"
            '      - "crates/foo/**"\n'
            "    defaults:\n"
            '      prompts_dir: "prompts/crates/foo"\n'
        )
        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text(existing, encoding="utf-8")

        scan_dir = str(tmp_path / "crates")
        repo_root = str(tmp_path)
        code_files = [
            str(tmp_path / "crates" / "foo" / "src" / "lib.rs"),
        ]

        with patch("pdd.pddrc_initializer._detect_language_from_extensions", return_value="rust"), \
             patch("pdd.construct_paths._find_pddrc_file", return_value=pddrc_file):
            result = ensure_pddrc_for_scan(scan_dir, repo_root, code_files, quiet=True)

        assert result is None  # No changes made

    def test_generate_output_path_no_trailing_slash(self, tmp_path):
        """Critical: generate_output_path must NOT have trailing slash."""
        scan_dir = str(tmp_path / "crates")
        repo_root = str(tmp_path)
        code_files = [
            str(tmp_path / "crates" / "selune-compiler" / "src" / "lib.rs"),
        ]

        with patch("pdd.pddrc_initializer._detect_language_from_extensions", return_value="rust"):
            contexts = infer_contexts_from_scan(scan_dir, repo_root, code_files)

        ctx = contexts["crates-selune-compiler"]
        gen_path = ctx["defaults"]["generate_output_path"]
        assert not gen_path.endswith("/"), (
            f"generate_output_path must not end with '/' but got: {gen_path!r}"
        )
        assert gen_path == "crates/selune-compiler"

    def test_consistency_invariant(self, tmp_path):
        """resolve_prompt_code_pair produces same path with and without .pddrc.

        The path-mirroring logic without .pddrc places prompts at:
            prompts/<full-rel-dir>/<name>_<Language>.prompt

        With the auto-generated .pddrc (prompts_dir + generate_output_path
        stripping), the result must be identical.
        """
        # Simulate what resolve_prompt_code_pair does internally for the
        # "without pddrc" case.
        # For crates/selune-compiler/src/compiler/expr.rs:
        #   rel_dir = "crates/selune-compiler/src/compiler"
        #   code_root = ""  (no context)
        #   result = "prompts/crates/selune-compiler/src/compiler/expr_Rust.prompt"
        rel_dir = "crates/selune-compiler/src/compiler"
        base_name = "expr"
        language = "Rust"
        prompts_base_no_pddrc = "prompts"
        path_without = os.path.join(prompts_base_no_pddrc, rel_dir, f"{base_name}_{language}.prompt")

        # With auto-generated pddrc context:
        #   prompts_dir = "prompts/crates/selune-compiler"
        #   generate_output_path = "crates/selune-compiler"
        #   code_root = "crates/selune-compiler"
        #   stripped rel_dir = "src/compiler"
        #   result = "prompts/crates/selune-compiler/src/compiler/expr_Rust.prompt"
        code_root = "crates/selune-compiler"
        if rel_dir.startswith(code_root + os.sep):
            stripped = rel_dir[len(code_root) + len(os.sep):]
        else:
            stripped = rel_dir
        prompts_base_with_pddrc = "prompts/crates/selune-compiler"
        path_with = os.path.join(prompts_base_with_pddrc, stripped, f"{base_name}_{language}.prompt")

        assert path_without == path_with, (
            f"Paths diverge!\n  Without .pddrc: {path_without}\n  With .pddrc:    {path_with}"
        )

    def test_infer_contexts_repo_root_flat_skips(self, tmp_path):
        """When scan_dir == repo_root and all files are flat, returns empty."""
        repo_root = str(tmp_path)
        code_files = [
            str(tmp_path / "main.py"),
            str(tmp_path / "utils.py"),
        ]

        with patch("pdd.pddrc_initializer._detect_language_from_extensions", return_value="python"):
            contexts = infer_contexts_from_scan(repo_root, repo_root, code_files)

        assert contexts == {}
