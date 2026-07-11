"""Regression tests for issue #1903 — adopt the runner-collected co-located test.

PDD derives its canonical test-output path purely from ``.pddrc`` /
default conventions (``tests/test_{basename}{ext}``), blind to the project's
real test runner. On a jest/Next.js project the test the runner actually
collects is co-located (e.g. ``.../__test__/page.test.tsx``) while PDD writes
and verifies a root ``tests/`` shadow the runner never sees — a false-green.

The fix adds a pure detector (:func:`find_collocated_test`) and an adopter
(:func:`resolve_test_output_path`) and wires them into the two write-decision
points: :func:`cmd_test_main` (direct ``pdd test``) and
:func:`get_pdd_file_paths` (sync / change). These tests pin that behavior and
guard the regression traps (Python default unchanged, honor explicit pins,
never adopt on ambiguity, never raise).

The integration tests drive the REAL ``construct_paths`` (never a mock of it):
``construct_paths`` injects a generated-default ``test_output_path`` back into
the ``resolved_config`` it returns, so a mocked ``construct_paths`` would hide
the very pollution this fix routes around (the provenance is read from the raw
``.pddrc`` defaults instead). Mocking path construction here would produce a
false green — see the round-4 blocker.
"""
import json
import sys
from pathlib import Path

# Prioritize the local package (mirrors sibling test modules).
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import pytest

from pdd.content_selector import (
    _pins_test_output_location,
    _validated_project_path,
    configured_test_output_pinned,
    find_collocated_test,
    find_runner_collected_test_path,
    resolve_test_output_path,
)
from pdd.sync_determine_operation import (
    get_pdd_file_paths,
    _adopt_collocated_test,
    _get_pdd_file_paths_uncollocated,
)
from pdd.cmd_test_main import cmd_test_main
from pdd.code_generator_main import _is_test_output_path


def _write(path: Path, content: str = "// placeholder\n") -> Path:
    """Create *path* (and parents) with *content*; return it."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# 1) find_collocated_test — the pure detector
# ---------------------------------------------------------------------------

class TestFindCollocatedTest:
    def test_finds_test_under_dunder_test_dir(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        code = _write(tmp_path / "frontend/src/app/contributions/page.tsx")
        real = _write(code.parent / "__test__" / "page.test.tsx")
        assert find_collocated_test(code).resolve() == real.resolve()

    def test_finds_spec_file(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        code = _write(tmp_path / "src/widget.ts")
        spec = _write(code.parent / "widget.spec.ts")
        assert find_collocated_test(code).resolve() == spec.resolve()

    def test_finds_beside_module_test(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        code = _write(tmp_path / "src/button.tsx")
        test = _write(code.parent / "button.test.tsx")
        assert find_collocated_test(code).resolve() == test.resolve()

    def test_finds_python_sibling(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        code = _write(tmp_path / "src/foo.py", "def foo():\n    return 1\n")
        test = _write(tmp_path / "tests" / "test_foo.py",
                      "def test_foo():\n    assert True\n")
        assert find_collocated_test(code).resolve() == test.resolve()

    def test_module_self_never_counts(self, tmp_path):
        # A lone module with no sibling test -> None (the module is excluded).
        code = _write(tmp_path / "src/page.tsx")
        assert find_collocated_test(code) is None

    def test_zero_matches_returns_none(self, tmp_path):
        code = _write(tmp_path / "src/thing.ts")
        # A same-stem non-test neighbor must not be mistaken for a test.
        _write(code.parent / "thing.helper.ts")
        assert find_collocated_test(code) is None

    def test_multiple_matches_returns_none(self, tmp_path):
        code = _write(tmp_path / "src/page.tsx")
        _write(code.parent / "page.test.tsx")
        _write(code.parent / "__tests__" / "page.test.tsx")
        assert find_collocated_test(code) is None

    def test_bad_path_returns_none_without_raising(self):
        assert find_collocated_test("/no/such/dir/page.tsx") is None
        assert find_collocated_test("") is None

    def test_unsupported_language_never_matches_python_sibling(self, tmp_path):
        # Go module with a same-stem Python test nearby must NOT be adopted
        # (cross-language mis-adoption regression, #1903 finding 1).
        code = _write(tmp_path / "src/foo.go", "package main\n")
        _write(tmp_path / "tests" / "test_foo.py", "def test_foo():\n    assert True\n")
        assert find_collocated_test(code) is None

    def test_unsupported_suffix_returns_none(self, tmp_path):
        code = _write(tmp_path / "src/foo.rs", "fn main() {}\n")
        _write(tmp_path / "tests" / "test_foo.py", "def test_foo():\n    assert True\n")
        assert find_collocated_test(code) is None


# ---------------------------------------------------------------------------
# 2) resolve_test_output_path — the adopter
# ---------------------------------------------------------------------------

class TestResolveTestOutputPath:
    def test_adopts_collocated_over_shadow(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        code = _write(tmp_path / "frontend/src/app/contributions/page.tsx")
        real = _write(code.parent / "__test__" / "page.test.tsx")
        shadow = tmp_path / "tests" / "test_page.tsx"  # runner-blind, not on disk
        got = resolve_test_output_path(code, shadow, user_pinned=False)
        assert Path(got).resolve() == real.resolve()

    def test_user_pinned_returns_derived_unchanged(self, tmp_path):
        code = _write(tmp_path / "frontend/src/app/contributions/page.tsx")
        _write(code.parent / "__test__" / "page.test.tsx")
        shadow = tmp_path / "tests" / "test_page.tsx"
        got = resolve_test_output_path(code, shadow, user_pinned=True)
        assert Path(got) == shadow

    def test_returns_derived_when_sibling_equals_derived(self, tmp_path):
        code = _write(tmp_path / "src/foo.py", "def foo():\n    return 1\n")
        derived = _write(tmp_path / "tests" / "test_foo.py",
                         "def test_foo():\n    assert True\n")
        got = resolve_test_output_path(code, derived, user_pinned=False)
        assert Path(got).resolve() == derived.resolve()

    def test_returns_derived_when_no_sibling(self, tmp_path):
        code = _write(tmp_path / "src/page.tsx")
        shadow = tmp_path / "tests" / "test_page.tsx"
        got = resolve_test_output_path(code, shadow, user_pinned=False)
        assert Path(got) == shadow

    def test_go_module_keeps_derived_go_path(self, tmp_path):
        # Go generation must not be retargeted into a co-located `.py` test.
        code = _write(tmp_path / "src/foo.go", "package main\n")
        _write(tmp_path / "tests" / "test_foo.py", "def test_foo():\n    assert True\n")
        derived = tmp_path / "tests" / "test_foo.go"
        got = resolve_test_output_path(code, derived, user_pinned=False)
        assert Path(got) == derived


# ---------------------------------------------------------------------------
# 2b) Greenfield runner discovery — issue #1903 §A (write the FIRST test where
#     the runner collects it, not a runner-blind tests/ shadow).
# ---------------------------------------------------------------------------

class TestGreenfieldRunnerDiscovery:
    def test_jest_config_js_greenfield_co_locates(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "jest.config.js", "module.exports = {};\n")
        code = _write(tmp_path / "src/app/page.tsx",
                      "export default function P(){return null;}\n")
        got = find_runner_collected_test_path(code)
        assert got is not None
        assert Path(got).resolve() == (
            tmp_path / "src/app/__test__/page.test.tsx"
        ).resolve()

    def test_package_json_devdep_jest_detected(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", '{"devDependencies": {"jest": "^29"}}\n')
        code = _write(tmp_path / "src/widget.ts")
        got = find_runner_collected_test_path(code)
        assert Path(got).resolve() == (
            tmp_path / "src/__test__/widget.test.ts"
        ).resolve()

    def test_package_json_inline_jest_block_detected(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", '{"jest": {"testEnvironment": "jsdom"}}\n')
        code = _write(tmp_path / "src/button.jsx")
        got = find_runner_collected_test_path(code)
        assert Path(got).resolve() == (
            tmp_path / "src/__test__/button.test.jsx"
        ).resolve()

    def test_vitest_config_detected(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "vitest.config.ts", "export default {};\n")
        code = _write(tmp_path / "lib/util.ts")
        got = find_runner_collected_test_path(code)
        assert Path(got).resolve() == (
            tmp_path / "lib/__test__/util.test.ts"
        ).resolve()

    def test_config_found_by_walking_up_to_root(self, tmp_path, monkeypatch):
        # jest.config sits at the project root; the module is nested deep.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "frontend/jest.config.js", "module.exports = {};\n")
        code = _write(tmp_path / "frontend/src/app/contributions/page.tsx")
        got = find_runner_collected_test_path(code)
        assert Path(got).resolve() == (
            tmp_path / "frontend/src/app/contributions/__test__/page.test.tsx"
        ).resolve()

    def test_no_runner_config_returns_none(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        code = _write(tmp_path / "src/page.tsx")
        assert find_runner_collected_test_path(code) is None

    def test_package_json_without_runner_ignored(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", '{"dependencies": {"react": "^18"}}\n')
        code = _write(tmp_path / "src/page.tsx")
        assert find_runner_collected_test_path(code) is None

    def test_python_module_keeps_pytest_default(self, tmp_path, monkeypatch):
        # A JS runner nearby must NOT redirect Python (pytest tests/ is correct).
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", '{"devDependencies": {"jest": "^29"}}\n')
        code = _write(tmp_path / "src/foo.py", "def foo():\n    return 1\n")
        assert find_runner_collected_test_path(code) is None

    def test_malformed_package_json_returns_none(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", "{ this is not json\n")
        code = _write(tmp_path / "src/page.tsx")
        assert find_runner_collected_test_path(code) is None

    def test_resolve_greenfield_co_locates_over_shadow(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "frontend/package.json",
               '{"devDependencies":{"jest":"^29"}}\n')
        code = _write(tmp_path / "frontend/src/app/contributions/page.tsx")
        shadow = tmp_path / "tests" / "test_page.tsx"  # runner-blind, not on disk
        got = resolve_test_output_path(code, shadow, user_pinned=False)
        assert Path(got).resolve() == (
            code.parent / "__test__" / "page.test.tsx"
        ).resolve()

    def test_resolve_greenfield_honors_user_pin(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "jest.config.js", "module.exports = {};\n")
        code = _write(tmp_path / "src/page.tsx")
        shadow = tmp_path / "tests" / "test_page.tsx"
        got = resolve_test_output_path(code, shadow, user_pinned=True)
        assert Path(got) == shadow


# ---------------------------------------------------------------------------
# 3) get_pdd_file_paths integration — mirror the investigator repro using the
#    REAL construct_paths (a mock would inject nothing and mask the round-4
#    resolved_config-pollution blocker this fix routes around — see #1903).
# ---------------------------------------------------------------------------

def _build_jest_project(tmp_path: Path, *, test_output_path: str | None) -> tuple[Path, Path]:
    """Realistic Next.js/jest project on disk with a co-located test.

    Writes a single-context ``.pddrc`` (generate path + language + example path,
    plus an explicit ``test_output_path`` only when *test_output_path* is given),
    a real prompt, the module, and the co-located ``__test__/page.test.tsx`` the
    runner collects. Returns ``(code, real_test)``. No ``construct_paths`` mock —
    the whole derivation runs for real.
    """
    pddrc = (
        'version: "1.0"\n'
        "contexts:\n"
        "  default:\n"
        "    defaults:\n"
        '      generate_output_path: "frontend/src/app/contributions/"\n'
        '      default_language: "typescriptreact"\n'
        '      example_output_path: "examples/"\n'
    )
    if test_output_path is not None:
        pddrc += f'      test_output_path: "{test_output_path}"\n'
    _write(tmp_path / ".pddrc", pddrc)
    code = _write(
        tmp_path / "frontend/src/app/contributions/page.tsx",
        "export default function Page() { return null; }\n",
    )
    real = _write(code.parent / "__test__" / "page.test.tsx", "test('x', () => {});\n")
    _write(tmp_path / "prompts/page_typescriptreact.prompt", "Generate a page.\n")
    return code, real


def test_get_pdd_file_paths_adopts_collocated_jest_test(tmp_path, monkeypatch):
    """Default naming (.pddrc omits test_output_path) adopts the co-located test the
    jest runner collects, not the runner-blind shadow. Uses the REAL construct_paths,
    whose resolved_config injects a generated-default test_output_path — the exact
    pollution the round-4 blocker exposed (#1903)."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    _, real = _build_jest_project(tmp_path, test_output_path=None)

    # Pre-fix behavior: the raw derivation returns the runner-blind shadow and the
    # provenance signal is NOT pinned (the .pddrc omits the test location). This is
    # the assertion the round-4 blocker would have failed with a mocked construct_paths.
    raw, raw_pinned = _get_pdd_file_paths_uncollocated("page", "typescriptreact", "prompts")
    assert Path(raw["test"]).name == "test_page.tsx"
    assert Path(raw["test"]).resolve() != real.resolve()
    assert raw_pinned is False  # no explicit test config -> adoption allowed

    # Post-fix behavior: the public entry point adopts the co-located test.
    paths = get_pdd_file_paths("page", "typescriptreact", "prompts")
    assert Path(paths["test"]).resolve() == real.resolve()
    assert [Path(p).resolve() for p in paths["test_files"]] == [real.resolve()]
    # No stray tests/ shadow is selected.
    shadow = (tmp_path / "tests" / "test_page.tsx").resolve()
    assert all(Path(p).resolve() != shadow for p in paths["test_files"])


def _build_greenfield_jest_project(tmp_path: Path) -> tuple[Path, Path]:
    """Fresh Next.js/jest project with a runner config but NO test yet (#1903 §A).

    Writes a single-context ``.pddrc`` (no ``test_output_path`` override), a
    ``jest.config.js`` and a ``package.json`` declaring jest under ``frontend/``,
    a real prompt, and the module — but deliberately NO co-located test. Returns
    ``(code, expected_runner_path)`` where ``expected_runner_path`` is the
    co-located ``__test__/page.test.tsx`` the jest runner collects (not on disk
    yet). Mirrors :func:`_build_jest_project` sans the pre-existing test.
    """
    pddrc = (
        'version: "1.0"\n'
        "contexts:\n"
        "  default:\n"
        "    defaults:\n"
        '      generate_output_path: "frontend/src/app/contributions/"\n'
        '      default_language: "typescriptreact"\n'
        '      example_output_path: "examples/"\n'
    )
    _write(tmp_path / ".pddrc", pddrc)
    _write(tmp_path / "frontend/jest.config.js", "module.exports = { rootDir: '.' };\n")
    _write(tmp_path / "frontend/package.json", '{"devDependencies": {"jest": "^29"}}\n')
    code = _write(
        tmp_path / "frontend/src/app/contributions/page.tsx",
        "export default function Page() { return null; }\n",
    )
    _write(tmp_path / "prompts/page_typescriptreact.prompt", "Generate a page.\n")
    expected = tmp_path / "frontend/src/app/contributions/__test__/page.test.tsx"
    return code, expected


def test_get_pdd_file_paths_greenfield_writes_runner_collected_path(tmp_path, monkeypatch):
    """Issue #1903 §A acceptance: a fresh Next.js/jest project (runner config,
    NO existing test, NO ``.pddrc`` ``test_output_path`` override) targets the
    FIRST test at the runner-collected co-located ``__test__/page.test.tsx`` —
    never a root ``tests/`` orphan. Uses the REAL construct_paths."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    _code, expected = _build_greenfield_jest_project(tmp_path)
    assert not expected.exists()  # greenfield: the runner test does not exist yet

    # Pre-fix behavior: the raw derivation is the runner-blind shadow, unpinned.
    raw, raw_pinned = _get_pdd_file_paths_uncollocated("page", "typescriptreact", "prompts")
    assert Path(raw["test"]).name == "test_page.tsx"
    assert raw_pinned is False  # no explicit test config -> greenfield allowed

    # Post-fix behavior: the public entry point targets the runner-collected path.
    paths = get_pdd_file_paths("page", "typescriptreact", "prompts")
    assert Path(paths["test"]).resolve() == expected.resolve()
    # No root tests/ shadow orphan is selected.
    shadow = (tmp_path / "tests" / "test_page.tsx").resolve()
    assert Path(paths["test"]).resolve() != shadow
    assert all(Path(p).resolve() != shadow for p in paths["test_files"])


def test_get_pdd_file_paths_no_adopt_when_explicit_non_default(tmp_path, monkeypatch):
    """Explicit `.pddrc test_output_path: contract-tests/` is never overridden
    (real construct_paths; the pin is read from the raw .pddrc defaults)."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    _, real = _build_jest_project(tmp_path, test_output_path="contract-tests/")

    _, pinned = _get_pdd_file_paths_uncollocated("page", "typescriptreact", "prompts")
    assert pinned is True
    paths = get_pdd_file_paths("page", "typescriptreact", "prompts")
    assert "contract-tests" in Path(paths["test"]).parts
    assert Path(paths["test"]).resolve() != real.resolve()


def test_pins_predicate_explicit_empty_is_pinned():
    """Round-8 finding: an explicit empty ``test_output_path``/``outputs.test.path``
    (root-level output) is a real user pin — presence, not truthiness. A genuinely
    absent or explicitly-null key is not a pin."""
    assert _pins_test_output_location({"test_output_path": ""}) is True
    assert _pins_test_output_location({"outputs": {"test": {"path": ""}}}) is True
    assert _pins_test_output_location({}) is False
    assert _pins_test_output_location({"test_output_path": None}) is False


def test_get_pdd_file_paths_no_adopt_when_explicit_empty_test_output(tmp_path, monkeypatch):
    """Round-8 finding: `.pddrc test_output_path: ""` (explicit root-level output) is a
    user pin and must NOT be adopted away to the co-located test (real construct_paths).
    Fails before the presence-based `_pins_test_output_location`."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    _, real = _build_jest_project(tmp_path, test_output_path="")

    _, pinned = _get_pdd_file_paths_uncollocated("page", "typescriptreact", "prompts")
    assert pinned is True
    paths = get_pdd_file_paths("page", "typescriptreact", "prompts")
    assert Path(paths["test"]).resolve() != real.resolve()


def test_get_pdd_file_paths_no_adopt_when_explicit_tests_dir(tmp_path, monkeypatch):
    """Explicit `.pddrc test_output_path: tests/` (equal to the default value) is
    still an explicit pin -> NO adoption (real construct_paths; finding-2
    regression)."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    _, real = _build_jest_project(tmp_path, test_output_path="tests/")

    _, pinned = _get_pdd_file_paths_uncollocated("page", "typescriptreact", "prompts")
    assert pinned is True
    paths = get_pdd_file_paths("page", "typescriptreact", "prompts")
    assert Path(paths["test"]).parts[-2:] == ("tests", "test_page.tsx")
    assert Path(paths["test"]).resolve() != real.resolve()


def test_get_pdd_file_paths_env_var_pins(tmp_path, monkeypatch):
    """PDD_TEST_OUTPUT_PATH pins the location -> NO adoption (real construct_paths)."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_TEST_OUTPUT_PATH", "contract-tests/")
    _, real = _build_jest_project(tmp_path, test_output_path=None)

    _, pinned = _get_pdd_file_paths_uncollocated("page", "typescriptreact", "prompts")
    assert pinned is True
    paths = get_pdd_file_paths("page", "typescriptreact", "prompts")
    assert Path(paths["test"]).resolve() != real.resolve()


def test_get_pdd_file_paths_no_adopt_with_prompts_dir_anchored_context(
    tmp_path, monkeypatch
):
    """Finding-2 regression: an explicit test_output_path lives in a context
    selected by a prompts_dir prefix (`prompts/frontend`), NOT by the bare
    basename/CWD. The authoritative resolution must see the pin and NOT adopt —
    a bare-basename context lookup would miss it and wrongly retarget. Uses the
    REAL construct_paths (no mock) so the prompts_dir anchoring actually runs."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    _write(
        tmp_path / ".pddrc",
        'version: "1.0"\n'
        "contexts:\n"
        "  frontend:\n"
        "    defaults:\n"
        '      prompts_dir: "prompts/frontend"\n'
        '      generate_output_path: "frontend/src/app/contributions/"\n'
        '      test_output_path: "contract-tests/"\n'
        '      default_language: "typescriptreact"\n'
        "  default:\n"
        "    defaults:\n"
        '      default_language: "python"\n',
    )
    code = _write(
        tmp_path / "frontend/src/app/contributions/page.tsx",
        "export default function Page() { return null; }\n",
    )
    real = _write(
        code.parent / "__test__" / "page.test.tsx", "test('x', () => {});\n"
    )
    _write(
        tmp_path / "prompts/frontend/page_typescriptreact.prompt",
        "Generate a contributions page.\n",
    )

    # The authoritative (prompts_dir-anchored) resolution sees the explicit pin...
    raw, pinned = _get_pdd_file_paths_uncollocated(
        "page", "typescriptreact", "prompts/frontend"
    )
    assert pinned is True
    # ...and the co-located test IS otherwise detectable, so only the pin (not a
    # missing sibling) prevents adoption — proving the regression is real.
    would_adopt = _adopt_collocated_test(dict(raw), user_pinned=False)
    assert Path(would_adopt["test"]).resolve() == real.resolve()

    # Public entry point: explicit pin honored, co-located test NOT adopted.
    paths = get_pdd_file_paths("page", "typescriptreact", "prompts/frontend")
    assert "contract-tests" in Path(paths["test"]).parts
    assert Path(paths["test"]).resolve() != real.resolve()


def test_get_pdd_file_paths_python_default_unchanged(tmp_path, monkeypatch):
    """Standard Python layout (src/foo.py + tests/test_foo.py) is a no-op: the
    derived shadow equals the real co-located test, so nothing is retargeted
    (real construct_paths)."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    _write(
        tmp_path / ".pddrc",
        'version: "1.0"\n'
        "contexts:\n"
        "  default:\n"
        "    defaults:\n"
        '      generate_output_path: "src/"\n'
        '      test_output_path: "tests/"\n'
        '      example_output_path: "examples/"\n'
        '      default_language: "python"\n',
    )
    _write(tmp_path / "src/foo.py", "def foo():\n    return 1\n")
    real = _write(tmp_path / "tests/test_foo.py", "def test_foo():\n    assert True\n")
    _write(tmp_path / "prompts/foo_python.prompt", "Generate foo\n")

    paths = get_pdd_file_paths("foo", "python", "prompts")
    assert Path(paths["test"]).resolve() == real.resolve()


# ---------------------------------------------------------------------------
# 3b) Provenance signal — explicit-vs-default detection
# ---------------------------------------------------------------------------

class TestExplicitConfigProvenance:
    def test_pins_predicate_flat_key(self):
        assert _pins_test_output_location({"test_output_path": "tests/"}) is True

    def test_pins_predicate_template_form(self):
        assert _pins_test_output_location(
            {"outputs": {"test": {"path": "tests/test_{name}{ext}"}}}
        ) is True

    def test_pins_predicate_absent(self):
        assert _pins_test_output_location({"generate_output_path": "src/"}) is False
        assert _pins_test_output_location({}) is False

    def test_configured_pin_reads_raw_default_context(self, tmp_path, monkeypatch):
        """`configured_test_output_pinned` reads the raw `.pddrc` default context —
        NOT construct_paths' resolved_config — so a `default`-context test_output_path
        is recognized while an omitted one is not."""
        monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
        _write(
            tmp_path / ".pddrc",
            'version: "1.0"\ncontexts:\n  default:\n    defaults:\n'
            '      test_output_path: "contract-tests/"\n',
        )
        code = _write(tmp_path / "src/foo.py", "def foo():\n    return 1\n")
        assert configured_test_output_pinned(code) is True

        # A sibling project with no test_output_path -> not pinned.
        other = tmp_path.parent / (tmp_path.name + "_other")
        _write(
            other / ".pddrc",
            'version: "1.0"\ncontexts:\n  default:\n    defaults:\n'
            '      generate_output_path: "src/"\n',
        )
        other_code = _write(other / "src/foo.py", "def foo():\n    return 1\n")
        assert configured_test_output_pinned(other_code) is False

    def test_env_var_pins_via_configured(self, tmp_path, monkeypatch):
        """PDD_TEST_OUTPUT_PATH alone makes the location pinned (no .pddrc needed)."""
        monkeypatch.setenv("PDD_TEST_OUTPUT_PATH", "contract-tests/")
        code = _write(tmp_path / "src/foo.py", "def foo():\n    return 1\n")
        assert configured_test_output_pinned(code) is True


# ---------------------------------------------------------------------------
# 4) cmd_test_main — direct `pdd test` (REAL construct_paths; only generation
#    is mocked so path construction and adoption run end-to-end).
# ---------------------------------------------------------------------------

@pytest.fixture
def local_ctx():
    """Click context forcing local execution (no cloud round-trip)."""
    import click
    ctx = click.Context(click.Command("test"))
    ctx.obj = {
        "verbose": False,
        "strength": 0.5,
        "temperature": 0.0,
        "force": False,
        "quiet": True,
        "local": True,
    }
    return ctx


def _cmd_project(tmp_path: Path, *, test_output_path: str | None) -> tuple[Path, Path, Path]:
    """A minimal Python project for `pdd test`: `.pddrc` + module + co-located
    (empty) sibling test + prompt. Returns ``(code, prompt, collocated)``."""
    pddrc = (
        'version: "1.0"\n'
        "contexts:\n"
        "  default:\n"
        "    defaults:\n"
        '      generate_output_path: "src/"\n'
        '      default_language: "python"\n'
    )
    if test_output_path is not None:
        pddrc += f'      test_output_path: "{test_output_path}"\n'
    _write(tmp_path / ".pddrc", pddrc)
    code = _write(tmp_path / "src/foo.py", "def foo():\n    return 1\n")
    prompt = _write(tmp_path / "prompts/foo_python.prompt", "Generate foo\n")
    # Empty co-located sibling -> first-time generation (no churn).
    collocated = _write(code.parent / "test_foo.py", "")
    return code, prompt, collocated


def test_cmd_test_main_retargets_to_collocated_when_output_absent(
    tmp_path, local_ctx, monkeypatch
):
    """With no --output and no explicit .pddrc pin, direct `pdd test` writes to the
    co-located sibling instead of the runner-blind root shadow (real construct_paths)."""
    from unittest.mock import patch

    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    code, prompt, collocated = _cmd_project(tmp_path, test_output_path=None)
    shadow = tmp_path / "test_foo.py"  # derived root shadow
    generated = "def test_foo():\n    assert foo() == 1\n"

    with patch("pdd.cmd_test_main.generate_test") as mock_gen:
        mock_gen.return_value = (generated, 0.01, "model")
        cmd_test_main(
            ctx=local_ctx,
            prompt_file=str(prompt),
            code_file=str(code),
            output=None,
            language="python",
        )

    assert collocated.read_text(encoding="utf-8") == generated
    assert not shadow.exists()


def test_cmd_test_main_honors_explicit_output(tmp_path, local_ctx, monkeypatch):
    """An explicit --output is never replaced by a co-located sibling (real
    construct_paths)."""
    from unittest.mock import patch

    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    code, prompt, collocated = _cmd_project(tmp_path, test_output_path=None)
    pinned = tmp_path / "custom" / "my_test.py"
    generated = "def test_foo():\n    assert foo() == 1\n"

    with patch("pdd.cmd_test_main.generate_test") as mock_gen:
        mock_gen.return_value = (generated, 0.01, "model")
        cmd_test_main(
            ctx=local_ctx,
            prompt_file=str(prompt),
            code_file=str(code),
            output=str(pinned),
            language="python",
        )

    assert pinned.read_text(encoding="utf-8") == generated
    assert collocated.read_text(encoding="utf-8") == ""  # untouched


def test_cmd_test_main_no_adopt_when_pddrc_pins_test_output(
    tmp_path, local_ctx, monkeypatch
):
    """No --output, but `.pddrc` explicitly pins test_output_path for the code file's
    context: the co-located sibling must NOT override it (finding 1). The pin is read
    from the RAW `.pddrc` (not construct_paths' resolved_config), so a real `.pddrc`
    is on disk and construct_paths runs for real."""
    from unittest.mock import patch

    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    code, prompt, collocated = _cmd_project(tmp_path, test_output_path="contract-tests/")
    pinned = tmp_path / "contract-tests" / "test_foo.py"  # explicit .pddrc dir
    generated = "def test_foo():\n    assert foo() == 1\n"

    with patch("pdd.cmd_test_main.generate_test") as mock_gen:
        mock_gen.return_value = (generated, 0.01, "model")
        cmd_test_main(
            ctx=local_ctx,
            prompt_file=str(prompt),
            code_file=str(code),
            output=None,
            language="python",
        )

    assert pinned.read_text(encoding="utf-8") == generated
    assert collocated.read_text(encoding="utf-8") == ""  # untouched


def test_cmd_test_main_no_adopt_with_prompts_dir_context_pin(
    tmp_path, local_ctx, monkeypatch
):
    """Round-4 finding: the explicit ``test_output_path`` lives in a context selected
    by ``prompts_dir`` (``prompts/backend``), so reading the pin from the CODE file
    alone resolves to ``default``/unpinned and would wrongly adopt. Direct ``pdd test``
    must read the pin from the PROMPT side (the way ``construct_paths`` selects the
    context) and NOT adopt the co-located sibling. Real ``construct_paths``; only
    generation is mocked."""
    from unittest.mock import patch

    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    _write(
        tmp_path / ".pddrc",
        'version: "1.0"\n'
        "contexts:\n"
        "  backend:\n"
        "    defaults:\n"
        '      prompts_dir: "prompts/backend"\n'
        '      generate_output_path: "services/api/"\n'
        '      test_output_path: "contract-tests/"\n'
        '      default_language: "python"\n'
        "  default:\n"
        "    defaults:\n"
        '      generate_output_path: "src/"\n'
        '      default_language: "python"\n',
    )
    code = _write(tmp_path / "services/api/foo.py", "def foo():\n    return 1\n")
    prompt = _write(tmp_path / "prompts/backend/foo_python.prompt", "Generate foo\n")
    collocated = _write(code.parent / "test_foo.py", "")  # empty co-located sibling
    pinned = tmp_path / "contract-tests" / "test_foo.py"  # prompts_dir-context pin
    generated = "def test_foo():\n    assert foo() == 1\n"

    with patch("pdd.cmd_test_main.generate_test") as mock_gen:
        mock_gen.return_value = (generated, 0.01, "model")
        cmd_test_main(
            ctx=local_ctx,
            prompt_file=str(prompt),
            code_file=str(code),
            output=None,
            language="python",
        )

    # Pin (from the prompts_dir-selected context) honored: written to contract-tests/,
    # the co-located sibling left untouched.
    assert pinned.read_text(encoding="utf-8") == generated
    assert collocated.read_text(encoding="utf-8") == ""


# ---------------------------------------------------------------------------
# 5) architecture.json branch — the pin must be read from the context the arch
#    branch derives `test_dir` from (issue #1903 finding 1). REAL construct_paths
#    and a REAL architecture.json on disk.
# ---------------------------------------------------------------------------

def test_arch_json_branch_honors_pin_from_code_path_context(tmp_path, monkeypatch):
    """Finding 1: with architecture.json driving path derivation, the explicit
    `test_output_path` lives in a context selected by the arch CODE path
    (`frontend/**`), NOT by the prompt (which sits at `prompts/` and resolves to
    `default`). The arch branch must read its pin from THAT code-path context and
    NOT adopt the co-located test — a prompt-side-only pin would miss it and wrongly
    retarget the explicit `contract-tests/` path onto the co-located sibling."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    _write(
        tmp_path / ".pddrc",
        json.dumps({
            "version": "1.0",
            "contexts": {
                "frontend": {
                    "paths": ["frontend/**"],
                    "defaults": {
                        "generate_output_path": "frontend/src/app/",
                        "test_output_path": "contract-tests/",
                        "default_language": "typescriptreact",
                    },
                },
                "default": {"defaults": {"default_language": "python"}},
            },
        }),
    )
    (tmp_path / "architecture.json").write_text(
        json.dumps([
            {"filename": "page_typescriptreact.prompt",
             "filepath": "frontend/src/app/page.tsx"},
        ]),
        encoding="utf-8",
    )
    code = _write(
        tmp_path / "frontend/src/app/page.tsx",
        "export default function Page() { return null; }\n",
    )
    real = _write(code.parent / "__test__" / "page.test.tsx", "test('x', () => {});\n")
    # Prompt at the top level -> matches `default`, NOT the `frontend` context.
    _write(tmp_path / "prompts/page_typescriptreact.prompt", "Generate a page.\n")

    # The arch branch resolves the pin from the code-path (`frontend`) context...
    raw, pinned = _get_pdd_file_paths_uncollocated("page", "typescriptreact", "prompts")
    assert pinned is True
    assert "contract-tests" in Path(raw["test"]).parts
    # ...and the co-located test IS otherwise detectable, so ONLY the pin (not a
    # missing sibling) prevents adoption — proving the regression is real.
    would_adopt = _adopt_collocated_test(dict(raw), user_pinned=False)
    assert Path(would_adopt["test"]).resolve() == real.resolve()

    # Public entry point: explicit pin honored, co-located test NOT adopted.
    paths = get_pdd_file_paths("page", "typescriptreact", "prompts")
    assert "contract-tests" in Path(paths["test"]).parts
    assert Path(paths["test"]).resolve() != real.resolve()


# ---------------------------------------------------------------------------
# 6) churn guard coverage — `_is_test_output_path` must recognize the adopted
#    `.mjs/.cjs` test files and the singular `__test__` dir (issue #1903
#    finding 2), so an adopted human test is never wholesale-rewritten outside
#    the TestChurnError guard.
# ---------------------------------------------------------------------------

class TestIsTestOutputPathChurnCoverage:
    def test_recognizes_mjs_cjs_suffixes(self):
        assert _is_test_output_path("src/__test__/page.test.mjs") is True
        assert _is_test_output_path("foo.spec.cjs") is True
        assert _is_test_output_path("src/page.test.cjs") is True
        assert _is_test_output_path("src/page.spec.mjs") is True

    def test_recognizes_singular_dunder_test_dir(self):
        assert _is_test_output_path("pkg/__test__/widget.test.tsx") is True
        assert _is_test_output_path("frontend/src/app/__test__/page.tsx") is True

    def test_plain_module_still_not_a_test(self):
        assert _is_test_output_path("src/page.mjs") is False
        assert _is_test_output_path("src/page.cjs") is False


# ---------------------------------------------------------------------------
# 7) cmd_test_main generation destination — native generation must be told the
#    ADOPTED test path, not the stale pre-adoption default (issue #1903
#    finding 3). REAL construct_paths; only generation is mocked.
# ---------------------------------------------------------------------------

def test_cmd_test_main_generation_uses_adopted_path(tmp_path, local_ctx, monkeypatch):
    """Finding 3: after adoption retargets the write to the co-located sibling, the
    native generation must be prompted with THAT destination (so relative imports
    are correct) — not the stale `output_file` default (`test_output.py`)."""
    from unittest.mock import patch

    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    code, prompt, collocated = _cmd_project(tmp_path, test_output_path=None)
    generated = "def test_foo():\n    assert foo() == 1\n"

    with patch("pdd.cmd_test_main.generate_test") as mock_gen:
        mock_gen.return_value = (generated, 0.01, "model")
        cmd_test_main(
            ctx=local_ctx,
            prompt_file=str(prompt),
            code_file=str(code),
            output=None,
            language="python",
        )

    # Generation was told the adopted co-located destination, not `test_output.py`.
    passed_test_path = Path(mock_gen.call_args.kwargs["test_file_path"])
    assert passed_test_path.resolve() == collocated.resolve()
    assert passed_test_path.name != "test_output.py"
    # And the write landed there.
    assert collocated.read_text(encoding="utf-8") == generated


def test_cmd_test_main_generation_uses_explicit_output(tmp_path, local_ctx, monkeypatch):
    """Round-6 finding: when sync passes the ALREADY-adopted path in as an explicit
    ``output`` (so cmd_test_main itself does NOT retarget), native generation must
    still be prompted with that real destination — not the bare ``test_output.py``
    fallback (``output_file`` is absent for ``test`` commands). Mirrors
    ``sync_orchestration`` calling ``cmd_test_main(output=str(pdd_files['test']))``.
    Fails before the ``setdefault('output_file', output)`` fix (test_file_path would
    be ``test_output.py``)."""
    from unittest.mock import patch

    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    code, prompt, collocated = _cmd_project(tmp_path, test_output_path=None)
    generated = "def test_foo():\n    assert foo() == 1\n"

    with patch("pdd.cmd_test_main.generate_test") as mock_gen:
        mock_gen.return_value = (generated, 0.01, "model")
        cmd_test_main(
            ctx=local_ctx,
            prompt_file=str(prompt),
            code_file=str(code),
            output=str(collocated),  # sync passes the already-adopted path explicitly
            language="python",
        )

    # Generation is prompted with the real write destination's directory (correct
    # relative imports), never the bare `test_output.py` fallback. (The exact leaf
    # may differ from `collocated` under construct_paths' force=False dedup, which
    # real sync avoids via merge=True; the invariant we lock is: not the fallback,
    # and co-located with the module.)
    passed_test_path = Path(mock_gen.call_args.kwargs["test_file_path"])
    assert passed_test_path.name != "test_output.py"
    assert passed_test_path.parent.resolve() == collocated.parent.resolve()


def test_cmd_test_main_sync_merge_writes_real_collocated_test_no_shadow(
    tmp_path, local_ctx, monkeypatch
):
    """Round-7 finding (core jest case): sync regenerates by MERGING into the
    EXISTING adopted co-located TSX test — `cmd_test_main(output=str(real_test),
    existing_tests=[real_test], merge=True, language='typescriptreact')`. With
    force=False, construct_paths would number the existing path to
    `page.test_1.tsx` and the agentic branch would write that NEW shadow, leaving
    the real test stale (the #1903 false-green persists). Assert the agentic write
    targets the REAL co-located test and no numbered shadow is created. Fails
    before the merge-target pin."""
    from unittest.mock import patch

    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    _write(
        tmp_path / ".pddrc",
        'version: "1.0"\n'
        "contexts:\n"
        "  default:\n"
        "    defaults:\n"
        '      generate_output_path: "frontend/src/app/contributions/"\n'
        '      default_language: "typescriptreact"\n',
    )
    code = _write(
        tmp_path / "frontend/src/app/contributions/page.tsx",
        "export default function Page(){return null;}\n",
    )
    generated = "test('renders', () => { expect(true).toBe(true); });\n"
    # Existing content == generated so the churn guard is a no-op; the invariant
    # under test is the WRITE PATH, not churn.
    real_test = _write(code.parent / "__test__" / "page.test.tsx", generated)
    prompt = _write(tmp_path / "prompts/page_typescriptreact.prompt", "Generate a page.\n")

    captured = {}

    def fake_agentic(*args, **kwargs):
        out = kwargs.get("output_test_file")
        captured["output_test_file"] = out
        Path(out).write_text(generated, encoding="utf-8")
        return (generated, 0.01, "model", True, None)

    with patch(
        "pdd.agentic_test_generate.run_agentic_test_generate", side_effect=fake_agentic
    ):
        cmd_test_main(
            ctx=local_ctx,
            prompt_file=str(prompt),
            code_file=str(code),
            output=str(real_test),           # sync passes the adopted existing test
            existing_tests=[str(real_test)],
            merge=True,
            language="typescriptreact",
        )

    assert Path(captured["output_test_file"]).resolve() == real_test.resolve()
    assert not (real_test.parent / "page.test_1.tsx").exists()
    assert real_test.read_text(encoding="utf-8") == generated


def test_env_var_present_but_empty_is_pinned(tmp_path, monkeypatch):
    """An explicitly exported `PDD_TEST_OUTPUT_PATH=` (present but EMPTY) is a
    root-level pin — presence, not truthiness — consistent with `.pddrc
    test_output_path: ""`; a co-located test must NOT be adopted over it. Fails
    before the presence-based env check (empty env would read as unpinned)."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_TEST_OUTPUT_PATH", "")  # present but empty
    code, real = _build_jest_project(tmp_path, test_output_path=None)

    # The predicate short-circuits to pinned on a present (even empty) env var.
    assert configured_test_output_pinned(str(code)) is True
    _, pinned = _get_pdd_file_paths_uncollocated("page", "typescriptreact", "prompts")
    assert pinned is True
    paths = get_pdd_file_paths("page", "typescriptreact", "prompts")
    assert Path(paths["test"]).resolve() != real.resolve()


def test_evidence_manifest_resolve_test_output_uses_adopted_path(tmp_path, monkeypatch):
    """`evidence_manifest.resolve_test_output_paths` must record the ADOPTED co-located
    test (the file PDD actually writes/runs), not the runner-blind derived shadow —
    mirroring cmd_test_main so `pdd test --evidence` audit/replay points at the right
    artifact (#1903). Fails before the evidence-side adoption fix."""
    from pdd.evidence_manifest import resolve_test_output_paths

    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_TEST_OUTPUT_PATH", raising=False)
    code, real = _build_jest_project(tmp_path, test_output_path=None)
    prompt = tmp_path / "prompts" / "page_typescriptreact.prompt"

    got = resolve_test_output_paths(str(prompt), str(code))
    assert [Path(p).resolve() for p in got] == [real.resolve()]

    # An explicit pin is still respected (no adoption).
    monkeypatch.setenv("PDD_TEST_OUTPUT_PATH", "contract-tests/")
    got_pinned = resolve_test_output_paths(str(prompt), str(code))
    assert Path(got_pinned[0]).resolve() != real.resolve()


# ---------------------------------------------------------------------------
# CWE-022 containment (PR #1914 CodeQL alerts #339-#342): adoption candidates
# derived from a caller-supplied code-file path must never escape the working
# tree — the adopted path becomes a generated-test WRITE target.
# ---------------------------------------------------------------------------


def test_find_collocated_test_rejects_candidates_outside_cwd(tmp_path, monkeypatch):
    """A code file outside the working tree (traversal shape) is never adopted:
    its real sibling test exists but lies outside cwd -> no match."""
    outside = tmp_path / "outside"
    module = _write(outside / "widget.ts", "export const x = 1;\n")
    _write(outside / "widget.test.ts", "test('x', () => {});\n")

    workdir = tmp_path / "repo"
    workdir.mkdir()
    monkeypatch.chdir(workdir)

    # Reachable via traversal from cwd, but resolves outside the working tree.
    traversal = Path("..") / "outside" / "widget.ts"
    assert find_collocated_test(traversal) is None
    assert find_collocated_test(module) is None  # absolute form, same escape


def test_resolve_test_output_path_traversal_returns_derived(tmp_path, monkeypatch):
    outside = tmp_path / "outside"
    _write(outside / "widget.ts", "export const x = 1;\n")
    _write(outside / "widget.test.ts", "test('x', () => {});\n")

    workdir = tmp_path / "repo"
    workdir.mkdir()
    monkeypatch.chdir(workdir)

    derived = Path("tests") / "test_widget.ts"
    got = resolve_test_output_path(
        Path("..") / "outside" / "widget.ts", derived, user_pinned=False
    )
    assert got == derived  # no adoption, safe degradation


def test_adopt_collocated_test_keeps_result_when_adoption_escapes_root(
    tmp_path, monkeypatch
):
    """Sink-side defense in depth: even if a containing-escape path reached
    _adopt_collocated_test, the derived result is kept unchanged."""
    outside = tmp_path / "outside"
    module = _write(outside / "widget.ts", "export const x = 1;\n")
    _write(outside / "widget.test.ts", "test('x', () => {});\n")

    workdir = tmp_path / "repo"
    workdir.mkdir()
    monkeypatch.chdir(workdir)

    derived = {
        "code": module,
        "test": Path("tests") / "test_widget.ts",
        "test_files": [Path("tests") / "test_widget.ts"],
    }
    got = _adopt_collocated_test(dict(derived), user_pinned=False)
    assert got["test"] == derived["test"]
    assert got["test_files"] == derived["test_files"]


def test_in_repo_adoption_still_works_after_containment(tmp_path, monkeypatch):
    """Containment must not break the normal in-repo adoption path."""
    monkeypatch.chdir(tmp_path)
    code, real = _build_jest_project(tmp_path, test_output_path=None)
    got = resolve_test_output_path(
        code, Path("tests") / "test_page.tsx", user_pinned=False
    )
    assert Path(got).resolve() == real.resolve()


def test_validated_project_path_sanitizes_before_filesystem_use(tmp_path, monkeypatch):
    """Only component-sanitized paths under the trusted root are canonicalized."""
    repo = tmp_path / "repo"
    repo.mkdir()
    module = _write(repo / "src" / "widget.ts", "export const x = 1;\n")
    outside = _write(tmp_path / "outside.ts", "export const y = 2;\n")
    monkeypatch.chdir(repo)

    assert _validated_project_path("src/widget.ts") == module.resolve()
    assert _validated_project_path(module) == module.resolve()
    assert _validated_project_path(Path("..") / "outside.ts") is None
    assert _validated_project_path(outside) is None


def test_find_collocated_test_rejects_symlink_escape(tmp_path, monkeypatch):
    """A lexical in-repo candidate whose symlink target escapes is rejected."""
    repo = tmp_path / "repo"
    code = _write(repo / "src" / "widget.ts", "export const x = 1;\n")
    outside_test = _write(tmp_path / "widget.test.ts", "test('x', () => {});\n")
    (code.parent / "widget.test.ts").symlink_to(outside_test)
    monkeypatch.chdir(repo)

    assert find_collocated_test(code) is None
