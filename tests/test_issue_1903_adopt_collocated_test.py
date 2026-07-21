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
import re
import subprocess
import sys
from pathlib import Path

# Prioritize the local package (mirrors sibling test modules).
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import pytest

from pdd.content_selector import (
    _micromatch_to_regex,
    _parse_static_js_runner_config,
    _pins_test_output_location,
    _validated_project_path,
    configured_test_output_pinned,
    find_collocated_test,
    find_runner_collected_test_path,
    resolve_test_output_path,
    was_test_adopted,
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

    def test_default_jest_adopts_collected_beside_module_sibling(
        self, tmp_path, monkeypatch
    ):
        """A default-collected human test need not be the first candidate."""
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", '{"devDependencies":{"jest":"^30.0.0"}}')
        code = _write(tmp_path / "src/page.tsx")
        real = _write(code.parent / "page.test.tsx", "test('kept', () => {});\n")
        shadow = tmp_path / "tests/test_page.tsx"

        got = resolve_test_output_path(code, shadow, user_pinned=False)

        assert got is not None
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

    def test_excluded_sibling_is_not_adopted(self, tmp_path, monkeypatch):
        # Round 9: an existing co-located sibling the runner PROVABLY does not
        # collect (a PARSEABLE custom testMatch that excludes it) must NOT be
        # adopted — that would preserve the false-green on an excluded file.
        # Redirect away from the stale excluded sibling.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", '{"devDependencies": {"jest": "^30"}}\n')
        _write(tmp_path / "jest.config.json",
               json.dumps({"testMatch": ["<rootDir>/qa/**/*.spec.ts"]}))
        code = _write(tmp_path / "src/page.ts")
        stale = _write(tmp_path / "src/__test__/page.test.ts")  # NOT under qa/
        derived = tmp_path / "tests" / "test_page.ts"
        got = resolve_test_output_path(code, derived, user_pinned=False)
        assert Path(got).resolve() != stale.resolve(), \
            "must not adopt a runner-excluded sibling"
        # And was_test_adopted must NOT claim adoption for the redirect target.
        assert was_test_adopted(code, str(got), str(derived), user_pinned=False) is False

    def test_collected_sibling_still_adopted(self, tmp_path, monkeypatch):
        # Control: when the runner (default jest) DOES collect the co-located
        # sibling, adoption still fires as before.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", '{"devDependencies": {"jest": "^30"}}\n')
        code = _write(tmp_path / "src/page.tsx")
        real = _write(tmp_path / "src/__test__/page.test.tsx")
        derived = tmp_path / "tests" / "test_page.tsx"
        got = resolve_test_output_path(code, derived, user_pinned=False)
        assert Path(got).resolve() == real.resolve()
        assert was_test_adopted(code, str(got), str(derived), user_pinned=False) is True


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

    # --- config-aware placement (issue #1903 §A: honor testMatch/roots/rootDir) ---

    def test_custom_testmatch_spec_co_locates_spec(self, tmp_path, monkeypatch):
        # testMatch requires `.spec` -> write `.spec`, not `.test`.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json",
               json.dumps({"jest": {"testMatch": ["**/*.spec.tsx"]}}))
        code = _write(tmp_path / "src/page.tsx")
        got = find_runner_collected_test_path(code)
        assert Path(got).resolve() == (tmp_path / "src/__test__/page.spec.tsx").resolve()

    def test_custom_testmatch_requires_dunder_tests_dir(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json",
               json.dumps({"jest": {"testMatch": ["**/__tests__/**/*.tsx"]}}))
        code = _write(tmp_path / "src/page.tsx")
        got = find_runner_collected_test_path(code)
        assert Path(got).resolve() == (tmp_path / "src/__tests__/page.test.tsx").resolve()

    def test_centralized_testmatch_derives_collected_path(self, tmp_path, monkeypatch):
        # A centralized layout (tests only under top-level test/) does NOT collect
        # a co-located test -> DERIVE a path UNDER the collected directory (never
        # the runner-blind tests/ shadow, and never an uncollected co-located
        # orphan). The derived path must satisfy the configured testMatch.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json",
               json.dumps({"jest": {"testMatch": ["<rootDir>/test/**/*.test.ts"]}}))
        code = _write(tmp_path / "src/util.ts")
        got = find_runner_collected_test_path(code)
        assert got is not None
        rel = Path(got).resolve().relative_to(tmp_path.resolve()).as_posix()
        assert rel.startswith("test/") and rel.endswith("util.test.ts"), rel

    def test_roots_excluding_module_derives_under_root(self, tmp_path, monkeypatch):
        # roots restricts collection to test/; a module under src/ cannot be
        # co-located within a collected root -> derive a path UNDER test/.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json",
               json.dumps({"jest": {"roots": ["<rootDir>/test"]}}))
        code = _write(tmp_path / "src/app/page.tsx")
        got = find_runner_collected_test_path(code)
        assert got is not None
        rel = Path(got).resolve().relative_to(tmp_path.resolve()).as_posix()
        assert rel.startswith("test/") and rel.endswith("page.test.tsx"), rel

    def test_js_config_plain_uses_default_convention(self, tmp_path, monkeypatch):
        # A jest.config.js with NO discovery keys uses jest defaults, which
        # collect the co-located __test__/*.test.tsx we write.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "jest.config.js", "module.exports = {};\n")
        code = _write(tmp_path / "src/page.tsx")
        got = find_runner_collected_test_path(code)
        assert Path(got).resolve() == (tmp_path / "src/__test__/page.test.tsx").resolve()

    def test_js_config_custom_discovery_refuses_conservatively(self, tmp_path, monkeypatch):
        # A literal custom Jest config is statically resolved without executing
        # repository code, so greenfield placement is provably collected.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "jest.config.js",
               "module.exports = { testMatch: ['<rootDir>/qa/**/*.test.ts'] };\n")
        code = _write(tmp_path / "src/page.ts")
        collected = find_runner_collected_test_path(code)
        assert collected is not None
        assert Path(collected).resolve().relative_to(tmp_path).as_posix().startswith("qa/")
        shadow = tmp_path / "tests" / "test_page.ts"
        assert resolve_test_output_path(code, shadow, user_pinned=False) == collected

    def test_roots_including_module_co_locates(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json",
               json.dumps({"jest": {"roots": ["<rootDir>/src"]}}))
        code = _write(tmp_path / "src/app/page.tsx")
        got = find_runner_collected_test_path(code)
        assert Path(got).resolve() == (
            tmp_path / "src/app/__test__/page.test.tsx"
        ).resolve()

    def test_testpathignore_routes_to_alternate_dir(self, tmp_path, monkeypatch):
        # testPathIgnorePatterns excludes __test__/ -> use __tests__ (default
        # testMatch still collects it).
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json",
               json.dumps({"jest": {"testPathIgnorePatterns": ["__test__/"]}}))
        code = _write(tmp_path / "src/page.tsx")
        got = find_runner_collected_test_path(code)
        assert Path(got).resolve() == (tmp_path / "src/__tests__/page.test.tsx").resolve()

    def test_jest_config_json_is_parsed(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "jest.config.json",
               json.dumps({"testMatch": ["**/*.spec.ts"]}))
        code = _write(tmp_path / "lib/util.ts")
        got = find_runner_collected_test_path(code)
        assert Path(got).resolve() == (tmp_path / "lib/__test__/util.spec.ts").resolve()

    def test_centralized_same_stem_modules_do_not_collide(self, tmp_path, monkeypatch):
        # Two different modules that share a stem MUST map to DISTINCT centralized
        # test paths — else syncing the second overwrites the first (never fork,
        # never overwrite).
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json",
               json.dumps({"jest": {"testMatch": ["<rootDir>/test/**/*.test.ts"]}}))
        a = _write(tmp_path / "src/a/util.ts")
        b = _write(tmp_path / "src/b/util.ts")
        got_a = find_runner_collected_test_path(a)
        got_b = find_runner_collected_test_path(b)
        assert got_a is not None and got_b is not None
        assert Path(got_a).resolve() != Path(got_b).resolve(), (got_a, got_b)
        # Each preserves its module's relative directory under the test root.
        assert "a" in Path(got_a).resolve().relative_to(tmp_path.resolve()).parts
        assert "b" in Path(got_b).resolve().relative_to(tmp_path.resolve()).parts

    def test_vitest_custom_include_refuses(self, tmp_path, monkeypatch):
        # A vitest.config.ts with a custom test.include (unparseable) must NOT be
        # assumed default -> refuse (fall back to derived), never a false-green.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "vitest.config.ts",
               "export default { test: { include: ['custom/**/*.spec.ts'] } }\n")
        code = _write(tmp_path / "src/page.tsx")
        assert find_runner_collected_test_path(code) is None

    def test_vitest_plain_config_co_locates(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "vitest.config.ts", "export default { test: {} }\n")
        _write(tmp_path / "package.json", '{"devDependencies": {"vitest": "^1"}}\n')
        code = _write(tmp_path / "src/page.tsx")
        got = find_runner_collected_test_path(code)
        assert Path(got).resolve() == (tmp_path / "src/__test__/page.test.tsx").resolve()

    def test_jest_testmatch_negation_excludes(self, tmp_path, monkeypatch):
        # An ordered negation (`!**/src/**`) removes matches; a module under src
        # is NOT collected co-located -> refuse (no false-green).
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", json.dumps(
            {"jest": {"testMatch": ["**/*.test.tsx", "!**/src/**"]}}))
        excluded = _write(tmp_path / "src/page.tsx")
        included = _write(tmp_path / "lib/widget.tsx")
        assert find_runner_collected_test_path(excluded) is None
        got = find_runner_collected_test_path(included)
        assert Path(got).resolve() == (tmp_path / "lib/__test__/widget.test.tsx").resolve()

    def test_jest_projects_config_refuses(self, tmp_path, monkeypatch):
        # jest `projects` restructures discovery in ways we do not resolve -> refuse.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json",
               json.dumps({"jest": {"projects": ["<rootDir>/a", "<rootDir>/b"]}}))
        code = _write(tmp_path / "src/page.tsx")
        assert find_runner_collected_test_path(code) is None

    def test_delegating_js_config_refuses(self, tmp_path, monkeypatch):
        # A jest.config.js that require()s a base config could set discovery in a
        # file we can't read -> refuse rather than assume defaults.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "jest.config.js", "module.exports = require('./config/jest.base.js')\n")
        code = _write(tmp_path / "src/page.tsx")
        assert find_runner_collected_test_path(code) is None

    def test_preset_and_function_js_config_refuse(self, tmp_path, monkeypatch):
        # preset / function configs can change discovery in ways we can't resolve.
        monkeypatch.chdir(tmp_path)
        for content in (
            "module.exports = { preset: 'ts-jest' }\n",
            "module.exports = () => ({})\n",
            "import base from './base'\nexport default { ...base }\n",
        ):
            (tmp_path / "jest.config.js").write_text(content, encoding="utf-8")
            code = _write(tmp_path / f"src/m{abs(hash(content))}.ts")
            assert find_runner_collected_test_path(code) is None, content

    def test_rootdir_only_derives_under_rootdir(self, tmp_path, monkeypatch):
        # rootDir centralizes collection; a module outside it derives under rootDir.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", json.dumps({"jest": {"rootDir": "test"}}))
        code = _write(tmp_path / "src/page.tsx")
        got = find_runner_collected_test_path(code)
        assert got is not None
        rel = Path(got).resolve().relative_to(tmp_path.resolve()).as_posix()
        assert rel.startswith("test/") and rel.endswith("page.test.tsx"), rel

    def test_mjs_module_default_config_refuses(self, tmp_path, monkeypatch):
        # jest's DEFAULT testMatch collects js/jsx/ts/tsx, NOT mjs/cjs.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "jest.config.js", "module.exports = {}\n")
        code = _write(tmp_path / "src/util.mjs")
        assert find_runner_collected_test_path(code) is None

    def test_testmatch_negation_then_positive_reincludes(self, tmp_path, monkeypatch):
        # Ordered semantics: a later positive re-includes a path an earlier
        # negation excluded (module under __tests__/, re-included by the 2nd glob).
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", json.dumps({"jest": {"testMatch": [
            "!**/__fixtures__/**", "**/__tests__/**/*.tsx"]}}))
        code = _write(tmp_path / "src/__tests__/page.tsx")
        got = find_runner_collected_test_path(code)
        assert got is not None and Path(got).name == "page.test.tsx"

    def test_char_class_negation_matcher(self):
        from pdd.content_selector import _glob_matches
        # `[!_]` = "not underscore" (bash/micromatch), NOT "! or _".
        assert _glob_matches("**/[!_]*.test.ts", "src/page.test.ts") is True
        assert _glob_matches("**/[!_]*.test.ts", "src/_hidden.test.ts") is False

    def test_ambiguous_existing_tests_not_greenfield(self, tmp_path, monkeypatch):
        # TWO existing co-located tests -> ambiguous -> resolve must NOT greenfield
        # (would fork a third file). Falls back to the derived path.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "jest.config.js", "module.exports = {}\n")
        code = _write(tmp_path / "src/page.tsx")
        _write(tmp_path / "src/page.test.tsx")
        _write(tmp_path / "src/__tests__/page.test.tsx")
        shadow = tmp_path / "tests" / "test_page.tsx"
        assert resolve_test_output_path(code, shadow, user_pinned=False) == shadow

    def test_explicit_testmatch_no_match_refuses(self, tmp_path, monkeypatch):
        # An explicit testMatch that matches NO co-located candidate must fail
        # closed (refuse), not fall through to an uncollected default path.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json",
               json.dumps({"jest": {"testMatch": ["<rootDir>/qa/**/*-test.ts"]}}))
        code = _write(tmp_path / "src/page.ts")
        assert find_runner_collected_test_path(code) is None

    def test_vitest_dir_and_call_config_refuse(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        for content in (
            "export default { test: { dir: './tests' } }\n",   # vitest dir
            "export default { test: { root: './src' } }\n",    # vitest root
            "module.exports = buildConfig()\n",                # call-expr export
        ):
            (tmp_path / "vitest.config.ts").write_text(content, encoding="utf-8")
            code = _write(tmp_path / f"src/m{abs(hash(content))}.tsx")
            assert find_runner_collected_test_path(code) is None, content

    def test_vitest_default_collects_mjs(self, tmp_path, monkeypatch):
        # vitest's default include collects .mjs -> a plain vitest project
        # co-locates an .mjs module (jest would not; dialect-aware).
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "vitest.config.ts", "export default { test: {} }\n")
        _write(tmp_path / "package.json", '{"devDependencies": {"vitest": "^1"}}\n')
        code = _write(tmp_path / "src/util.mjs")
        got = find_runner_collected_test_path(code)
        assert got is not None and Path(got).name == "util.test.mjs"

    def test_jest30_collects_mjs_but_jest29_does_not(self, tmp_path, monkeypatch):
        # Jest 30's default testMatch collects .mjs/.cjs; Jest 29 does not.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json",
               json.dumps({"devDependencies": {"jest": "^30.0.0"}}))
        got = find_runner_collected_test_path(_write(tmp_path / "src/util.mjs"))
        assert got is not None and Path(got).name == "util.test.mjs"
        # Downgrade to jest 29 -> refuse the .mjs (would be uncollected).
        (tmp_path / "package.json").write_text(
            json.dumps({"devDependencies": {"jest": "^29.7.0"}}), encoding="utf-8")
        assert find_runner_collected_test_path(_write(tmp_path / "lib/util.mjs")) is None

    def test_computed_key_and_identifier_configs_refuse(self, tmp_path, monkeypatch):
        # Statically-computable keys and identifier exports of literal objects
        # are resolved without executing the config.
        monkeypatch.chdir(tmp_path)
        for content in (
            "const c = {['test' + 'Match']: ['<rootDir>/qa/**/*.test.ts']}; module.exports = c\n",
            "const config = {}; module.exports = config\n",
        ):
            (tmp_path / "jest.config.js").write_text(content, encoding="utf-8")
            code = _write(tmp_path / f"src/m{abs(hash(content))}.ts")
            collected = find_runner_collected_test_path(code)
            assert collected is not None, content
            if "testMatch" in content or "'Match'" in content:
                assert "qa/" in Path(collected).resolve().relative_to(tmp_path).as_posix()

    def test_computed_config_rehomes_existing_uncollected_sibling(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        _write(
            tmp_path / "jest.config.js",
            "const c = {['test' + 'Match']: ['<rootDir>/qa/**/*.spec.ts']}; module.exports = c\n",
        )
        code = _write(tmp_path / "src/page.ts")
        stale = _write(tmp_path / "src/page.test.ts")
        shadow = tmp_path / "tests/test_page.ts"

        resolved = resolve_test_output_path(code, shadow, user_pinned=False)

        assert resolved != stale
        assert resolved != shadow
        assert Path(resolved).resolve().relative_to(tmp_path).as_posix().startswith("qa/")

    @pytest.mark.parametrize(
        ("content", "expect_default"),
        [
            ("// module.exports = { testMatch: ['<rootDir>/qa/**/*.test.ts'] }\nmodule.exports = {}\n", True),
            ("module.exports = { note: \"testMatch: ['<rootDir>/qa/**/*.test.ts']\" }\n", True),
            ("const unrelated = { testMatch: ['<rootDir>/qa/**/*.test.ts'] }; module.exports = {}\n", False),
            ("module.exports = { unrelated: { testMatch: ['<rootDir>/qa/**/*.test.ts'] } }\n", False),
        ],
        ids=("comment", "string", "unrelated-binding", "unrelated-nested-object"),
    )
    def test_discovery_syntax_outside_exported_runner_config_is_not_authority(
        self, tmp_path, monkeypatch, content, expect_default
    ):
        """Only a structurally parsed exported runner config can route output."""
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "jest.config.js", content)
        code = _write(tmp_path / "src/page.ts")

        collected = find_runner_collected_test_path(code)

        if expect_default:
            assert collected is not None
        else:
            assert collected is None
        if collected is not None:
            relative = Path(collected).resolve().relative_to(tmp_path).as_posix()
            assert not relative.startswith("qa/")

    @pytest.mark.parametrize(
        "content",
        [
            "module.exports = { workspace: ['./packages/*'] }\n",
            "module.exports = { testMatch: [123] }\n",
            "module.exports = { rootDir: 123 }\n",
        ],
        ids=("vitest-workspace", "numeric-test-match", "numeric-root-dir"),
    )
    def test_unsupported_literal_runner_config_is_directly_opaque(
        self, tmp_path, content
    ):
        config = _write(tmp_path / "vitest.config.js", content)

        assert _parse_static_js_runner_config(config) is None

    @pytest.mark.parametrize(
        "content",
        [
            "module.exports = { workspace: ['./packages/*'] }\n",
            "module.exports = { testMatch: [123] }\n",
            "module.exports = { rootDir: 123 }\n",
        ],
        ids=("vitest-workspace", "numeric-test-match", "numeric-root-dir"),
    )
    def test_unsupported_literal_runner_config_cannot_authorize_placement(
        self, tmp_path, monkeypatch, content
    ):
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "vitest.config.js", content)
        code = _write(tmp_path / "src/page.ts")
        shadow = tmp_path / "tests/test_page.ts"

        assert find_runner_collected_test_path(code) is None
        assert resolve_test_output_path(code, shadow, user_pinned=False) is None
        assert not shadow.exists()

    def test_bare_roots_resolved_against_rootdir(self, tmp_path, monkeypatch):
        # roots:["src"] with rootDir:"frontend" -> collected root is
        # frontend/src (jest resolves roots against effective rootDir). A module
        # under frontend/src co-locates; the wrong base would exclude it.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json",
               json.dumps({"jest": {"rootDir": "frontend", "roots": ["src"]}}))
        code = _write(tmp_path / "frontend/src/a/page.tsx")
        got = find_runner_collected_test_path(code)
        assert got is not None
        rel = Path(got).resolve().relative_to(tmp_path.resolve()).as_posix()
        assert rel.startswith("frontend/src/") and rel.endswith("page.test.tsx"), rel

    def test_explicit_empty_and_both_configs_refuse(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        # testMatch: [] matches nothing in jest -> refuse.
        _write(tmp_path / "package.json", json.dumps({"jest": {"testMatch": []}}))
        assert find_runner_collected_test_path(_write(tmp_path / "src/a.tsx")) is None
        # Both testMatch AND testRegex configured -> jest rejects -> refuse.
        _write(tmp_path / "package.json",
               json.dumps({"jest": {"testMatch": ["**/*.test.tsx"], "testRegex": ".*"}}))
        assert find_runner_collected_test_path(_write(tmp_path / "src/b.tsx")) is None

    def test_script_substring_is_not_a_runner(self, tmp_path):
        from pdd.content_selector import _package_json_declares_js_runner
        _write(tmp_path / "p1.json", json.dumps({"scripts": {"build": "echo no-jest"}}))
        assert _package_json_declares_js_runner(tmp_path / "p1.json") is False
        _write(tmp_path / "p2.json", json.dumps({"scripts": {"test": "jest --ci"}}))
        assert _package_json_declares_js_runner(tmp_path / "p2.json") is True
        _write(tmp_path / "p3.json", json.dumps({"scripts": {"test:unit": "vitest run"}}))
        assert _package_json_declares_js_runner(tmp_path / "p3.json") is True

    def test_extglob_comma_is_literal_brace_comma_alternates(self):
        from pdd.content_selector import _glob_matches
        # extglob @(foo,bar): "foo,bar" is a LITERAL alternative (pipe alternates).
        assert _glob_matches("**/@(foo,bar).test.ts", "x/foo.test.ts") is False
        assert _glob_matches("**/@(foo|bar).test.ts", "x/foo.test.ts") is True
        # brace {foo,bar}: comma alternates.
        assert _glob_matches("**/{foo,bar}.test.ts", "x/foo.test.ts") is True

    def test_excessive_pattern_count_refuses(self, tmp_path, monkeypatch):
        # A hostile config with a huge pattern count fails closed (DoS bound).
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json",
               json.dumps({"jest": {"testMatch": ["**/*.test.tsx"] * 200}}))
        code = _write(tmp_path / "src/page.tsx")
        assert find_runner_collected_test_path(code) is None

    def test_second_statement_mutation_config_refuses(self, tmp_path, monkeypatch):
        # A whitelist (single plain-literal export) refuses a config that mutates
        # the export in a SECOND statement (blacklist-evading, round 7).
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "jest.config.js",
               "module.exports = {}; module.exports['testMatch'] = ['qa/**/*.test.ts']\n")
        assert find_runner_collected_test_path(_write(tmp_path / "src/p.tsx")) is None
        # A plain literal with only a NON-discovery key is still default.
        _write(tmp_path / "jest.config.js", "module.exports = { testEnvironment: 'jsdom' }\n")
        got = find_runner_collected_test_path(_write(tmp_path / "src/q.tsx"))
        assert got is not None and Path(got).name == "q.test.tsx"

    def test_ambiguous_config_sources_refuse(self, tmp_path, monkeypatch):
        # An inline package.json jest block AND a vitest.config.ts at the same
        # level -> ambiguous active runner -> refuse (round 7).
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", json.dumps({"jest": {}}))
        _write(tmp_path / "vitest.config.ts", "export default { test: {} }\n")
        assert find_runner_collected_test_path(_write(tmp_path / "src/p.tsx")) is None

    def test_greenfield_ownership_not_reclassified_as_adopted(self, tmp_path, monkeypatch):
        # Two-run provenance: PDD greenfield-creates a co-located test, records
        # ownership; a LATER resolution must NOT call it human-adopted.
        from pdd.content_selector import (
            was_test_adopted, record_pdd_created_test, is_pdd_created_test,
        )
        monkeypatch.chdir(tmp_path)
        code = _write(tmp_path / "src/foo.tsx")
        gf = tmp_path / "src/__test__/foo.test.tsx"
        derived = tmp_path / "tests/test_foo.tsx"
        # Simulate run 1: PDD creates the greenfield test and records ownership.
        _write(gf, "test('x', () => {})\n")
        record_pdd_created_test(str(gf))
        assert is_pdd_created_test(str(gf)) is True
        # Run 2: the file now exists as a single co-located sibling, but ownership
        # provenance keeps it OUT of the human-adopted never-block.
        assert was_test_adopted(code, str(gf), str(derived), user_pinned=False) is False

    def test_concurrent_ownership_records_are_not_lost(self, tmp_path, monkeypatch):
        # Round 9: parallel children recording greenfield ownership must not
        # clobber each other (locked, atomic RMW). Every recorded path survives.
        import threading
        from pdd.content_selector import record_pdd_created_test, is_pdd_created_test
        monkeypatch.chdir(tmp_path)
        paths = [f"src/mod{i}/__test__/mod{i}.test.tsx" for i in range(40)]
        barrier = threading.Barrier(len(paths))

        def _rec(p):
            barrier.wait()  # maximize contention on the shared manifest
            record_pdd_created_test(p)

        threads = [threading.Thread(target=_rec, args=(p,)) for p in paths]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        missing = [p for p in paths if not is_pdd_created_test(p)]
        assert missing == [], f"lost ownership records under contention: {missing}"

    def test_protected_ownership_survives_candidate_manifest_deletion(
        self, tmp_path, monkeypatch
    ):
        """Deleting/truncating candidate evidence cannot make PDD output human-owned."""
        from pdd.content_selector import is_pdd_created_test

        monkeypatch.chdir(tmp_path)
        owned = tmp_path / "src" / "widget_test.py"
        owned.parent.mkdir()
        owned.write_text("def test_widget(): pass\n", encoding="utf-8")
        manifest = tmp_path / ".pdd" / "meta" / "pdd_created_tests.json"
        manifest.parent.mkdir(parents=True)
        manifest.write_text('["src/widget_test.py"]\n', encoding="utf-8")
        subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            [
                "git", "-c", "user.name=PDD Test", "-c",
                "user.email=pdd-test@example.com", "commit", "-qm", "protected base",
            ],
            cwd=tmp_path,
            check=True,
        )
        base = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=tmp_path, text=True
        ).strip()
        monkeypatch.setenv("PDD_PROTECTED_BASE_REF", base)

        manifest.unlink()
        assert is_pdd_created_test(owned)
        manifest.write_text("[]\n", encoding="utf-8")
        assert is_pdd_created_test(owned)
        manifest.write_text("not-json\n", encoding="utf-8")
        assert is_pdd_created_test(tmp_path / "src" / "unknown_test.py")

    def test_default_issue_runner_pins_ownership_base(
        self, tmp_path, monkeypatch
    ):
        """Non-durable issue sync passes the same immutable ownership authority."""
        from pdd.agentic_sync_runner import AsyncSyncRunner
        from pdd.content_selector import is_pdd_created_test

        monkeypatch.chdir(tmp_path)
        owned = tmp_path / "src" / "widget_test.py"
        owned.parent.mkdir()
        owned.write_text("def test_widget(): pass\n", encoding="utf-8")
        manifest = tmp_path / ".pdd" / "meta" / "pdd_created_tests.json"
        manifest.parent.mkdir(parents=True)
        manifest.write_text('["src/widget_test.py"]\n', encoding="utf-8")
        subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            [
                "git", "-c", "user.name=PDD Test", "-c",
                "user.email=pdd-test@example.com", "commit", "-qm", "issue base",
            ],
            cwd=tmp_path,
            check=True,
        )
        base = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=tmp_path, text=True
        ).strip()
        runner = AsyncSyncRunner(
            basenames=["widget"],
            dep_graph={"widget": []},
            sync_options={
                "protected_base_ref": base,
                "require_protected_base": True,
            },
            github_info={"cwd": tmp_path},
        )
        child_env = runner._build_env(str(tmp_path / "cost.csv"))
        assert child_env["PDD_PROTECTED_BASE_REF"] == base

        manifest.unlink()
        monkeypatch.setenv(
            "PDD_PROTECTED_BASE_REF", child_env["PDD_PROTECTED_BASE_REF"]
        )
        assert is_pdd_created_test(owned)

    def test_ownership_persistence_path_failure_blocks(self, tmp_path, monkeypatch):
        """An escaping path cannot silently skip durable ownership recording."""
        from pdd.content_selector import record_pdd_created_test

        monkeypatch.chdir(tmp_path)
        with pytest.raises(RuntimeError, match="outside the project"):
            record_pdd_created_test(tmp_path.parent / "outside_test.py")

    def test_dynamic_config_construction_refuses(self, tmp_path, monkeypatch):
        # A join of literal key fragments is still statically provable and is
        # resolved without executing repository configuration.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "jest.config.js",
               "const k = ['test','Match'].join(''); module.exports = {[k]: ['<rootDir>/qa/**/*.test.ts']}\n")
        collected = find_runner_collected_test_path(_write(tmp_path / "src/p.ts"))
        assert collected is not None
        assert Path(collected).resolve().relative_to(tmp_path).as_posix().startswith("qa/")

    def test_quoted_discovery_key_config_is_statically_resolved(self, tmp_path, monkeypatch):
        # A quoted literal discovery key is safe to parse without executing the
        # repository config and must direct output into the collected tree.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "jest.config.js",
               'module.exports = { "testMatch": ["<rootDir>/qa/**/*.test.ts"] }\n')
        collected = find_runner_collected_test_path(_write(tmp_path / "src/p.ts"))
        assert collected is not None
        assert Path(collected).resolve().relative_to(tmp_path).as_posix().startswith("qa/")

    def test_two_js_config_files_are_ambiguous(self, tmp_path, monkeypatch):
        # Two distinct runner config FILES at the same level (round 8): the loop
        # must count both, not keep only the first -> ambiguous -> refuse.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "jest.config.js", "module.exports = {}\n")
        _write(tmp_path / "vitest.config.ts",
               "export default { test: { include: ['x/**/*.spec.ts'] } }\n")
        assert find_runner_collected_test_path(_write(tmp_path / "src/p.tsx")) is None

    def test_jest_semver_range_min_major_is_conservative(self):
        # Round 10: enable jest-30-only defaults ONLY when the WHOLE range
        # guarantees major >= 30 — a first-integer parse would misread `<30`/
        # `^30 || ^29` and certify an uncollected .mjs test.
        from pdd.content_selector import _semver_range_min_major as mm
        assert mm("<30") == 0
        assert mm("^30 || ^29") == 29
        assert mm("^30") == 30
        assert mm(">=30") == 30
        assert mm("~30.1") == 30
        assert mm("*") == 0 and mm("latest") == 0 and mm("") == 0
        assert mm(">=29 <31") == 29

    def test_jest_below_30_range_refuses_mjs(self, tmp_path, monkeypatch):
        # A `<30` jest range must NOT enable mjs default discovery (jest <=29
        # does not collect .mjs) -> greenfield refuses for a .mjs module.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", json.dumps({"devDependencies": {"jest": "<30"}}))
        assert find_runner_collected_test_path(_write(tmp_path / "src/u.mjs")) is None
        # A jest `^30` range DOES collect .mjs -> co-locates.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", json.dumps({"devDependencies": {"jest": "^30"}}))
        assert find_runner_collected_test_path(_write(tmp_path / "src/v.mjs")) is not None

    def test_node_modules_candidate_is_not_collected(self, tmp_path, monkeypatch):
        # Round 10: default jest/vitest discovery excludes node_modules, so a
        # co-located candidate there is a false-green -> refuse.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", '{"devDependencies": {"jest": "^30"}}\n')
        code = _write(tmp_path / "node_modules/pkg/src/thing.tsx")
        assert find_runner_collected_test_path(code) is None

    def test_globstar_only_crosses_separators_at_segment_boundary(self):
        # Round 9: `**` is a globstar (crosses `/`) ONLY as a whole segment.
        # Embedded `**` (`qa**/`, `**bar`) is a single-segment `*` in micromatch;
        # translating it to `.*` would certify paths jest rejects.
        def matches(glob, path):
            rx = _micromatch_to_regex(glob)
            return bool(rx) and bool(re.match(rx + r"$", path))
        assert matches("**/qa/x.test.ts", "qa/x.test.ts")
        assert matches("**/a/b.ts", "x/y/a/b.ts")
        assert matches("qa**/page.test.ts", "qafoo/page.test.ts")   # single-segment
        assert not matches("qa**/page.test.ts", "qa/x/page.test.ts")  # must NOT cross /
        assert not matches("**bar/x.ts", "a/bar/x.ts")               # embedded, no cross

    def test_oversized_raw_pattern_is_bounded(self, tmp_path, monkeypatch):
        # A multi-megabyte raw testMatch glob must be rejected BEFORE translation
        # (round 8) — it must not hang and must not certify a co-located path.
        import time
        monkeypatch.chdir(tmp_path)
        huge = "a" * 200_000
        _write(tmp_path / "package.json", json.dumps(
            {"jest": {"testMatch": [f"<rootDir>/{huge}/**/*.test.ts"]}}))
        code = _write(tmp_path / "src/p.tsx")
        start = time.time()
        find_runner_collected_test_path(code)  # must not hang on the giant glob
        assert time.time() - start < 3.0

    def test_jest29_with_vitest_dep_is_ambiguous_mjs_refused(self, tmp_path, monkeypatch):
        # jest<=29 AND a vitest dependency is ambiguous for .mjs (a jest run would
        # not collect it) -> fail closed.
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json",
               json.dumps({"devDependencies": {"jest": "^29.0.0", "vitest": "^1"}}))
        assert find_runner_collected_test_path(_write(tmp_path / "src/u.mjs")) is None
        # A .tsx module is unaffected (collected by both).
        got = find_runner_collected_test_path(_write(tmp_path / "src/w.tsx"))
        assert got is not None

    def test_discovery_has_total_time_budget(self, tmp_path, monkeypatch):
        # Even at the pattern cap, the whole discovery call is time-bounded.
        import time
        monkeypatch.chdir(tmp_path)
        _write(tmp_path / "package.json", json.dumps(
            {"jest": {"testMatch": ["**/+(a|aa)b.test.ts"] * 30}}))
        code = _write(tmp_path / f"src/{'a' * 44}.tsx")
        start = time.time()
        find_runner_collected_test_path(code)  # must not hang
        assert time.time() - start < 5.0, "discovery must be time-bounded"

    def test_runner_pattern_matching_is_redos_bounded(self):
        # A catastrophic-backtracking testMatch pattern must not stall: the
        # bounded matcher fails closed (None) rather than hanging.
        import time
        from pdd.content_selector import _safe_regex_search, _micromatch_to_regex
        pat = _micromatch_to_regex("**/+(a|aa)b.test.ts")
        # all 'a', no trailing 'b' -> exponential backtracking on a naive engine.
        text = "src/" + ("a" * 48) + ".test.ts"
        start = time.time()
        result = _safe_regex_search(pat, text)
        elapsed = time.time() - start
        assert result is None, "catastrophic pattern must fail closed"
        assert elapsed < 1.0, f"matcher must be time-bounded, took {elapsed:.2f}s"


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
    # A plain jest.config.js (no discovery keys) uses jest defaults, which
    # collect the co-located __test__/*.test.tsx.
    _write(tmp_path / "frontend/jest.config.js", "module.exports = {};\n")
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


def _build_opaque_runner_project(
    tmp_path: Path, config: str, *, excluded_sibling: bool = False
) -> tuple[Path, Path, Path]:
    """Create a real TS project whose configured runner cannot prove placement."""
    pddrc = (
        'version: "1.0"\ncontexts:\n  default:\n    defaults:\n'
        '      generate_output_path: "frontend/src/app/contributions/"\n'
        '      default_language: "typescriptreact"\n'
        '      example_output_path: "examples/"\n'
    )
    _write(tmp_path / ".pddrc", pddrc)
    _write(tmp_path / "frontend/vitest.config.js", config)
    code = _write(
        tmp_path / "frontend/src/app/contributions/page.tsx",
        "export default function Page() { return null; }\n",
    )
    prompt = _write(
        tmp_path / "prompts/page_typescriptreact.prompt", "Generate a page.\n"
    )
    sibling = code.parent / "page.test.tsx"
    if excluded_sibling:
        _write(sibling, "test('kept', () => {});\n")
    return code, prompt, sibling


@pytest.mark.parametrize(
    "config",
    [
        "module.exports = { workspace: ['./packages/*'] }\n",
        "module.exports = { testMatch: [123] }\n",
        "const base = loadConfig(); module.exports = base\n",
    ],
    ids=("workspace", "numeric", "dynamic"),
)
def test_get_pdd_file_paths_opaque_runner_suppresses_root_shadow(
    tmp_path, monkeypatch, config
):
    monkeypatch.chdir(tmp_path)
    _build_opaque_runner_project(tmp_path, config)
    shadow = tmp_path / "tests/test_page.tsx"

    paths = get_pdd_file_paths("page", "typescriptreact", "prompts")

    assert paths["test"] is None
    assert paths["test_files"] == []
    assert "could not be proven safely" in paths["test_output_needs_review"]
    assert not shadow.exists()


def test_get_pdd_file_paths_excluded_sibling_without_safe_redirect_is_nonwrite(
    tmp_path, monkeypatch
):
    monkeypatch.chdir(tmp_path)
    code, _prompt, sibling = _build_opaque_runner_project(
        tmp_path,
        "module.exports = { testMatch: ['<rootDir>/qa/**/*-test.tsx'] }\n",
        excluded_sibling=True,
    )
    original = sibling.read_text(encoding="utf-8")
    shadow = tmp_path / "tests/test_page.tsx"

    paths = get_pdd_file_paths("page", "typescriptreact", "prompts")

    assert find_collocated_test(code) == sibling.resolve()
    assert paths["test"] is None
    assert paths["test_files"] == []
    assert sibling.read_text(encoding="utf-8") == original
    assert not shadow.exists()


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


@pytest.mark.parametrize(
    "config",
    [
        "module.exports = { workspace: ['./packages/*'] }\n",
        "module.exports = { testMatch: [123] }\n",
        "const base = loadConfig(); module.exports = base\n",
    ],
    ids=("workspace", "numeric", "dynamic"),
)
def test_cmd_test_main_opaque_runner_returns_needs_review_without_writing(
    tmp_path, local_ctx, monkeypatch, capsys, config
):
    from unittest.mock import patch

    monkeypatch.chdir(tmp_path)
    code, prompt, _sibling = _build_opaque_runner_project(tmp_path, config)
    shadow = tmp_path / "tests/test_page.tsx"

    with patch("pdd.agentic_test_generate.run_agentic_test_generate") as generate:
        result = cmd_test_main(
            ctx=local_ctx,
            prompt_file=str(prompt),
            code_file=str(code),
            output=None,
            language="typescriptreact",
        )

    generate.assert_not_called()
    assert result.agentic_success is True
    assert result.model == "needs-review"
    assert "PDD_TEST_OUTPUT_NEEDS_REVIEW:" in capsys.readouterr().out
    assert not shadow.exists()


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


def test_validated_project_path_allows_only_policy_contained_components(tmp_path, monkeypatch):
    """The shared resolver accepts valid paths but rejects traversal, outside
    absolutes, and an in-tree symlink that targets outside the trusted root."""
    repo = tmp_path / "repo"
    module = _write(repo / "src" / "widget.ts", "export const x = 1;\n")
    outside = _write(tmp_path / "outside.ts", "export const y = 2;\n")
    escaped_link = repo / "src" / "escaped.ts"
    escaped_link.symlink_to(outside)
    monkeypatch.chdir(repo)

    assert _validated_project_path("src/widget.ts") == module.resolve()
    assert _validated_project_path(module) == module.resolve()
    assert _validated_project_path("../outside.ts") is None
    assert _validated_project_path(outside) is None
    assert _validated_project_path(escaped_link) is None


def test_find_collocated_test_rejects_symlink_escape(tmp_path, monkeypatch):
    """A lexical in-repo candidate whose symlink target escapes is rejected."""
    repo = tmp_path / "repo"
    code = _write(repo / "src" / "widget.ts", "export const x = 1;\n")
    outside_test = _write(tmp_path / "widget.test.ts", "test('x', () => {});\n")
    (code.parent / "widget.test.ts").symlink_to(outside_test)
    monkeypatch.chdir(repo)

    assert find_collocated_test(code) is None


def test_pdd_created_tests_lock_is_gitignored_but_manifest_tracked():
    """The transient ownership-manifest lock must never be stageable.

    Codex review (PR #1998): `record_pdd_created_test` opens
    `.pdd/meta/pdd_created_tests.json.lock` (O_CREAT) and does NOT unlink it
    (advisory flock is fd-bound; unlinking would break mutual exclusion). If it
    is stageable, durable sync's `git add -A` stages a `.lock` the allowlist then
    rejects (not the ownership manifest, not a module-prefixed `.json`), failing
    an otherwise-successful greenfield module. The lock must be gitignored while
    the manifest itself stays tracked.
    """
    import subprocess
    from pathlib import Path

    repo_root = Path(__file__).resolve().parents[1]

    def _ignored(rel: str) -> bool:
        return (
            subprocess.run(
                ["git", "check-ignore", "-q", rel],
                cwd=repo_root,
            ).returncode
            == 0
        )

    assert _ignored(".pdd/meta/pdd_created_tests.json.lock"), (
        "the ownership-manifest lock file must be gitignored"
    )
    assert not _ignored(".pdd/meta/pdd_created_tests.json"), (
        "the ownership manifest itself must remain tracked"
    )


def test_ownership_lock_uses_portable_filelock_backend(tmp_path):
    """Ownership serialization must retain a real Windows-capable backend."""
    from unittest.mock import MagicMock, patch
    import pdd.content_selector as selector

    lock = MagicMock()
    lock.__enter__.return_value = lock
    with patch.object(selector, "FileLock", return_value=lock) as file_lock:
        with selector._interprocess_lock(tmp_path / "ownership.lock"):
            pass

    file_lock.assert_called_once_with(str(tmp_path / "ownership.lock"))
    lock.__enter__.assert_called_once_with()
    lock.__exit__.assert_called_once()


def test_safe_regex_search_fails_closed_without_timeout_engine(monkeypatch):
    """Without the wall-clock-timeout regex engine, untrusted patterns must not run.

    Codex review (PR #1998): repo-controlled testRegex/testMatch are ReDoS
    vectors. The length caps do not bound a SHORT catastrophic pattern, so when
    the timeout-capable `regex` package is unavailable the fallback must fail
    closed (return None) rather than evaluate the pattern with unbounded stdlib
    `re`.
    """
    import pdd.content_selector as cs

    monkeypatch.setattr(cs, "_HAVE_REDOS_REGEX", False)
    # Even a trivially-matching pattern is not evaluated on the fallback path.
    assert cs._safe_regex_search("a", "a") is None


def test_safe_regex_search_times_out_on_catastrophic_pattern():
    """A catastrophic short pattern fails closed (None) quickly, never hangs."""
    import time
    import pdd.content_selector as cs

    if not cs._HAVE_REDOS_REGEX:
        import pytest as _pytest
        _pytest.skip("timeout-capable regex engine not installed")

    evil = "(a+)+$"
    text = "a" * 2000 + "!"  # forces catastrophic backtracking, non-matching tail
    start = time.monotonic()
    result = cs._safe_regex_search(evil, text)
    elapsed = time.monotonic() - start

    assert result is None  # fail closed on timeout
    assert elapsed < 2.0, f"ReDoS not bounded: took {elapsed:.2f}s"
