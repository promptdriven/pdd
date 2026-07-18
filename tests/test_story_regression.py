"""Tests for ``pdd.story_regression`` -- the deterministic story<->test oracle.

Test plan (one or more tests per spec requirement in
``pdd/prompts/story_regression_python.prompt``):

R1  One identity space: ``story_id`` reused from ``user_story_tests`` (str + Path,
    bare-name + full-path) -> TestStoryIdIdentity.
R2  Map built by collection, not execution: ``build_story_map`` over a temp tree
    -> TestBuildStoryMap; bodies never run -> TestNoExecution.
R3  Both marker forms (keyword ``story_id=`` and positional ``args[0]``) normalize
    -> TestMarkerForms; valueless marker -> TestMarkerForms.test_valueless_marker.
R4  Two resolvers over ONE map (cannot drift) -> TestBidirectionalResolution.
R5  Cardinality one->many and one test->many stories -> TestCardinality.
R6  Orphan detection both directions -> TestOrphanDetection.
R7  ``has_regression_test`` predicate True/False -> TestHasRegressionTest.
R8  MUST NOT execute test bodies / no e2e side effects -> TestNoExecution.
R9  Graceful degradation (absent tests dir, unparseable module) -> TestGracefulDegradation.
Marker registration: ``pytest -m story`` selects exactly story-backed tests
    -> TestMarkerSelection; pyproject.toml registers the marker -> TestMarkerRegistration.
Default-map plumbing (set/reset + bare module-level resolvers) -> TestDefaultMap.
"""
from __future__ import annotations

import tomllib
import sys
from pathlib import Path
from typing import Optional

import pytest

from pdd import story_regression
from pdd.story_regression import (
    StoryTestMap,
    build_story_map,
    discover_story_ids,
    has_regression_test,
    markers_without_story,
    reset_default_map,
    set_default_map,
    stories_without_tests,
    story_for_test,
    story_id,
)

# NB: ``tests_for_story`` is referenced via ``story_regression.tests_for_story``
# rather than imported here -- a bare module-level ``tests_for_story`` name would
# match pytest's default ``test*`` collection glob and be (wrongly) collected.


# --- fixtures / helpers --------------------------------------------------------


def test_repeated_same_basename_collection_does_not_reuse_stale_markers(
    tmp_path: Path,
) -> None:
    """Nested collection must not leak a temp test module into the next run."""
    marked = tmp_path / "marked" / "tests"
    plain = tmp_path / "plain" / "tests"
    marked.mkdir(parents=True)
    plain.mkdir(parents=True)
    (marked / "test_foo.py").write_text(
        "import pytest\n@pytest.mark.story('foo_flow')\n"
        "def test_plain():\n    assert True\n",
        encoding="utf-8",
    )
    (plain / "test_foo.py").write_text(
        "def test_plain():\n    assert True\n",
        encoding="utf-8",
    )

    assert build_story_map(marked).has_regression_test("foo_flow") is True
    assert "test_foo" not in sys.modules
    assert build_story_map(plain).has_regression_test("foo_flow") is False
    assert "test_foo" not in sys.modules

SAMPLE = "\n".join(
    [
        "import pytest",
        "",
        '@pytest.mark.story("checkout_flow")',
        "def test_a():",
        "    assert True",
        "",
        '@pytest.mark.story("checkout_flow")',
        "def test_b():",
        "    assert True",
        "",
        '@pytest.mark.story(story_id="refund_flow")',
        "def test_c():",
        "    assert True",
        "",
        '@pytest.mark.story("checkout_flow")',
        '@pytest.mark.story("refund_flow")',
        "def test_d():",
        "    assert True",
        "",
        '@pytest.mark.story("ghost_flow")',
        "def test_e():",
        "    assert True",
        "",
        '@pytest.mark.story("user_stories/story__path_marked_flow.md")',
        "def test_path_marked():",
        "    assert True",
        "",
        "def test_unmarked():",
        "    assert True",
        "",
    ]
)


@pytest.fixture
def tests_dir(tmp_path: Path) -> Path:
    d = tmp_path / "tests"
    d.mkdir()
    (d / "test_sample.py").write_text(SAMPLE, encoding="utf-8")
    return d


@pytest.fixture
def smap(tests_dir: Path) -> StoryTestMap:
    return build_story_map(tests_dir)


@pytest.fixture(autouse=True)
def _clean_default_map():
    # Never let a test leak a default map into another.
    reset_default_map()
    yield
    reset_default_map()


def _node(tests_dir: Path, name: str) -> str:
    return f"test_sample.py::{name}"


# --- R1: identity space --------------------------------------------------------

class TestStoryIdIdentity:
    def test_str_full_path(self):
        assert story_id("user_stories/story__checkout_flow.md") == "checkout_flow"

    def test_bare_name(self):
        assert story_id("story__refund_flow.md") == "refund_flow"

    def test_path_object(self):
        assert story_id(Path("user_stories/story__a_b_c.md")) == "a_b_c"

    def test_is_the_user_story_tests_helper(self):
        # Same object reused -> one identity space, not a second convention.
        from pdd import user_story_tests
        assert story_regression.story_id is user_story_tests.story_id


# --- R2: build by collection ---------------------------------------------------

class TestBuildStoryMap:
    def test_returns_storytestmap(self, smap):
        assert isinstance(smap, StoryTestMap)

    def test_story_to_tests_populated(self, smap, tests_dir):
        assert smap.tests_for_story("checkout_flow") == {
            _node(tests_dir, "test_a"),
            _node(tests_dir, "test_b"),
            _node(tests_dir, "test_d"),
        }

    def test_tests_for_story_accepts_story_file_path(self, smap, tests_dir):
        assert smap.tests_for_story("user_stories/story__checkout_flow.md") == {
            _node(tests_dir, "test_a"),
            _node(tests_dir, "test_b"),
            _node(tests_dir, "test_d"),
        }

    def test_unmarked_test_absent_from_map(self, smap, tests_dir):
        assert smap.story_for_test(_node(tests_dir, "test_unmarked")) is None


# --- R3: both marker forms -----------------------------------------------------

class TestMarkerForms:
    def test_positional_form(self, smap, tests_dir):
        assert smap.story_for_test(_node(tests_dir, "test_a")) == "checkout_flow"

    def test_keyword_form(self, smap, tests_dir):
        assert smap.story_for_test(_node(tests_dir, "test_c")) == "refund_flow"

    def test_valueless_marker_resolves_none(self):
        class _Mark:
            args = ()
            kwargs: dict = {}
        assert story_regression._story_id_from_mark(_Mark()) is None

    def test_positional_value_coerced_to_str(self):
        class _Mark:
            args = (123,)
            kwargs: dict = {}
        assert story_regression._story_id_from_mark(_Mark()) == "123"

    def test_marker_story_file_path_normalized(self, smap, tests_dir):
        assert smap.story_for_test(_node(tests_dir, "test_path_marked")) == "path_marked_flow"


# --- R4: bidirectional, one map ------------------------------------------------

class TestBidirectionalResolution:
    def test_directions_are_consistent(self, smap, tests_dir):
        node = _node(tests_dir, "test_c")
        assert node in smap.tests_for_story("refund_flow")
        assert smap.story_for_test(node) == "refund_flow"

    def test_tests_for_story_returns_copy(self, smap):
        first = smap.tests_for_story("checkout_flow")
        first.add("polluting::node")
        assert "polluting::node" not in smap.tests_for_story("checkout_flow")

    def test_unknown_story_empty_set(self, smap):
        assert smap.tests_for_story("does_not_exist") == set()

    def test_unknown_nodeid_returns_none(self, smap):
        assert smap.story_for_test("nope.py::test_x") is None


# --- R5: cardinality -----------------------------------------------------------

class TestCardinality:
    def test_one_story_many_tests(self, smap):
        assert len(smap.tests_for_story("checkout_flow")) == 3

    def test_one_test_many_stories_returns_set(self, smap, tests_dir):
        owners = smap.story_for_test(_node(tests_dir, "test_d"))
        assert owners == {"checkout_flow", "refund_flow"}
        assert isinstance(owners, set)

    def test_single_story_returns_str(self, smap, tests_dir):
        owner = smap.story_for_test(_node(tests_dir, "test_a"))
        assert owner == "checkout_flow"
        assert isinstance(owner, str)


# --- R6: orphan detection ------------------------------------------------------

class TestOrphanDetection:
    @pytest.fixture
    def stories_dir(self, tmp_path: Path) -> Path:
        d = tmp_path / "user_stories"
        d.mkdir()
        # checkout_flow + refund_flow have tests; lonely_flow has NO test.
        # ghost_flow is referenced by a marker but has NO story file.
        for slug in ("checkout_flow", "refund_flow", "path_marked_flow", "lonely_flow"):
            (d / f"story__{slug}.md").write_text("## Story\n", encoding="utf-8")
        return d

    def test_discover_story_ids(self, stories_dir):
        assert discover_story_ids(str(stories_dir)) == {
            "checkout_flow",
            "refund_flow",
            "path_marked_flow",
            "lonely_flow",
        }

    def test_stories_without_tests(self, smap, stories_dir):
        assert stories_without_tests(smap, stories_dir=str(stories_dir)) == {"lonely_flow"}

    def test_markers_without_story(self, smap, stories_dir):
        # ghost_flow is named by test_e's marker but has no story__ghost_flow.md.
        assert markers_without_story(smap, stories_dir=str(stories_dir)) == {"ghost_flow"}

    def test_two_orphan_kinds_are_distinct(self, smap, stories_dir):
        no_tests = stories_without_tests(smap, stories_dir=str(stories_dir))
        bad_markers = markers_without_story(smap, stories_dir=str(stories_dir))
        assert no_tests.isdisjoint(bad_markers)


# --- R7: coverage predicate ----------------------------------------------------

class TestHasRegressionTest:
    def test_true_when_claimed(self, smap):
        assert smap.has_regression_test("checkout_flow") is True

    def test_true_when_path_is_claimed(self, smap):
        assert smap.has_regression_test(Path("user_stories/story__checkout_flow.md")) is True

    def test_false_when_unclaimed(self, smap):
        assert smap.has_regression_test("never_referenced") is False


# --- R8: no execution / no side effects ----------------------------------------

class TestNoExecution:
    def test_test_bodies_do_not_run(self, tmp_path: Path):
        d = tmp_path / "tests"
        d.mkdir()
        sentinel = tmp_path / "executed.flag"
        body = "\n".join(
            [
                "import pytest",
                "from pathlib import Path",
                f"SENTINEL = Path({str(sentinel)!r})",
                '@pytest.mark.story("exec_check")',
                "def test_writes_sentinel():",
                "    SENTINEL.write_text('ran')",
                "",
            ]
        )
        (d / "test_exec.py").write_text(body, encoding="utf-8")

        smap = build_story_map(d)

        # Collected (so the marker was read) ...
        assert smap.has_regression_test("exec_check") is True
        # ... but the body never ran (collection only, not execution).
        assert not sentinel.exists()


class TestStaticFallback:
    def test_literal_story_markers_survive_empty_pytest_collection(self, tmp_path: Path, monkeypatch):
        d = tmp_path / "tests"
        d.mkdir()
        sentinel = tmp_path / "executed.flag"
        (d / "test_static.py").write_text(
            "\n".join(
                [
                    "import pytest",
                    "from pathlib import Path",
                    f"SENTINEL = Path({str(sentinel)!r})",
                    '@pytest.mark.story("checkout_flow")',
                    '@pytest.mark.story(story_id="refund_flow")',
                    "def test_literal_story_marker():",
                    "    SENTINEL.write_text('ran')",
                    "",
                ]
            ),
            encoding="utf-8",
        )

        def _empty_collect(*_args, **_kwargs):
            return 0

        monkeypatch.setattr(story_regression.pytest, "main", _empty_collect)
        smap = build_story_map(d)

        assert smap.tests_for_story("checkout_flow") == {"test_static.py::test_literal_story_marker"}
        assert smap.tests_for_story("refund_flow") == {"test_static.py::test_literal_story_marker"}
        assert not sentinel.exists()

    def test_constant_story_id_markers_survive_empty_pytest_collection(
        self, tmp_path: Path, monkeypatch
    ):
        """pdd#1889 Bug 3: generated tests declare ``story_id=STORY_ID`` (a module
        constant), not a bare literal. The static fallback (used when pytest
        collection yields zero markers) must resolve those module constants --
        exactly as the gate's own AST scanner already does -- or the whole story
        is (wrongly) reported as having no regression test."""
        d = tmp_path / "tests"
        d.mkdir()
        (d / "test_static_const.py").write_text(
            "\n".join(
                [
                    "import pytest",
                    'PDD_STORY_ID = "checkout_flow"',
                    "@pytest.mark.story(story_id=PDD_STORY_ID)",
                    "def test_const_marker():",
                    "    assert True",
                    "",
                ]
            ),
            encoding="utf-8",
        )

        def _empty_collect(*_args, **_kwargs):
            return 0

        monkeypatch.setattr(story_regression.pytest, "main", _empty_collect)
        smap = build_story_map(d)

        assert smap.tests_for_story("checkout_flow") == {
            "test_static_const.py::test_const_marker"
        }


# --- R9: graceful degradation --------------------------------------------------

class TestGracefulDegradation:
    def test_absent_tests_dir_yields_empty_map(self, tmp_path: Path):
        smap = build_story_map(tmp_path / "no_such_tests")
        assert smap.story_to_tests == {}
        assert smap.test_to_stories == {}

    @pytest.mark.parametrize("non_python_file", [None, "README.md"])
    def test_existing_tests_dir_without_python_files_skips_nested_pytest(
        self, tmp_path: Path, monkeypatch, non_python_file: Optional[str]
    ):
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        if non_python_file:
            (tests_dir / non_python_file).write_text("No tests.\n", encoding="utf-8")

        nested_pytest_calls = []

        def _record_pytest_main(*args, **kwargs):
            nested_pytest_calls.append((args, kwargs))
            return 5

        monkeypatch.setattr(story_regression.pytest, "main", _record_pytest_main)

        smap = build_story_map(tests_dir)

        assert smap.story_to_tests == {}
        assert smap.test_to_stories == {}
        assert nested_pytest_calls == [], (
            "tests directory without Python files invoked pytest.main"
        )

    def test_pytest_suffix_named_candidate_still_starts_collection(
        self, tmp_path: Path, monkeypatch
    ):
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        (tests_dir / "example_test.py").write_text(
            "def test_example():\n    assert True\n", encoding="utf-8"
        )
        nested_pytest_calls = []

        def _record_pytest_main(*args, **kwargs):
            nested_pytest_calls.append((args, kwargs))
            return 0

        monkeypatch.setattr(story_regression.pytest, "main", _record_pytest_main)

        build_story_map(tests_dir)

        assert len(nested_pytest_calls) == 1, (
            "pytest's default *_test.py discovery pattern must remain supported"
        )

    def test_direct_test_file_input_preserves_story_marker(self, tmp_path: Path):
        test_file = tmp_path / "test_direct.py"
        test_file.write_text(
            "import pytest\n"
            "@pytest.mark.story('direct_flow')\n"
            "def test_direct():\n"
            "    assert True\n",
            encoding="utf-8",
        )

        smap = build_story_map(test_file)

        assert smap.has_regression_test("direct_flow") is True

    def test_custom_named_python_candidate_still_starts_collection(
        self, tmp_path: Path, monkeypatch
    ):
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        (tests_dir / "custom_spec.py").write_text(
            "def custom_case():\n    assert True\n", encoding="utf-8"
        )
        nested_pytest_calls = []

        def _record_pytest_main(*args, **kwargs):
            nested_pytest_calls.append((args, kwargs))
            return 0

        monkeypatch.setattr(story_regression.pytest, "main", _record_pytest_main)

        build_story_map(tests_dir)

        assert len(nested_pytest_calls) == 1, (
            "custom pytest python_files candidates must not be pre-skipped"
        )

    def test_unparseable_module_is_skipped(self, tmp_path: Path):
        d = tmp_path / "tests"
        d.mkdir()
        (d / "test_broken.py").write_text("def test_oops(:\n    pass\n", encoding="utf-8")
        good = "\n".join(
            [
                "import pytest",
                '@pytest.mark.story("survives")',
                "def test_ok():",
                "    assert True",
                "",
            ]
        )
        (d / "test_good.py").write_text(good, encoding="utf-8")

        smap = build_story_map(d)
        # The valid sibling is still collected despite the broken module.
        assert smap.has_regression_test("survives") is True


# --- marker registration / selection -------------------------------------------

class TestMarkerRegistration:
    def test_pyproject_registers_story_marker(self):
        pyproject = tomllib.loads(
            (Path(__file__).resolve().parents[1] / "pyproject.toml").read_text(
                encoding="utf-8"
            )
        )
        markers = pyproject["tool"]["pytest"]["ini_options"]["markers"]

        assert any(marker.startswith("story(") for marker in markers)


class TestMarkerSelection:
    def test_dash_m_story_selects_only_story_tests(self, tests_dir: Path):
        class _Counter:
            def __init__(self):
                self.selected: list[str] = []

            def pytest_configure(self, config):
                config.addinivalue_line(
                    "markers",
                    "story(story_id): mark a regression test as the executable oracle "
                    "for a user story",
                )

            def pytest_collection_finish(self, session):
                self.selected = [item.name for item in session.items]

        counter = _Counter()
        pytest.main(
            [
                "-m",
                "story",
                "--collect-only",
                "-q",
                "-p",
                "no:cacheprovider",
                "--import-mode=importlib",
                str(tests_dir),
            ],
            plugins=[counter],
        )
        # Exactly the story-marked tests, and nothing unmarked.
        assert set(counter.selected) == {
            "test_a",
            "test_b",
            "test_c",
            "test_d",
            "test_e",
            "test_path_marked",
        }
        assert "test_unmarked" not in counter.selected


# --- default-map plumbing ------------------------------------------------------

class TestDefaultMap:
    def test_set_default_map_backs_bare_resolvers(self, smap, tests_dir):
        set_default_map(smap)
        assert story_regression.tests_for_story("refund_flow") == {
            _node(tests_dir, "test_c"),
            _node(tests_dir, "test_d"),
        }
        assert story_for_test(_node(tests_dir, "test_a")) == "checkout_flow"
        assert has_regression_test("checkout_flow") is True
        assert has_regression_test("never") is False

    def test_reset_default_map_clears_injected(self, smap):
        set_default_map(smap)
        reset_default_map()
        assert story_regression._DEFAULT_MAP is None
