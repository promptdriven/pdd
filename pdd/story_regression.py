"""Deterministic, marker-traceable pytest story<->test traceability for PDD.

This module is the *deterministic* counterpart to the LLM oracle in
``pdd.user_story_tests``. Where ``user_story_tests`` links a story to the
*prompts* it validates (via ``detect_change``, an LLM call), this module links a
story to the pytest **regression tests** that claim it through the
``@pytest.mark.story`` marker.

The map is built by **collection only** -- a ``pytest --collect-only`` plugin
that reads ``@pytest.mark.story`` markers. It never runs an LLM, never executes
test bodies, and never triggers ``e2e``/``real`` collection side effects. The
only concept shared with ``user_story_tests`` is the :func:`story_id` identity
helper, re-exported here so both systems live in one identity space.
"""
from __future__ import annotations

import contextlib
import io
import logging
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Set, Union

import pytest

# Re-export the single, public ``story_id`` identity helper so callers can rely
# on one slug convention regardless of which module they import it from.
from .user_story_tests import discover_story_files, story_id

__all__ = [
    "story_id",
    "tests_for_story",
    "story_for_test",
    "has_regression_test",
    "build_story_map",
    "StoryTestMap",
    "discover_story_ids",
    "stories_without_tests",
    "markers_without_story",
    "set_default_map",
    "reset_default_map",
]

logger = logging.getLogger(__name__)

STORY_MARKER = "story"
_STORY_MARKER_HELP = (
    "story(story_id): mark a regression test as the executable oracle for a user story"
)

PathLike = Union[str, Path]


def _default_tests_dir() -> Path:
    """Return the repository's ``tests/`` directory (sibling of the ``pdd`` package)."""
    return Path(__file__).resolve().parents[1] / "tests"


def _story_id_from_mark(mark: pytest.Mark) -> Optional[str]:
    """Resolve a single ``story_id`` from one ``@pytest.mark.story`` application.

    Accepts both the keyword form ``@pytest.mark.story(story_id="x")`` and the
    positional form ``@pytest.mark.story("x")`` (``args[0]``). Returns ``None``
    for an empty/valueless marker rather than raising.
    """
    if "story_id" in mark.kwargs:
        value = mark.kwargs["story_id"]
    elif mark.args:
        value = mark.args[0]
    else:
        return None
    if value is None:
        return None
    return str(value)


@dataclass
class StoryTestMap:
    """Immutable view of the collected story<->test relation.

    Both ``story_to_tests`` and ``test_to_stories`` are derived from the **same**
    collection pass, so the two resolver directions cannot drift apart.
    """

    story_to_tests: Dict[str, Set[str]] = field(default_factory=dict)
    test_to_stories: Dict[str, Set[str]] = field(default_factory=dict)

    def tests_for_story(self, story_id_value: str) -> Set[str]:
        """Return the node ids that claim *story_id_value* (a fresh copy)."""
        return set(self.story_to_tests.get(story_id_value, ()))

    def story_for_test(self, nodeid: str) -> Union[str, Set[str], None]:
        """Return the owning story id(s) for *nodeid*.

        Returns a plain ``str`` when exactly one story is claimed, a ``set`` when
        more than one is claimed, and ``None`` when the node claims no story.
        """
        stories = self.test_to_stories.get(nodeid)
        if not stories:
            return None
        if len(stories) == 1:
            return next(iter(stories))
        return set(stories)

    def has_regression_test(self, story_id_value: str) -> bool:
        """Return ``True`` when at least one collected test claims *story_id_value*."""
        return bool(self.story_to_tests.get(story_id_value))

    @property
    def referenced_story_ids(self) -> Set[str]:
        """Return every story id named by at least one ``@pytest.mark.story`` marker."""
        return set(self.story_to_tests.keys())


class _StoryCollector:
    """A ``--collect-only`` plugin that records the story<->test relation."""

    def __init__(self) -> None:
        self.story_to_tests: Dict[str, Set[str]] = {}
        self.test_to_stories: Dict[str, Set[str]] = {}

    def pytest_configure(self, config: pytest.Config) -> None:
        # Register the marker in the (possibly fresh) inner session so collection
        # does not emit ``PytestUnknownMarkWarning`` when an outer pytest.ini is
        # not in scope.
        config.addinivalue_line("markers", _STORY_MARKER_HELP)

    def pytest_collection_modifyitems(self, items: List[pytest.Item]) -> None:
        for item in items:
            story_ids: Set[str] = set()
            # ``iter_markers`` yields one Mark per decorator application, so a test
            # stacked with several @story markers contributes to several stories.
            for mark in item.iter_markers(name=STORY_MARKER):
                resolved = _story_id_from_mark(mark)
                if resolved:
                    story_ids.add(resolved)
            if not story_ids:
                continue
            nodeid = item.nodeid
            self.test_to_stories.setdefault(nodeid, set()).update(story_ids)
            for sid in story_ids:
                self.story_to_tests.setdefault(sid, set()).add(nodeid)


def build_story_map(tests_dir: Optional[PathLike] = None) -> StoryTestMap:
    """Collect the story<->test map from *tests_dir* (defaults to repo ``tests/``).

    Collection only: ``pytest --collect-only`` imports test modules to read their
    ``@pytest.mark.story`` markers but never executes test bodies or fixtures, so
    no ``e2e``/``real`` side effects fire. An absent ``tests/`` directory yields
    an empty map without error, and an unparseable test module is skipped (via
    ``--continue-on-collection-errors``) rather than crashing the build.
    """
    resolved_dir = Path(tests_dir) if tests_dir is not None else _default_tests_dir()
    collector = _StoryCollector()
    if not resolved_dir.exists():
        return StoryTestMap({}, {})

    args = [
        "--collect-only",
        "-q",
        "-p",
        "no:cacheprovider",
        "--continue-on-collection-errors",
        # importlib import-mode keeps collection from polluting ``sys.modules``
        # with the test package, so repeated calls (and same-basename test files
        # under different roots) don't collide.
        "--import-mode=importlib",
        str(resolved_dir),
    ]
    try:
        # Keep the inner collection run silent: this is a library helper, not a
        # test runner, so its callers should not see pytest's terminal output.
        sink = io.StringIO()
        with contextlib.redirect_stdout(sink), contextlib.redirect_stderr(sink):
            pytest.main(args, plugins=[collector])
    except Exception:  # pylint: disable=broad-except
        # Graceful degradation: never let a collection failure crash a caller.
        logger.warning("story collection over %s failed; returning partial map", resolved_dir)

    return StoryTestMap(
        story_to_tests=collector.story_to_tests,
        test_to_stories=collector.test_to_stories,
    )


# --- Default (lazily built) map backing the bare module-level resolvers --------

_DEFAULT_MAP: Optional[StoryTestMap] = None


def _get_default_map() -> StoryTestMap:
    global _DEFAULT_MAP  # pylint: disable=global-statement
    if _DEFAULT_MAP is None:
        _DEFAULT_MAP = build_story_map()
    return _DEFAULT_MAP


def set_default_map(story_map: StoryTestMap) -> None:
    """Install *story_map* as the map backing the bare resolver functions."""
    global _DEFAULT_MAP  # pylint: disable=global-statement
    _DEFAULT_MAP = story_map


def reset_default_map() -> None:
    """Drop the cached default map so the next resolver call rebuilds it."""
    global _DEFAULT_MAP  # pylint: disable=global-statement
    _DEFAULT_MAP = None


def tests_for_story(story_id_value: str) -> Set[str]:
    """Return the set of test node ids that claim *story_id_value*."""
    return _get_default_map().tests_for_story(story_id_value)


def story_for_test(nodeid: str) -> Union[str, Set[str], None]:
    """Return the owning story id(s) for the test *nodeid* (``None`` if unclaimed)."""
    return _get_default_map().story_for_test(nodeid)


def has_regression_test(story_id_value: str) -> bool:
    """Return ``True`` when >=1 collected regression test claims *story_id_value*."""
    return _get_default_map().has_regression_test(story_id_value)


# --- Orphan detection (both directions) ----------------------------------------


def discover_story_ids(stories_dir: Optional[str] = None) -> Set[str]:
    """Return the ``story_id`` of every ``story__<slug>.md`` on disk."""
    return {story_id(path) for path in discover_story_files(stories_dir)}


def stories_without_tests(
    story_map: Optional[StoryTestMap] = None,
    stories_dir: Optional[str] = None,
) -> Set[str]:
    """Return story ids that exist on disk but have no claiming regression test.

    This is the "no executable regression test" coverage gap.
    """
    smap = story_map if story_map is not None else _get_default_map()
    return {sid for sid in discover_story_ids(stories_dir) if not smap.has_regression_test(sid)}


def markers_without_story(
    story_map: Optional[StoryTestMap] = None,
    stories_dir: Optional[str] = None,
) -> Set[str]:
    """Return story ids named by a marker but with no matching ``story__<slug>.md``.

    Distinct from :func:`stories_without_tests`: this surfaces a *validation
    warning* -- a test claims a story that does not exist on disk (typo or stale
    rename).
    """
    smap = story_map if story_map is not None else _get_default_map()
    known = discover_story_ids(stories_dir)
    return {sid for sid in smap.referenced_story_ids if sid not in known}
