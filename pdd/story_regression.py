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

import ast
import contextlib
import io
import logging
import sys
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
    "story(story_id, story_hash): mark a regression test as the executable oracle for a user story"
)

PathLike = Union[str, Path]
_STORY_TEST_GLOBS = ("test*.py", "*_test.py")


def _default_tests_dir() -> Path:
    """Return the repository's ``tests/`` directory (sibling of the ``pdd`` package)."""
    return Path(__file__).resolve().parents[1] / "tests"


def _normalize_story_ref(value: object) -> str:
    """Return the canonical story id for either an id or story file path."""
    text = str(value)
    name = Path(text).name
    if name.startswith("story__") or name.endswith(".md"):
        return story_id(text)
    return text


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
    return _normalize_story_ref(value)


def _relative_nodeid(item: pytest.Item, root: Path) -> str:
    """Return a stable node id relative to the collected tests root."""
    suffix = ""
    if "::" in item.nodeid:
        suffix = "::" + item.nodeid.split("::", 1)[1]
    try:
        test_path = Path(str(item.path)).resolve().relative_to(root.resolve())
        return test_path.as_posix() + suffix
    except (AttributeError, ValueError, OSError):
        # Fall back to pytest's nodeid, but strip a leading slash so absolute
        # temp paths do not vary across machines.
        return item.nodeid.lstrip("/")


def _module_string_constants(tree: ast.AST) -> Dict[str, str]:
    """Return top-level ``NAME = "literal"`` string constants in a module.

    Mirrors the gate's own AST constant resolver so the static fallback can
    resolve ``story_id=STORY_ID`` / ``story_id=PDD_STORY_ID`` module constants
    that generated tests emit (pdd#1889 Bug 3), not only bare string literals.
    """
    constants: Dict[str, str] = {}
    for node in getattr(tree, "body", []):
        if isinstance(node, ast.Assign):
            targets = list(node.targets)
            value = node.value
        elif isinstance(node, ast.AnnAssign):
            targets = [node.target]
            value = node.value
        else:
            continue
        if not (isinstance(value, ast.Constant) and isinstance(value.value, str)):
            continue
        for target in targets:
            if isinstance(target, ast.Name):
                constants[target.id] = value.value
    return constants


def _literal_story_id(
    node: ast.AST, constants: Optional[Dict[str, str]] = None
) -> Optional[str]:
    """Return a story id from a decorator argument (literal or module constant)."""
    if isinstance(node, ast.Constant) and node.value is not None:
        return _normalize_story_ref(node.value)
    if constants is not None and isinstance(node, ast.Name):
        resolved = constants.get(node.id)
        if resolved is not None:
            return _normalize_story_ref(resolved)
    return None


def _story_id_from_decorator(
    decorator: ast.AST, constants: Optional[Dict[str, str]] = None
) -> Optional[str]:
    """Resolve a ``@pytest.mark.story`` decorator's story id without executing code."""
    if not isinstance(decorator, ast.Call):
        return None

    func = decorator.func
    is_story_mark = (
        isinstance(func, ast.Attribute)
        and func.attr == STORY_MARKER
        and isinstance(func.value, ast.Attribute)
        and func.value.attr == "mark"
        and isinstance(func.value.value, ast.Name)
        and func.value.value.id == "pytest"
    )
    if not is_story_mark:
        return None

    for keyword in decorator.keywords:
        if keyword.arg == "story_id":
            return _literal_story_id(keyword.value, constants)

    if decorator.args:
        return _literal_story_id(decorator.args[0], constants)

    return None


def _scan_story_markers_static(tests_dir: Path) -> StoryTestMap:
    """Best-effort static fallback for ``@pytest.mark.story`` decorators.

    Resolves both string-literal and module-constant ``story_id`` forms.
    """
    story_to_tests: Dict[str, Set[str]] = {}
    test_to_stories: Dict[str, Set[str]] = {}
    root = tests_dir.resolve()

    for path in sorted(tests_dir.rglob("test*.py")):
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        except (OSError, SyntaxError, UnicodeDecodeError):
            continue

        try:
            rel_path = path.resolve().relative_to(root).as_posix()
        except (ValueError, OSError):
            rel_path = path.name

        constants = _module_string_constants(tree)
        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            if not node.name.startswith("test"):
                continue
            story_ids = {
                sid
                for decorator in node.decorator_list
                for sid in [_story_id_from_decorator(decorator, constants)]
                if sid
            }
            if not story_ids:
                continue
            nodeid = f"{rel_path}::{node.name}"
            test_to_stories.setdefault(nodeid, set()).update(story_ids)
            for sid in story_ids:
                story_to_tests.setdefault(sid, set()).add(nodeid)

    return StoryTestMap(story_to_tests=story_to_tests, test_to_stories=test_to_stories)


@dataclass
class StoryTestMap:
    """Immutable view of the collected story<->test relation.

    Both ``story_to_tests`` and ``test_to_stories`` are derived from the **same**
    collection pass, so the two resolver directions cannot drift apart.
    """

    story_to_tests: Dict[str, Set[str]] = field(default_factory=dict)
    test_to_stories: Dict[str, Set[str]] = field(default_factory=dict)

    def tests_for_story(self, story_ref: PathLike) -> Set[str]:
        """Return the node ids that claim *story_ref* (a fresh copy).

        ``story_ref`` may be either a canonical story id (``checkout_flow``) or a
        story file path such as ``user_stories/story__checkout_flow.md``.
        """
        return set(self.story_to_tests.get(_normalize_story_ref(story_ref), ()))

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

    def has_regression_test(self, story_ref: PathLike) -> bool:
        """Return ``True`` when at least one collected test claims *story_ref*."""
        return bool(self.story_to_tests.get(_normalize_story_ref(story_ref)))

    @property
    def referenced_story_ids(self) -> Set[str]:
        """Return every story id named by at least one ``@pytest.mark.story`` marker."""
        return set(self.story_to_tests.keys())


class _StoryCollector:
    """A ``--collect-only`` plugin that records the story<->test relation."""

    def __init__(self, root: Path) -> None:
        self.root = root
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
            nodeid = _relative_nodeid(item, self.root)
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
    if not resolved_dir.exists():
        return StoryTestMap({}, {})
    has_collection_candidate = any(
        path.is_file()
        for pattern in _STORY_TEST_GLOBS
        for path in resolved_dir.rglob(pattern)
    )
    if not has_collection_candidate:
        return StoryTestMap({}, {})

    collector = _StoryCollector(resolved_dir)

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
        resolved_root = resolved_dir.resolve()
        candidate_module_leaves = {
            path.stem for path in resolved_dir.rglob("*.py") if path.is_file()
        }
        # A previous nested collection (or another caller) may already have
        # imported a same-named test module from a different root.  Pytest can
        # reuse that entry even in importlib mode, so remove such collisions for
        # the duration of this collection and restore them afterward.
        colliding_modules = {
            name: module
            for name, module in list(sys.modules.items())
            if name.rsplit(".", 1)[-1] in candidate_module_leaves
            and getattr(module, "__file__", None)
        }
        for name in colliding_modules:
            sys.modules.pop(name, None)
        modules_before = dict(sys.modules)
        try:
            with contextlib.redirect_stdout(sink), contextlib.redirect_stderr(sink):
                pytest.main(args, plugins=[collector])
        finally:
            # Nested pytest collection imports test modules into this process.
            # Restore every module loaded from this tests root so a later
            # collection of a same-named file in another root cannot reuse its
            # stale markers (common for repeated temporary ``test_foo.py``).
            for name, module in list(sys.modules.items()):
                module_file = getattr(module, "__file__", None)
                if not module_file:
                    continue
                try:
                    Path(module_file).resolve().relative_to(resolved_root)
                except (OSError, ValueError):
                    continue
                if name in modules_before:
                    sys.modules[name] = modules_before[name]
                else:
                    sys.modules.pop(name, None)
            sys.modules.update(colliding_modules)
    except Exception:  # pylint: disable=broad-except
        # Graceful degradation: never let a collection failure crash a caller.
        logger.warning("story collection over %s failed; returning partial map", resolved_dir)

    if not collector.story_to_tests:
        return _scan_story_markers_static(resolved_dir)

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


def tests_for_story(story_ref: PathLike) -> Set[str]:
    """Return the set of test node ids that claim *story_ref*."""
    return _get_default_map().tests_for_story(story_ref)


def story_for_test(nodeid: str) -> Union[str, Set[str], None]:
    """Return the owning story id(s) for the test *nodeid* (``None`` if unclaimed)."""
    return _get_default_map().story_for_test(nodeid)


def has_regression_test(story_ref: PathLike) -> bool:
    """Return ``True`` when >=1 collected regression test claims *story_ref*."""
    return _get_default_map().has_regression_test(story_ref)


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
