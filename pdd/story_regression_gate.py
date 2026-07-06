"""Deterministic, public-safe CI gate for story-driven regression tests.

Capstone of EPIC #1698 (issue #1702). Enforces that every user story ships
with a passing, non-stale executable regression test. A regression test
declares which story it protects -- and the story content it was generated
against -- via a marker::

    @pytest.mark.story(story_id="pdd_sync", story_hash="a1b2c3d4e5f6a7b8")
    def test_sync_round_trips():
        ...

The gate reads that marker, recomputes the story's current content hash with
the canonical primitive (``user_story_tests._story_content_hash``), and reports
``story-regression-missing`` / ``story-regression-stale`` accordingly. It runs
entirely offline: no LLM, no cloud credentials, no network -- the same decision
with and without secrets.

Public API
----------
story_id_from_path(path) -> str
discover_story_markers(tests_dir) -> dict[str, StoryMarker]
classify_story(story_path, markers, *, story_text=None) -> StoryRegressionResult
evaluate_stories(*, stories_dir, tests_dir, only_story_ids) -> list[StoryRegressionResult]
changed_story_ids(project_root, *, base_ref) -> Optional[set[str]]
load_story_regression_gate_config(project_root) -> str
resolve_story_regression_gate_mode(*, cli_override, disabled, project_root) -> str
run_story_regression_gate(*, project_root, ...) -> StoryRegressionGateResult
"""
from __future__ import annotations

import ast
import logging
import re
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence

import click

from .construct_paths import _find_pddrc_file, _load_pddrc_config
from .path_resolution import find_project_root_from_path
from .story_regression import StoryTestMap, build_story_map
from .story_test_generation import story_bundle_hash
from .user_story_tests import (
    DEFAULT_STORIES_DIR,
    STORY_PREFIX,
    STORY_SUFFIX,
    _story_content_hash,
    discover_story_files,
    story_id,
)

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Status constants
# ---------------------------------------------------------------------------

STATUS_STORY_REGRESSION_OK = "story-regression-ok"
STATUS_STORY_REGRESSION_MISSING = "story-regression-missing"
STATUS_STORY_REGRESSION_STALE = "story-regression-stale"
STATUS_PASSING = "story-regression-passing"
STATUS_MISSING = STATUS_STORY_REGRESSION_MISSING
STATUS_STALE = STATUS_STORY_REGRESSION_STALE

_GATE_MODES = frozenset({"off", "warn", "strict"})
_DEFAULT_MODE = "warn"
_STRICT_FAIL_EXIT = 2
_DEFAULT_TESTS_DIR = "tests"
_HASH_ASSIGN_RE = re.compile(
    r"^(?:PDD_)?STORY_HASH\s*=\s*(?P<value>['\"].*?['\"])",
    re.MULTILINE,
)


# ---------------------------------------------------------------------------
# Data shapes
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class StoryMarker:
    """A discovered ``@pytest.mark.story(...)`` decorator."""

    story_id: str
    story_hash: Optional[str]
    test_file: str
    test_name: str
    lineno: int


@dataclass(frozen=True)
class StoryRegressionResult:
    """Per-story classification result."""

    story_id: str
    story_path: str
    status: str
    current_hash: str
    recorded_hash: Optional[str]
    test_file: Optional[str]
    test_name: Optional[str]
    detail: str


@dataclass(frozen=True)
class StoryRegressionGateResult:
    """Outcome of a full gate run."""

    mode: str
    ok: bool
    exit_code: int
    results: tuple

    @property
    def offending(self) -> tuple:
        """Results whose status is missing or stale."""
        return tuple(
            r
            for r in self.results
            if r.status
            in (STATUS_STORY_REGRESSION_MISSING, STATUS_STORY_REGRESSION_STALE)
        )


# ---------------------------------------------------------------------------
# Story identity
# ---------------------------------------------------------------------------


def story_id_from_path(path) -> str:
    """Derive the ``story_id`` from a ``story__<id>.md`` path.

    Strips the ``story__`` prefix and ``.md`` suffix from the filename stem.
    A path without the prefix yields its plain stem.
    """
    name = Path(path).name
    if name.endswith(STORY_SUFFIX):
        name = name[: -len(STORY_SUFFIX)]
    if name.startswith(STORY_PREFIX):
        name = name[len(STORY_PREFIX) :]
    return name


# ---------------------------------------------------------------------------
# Marker discovery (AST only -- never executes test code)
# ---------------------------------------------------------------------------


def _literal_str(node: ast.AST) -> Optional[str]:
    """Return the value of a string-literal AST node, else ``None``."""
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    return None


def _module_string_constants(tree: ast.AST) -> Dict[str, str]:
    """Return top-level string constants declared in a test module."""
    constants: Dict[str, str] = {}
    for node in getattr(tree, "body", []):
        targets: list[ast.AST]
        value: ast.AST
        if isinstance(node, ast.Assign):
            targets = list(node.targets)
            value = node.value
        elif isinstance(node, ast.AnnAssign):
            targets = [node.target]
            value = node.value
        else:
            continue
        literal = _literal_str(value)
        if literal is None:
            continue
        for target in targets:
            if isinstance(target, ast.Name):
                constants[target.id] = literal
    return constants


def _string_value(node: ast.AST, constants: Dict[str, str]) -> Optional[str]:
    """Return a literal string or a string module constant referenced by name."""
    literal = _literal_str(node)
    if literal is not None:
        return literal
    if isinstance(node, ast.Name):
        return constants.get(node.id)
    return None


def _is_story_decorator(node: ast.AST) -> bool:
    """True when *node* is a ``pytest.mark.story`` (or ``mark.story``) call/attr."""
    target = node.func if isinstance(node, ast.Call) else node
    # We want the attribute chain ending in ``.story`` preceded by ``.mark``.
    if not isinstance(target, ast.Attribute) or target.attr != "story":
        return False
    parent = target.value
    return isinstance(parent, ast.Attribute) and parent.attr == "mark"


def _marker_from_decorator(
    node: ast.AST,
    *,
    test_name: str,
    test_file: str,
    lineno: int,
    constants: Dict[str, str],
) -> Optional[StoryMarker]:
    """Build a :class:`StoryMarker` from a decorator node, if it is a story marker."""
    if not _is_story_decorator(node):
        return None
    story_id: Optional[str] = None
    story_hash: Optional[str] = None
    if isinstance(node, ast.Call):
        # Support positional story_id as the first arg, plus keywords.
        if node.args:
            story_id = _string_value(node.args[0], constants)
        for kw in node.keywords:
            if kw.arg == "story_id":
                story_id = _string_value(kw.value, constants)
            elif kw.arg == "story_hash":
                story_hash = _string_value(kw.value, constants)
    if not story_id:
        return None
    if not story_hash:
        story_hash = constants.get("PDD_STORY_HASH") or constants.get("STORY_HASH")
    return StoryMarker(
        story_id=story_id,
        story_hash=story_hash or None,
        test_file=test_file,
        test_name=test_name,
        lineno=lineno,
    )


def _markers_in_source(source: str, test_file: str) -> List[StoryMarker]:
    """Parse *source* and return every story marker it declares."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        logger.debug("story-gate: skipping unparsable test file %s", test_file)
        return []
    constants = _module_string_constants(tree)
    found: List[StoryMarker] = []
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for deco in node.decorator_list:
            marker = _marker_from_decorator(
                deco,
                test_name=node.name,
                test_file=test_file,
                lineno=getattr(deco, "lineno", node.lineno),
                constants=constants,
            )
            if marker is not None:
                found.append(marker)
    return found


def discover_story_markers(tests_dir) -> Dict[str, StoryMarker]:
    """AST-scan *tests_dir* for ``@pytest.mark.story`` markers, keyed by story_id.

    Never imports or executes test modules. Returns ``{}`` when the directory
    is missing or empty. When multiple tests claim the same ``story_id`` the
    first by (file path, line) wins, so the result is deterministic.
    """
    base = Path(tests_dir)
    if not base.exists() or not base.is_dir():
        return {}
    markers: Dict[str, StoryMarker] = {}
    for py in sorted(base.rglob("*.py")):
        try:
            source = py.read_text(encoding="utf-8")
        except OSError:
            continue
        for marker in sorted(
            _markers_in_source(source, str(py)), key=lambda m: m.lineno
        ):
            markers.setdefault(marker.story_id, marker)
    return markers


def discover_all_story_markers(tests_dir) -> Dict[str, List[StoryMarker]]:
    """Like :func:`discover_story_markers`, but keeps *every* marker claiming a
    ``story_id`` (deterministically ordered by file path then line).

    A story may legitimately be claimed by more than one test; collapsing to a
    single first-wins marker lets a stale duplicate shadow a fresh sibling and
    misreport the whole story as stale. Callers that judge freshness should use
    this so any fresh claim counts.
    """
    base = Path(tests_dir)
    if not base.exists() or not base.is_dir():
        return {}
    markers: Dict[str, List[StoryMarker]] = {}
    for py in sorted(base.rglob("*.py")):
        try:
            source = py.read_text(encoding="utf-8")
        except OSError:
            continue
        for marker in sorted(
            _markers_in_source(source, str(py)), key=lambda m: m.lineno
        ):
            markers.setdefault(marker.story_id, []).append(marker)
    return markers


# ---------------------------------------------------------------------------
# Classification
# ---------------------------------------------------------------------------


def _classify_story_from_markers(
    story_path,
    story_markers: Sequence[StoryMarker],
    *,
    story_text: Optional[str] = None,
) -> StoryRegressionResult:
    """Classify a story against every marker that claims it.

    A story is fresh if *any* claiming test records an acceptable hash, so a
    stale duplicate marker can never shadow a fresh one. When none is fresh the
    stale/missing detail is drawn from the first marker (by file, then line)
    that records a hash, keeping the message deterministic.
    """
    path = Path(story_path)
    story_id = story_id_from_path(path)
    if story_text is None:
        story_text = path.read_text(encoding="utf-8")
    current_hash = _story_content_hash(story_text)
    acceptable_hashes = {current_hash}
    if path.exists():
        try:
            acceptable_hashes.add(story_bundle_hash(path))
        except OSError:
            pass

    if not story_markers:
        return StoryRegressionResult(
            story_id=story_id,
            story_path=str(path),
            status=STATUS_STORY_REGRESSION_MISSING,
            current_hash=current_hash,
            recorded_hash=None,
            test_file=None,
            test_name=None,
            detail="No @pytest.mark.story regression test resolves to this story.",
        )

    # Fresh if ANY claiming test records an acceptable hash.
    for marker in story_markers:
        if marker.story_hash and marker.story_hash in acceptable_hashes:
            return StoryRegressionResult(
                story_id=story_id,
                story_path=str(path),
                status=STATUS_STORY_REGRESSION_OK,
                current_hash=current_hash,
                recorded_hash=marker.story_hash,
                test_file=marker.test_file,
                test_name=marker.test_name,
                detail="Story has a fresh regression test.",
            )

    # None fresh: prefer a marker that at least records a hash for a precise message.
    hashed = [m for m in story_markers if m.story_hash]
    if not hashed:
        marker = story_markers[0]
        return StoryRegressionResult(
            story_id=story_id,
            story_path=str(path),
            status=STATUS_STORY_REGRESSION_STALE,
            current_hash=current_hash,
            recorded_hash=None,
            test_file=marker.test_file,
            test_name=marker.test_name,
            detail="Regression test records no story_hash; cannot prove freshness.",
        )

    marker = hashed[0]
    return StoryRegressionResult(
        story_id=story_id,
        story_path=str(path),
        status=STATUS_STORY_REGRESSION_STALE,
        current_hash=current_hash,
        recorded_hash=marker.story_hash,
        test_file=marker.test_file,
        test_name=marker.test_name,
        detail=(
            f"Story changed since the regression test was generated "
            f"(recorded {marker.story_hash}, now {current_hash})."
        ),
    )


def classify_story(
    story_path,
    markers: Dict[str, StoryMarker],
    *,
    story_text: Optional[str] = None,
) -> StoryRegressionResult:
    """Classify a single story against a first-wins marker map.

    Retained for backward compatibility. Prefer :func:`evaluate_stories`, which
    considers every marker that claims a story (via
    :func:`discover_all_story_markers`) so a stale duplicate cannot shadow a
    fresh one.
    """
    marker = markers.get(story_id_from_path(Path(story_path)))
    return _classify_story_from_markers(
        story_path,
        [marker] if marker is not None else [],
        story_text=story_text,
    )


def evaluate_stories(
    *,
    stories_dir: Optional[str] = None,
    tests_dir: Optional[str] = None,
    only_story_ids: Optional[Sequence[str]] = None,
) -> List[StoryRegressionResult]:
    """Classify every discovered story (sorted by story_id).

    ``only_story_ids`` restricts evaluation to that set, e.g. to scope the gate
    to the stories touched by a pull request.
    """
    markers = discover_all_story_markers(tests_dir or _DEFAULT_TESTS_DIR)
    wanted = set(only_story_ids) if only_story_ids is not None else None
    results: List[StoryRegressionResult] = []
    for story_path in discover_story_files(stories_dir):
        story_id = story_id_from_path(story_path)
        if wanted is not None and story_id not in wanted:
            continue
        results.append(_classify_story_from_markers(story_path, markers.get(story_id, [])))
    results.sort(key=lambda r: r.story_id)
    return results


# ---------------------------------------------------------------------------
# PR-delta scoping (git diff, offline)
# ---------------------------------------------------------------------------


def _resolve_base_spec(
    project_root: Path, base_ref: Optional[str], git_cmd: str
) -> Optional[str]:
    """Resolve a verifiable base refspec, mirroring the checkup-gate order."""
    candidates: List[str] = []
    if base_ref:
        if base_ref.startswith("refs/"):
            candidates.append(base_ref)
        else:
            candidates.append(f"origin/{base_ref}")
            candidates.append(base_ref)
    candidates.extend(["origin/main", "origin/master", "main", "master"])
    seen: set = set()
    for cand in candidates:
        if cand in seen:
            continue
        seen.add(cand)
        try:
            res = subprocess.run(
                [git_cmd, "-C", str(project_root), "rev-parse", "--verify", cand],
                capture_output=True,
                text=True,
                check=False,
                timeout=5,
            )
        except (OSError, subprocess.SubprocessError):
            continue
        if res.returncode == 0 and res.stdout.strip():
            return cand
    return None


def _git_changed_story_files(
    project_root: Path, git_cmd: str, base_spec: Optional[str]
) -> set:
    """Return story file paths changed vs *base_spec* plus the working tree.

    Covers three sources so a story counts as "in the PR delta" however it
    arrives: committed changes vs the base (``diff base...HEAD``), unstaged/
    staged edits to tracked files (``diff HEAD``), and brand-new untracked
    files (``ls-files --others``), which ``git diff`` alone never reports.
    """
    changed: set = set()
    commands: List[List[str]] = [["diff", "--name-only", "HEAD"]]
    if base_spec:
        commands.insert(0, ["diff", "--name-only", f"{base_spec}...HEAD"])
    commands.append(["ls-files", "--others", "--exclude-standard"])
    for args in commands:
        try:
            res = subprocess.run(
                [git_cmd, "-C", str(project_root), *args],
                capture_output=True,
                text=True,
                check=False,
                timeout=10,
            )
        except (OSError, subprocess.SubprocessError):
            continue
        if res.returncode != 0:
            continue
        for line in res.stdout.splitlines():
            name = line.strip()
            base = name.rsplit("/", 1)[-1]
            if base.startswith(STORY_PREFIX) and base.endswith(STORY_SUFFIX):
                changed.add(name)
    return changed


def changed_story_ids(
    project_root, *, base_ref: Optional[str] = None
) -> Optional[set]:
    """Story ids of ``story__*.md`` files added/modified in the PR delta.

    Returns ``None`` (meaning "scope unknown -- evaluate everything") when git
    is unavailable or no base ref resolves. Never raises; never hits the network.
    """
    root = Path(project_root)
    git_cmd = shutil.which("git")
    if not git_cmd:
        return None
    base_spec = _resolve_base_spec(root, base_ref, git_cmd)
    if base_spec is None and base_ref is not None:
        # An explicit base was requested but could not be resolved: we cannot
        # reliably scope, so signal "evaluate all".
        return None
    changed = _git_changed_story_files(root, git_cmd, base_spec)
    if base_spec is None and not changed:
        # No base and a clean working tree -> we learned nothing about scope.
        return None
    return {story_id_from_path(p) for p in changed}


# ---------------------------------------------------------------------------
# Gate config (mirrors prompt_gate.py)
# ---------------------------------------------------------------------------


def _normalize_mode(raw: object, *, source: str) -> Optional[str]:
    if raw is None:
        return None
    if isinstance(raw, bool):
        if not raw:
            return "off"
        logger.warning(
            "checkup.story_regression_gate value %r in %s is boolean True; "
            "use 'off', 'warn', or 'strict'.",
            raw,
            source,
        )
        return None
    mode = str(raw).strip().lower()
    if mode not in _GATE_MODES:
        logger.warning(
            "Unknown checkup.story_regression_gate value %r in %s; ignoring.",
            raw,
            source,
        )
        return None
    return mode


def load_story_regression_gate_config(project_root) -> str:
    """Load ``checkup.story_regression_gate`` from ``.pddrc`` or ``pyproject.toml``."""
    root = Path(project_root).resolve()

    pddrc = _find_pddrc_file(root)
    if pddrc is not None:
        try:
            config = _load_pddrc_config(pddrc)
        except (OSError, ValueError) as exc:
            logger.warning("Failed to load .pddrc for story regression gate: %s", exc)
        else:
            checkup = config.get("checkup", {})
            if isinstance(checkup, dict) and "story_regression_gate" in checkup:
                mode = _normalize_mode(
                    checkup.get("story_regression_gate"), source=str(pddrc)
                )
                if mode is not None:
                    return mode

    pyproject = root / "pyproject.toml"
    if pyproject.is_file():
        try:
            import tomllib

            data = tomllib.loads(pyproject.read_text(encoding="utf-8"))
        except (OSError, ValueError, ImportError):
            return _DEFAULT_MODE
        checkup = data.get("tool", {}).get("pdd", {}).get("checkup", {})
        if isinstance(checkup, dict) and "story_regression_gate" in checkup:
            mode = _normalize_mode(
                checkup.get("story_regression_gate"), source=str(pyproject)
            )
            if mode is not None:
                return mode

    return _DEFAULT_MODE


def resolve_story_regression_gate_mode(
    *,
    cli_override: Optional[str] = None,
    disabled: bool = False,
    project_root,
) -> str:
    """Resolve the effective gate mode: ``disabled`` > CLI override > config."""
    if disabled:
        return "off"
    if cli_override is not None:
        mode = cli_override.strip().lower()
        if mode not in {"warn", "strict"}:
            raise click.BadParameter(
                "--story-regression-gate must be 'warn' or 'strict'.",
                param_hint="'--story-regression-gate'",
            )
        return mode
    return load_story_regression_gate_config(project_root)


# ---------------------------------------------------------------------------
# Gate orchestration
# ---------------------------------------------------------------------------


def run_story_regression_gate(
    *,
    project_root,
    mode: Optional[str] = None,
    base_ref: Optional[str] = None,
    stories_dir: Optional[str] = None,
    tests_dir: Optional[str] = None,
    scope_to_diff: bool = True,
) -> StoryRegressionGateResult:
    """Run the story-regression gate and return its decision.

    * ``off``    -> always passes, no work done.
    * ``warn``   -> reports missing/stale stories but never fails (exit 0).
    * ``strict`` -> fails (exit 2) when any in-scope story is missing or stale.

    Scope: when ``scope_to_diff`` is true the gate evaluates only stories
    changed in the PR delta (``changed_story_ids``); if that scope is unknown
    it evaluates every story.
    """
    root = Path(project_root)
    effective_mode = mode or load_story_regression_gate_config(root)

    if effective_mode == "off":
        return StoryRegressionGateResult(
            mode="off", ok=True, exit_code=0, results=()
        )

    only_ids: Optional[set] = None
    if scope_to_diff:
        only_ids = changed_story_ids(root, base_ref=base_ref)

    cwd = Path.cwd()
    stories_arg = stories_dir
    if stories_arg is None:
        candidate = root / DEFAULT_STORIES_DIR
        if root.resolve() != cwd.resolve():
            stories_arg = str(candidate)
    tests_arg = tests_dir
    if tests_arg is None:
        tests_arg = str(root / _DEFAULT_TESTS_DIR)

    results = evaluate_stories(
        stories_dir=stories_arg,
        tests_dir=tests_arg,
        only_story_ids=only_ids,
    )

    offending = [
        r
        for r in results
        if r.status
        in (STATUS_STORY_REGRESSION_MISSING, STATUS_STORY_REGRESSION_STALE)
    ]

    if effective_mode == "strict" and offending:
        return StoryRegressionGateResult(
            mode="strict",
            ok=False,
            exit_code=_STRICT_FAIL_EXIT,
            results=tuple(results),
        )

    return StoryRegressionGateResult(
        mode=effective_mode, ok=True, exit_code=0, results=tuple(results)
    )


@dataclass(frozen=True)
class StoryRegressionEvaluation:
    """Gate verdict for one story file."""

    story_id: str
    status: str
    current_hash: str
    tests: list[str]
    recorded_hashes: dict[str, str]

    @property
    def has_regression_test(self) -> bool:
        return bool(self.tests)

    @property
    def passed(self) -> bool:
        return self.status == STATUS_PASSING

    def as_dict(self) -> dict[str, object]:
        return {
            "story_id": self.story_id,
            "status": self.status,
            "has_regression_test": self.has_regression_test,
            "current_hash": self.current_hash,
            "tests": self.tests,
            "recorded_hashes": self.recorded_hashes,
        }


def _test_file_for_nodeid(nodeid: str, tests_dir: Path) -> Optional[Path]:
    path_part = nodeid.split("::", 1)[0]
    candidate = Path(path_part)
    if not candidate.is_absolute():
        candidate = tests_dir / candidate
    if candidate.exists():
        return candidate
    return None


def _recorded_hash(test_path: Path) -> Optional[str]:
    try:
        text = test_path.read_text(encoding="utf-8")
    except OSError:
        return None
    match = _HASH_ASSIGN_RE.search(text)
    if not match:
        return None
    try:
        return str(ast.literal_eval(match.group("value")))
    except (SyntaxError, ValueError):
        return None


def evaluate_story_regression(
    story_path: Path,
    *,
    tests_dir: Path,
    story_map: Optional[StoryTestMap] = None,
) -> StoryRegressionEvaluation:
    """Return missing/stale/passing status for a story without executing tests."""
    sid = story_id(story_path)
    current_hash = story_bundle_hash(story_path)
    smap = story_map if story_map is not None else build_story_map(tests_dir)
    tests = sorted(smap.tests_for_story(sid))
    if not tests:
        return StoryRegressionEvaluation(
            story_id=sid,
            status=STATUS_MISSING,
            current_hash=current_hash,
            tests=[],
            recorded_hashes={},
        )

    recorded: dict[str, str] = {}
    for nodeid in tests:
        test_path = _test_file_for_nodeid(nodeid, tests_dir)
        if test_path is None:
            continue
        found = _recorded_hash(test_path)
        if found:
            recorded[nodeid] = found

    if not recorded:
        # Coverage uses this lightweight evaluator to preserve #1699
        # compatibility with legacy story markers that prove traceability but
        # predate story-hash freshness metadata. The stricter full gate path
        # still reports hashless markers as stale via classify_story().
        return StoryRegressionEvaluation(
            story_id=sid,
            status=STATUS_PASSING,
            current_hash=current_hash,
            tests=tests,
            recorded_hashes={},
        )

    if current_hash not in set(recorded.values()):
        return StoryRegressionEvaluation(
            story_id=sid,
            status=STATUS_STALE,
            current_hash=current_hash,
            tests=tests,
            recorded_hashes=recorded,
        )

    return StoryRegressionEvaluation(
        story_id=sid,
        status=STATUS_PASSING,
        current_hash=current_hash,
        tests=tests,
        recorded_hashes=recorded,
    )
