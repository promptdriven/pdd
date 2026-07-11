"""Deterministic story-regression coverage evidence emitter."""
from __future__ import annotations

import contextlib
import io
import json
import os
import uuid
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

import pytest

SCHEMA_VERSION = 1
STORY_MARKER = "story"

_SCHEMA_PATH = Path(__file__).with_name("schemas") / "story_coverage.schema.json"


def _load_schema() -> Optional[dict]:
    """Load the packaged coverage schema, or ``None`` when unavailable."""
    try:
        return json.loads(_SCHEMA_PATH.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None


def _validate_against_schema(body: dict) -> None:
    """Validate an artifact body against the packaged schema.

    ``jsonschema`` is a declared dependency but the check is imported defensively
    so a stripped-down runtime that lacks it degrades to writing an unvalidated
    artifact rather than hard-crashing. When the library and schema are both
    present, an out-of-range or otherwise invalid body raises before it is
    persisted, so a structurally-impossible coverage result can never be written.
    """
    try:
        import jsonschema  # noqa: PLC0415  (defensive, optional at runtime)
    except ImportError:
        return
    schema = _load_schema()
    if schema is None:
        return
    jsonschema.validate(instance=body, schema=schema)


@dataclass(frozen=True)
class StoryCoverage:
    """Machine-readable story-regression coverage result."""

    schema_version: int
    status: str
    run_id: str
    generated_at: str
    story_count: int
    story_backed_test_count: int
    stories_covered: int
    story_coverage_pct: Optional[float]
    pass_rate: Optional[float]
    passing_test_count: int
    gap_stories: list[str] = field(default_factory=list)
    orphan_tests: list[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        """Return the JSON-serializable artifact body."""
        return asdict(self)


def _story_id_from_path(path: Path) -> str:
    name = path.name
    if name.startswith("story__"):
        name = name[len("story__"):]
    if name.endswith(".md"):
        name = name[:-3]
    return name


def _story_id_from_ref(value: object) -> str:
    text = str(value)
    name = Path(text).name
    if name.startswith("story__") or name.endswith(".md"):
        return _story_id_from_path(Path(text))
    return text


def _story_id_from_mark(mark: pytest.Mark) -> Optional[str]:
    if "story_id" in mark.kwargs:
        value = mark.kwargs["story_id"]
    elif mark.args:
        value = mark.args[0]
    else:
        return None
    if value is None:
        return None
    return _story_id_from_ref(value)


def _relative_nodeid(item: pytest.Item, root: Path) -> str:
    suffix = ""
    if "::" in item.nodeid:
        suffix = "::" + item.nodeid.split("::", 1)[1]
    try:
        return Path(str(item.path)).resolve().relative_to(root.resolve()).as_posix() + suffix
    except (AttributeError, OSError, ValueError):
        return item.nodeid.lstrip("/")


class _StoryCollectionPlugin:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.story_to_tests: dict[str, set[str]] = {}
        self.test_to_stories: dict[str, set[str]] = {}

    def pytest_configure(self, config: pytest.Config) -> None:
        config.addinivalue_line(
            "markers",
            "story(story_id): mark a regression test as an executable story oracle",
        )

    def pytest_collection_modifyitems(self, items: list[pytest.Item]) -> None:
        for item in items:
            stories = {
                sid
                for mark in item.iter_markers(name=STORY_MARKER)
                if (sid := _story_id_from_mark(mark))
            }
            if not stories:
                continue
            nodeid = _relative_nodeid(item, self.root)
            self.test_to_stories[nodeid] = stories
            for sid in stories:
                self.story_to_tests.setdefault(sid, set()).add(nodeid)


def _collect_story_tests(tests_dir: Path) -> _StoryCollectionPlugin:
    plugin = _StoryCollectionPlugin(tests_dir)
    if not tests_dir.exists():
        return plugin
    args = [
        "--collect-only",
        "-q",
        "-m",
        "story",
        "-p",
        "no:cacheprovider",
        "--continue-on-collection-errors",
        "--import-mode=importlib",
        str(tests_dir),
    ]
    sink = io.StringIO()
    with contextlib.redirect_stdout(sink), contextlib.redirect_stderr(sink):
        pytest.main(args, plugins=[plugin])
    return plugin


def _discover_story_ids(stories_dir: Path) -> set[str]:
    if not stories_dir.exists():
        return set()
    return {_story_id_from_path(path) for path in stories_dir.rglob("story__*.md")}


def compute_story_coverage(
    project_root: Path,
    *,
    stories_dir: Optional[Path] = None,
    tests_dir: Optional[Path] = None,
) -> StoryCoverage:
    """Compute deterministic story-regression coverage for *project_root*."""
    project_root = Path(project_root)
    stories_path = stories_dir or project_root / "user_stories"
    tests_path = tests_dir or project_root / "tests"

    story_ids = _discover_story_ids(stories_path)
    collected = _collect_story_tests(tests_path)
    referenced = set(collected.story_to_tests)
    test_count = len(collected.test_to_stories)

    # This adapter only performs pytest collection. It deliberately does not
    # execute tests or consume a gate-result feed, so pass/fail and non-stale
    # coverage evidence is unavailable and must not be inferred from markers.
    status = "not_applicable"
    stories_covered = 0
    coverage_pct = None

    return StoryCoverage(
        schema_version=SCHEMA_VERSION,
        status=status,
        run_id=uuid.uuid4().hex,
        generated_at=datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        story_count=len(story_ids),
        story_backed_test_count=test_count,
        stories_covered=stories_covered,
        story_coverage_pct=coverage_pct,
        pass_rate=None,
        passing_test_count=0,
        gap_stories=sorted(story_ids - referenced),
        orphan_tests=sorted(referenced - story_ids),
    )


def write_story_coverage(
    coverage: StoryCoverage,
    project_root: Path,
    *,
    run_id: Optional[str] = None,
) -> Path:
    """Write latest and per-run story coverage artifacts."""
    body = coverage.to_dict()
    if run_id is not None:
        body["run_id"] = run_id
    effective_run_id = str(body["run_id"])

    # Reject a structurally-impossible artifact before writing anything, so the
    # durable .pdd/evidence contract can never carry out-of-range values.
    _validate_against_schema(body)

    evidence_dir = Path(project_root) / ".pdd" / "evidence" / "stories"
    runs_dir = evidence_dir / "runs"
    runs_dir.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(body, indent=2, sort_keys=True) + "\n"

    latest = evidence_dir / "coverage.latest.json"
    snapshot = runs_dir / f"{effective_run_id}.json"
    latest.write_text(payload, encoding="utf-8")
    snapshot.write_text(payload, encoding="utf-8")
    return latest


def format_summary_line(coverage: StoryCoverage) -> str:
    """Return the CI summary line for *coverage*."""
    if coverage.status == "not_applicable" or coverage.story_coverage_pct is None:
        return (
            "story regression: not_applicable "
            f"({coverage.story_backed_test_count} collected story tests across "
            f"{coverage.stories_covered}/{coverage.story_count} verified stories; "
            "pass-rate unavailable)"
        )
    return (
        f"story regression: {coverage.story_backed_test_count} tests across "
        f"{coverage.stories_covered}/{coverage.story_count} stories "
        f"({coverage.story_coverage_pct:g}% covered), "
        f"{coverage.passing_test_count} passing"
    )


def emit_story_coverage(
    project_root: Path,
    *,
    stories_dir: Optional[Path] = None,
    tests_dir: Optional[Path] = None,
    run_id: Optional[str] = None,
) -> StoryCoverage:
    """Compute, write, and print story coverage evidence."""
    coverage = compute_story_coverage(project_root, stories_dir=stories_dir, tests_dir=tests_dir)
    if run_id is not None:
        coverage = StoryCoverage(**{**coverage.to_dict(), "run_id": run_id})
    write_story_coverage(coverage, project_root)
    line = format_summary_line(coverage)
    print(line)
    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary_path:
        with open(summary_path, "a", encoding="utf-8") as fh:
            fh.write(line + "\n")
    return coverage
