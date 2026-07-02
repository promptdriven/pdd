"""Deterministic missing/stale gate for story regression tests."""
from __future__ import annotations

import ast
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from .story_regression import StoryTestMap, build_story_map
from .story_test_generation import story_bundle_hash
from .user_story_tests import story_id


STATUS_PASSING = "story-regression-passing"
STATUS_MISSING = "story-regression-missing"
STATUS_STALE = "story-regression-stale"

_HASH_ASSIGN_RE = re.compile(r"^PDD_STORY_HASH\s*=\s*(?P<value>['\"].*?['\"])", re.MULTILINE)


@dataclass(frozen=True)
class StoryRegressionGateResult:
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
) -> StoryRegressionGateResult:
    """Return missing/stale/passing status for a story without executing tests."""
    sid = story_id(story_path)
    current_hash = story_bundle_hash(story_path)
    smap = story_map if story_map is not None else build_story_map(tests_dir)
    tests = sorted(smap.tests_for_story(sid))
    if not tests:
        return StoryRegressionGateResult(
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

    if recorded and current_hash not in set(recorded.values()):
        return StoryRegressionGateResult(
            story_id=sid,
            status=STATUS_STALE,
            current_hash=current_hash,
            tests=tests,
            recorded_hashes=recorded,
        )

    return StoryRegressionGateResult(
        story_id=sid,
        status=STATUS_PASSING,
        current_hash=current_hash,
        tests=tests,
        recorded_hashes=recorded,
    )
