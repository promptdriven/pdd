"""Deterministic ranked test packing for PDD generation and fix flows.

This module selects which test files to include in LLM context. Tests are
valuable generation context, but including too many of them consumes the
context window and crowds out the prompt, dependencies, and grounding
examples. ``TestContextPacker`` ranks candidate test files across four
signals, packs them greedily under a configurable token budget, and emits a
``TestPackingManifest`` explaining every selection and omission decision.

Responsibilities:
- Rank candidate test files by import-graph distance, symbol-reference
  overlap with the module under change, failure recency, and file recency.
- Always pack currently failing tests first, slicing oversized failing-test
  files via :class:`pdd.pytest_slicer.PytestSlicer`.
- Deduplicate near-duplicate test files and enforce a token cap.
- Emit a manifest of selected and omitted tests with reasons.

Non-responsibilities: it does not run tests, modify test files, assemble the
full sync context package, or perform semantic/embedding ranking.
"""

# pylint: disable=line-too-long,broad-exception-caught,too-many-instance-attributes

from __future__ import annotations

import ast
import json
import logging
import math
import os
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple

from .pytest_slicer import PytestSlicer, SlicerError

logger = logging.getLogger(__name__)

# AdaGReS-style redundancy trade-off parameter. Not exposed as configuration.
_LAMBDA = 0.5

# Configuration defaults (overridable via environment at instantiation).
_DEFAULT_TOKEN_BUDGET = 2000
_DEFAULT_DEDUP_THRESHOLD = 0.8
_DEFAULT_WEIGHTS = {
    "import_distance": 0.4,
    "symbol_overlap": 0.3,
    "failure_recency": 0.2,
    "file_recency": 0.1,
}


def _count_tokens(text: str) -> int:
    """Count tokens, preferring the model-aware counter when importable.

    Falls back to a ``len(text) // 4`` heuristic when ``pdd.server`` is not
    importable (avoids circular imports in CLI-only contexts).
    """
    if not text:
        return 0
    try:
        from .server.token_counter import count_tokens  # local import: optional dep
    except Exception:
        return max(1, len(text) // 4)
    try:
        return count_tokens(text)
    except Exception:
        return max(1, len(text) // 4)


@dataclass
class SelectedTestEntry:
    """A test file that was packed into the context."""

    file: str
    tests: List[str] = field(default_factory=list)
    token_count: int = 0
    score: float = 0.0
    reason: str = ""


@dataclass
class OmittedTestEntry:
    """A candidate test file that was not packed, with the reason why."""

    file: str
    reason: str
    score: float = 0.0


@dataclass
class TestPackingManifest:
    """Explains every selection and omission decision for one packing run."""

    # Prevent pytest from mis-collecting this ``Test*``-named dataclass.
    __test__ = False

    selected: List[SelectedTestEntry] = field(default_factory=list)
    omitted: List[OmittedTestEntry] = field(default_factory=list)
    budget_tokens: int = 0
    used_tokens: int = 0
    failing_test_priority_count: int = 0
    unavailability_reason: Optional[str] = None


@dataclass
class TestPackingResult:
    """The packed test context, its manifest, and total token count."""

    # Prevent pytest from mis-collecting this ``Test*``-named dataclass.
    __test__ = False

    context_text: str = ""
    manifest: TestPackingManifest = field(default_factory=TestPackingManifest)
    token_count: int = 0


class TestContextPacker:
    """Select and rank candidate test files under a configurable token budget."""

    # Prevent pytest from mis-collecting this ``Test*``-named class.
    __test__ = False

    def __init__(self, test_root: str | None = None) -> None:
        self.test_root = test_root or "tests"
        self.budget_tokens = self._read_int_env("PDD_TEST_TOKEN_BUDGET", _DEFAULT_TOKEN_BUDGET)
        self.dedup_threshold = self._read_float_env("PDD_TEST_DEDUP_THRESHOLD", _DEFAULT_DEDUP_THRESHOLD)
        self.weights = self._read_weights_env()
        # Per-instance caches keyed by the module under change.
        self._import_graph_cache: Dict[str, Dict[str, int]] = {}

    # ------------------------------------------------------------------ config
    @staticmethod
    def _read_int_env(key: str, default: int) -> int:
        raw = os.environ.get(key)
        if raw is None or raw.strip() == "":
            return default
        try:
            return int(raw)
        except ValueError:
            logger.warning("Invalid %s=%r; using default %s", key, raw, default)
            return default

    @staticmethod
    def _read_float_env(key: str, default: float) -> float:
        raw = os.environ.get(key)
        if raw is None or raw.strip() == "":
            return default
        try:
            return float(raw)
        except ValueError:
            logger.warning("Invalid %s=%r; using default %s", key, raw, default)
            return default

    def _read_weights_env(self) -> Dict[str, float]:
        weights = dict(_DEFAULT_WEIGHTS)
        raw = os.environ.get("PDD_TEST_RANKING_WEIGHTS")
        if not raw or not raw.strip():
            return weights
        try:
            override = json.loads(raw)
            for key in weights:
                if key in override:
                    weights[key] = float(override[key])
        except (ValueError, TypeError) as exc:
            logger.warning("Invalid PDD_TEST_RANKING_WEIGHTS=%r (%s); using defaults", raw, exc)
        return weights

    # -------------------------------------------------------------- public API
    def pack(
        self,
        module_path: str,
        failing_tests: Sequence[str] | None = None,
        budget_tokens: int | None = None,
        candidate_files: Sequence[str] | None = None,
        slice_failing_tests: bool = False,
    ) -> TestPackingResult:
        """Rank and pack candidate test files under the token budget.

        Failing tests are packed unconditionally before budget accounting.
        Non-failing candidates are scored, sorted, and greedily packed until
        the budget is exhausted, deduplicating near-duplicate coverage.
        When ``candidate_files`` is provided, only those explicit files are
        ranked; callers that pass resolved test paths must not be widened to a
        sibling directory scan.
        ``slice_failing_tests`` asks fix-loop callers to send only the failing
        tests and fixtures even when the full failing file would fit.
        """
        budget = self.budget_tokens if budget_tokens is None else budget_tokens
        manifest = TestPackingManifest(budget_tokens=budget)

        # budget <= 0 => "no test context"; valid for callers that skip tests.
        if budget <= 0:
            return TestPackingResult(context_text="", manifest=manifest, token_count=0)

        failing_ids = self._collect_failing_tests(failing_tests, manifest)
        candidates = self._candidate_test_files(candidate_files)
        if not candidates:
            manifest.unavailability_reason = "no test files found"
            return TestPackingResult(context_text="", manifest=manifest, token_count=0)

        # Map failing test IDs -> {file: [test names within file]}.
        failing_by_file = self._group_failing_by_file(failing_ids, candidates)

        blocks: List[Tuple[str, str]] = []  # (file, rendered content)
        used = 0
        selected_symbol_sets: List[Tuple[str, Set[str]]] = []  # (file, imported symbols)

        # 1. Priority-0 lane: failing tests, packed before budget accounting.
        for file in sorted(failing_by_file):
            names = failing_by_file[file]
            content = self._read_text(file)
            if content is None:
                continue
            tokens = _count_tokens(content)
            if slice_failing_tests or tokens > (budget - used):
                # Oversized failing-test file: slice to only the failing
                # functions and their fixtures rather than the whole file.
                sliced = self._slice_failing(content, file, names)
                if sliced is not None:
                    content = sliced
                    tokens = _count_tokens(content)
            blocks.append((file, content))
            used += tokens
            manifest.selected.append(
                SelectedTestEntry(
                    file=file,
                    tests=names,
                    token_count=tokens,
                    score=1.0,
                    reason="failing test (priority lane)",
                )
            )
            selected_symbol_sets.append((file, self._imported_symbols(file, module_path)))
        manifest.failing_test_priority_count = sum(len(v) for v in failing_by_file.values())

        # 2. Score the remaining (non-failing) candidates.
        remaining_files = [f for f in candidates if f not in failing_by_file]
        scored = self._score_candidates(remaining_files, module_path, failing_ids, manifest)

        # 3. Greedy packing with redundancy penalty + cross-file deduplication.
        for file, score in scored:
            symbols = self._imported_symbols(file, module_path)
            dup_of, max_sim = self._most_similar(symbols, selected_symbol_sets)
            if dup_of is not None and max_sim > self.dedup_threshold:
                manifest.omitted.append(
                    OmittedTestEntry(file=file, reason=f"near-duplicate of {dup_of}", score=score)
                )
                continue
            content = self._read_text(file)
            if content is None:
                continue
            tokens = _count_tokens(content)
            if used + tokens > budget:
                manifest.omitted.append(
                    OmittedTestEntry(file=file, reason="budget exhausted", score=score)
                )
                continue
            # AdaGReS-style marginal gain (records diminishing value of overlap).
            marginal = score - _LAMBDA * max_sim
            blocks.append((file, content))
            used += tokens
            selected_symbol_sets.append((file, symbols))
            manifest.selected.append(
                SelectedTestEntry(
                    file=file,
                    tests=self._test_names(file),
                    token_count=tokens,
                    score=round(marginal, 4),
                    reason="ranked by relevance",
                )
            )

        manifest.used_tokens = used
        context_text = self._render(blocks)
        return TestPackingResult(context_text=context_text, manifest=manifest, token_count=used)

    def _candidate_test_files(self, candidate_files: Sequence[str] | None) -> List[str]:
        if candidate_files is None:
            return self._discover_test_files()
        seen: Set[str] = set()
        files: List[str] = []
        for candidate in candidate_files:
            if not candidate:
                continue
            path = Path(candidate)
            if not path.is_file():
                continue
            key = str(path.resolve())
            if key in seen:
                continue
            seen.add(key)
            files.append(str(path))
        return files

    # ---------------------------------------------------------- failing tests
    def _collect_failing_tests(
        self, failing_tests: Sequence[str] | None, manifest: TestPackingManifest
    ) -> List[str]:
        """Union failing test IDs from the argument, env var, and pytest cache."""
        ids: List[str] = []
        seen: Set[str] = set()

        def _add(values: Sequence[str]) -> None:
            for value in values:
                value = value.strip()
                if value and value not in seen:
                    seen.add(value)
                    ids.append(value)

        if failing_tests:
            _add(list(failing_tests))

        env_value = os.environ.get("PDD_FAILING_TESTS")
        if env_value:
            _add([part for part in env_value.split(",") if part.strip()])

        cache_ids = self._read_lastfailed(manifest)
        if cache_ids:
            _add(cache_ids)
        return ids

    def _read_lastfailed(self, manifest: TestPackingManifest) -> List[str]:
        """Read failing test IDs from ``.pytest_cache/v/cache/lastfailed``."""
        for base in self._cache_search_roots():
            cache_file = base / ".pytest_cache" / "v" / "cache" / "lastfailed"
            if cache_file.is_file():
                try:
                    data = json.loads(cache_file.read_text(encoding="utf-8"))
                except (ValueError, OSError) as exc:
                    logger.warning("Could not read %s (%s)", cache_file, exc)
                    continue
                if isinstance(data, dict):
                    return [key for key, value in data.items() if value]
        return []

    def _cache_search_roots(self) -> List[Path]:
        roots: List[Path] = []
        seen: Set[str] = set()
        for candidate in (Path.cwd(), Path(self.test_root).resolve(), Path(self.test_root).resolve().parent):
            key = str(candidate)
            if key not in seen:
                seen.add(key)
                roots.append(candidate)
        return roots

    def _group_failing_by_file(
        self, failing_ids: Sequence[str], candidates: Sequence[str]
    ) -> Dict[str, List[str]]:
        """Map failing test IDs to the discovered candidate files that own them."""
        by_basename: Dict[str, str] = {}
        for path in candidates:
            by_basename.setdefault(Path(path).name, path)

        grouped: Dict[str, List[str]] = {}
        for test_id in failing_ids:
            parts = test_id.split("::")
            file_part = parts[0]
            resolved = self._match_candidate(file_part, candidates, by_basename)
            if resolved is None:
                continue
            test_name = ".".join(parts[1:]) if len(parts) > 1 else ""
            entries = grouped.setdefault(resolved, [])
            if test_name and test_name not in entries:
                entries.append(test_name)
        return grouped

    @staticmethod
    def _match_candidate(
        file_part: str, candidates: Sequence[str], by_basename: Dict[str, str]
    ) -> Optional[str]:
        target = Path(file_part)
        target_resolved = str(target.resolve()) if target.exists() else None
        for path in candidates:
            if path == file_part:
                return path
            if target_resolved and str(Path(path).resolve()) == target_resolved:
                return path
        return by_basename.get(target.name)

    def _slice_failing(self, content: str, file: str, names: Sequence[str]) -> Optional[str]:
        """Slice a failing-test file to only its failing functions + fixtures."""
        if not names:
            return None
        try:
            sliced, _ = PytestSlicer(content, file_path=file).slice(list(names))
            return sliced
        except SlicerError as exc:
            message = f"pytest slice failed for {file}: {exc}"
            try:
                from .compression_reporting import (
                    CompressionFallbackError,
                    record_compression_fallback,
                )

                record_compression_fallback(message)
                if os.environ.get("PDD_COMPRESSION_FALLBACK", "full").lower() == "error":
                    raise CompressionFallbackError(message) from exc
            except ImportError:
                pass
            logger.warning("Could not slice %s (%s); using full file", file, exc)
            return None

    # ----------------------------------------------------------- file scanning
    def _discover_test_files(self) -> List[str]:
        root = Path(self.test_root)
        if not root.exists() or not root.is_dir():
            return []
        files = {
            str(path)
            for pattern in ("test_*.py", "*_test.py")
            for path in root.rglob(pattern)
            if path.is_file()
        }
        return sorted(files)

    @staticmethod
    def _read_text(file: str) -> Optional[str]:
        try:
            return Path(file).read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            logger.warning("Could not read %s (%s)", file, exc)
            return None

    # --------------------------------------------------------------- scoring
    def _score_candidates(
        self,
        files: Sequence[str],
        module_path: str,
        failing_ids: Sequence[str],
        manifest: TestPackingManifest,
    ) -> List[Tuple[str, float]]:
        if not files:
            return []

        exports = self._module_exports(module_path)
        recency_only = not exports  # unparseable / no module => recency fallback
        if recency_only:
            logger.warning(
                "Module %r has no parseable exported API; falling back to recency-only ranking",
                module_path,
            )

        distances = {} if recency_only else self._build_import_graph(module_path)
        failing_files = {self._file_of(test_id) for test_id in failing_ids}

        mtimes: Dict[str, float] = {}
        raw: Dict[str, Dict[str, float]] = {}
        for file in files:
            mtimes[file] = self._mtime(file)
            resolved = str(Path(file).resolve())
            raw[file] = {
                "import_distance": self._distance_score(distances.get(resolved, math.inf)),
                "symbol_overlap": 0.0 if recency_only else self._symbol_overlap(file, exports),
                "failure_recency": 1.0 if Path(file).name in {Path(f).name for f in failing_files if f} else 0.0,
            }

        recency_scores = self._normalise_recency(mtimes)
        weights = self.weights
        scored: List[Tuple[str, float]] = []
        for file in files:
            signals = raw[file]
            signals["file_recency"] = recency_scores[file]
            if recency_only:
                composite = signals["file_recency"]
            else:
                composite = (
                    weights["import_distance"] * signals["import_distance"]
                    + weights["symbol_overlap"] * signals["symbol_overlap"]
                    + weights["failure_recency"] * signals["failure_recency"]
                    + weights["file_recency"] * signals["file_recency"]
                )
            scored.append((file, composite))

        # Deterministic: highest score first, ties broken by path.
        scored.sort(key=lambda item: (-item[1], item[0]))
        return scored

    @staticmethod
    def _distance_score(distance: float) -> float:
        if distance == math.inf:
            return 0.0
        return 1.0 / (1.0 + distance)

    @staticmethod
    def _normalise_recency(mtimes: Dict[str, float]) -> Dict[str, float]:
        if not mtimes:
            return {}
        values = list(mtimes.values())
        low, high = min(values), max(values)
        span = high - low
        if span <= 0:
            return {file: 1.0 for file in mtimes}
        return {file: (value - low) / span for file, value in mtimes.items()}

    @staticmethod
    def _mtime(file: str) -> float:
        try:
            return Path(file).stat().st_mtime
        except OSError:
            return 0.0

    @staticmethod
    def _file_of(test_id: str) -> str:
        return test_id.split("::")[0]

    # --------------------------------------------------------- symbol analysis
    def _module_exports(self, module_path: str) -> Set[str]:
        """Public top-level names defined by the module under change."""
        content = self._read_text(module_path) if module_path else None
        if not content:
            return set()
        try:
            tree = ast.parse(content, filename=module_path)
        except SyntaxError:
            return set()
        exports: Set[str] = set()
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                if not node.name.startswith("_"):
                    exports.add(node.name)
            elif isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name) and not target.id.startswith("_"):
                        exports.add(target.id)
            elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
                if not node.target.id.startswith("_"):
                    exports.add(node.target.id)
        return exports

    def _symbol_overlap(self, file: str, exports: Set[str]) -> float:
        """Fraction of the module's exported names referenced in the test file."""
        if not exports:
            return 0.0
        names = self._referenced_names(file)
        if not names:
            return 0.0
        return len(exports & names) / len(exports)

    def _referenced_names(self, file: str) -> Set[str]:
        content = self._read_text(file)
        if not content:
            return set()
        try:
            tree = ast.parse(content, filename=file)
        except SyntaxError:
            return set()
        return {node.id for node in ast.walk(tree) if isinstance(node, ast.Name)}

    def _imported_symbols(self, file: str, module_path: str) -> Set[str]:
        """Names imported from the module under change (for deduplication)."""
        content = self._read_text(file)
        if not content:
            return set()
        try:
            tree = ast.parse(content, filename=file)
        except SyntaxError:
            return set()
        module_token = Path(module_path).stem if module_path else ""
        symbols: Set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and node.module:
                if module_token and module_token in node.module.split("."):
                    for alias in node.names:
                        symbols.add(alias.name)
        if not symbols and module_token:
            # Fall back to referenced exports so overlapping coverage still
            # registers even when tests import the package, not the symbol.
            exports = self._module_exports(module_path)
            symbols = exports & self._referenced_names(file)
        return symbols

    @staticmethod
    def _most_similar(
        symbols: Set[str], selected: Sequence[Tuple[str, Set[str]]]
    ) -> Tuple[Optional[str], float]:
        best_file: Optional[str] = None
        best_sim = 0.0
        for file, other in selected:
            sim = _jaccard(symbols, other)
            if sim > best_sim:
                best_sim = sim
                best_file = file
        return best_file, best_sim

    def _test_names(self, file: str) -> List[str]:
        content = self._read_text(file)
        if not content:
            return []
        try:
            tree = ast.parse(content, filename=file)
        except SyntaxError:
            return []
        names: List[str] = []
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name.startswith("test"):
                names.append(node.name)
            elif isinstance(node, ast.ClassDef) and node.name.startswith("Test"):
                for item in node.body:
                    if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)) and item.name.startswith("test"):
                        names.append(f"{node.name}.{item.name}")
        return names

    # ------------------------------------------------------------ import graph
    def _build_import_graph(self, module_path: str) -> Dict[str, int]:
        """BFS hop distance from the module under change to each test file.

        Builds the graph lazily over stdlib ``ast``, caching the result per
        module path within the packer instance. Unreachable files get ``inf``.
        """
        if module_path in self._import_graph_cache:
            return self._import_graph_cache[module_path]

        roots = self._scan_roots(module_path)
        files = self._collect_python_files(roots)
        module_resolved = str(Path(module_path).resolve())
        if module_resolved not in files:
            files.append(module_resolved)

        # Reverse adjacency: imported_by[B] = {A : A imports B}.
        basenames: Dict[str, List[str]] = {}
        for path in files:
            basenames.setdefault(Path(path).stem, []).append(path)
        imported_by: Dict[str, Set[str]] = {path: set() for path in files}
        for path in files:
            for token in self._import_tokens(path):
                for target in basenames.get(token, []):
                    if target != path:
                        imported_by[target].add(path)

        distances: Dict[str, int] = {module_resolved: 0}
        queue: deque[str] = deque([module_resolved])
        while queue:
            current = queue.popleft()
            for importer in sorted(imported_by.get(current, set())):
                if importer not in distances:
                    distances[importer] = distances[current] + 1
                    queue.append(importer)

        self._import_graph_cache[module_path] = distances
        return distances

    def _scan_roots(self, module_path: str) -> List[Path]:
        roots: List[Path] = []
        seen: Set[str] = set()
        module_dir = Path(module_path).resolve().parent if module_path else Path.cwd()
        # Walk up the package (dirs containing __init__.py) to the import root.
        package_root = module_dir
        while (package_root / "__init__.py").exists() and package_root.parent != package_root:
            package_root = package_root.parent
        for candidate in (package_root, Path(self.test_root).resolve()):
            key = str(candidate)
            if key not in seen and candidate.exists():
                seen.add(key)
                roots.append(candidate)
        return roots

    @staticmethod
    def _collect_python_files(roots: Sequence[Path]) -> List[str]:
        skip = {".git", "__pycache__", ".venv", "node_modules", ".pdd", ".pytest_cache"}
        files: Set[str] = set()
        for root in roots:
            if not root.is_dir():
                continue
            for path in root.rglob("*.py"):
                if any(part in skip for part in path.parts):
                    continue
                files.add(str(path.resolve()))
        return sorted(files)

    def _import_tokens(self, path: str) -> Set[str]:
        content = self._read_text(path)
        if not content:
            return set()
        try:
            tree = ast.parse(content, filename=path)
        except SyntaxError:
            return set()
        tokens: Set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    tokens.add(alias.name.split(".")[-1])
            elif isinstance(node, ast.ImportFrom):
                if node.module:
                    tokens.add(node.module.split(".")[-1])
                for alias in node.names:
                    tokens.add(alias.name)
        return tokens

    # ------------------------------------------------------------- rendering
    @staticmethod
    def _render(blocks: Sequence[Tuple[str, str]]) -> str:
        parts: List[str] = []
        for file, content in blocks:
            parts.append(f"# --- {file} ---")
            parts.append(content.strip("\n"))
        return "\n".join(parts)


def _jaccard(a: Set[str], b: Set[str]) -> float:
    if not a and not b:
        return 0.0
    union = a | b
    if not union:
        return 0.0
    return len(a & b) / len(union)
