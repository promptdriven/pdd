"""Deterministic, serializable planning for agentic sync.

The planner deliberately has no provider, subprocess, or write dependency.  It
turns already-resolved :class:`~pdd.resolved_sync_unit.ResolvedSyncUnit`
instances into the immutable scope that both a normal sync and an agentic
fallback consume.  Keeping this boundary pure makes it possible to reject an
invalid scope before a child sync can generate code or change architecture.
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
from typing import Any, Iterable, Mapping, Sequence

from .resolved_sync_unit import ResolvedSyncUnit


MODULE_ID_RE = re.compile(
    r"^[A-Za-z0-9][A-Za-z0-9._-]*(?:/[A-Za-z0-9][A-Za-z0-9._-]*)*$"
)
PLAN_DIGEST_PREFIX = b"pdd.sync.plan.v1\n"
SELECTION_DIGEST_PREFIX = b"pdd.sync.selection.v1\n"
MODULE_ID_ENCODING = "pdd.module-id-list.v1"
MAX_AMBIGUITY_CANDIDATES = 64
MAX_SELECTED_MODULE_IDS = 64


class SyncPlanError(ValueError):
    """Raised when a plan or a frozen selection is unsafe to execute."""


class AmbiguousSyncModuleError(SyncPlanError):
    """A compatibility alias selected more than one canonical module."""

    def __init__(self, alias: str, candidates: Sequence[str]) -> None:
        self.alias = alias
        self.candidates = tuple(sorted(candidates))
        super().__init__(
            f"Ambiguous module '{alias}'; use one of: {', '.join(self.candidates)}"
        )


def _canonical_json(value: object) -> bytes:
    """Return the deterministic JSON form used for the V1 digest contracts.

    SyncPlan contains only strings, lists, dicts, booleans and integer indexes;
    this compact JSON representation is therefore RFC-8785 compatible for its
    supported value domain while avoiding a second identity/digest algorithm.
    """
    return json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")


def plan_digest(plan_document: Mapping[str, Any]) -> str:
    """Return the Wave 0 digest of a complete serialized SyncPlan document."""
    return hashlib.sha256(
        PLAN_DIGEST_PREFIX + _canonical_json(dict(plan_document))
    ).hexdigest()


def selection_digest(module_ids: Sequence[str]) -> str:
    """Return the Wave 0 selection digest for sorted canonical module IDs."""
    ids = list(module_ids)
    _require_canonical_ids(ids, allow_empty=True)
    return hashlib.sha256(SELECTION_DIGEST_PREFIX + _canonical_json(ids)).hexdigest()


def _require_canonical_ids(module_ids: Sequence[str], *, allow_empty: bool) -> None:
    if not allow_empty and not module_ids:
        raise SyncPlanError("module IDs must not be empty")
    if list(module_ids) != sorted(module_ids) or len(module_ids) != len(set(module_ids)):
        raise SyncPlanError("module IDs must be sorted and unique")
    if len(module_ids) > MAX_SELECTED_MODULE_IDS:
        raise SyncPlanError(
            f"module ID list exceeds the V1 limit of {MAX_SELECTED_MODULE_IDS}"
        )
    for module_id in module_ids:
        if not isinstance(module_id, str) or MODULE_ID_RE.fullmatch(module_id) is None:
            raise SyncPlanError(f"module ID is not canonical: {module_id!r}")


def canonical_module_id(project_root: Path, unit: ResolvedSyncUnit) -> str:
    """Return the path-qualified V1 identity for ``unit``.

    ``ResolvedSyncUnit.key`` is already the scheduler's canonical identity in
    normal operation.  The fallback below also makes direct/legacy callers safe
    by deriving a project-relative ID from the unit's owning cwd and target.
    """
    key = unit.key.replace("\\", "/").strip("/")
    if MODULE_ID_RE.fullmatch(key):
        return key
    try:
        relative_cwd = unit.cwd.resolve().relative_to(project_root.resolve())
    except ValueError as exc:
        raise SyncPlanError(f"module cwd escapes governing root: {unit.cwd}") from exc
    parts = [part for part in relative_cwd.parts if part not in (".", "")]
    parts.extend(part for part in unit.target_basename.replace("\\", "/").split("/") if part)
    module_id = "/".join(parts)
    if MODULE_ID_RE.fullmatch(module_id) is None:
        raise SyncPlanError(f"unable to create canonical module ID for {unit.key!r}")
    return module_id


def _root_relative(root: Path, path: Path | None) -> str | None:
    if path is None:
        return None
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError as exc:
        raise SyncPlanError(f"path escapes governing root: {path}") from exc


def _governing_root_label(root: Path, cwd: Path) -> str:
    """Serialize a validated unit's governing root without leaking a local path.

    The issue-sync dry-run adapter has already validated its cwd/target pair.
    Legacy callers can provide that pair from an isolated temporary checkout
    outside the process project root; it is not a prompt/output path and must
    not make the evidence serializer repeat resolution or reject the otherwise
    valid, canonical scheduler identity.  Actual prompt/output paths still use
    :func:`_root_relative` and fail closed when they escape the plan root.
    """
    try:
        return _root_relative(root, cwd) or "."
    except SyncPlanError:
        return "."


@dataclass(frozen=True)
class PlanProvenance:
    """Why a candidate entered the plan, without embedding prompt content."""

    source: str
    detail: str = ""

    def to_dict(self) -> dict[str, str]:
        """Serialize only stable provenance fields."""
        return {"source": self.source, "detail": self.detail}


@dataclass(frozen=True)
class SyncPlanDetails:
    """The mutable-in-principle facts captured when a candidate is frozen."""

    changed_reason: str = "unspecified"
    expected_operation: str = "generate"
    confidence: str = "high"
    provenance: tuple[PlanProvenance, ...] = ()


@dataclass(frozen=True)
class SyncPlanCandidate:
    """One resolved, path-aware candidate in the immutable SyncPlan."""

    module_id: str
    unit: ResolvedSyncUnit
    prompt_paths: tuple[Path, ...] = ()
    output_paths: tuple[Path, ...] = ()
    details: SyncPlanDetails = SyncPlanDetails()
    dependencies: tuple[str, ...] = ()

    @property
    def changed_reason(self) -> str:
        """Return the reason recorded when this candidate was selected."""
        return self.details.changed_reason

    @property
    def expected_operation(self) -> str:
        """Return the expected read-only operation classification."""
        return self.details.expected_operation

    @property
    def confidence(self) -> str:
        """Return the source confidence without reclassifying it at runtime."""
        return self.details.confidence

    @property
    def provenance(self) -> tuple[PlanProvenance, ...]:
        """Return immutable source evidence for the candidate."""
        return self.details.provenance

    def compact_metadata(self, root: Path) -> dict[str, object]:
        """Return bounded, path-only data safe to send to an ambiguity agent."""
        return {
            "module_id": self.module_id,
            "prompt_paths": [_root_relative(root, path) for path in self.prompt_paths],
            "output_paths": [_root_relative(root, path) for path in self.output_paths],
            "changed_reason": self.changed_reason,
            "expected_operation": self.expected_operation,
            "confidence": self.confidence,
        }

    def to_dict(
        self, root: Path, *, dependency_order: int, scc_index: int
    ) -> dict[str, object]:
        """Serialize a candidate without machine-local absolute paths."""
        return {
            "module_id": self.module_id,
            "target_basename": self.unit.target_basename,
            "prompt_paths": [_root_relative(root, path) for path in self.prompt_paths],
            "output_paths": [_root_relative(root, path) for path in self.output_paths],
            "governing_root": _governing_root_label(root, self.unit.cwd),
            "governing_pddrc": _root_relative(root, self.unit.pddrc_path),
            "context": self.unit.context,
            "changed_reason": self.changed_reason,
            "expected_operation": self.expected_operation,
            "dependency_order": dependency_order,
            "scc_index": scc_index,
            "confidence": self.confidence,
            "provenance": [item.to_dict() for item in self.provenance],
            "dependencies": list(sorted(self.dependencies)),
        }


@dataclass(frozen=True)
class SyncPlan:
    """The complete frozen candidate set and selected execution scope."""

    root: Path
    candidates: tuple[SyncPlanCandidate, ...]
    selected_module_ids: tuple[str, ...]
    dependency_order: tuple[str, ...]
    sccs: tuple[tuple[str, ...], ...]
    sync_plan_digest: str
    selection_digest: str

    def to_dict(self) -> dict[str, object]:
        """Serialize the frozen candidate and execution sets deterministically."""
        candidate_by_id = {candidate.module_id: candidate for candidate in self.candidates}
        order_index = {
            module_id: index
            for index, module_id in enumerate(self.dependency_order)
        }
        scc_index = {
            module_id: index
            for index, component in enumerate(self.sccs)
            for module_id in component
        }
        return {
            "schema_version": "pdd.sync.plan.v1",
            "module_id_encoding": MODULE_ID_ENCODING,
            "candidates": [
                candidate_by_id[module_id].to_dict(
                    self.root,
                    # Candidates outside the selected scope remain part of the
                    # frozen set for ambiguity/fallback validation, but are not
                    # executable and therefore have no execution position.
                    dependency_order=order_index.get(module_id, -1),
                    scc_index=scc_index.get(module_id, -1),
                )
                for module_id in sorted(candidate_by_id)
            ],
            "selected_module_ids": list(self.selected_module_ids),
            "dependency_order": list(self.dependency_order),
            "sccs": [list(component) for component in self.sccs],
        }

    def serialized(self) -> str:
        """Return canonical, stable JSON for operation evidence."""
        return _canonical_json(self.to_dict()).decode("utf-8")

    def candidate(self, module_id: str) -> SyncPlanCandidate:
        """Look up a candidate without allowing implicit alias resolution."""
        for candidate in self.candidates:
            if candidate.module_id == module_id:
                return candidate
        raise SyncPlanError(f"module {module_id!r} is not in the frozen candidate set")

    def validate_for_execution(self) -> None:
        """Fail atomically before writes when any frozen target is unsafe."""
        _require_canonical_ids(self.selected_module_ids, allow_empty=True)
        selected = set(self.selected_module_ids)
        candidates = {candidate.module_id: candidate for candidate in self.candidates}
        if len(candidates) != len(self.candidates):
            raise SyncPlanError("frozen candidates contain duplicate canonical IDs")
        if not selected <= set(candidates):
            raise SyncPlanError("selected module is absent from frozen candidates")
        if set(self.dependency_order) != selected or len(self.dependency_order) != len(selected):
            raise SyncPlanError("dependency order does not exactly cover selected modules")
        for module_id in self.selected_module_ids:
            candidate = candidates[module_id]
            canonical_module_id(self.root, candidate.unit)
            for path in (*candidate.prompt_paths, *candidate.output_paths):
                _root_relative(self.root, path)
        expected_plan_digest = plan_digest(self.to_dict())
        if self.sync_plan_digest != expected_plan_digest:
            raise SyncPlanError("frozen SyncPlan digest mismatch")
        if self.selection_digest != selection_digest(self.selected_module_ids):
            raise SyncPlanError("frozen selection digest mismatch")


def _stable_scc_order(
    selected: Sequence[str], dependencies: Mapping[str, Sequence[str]]
) -> tuple[tuple[str, ...], ...]:
    """Tarjan SCCs with sorted traversal, yielding stable component identities."""
    index = 0
    stack: list[str] = []
    on_stack: set[str] = set()
    indices: dict[str, int] = {}
    lowlinks: dict[str, int] = {}
    components: list[tuple[str, ...]] = []

    def visit(module_id: str) -> None:
        nonlocal index
        indices[module_id] = index
        lowlinks[module_id] = index
        index += 1
        stack.append(module_id)
        on_stack.add(module_id)
        for dependency in sorted(dependencies.get(module_id, ())):
            if dependency not in indices:
                visit(dependency)
                lowlinks[module_id] = min(lowlinks[module_id], lowlinks[dependency])
            elif dependency in on_stack:
                lowlinks[module_id] = min(lowlinks[module_id], indices[dependency])
        if lowlinks[module_id] == indices[module_id]:
            component: list[str] = []
            while True:
                member = stack.pop()
                on_stack.remove(member)
                component.append(member)
                if member == module_id:
                    break
            components.append(tuple(sorted(component)))

    for module_id in sorted(selected):
        if module_id not in indices:
            visit(module_id)
    return tuple(sorted(components, key=lambda component: component[0]))


def _dependency_order(
    selected: Sequence[str], dependencies: Mapping[str, Sequence[str]]
) -> tuple[str, ...]:
    """Return dependencies first; cycles use lexical order within their SCC."""
    selected_set = set(selected)
    remaining = {
        module_id: set(dependencies.get(module_id, ())) & selected_set
        for module_id in selected
    }
    ordered: list[str] = []
    while remaining:
        ready = sorted(module_id for module_id, deps in remaining.items() if not deps)
        if not ready:
            ready = [min(remaining)]
        for module_id in ready:
            if module_id not in remaining:
                continue
            ordered.append(module_id)
            remaining.pop(module_id)
            for deps in remaining.values():
                deps.discard(module_id)
    return tuple(ordered)


def build_sync_plan(
    root: Path,
    candidates: Iterable[SyncPlanCandidate],
    selected_module_ids: Iterable[str],
) -> SyncPlan:
    """Build and freeze a deterministic plan without running an LLM or writing.

    The selected set is intentionally sorted canonical IDs.  Callers retain a
    separate presentation order if desired; execution always follows the plan's
    dependency order.
    """
    root = Path(root).resolve()
    candidate_tuple = tuple(
        sorted(candidates, key=lambda candidate: candidate.module_id)
    )
    candidate_ids = [candidate.module_id for candidate in candidate_tuple]
    _require_canonical_ids(candidate_ids, allow_empty=True)
    selected = tuple(sorted(set(selected_module_ids)))
    _require_canonical_ids(selected, allow_empty=True)
    candidate_by_id = {candidate.module_id: candidate for candidate in candidate_tuple}
    if not set(selected) <= set(candidate_by_id):
        extras = sorted(set(selected) - set(candidate_by_id))
        raise SyncPlanError(f"selected targets are not frozen candidates: {extras}")
    dependency_graph: dict[str, tuple[str, ...]] = {}
    for candidate in candidate_tuple:
        missing = sorted(set(candidate.dependencies) - set(candidate_by_id))
        if missing:
            raise SyncPlanError(
                f"candidate '{candidate.module_id}' has missing dependency IDs: "
                + ", ".join(missing)
            )
        dependency_graph[candidate.module_id] = tuple(sorted(candidate.dependencies))

    # A selected module is not runnable without every declared dependency.
    # Close transitively before deriving SCCs and ordering so the runner and
    # evidence cannot silently disagree about an omitted edge.
    selected_set = set(selected)
    pending = list(selected)
    while pending:
        module_id = pending.pop()
        for dependency in dependency_graph[module_id]:
            if dependency not in selected_set:
                selected_set.add(dependency)
                pending.append(dependency)
    selected = tuple(sorted(selected_set))
    _require_canonical_ids(selected, allow_empty=True)
    order = _dependency_order(selected, dependency_graph)
    sccs = _stable_scc_order(selected, dependency_graph)
    provisional = SyncPlan(
        root, candidate_tuple, selected, order, sccs, "", selection_digest(selected)
    )
    digest = plan_digest(provisional.to_dict())
    plan = SyncPlan(
        root, candidate_tuple, selected, order, sccs, digest,
        provisional.selection_digest,
    )
    plan.validate_for_execution()
    return plan


def resolve_selection_aliases(
    aliases: Iterable[str], candidates: Iterable[SyncPlanCandidate]
) -> tuple[str, ...]:
    """Resolve legacy unique leaves while refusing ambiguous basenames."""
    candidates = tuple(candidates)
    by_id = {candidate.module_id: candidate.module_id for candidate in candidates}
    by_leaf: dict[str, list[str]] = {}
    for candidate in candidates:
        by_leaf.setdefault(candidate.module_id.rsplit("/", 1)[-1], []).append(
            candidate.module_id
        )
    resolved: list[str] = []
    for alias in aliases:
        normalized = alias.replace("\\", "/").strip("/")
        if normalized in by_id:
            resolved.append(normalized)
            continue
        matches = sorted(by_leaf.get(normalized, ()))
        if len(matches) == 1:
            resolved.append(matches[0])
        elif len(matches) > 1:
            raise AmbiguousSyncModuleError(alias, matches)
        else:
            raise SyncPlanError(
                f"unknown module {alias!r}; candidates: {sorted(by_id)}"
            )
    return tuple(sorted(set(resolved)))


def ambiguity_request(plan: SyncPlan, unresolved_ids: Iterable[str]) -> dict[str, object]:
    """Build the bounded protocol sent to a module-identification agent."""
    unresolved = tuple(sorted(set(unresolved_ids)))
    _require_canonical_ids(unresolved, allow_empty=True)
    if len(unresolved) > MAX_AMBIGUITY_CANDIDATES:
        raise SyncPlanError("ambiguity candidate set exceeds the V1 bound")
    return {
        "schema_version": "pdd.sync.ambiguity.v1",
        "candidate_ids": list(unresolved),
        "candidates": [
            plan.candidate(module_id).compact_metadata(plan.root)
            for module_id in unresolved
        ],
        "instruction": "Select only candidate_ids; do not invent modules, paths, or commands.",
    }


def apply_ambiguity_selection(
    plan: SyncPlan, unresolved_ids: Iterable[str], selected_ids: object
) -> SyncPlan:
    """Validate an agent's bounded choice and return a newly frozen plan."""
    unresolved = tuple(sorted(set(unresolved_ids)))
    _require_canonical_ids(unresolved, allow_empty=True)
    if not isinstance(selected_ids, list) or any(
        not isinstance(value, str) for value in selected_ids
    ):
        raise SyncPlanError("ambiguity response must contain a list of candidate IDs")
    selected = tuple(sorted(set(selected_ids)))
    if len(selected) != len(selected_ids) or not set(selected) <= set(unresolved):
        raise SyncPlanError(
            "ambiguity response contains invented or invalid targets; candidates: "
            + ", ".join(unresolved)
        )
    return build_sync_plan(
        plan.root, plan.candidates, (*plan.selected_module_ids, *selected)
    )


def validate_explicit_scope(plan: SyncPlan, scope: Mapping[str, Any]) -> tuple[str, ...]:
    """Validate fallback payload scope against a frozen primary candidate set."""
    required = {
        "module_id_encoding", "module_ids", "sync_plan_digest", "selection_digest"
    }
    if set(scope) != required or scope.get("module_id_encoding") != MODULE_ID_ENCODING:
        raise SyncPlanError("invalid explicit sync scope V1 payload")
    module_ids = scope["module_ids"]
    if not isinstance(module_ids, list) or any(not isinstance(value, str) for value in module_ids):
        raise SyncPlanError("explicit scope module_ids must be a string list")
    _require_canonical_ids(module_ids, allow_empty=False)
    if scope["sync_plan_digest"] != plan.sync_plan_digest:
        raise SyncPlanError("explicit scope SyncPlan digest does not match frozen plan")
    if scope["selection_digest"] != selection_digest(module_ids):
        raise SyncPlanError("explicit scope selection digest mismatch")
    frozen = {candidate.module_id for candidate in plan.candidates}
    if not set(module_ids) <= frozen:
        raise SyncPlanError("explicit scope contains stale or extra module IDs")
    return tuple(module_ids)


def parse_explicit_scope(raw_scope: str) -> dict[str, object]:
    """Parse the closed fallback JSON object before an execution write exists."""
    try:
        scope = json.loads(raw_scope)
    except (TypeError, json.JSONDecodeError) as exc:
        raise SyncPlanError("PDD_EXPLICIT_SYNC_SCOPE_V1 must be valid JSON") from exc
    if not isinstance(scope, dict):
        raise SyncPlanError("PDD_EXPLICIT_SYNC_SCOPE_V1 must be a JSON object")
    required = {
        "module_id_encoding", "module_ids", "sync_plan_digest", "selection_digest"
    }
    if set(scope) != required:
        raise SyncPlanError("PDD_EXPLICIT_SYNC_SCOPE_V1 must contain exactly V1 fields")
    if not all(isinstance(scope[field], str) for field in (
        "module_id_encoding", "sync_plan_digest", "selection_digest"
    )):
        raise SyncPlanError("PDD_EXPLICIT_SYNC_SCOPE_V1 contains non-string metadata")
    if not isinstance(scope["module_ids"], list):
        raise SyncPlanError("PDD_EXPLICIT_SYNC_SCOPE_V1 module_ids must be a list")
    return scope


def validate_explicit_scope_evidence(
    scope: Mapping[str, Any], evidence: Mapping[str, Any]
) -> tuple[dict[str, object], tuple[str, ...]]:
    """Validate a fallback scope against persisted primary-plan evidence.

    Unlike :func:`validate_explicit_scope`, this function deliberately consumes
    the durable serialized primary plan.  A fallback checkout has no authority
    to rediscover candidates from its diff or architecture state.
    """
    required_evidence = {
        "schema_version", "module_id_encoding", "selected_module_ids",
        "sync_plan_digest", "selection_digest", "sync_plan",
    }
    if set(evidence) != required_evidence:
        raise SyncPlanError("frozen scope evidence has an invalid V1 shape")
    plan = evidence["sync_plan"]
    if not isinstance(plan, dict):
        raise SyncPlanError("frozen scope evidence has no serialized SyncPlan")
    if evidence["sync_plan_digest"] != plan_digest(plan):
        raise SyncPlanError("persisted SyncPlan digest mismatch")
    module_ids = validate_explicit_scope(
        _plan_view_from_evidence(plan, evidence), scope
    )
    if evidence["module_id_encoding"] != MODULE_ID_ENCODING:
        raise SyncPlanError("persisted scope evidence has an unsupported ID encoding")
    return plan, module_ids


def _plan_view_from_evidence(plan: Mapping[str, Any], evidence: Mapping[str, Any]) -> SyncPlan:
    """Create a minimal immutable view used only by explicit-scope validation."""
    candidates = plan.get("candidates")
    if not isinstance(candidates, list):
        raise SyncPlanError("persisted SyncPlan candidates are missing")
    candidate_ids = []
    for candidate in candidates:
        if not isinstance(candidate, dict) or not isinstance(candidate.get("module_id"), str):
            raise SyncPlanError("persisted SyncPlan has malformed candidate IDs")
        candidate_ids.append(candidate["module_id"])
    _require_canonical_ids(sorted(candidate_ids), allow_empty=True)
    # Explicit validation only calls candidate membership/digests; dummy units
    # avoid rediscovery from a potentially changed fallback checkout.
    root = Path.cwd()
    synthetic = tuple(
        SyncPlanCandidate(
            module_id=module_id,
            unit=ResolvedSyncUnit(
                key=module_id, target_basename=module_id, cwd=root,
                pddrc_path=None, context=None, prompts_dir=root,
            ),
        )
        for module_id in sorted(candidate_ids)
    )
    selected = evidence.get("selected_module_ids")
    if not isinstance(selected, list):
        raise SyncPlanError("persisted scope evidence has no primary selection")
    selected_tuple = tuple(selected)
    _require_canonical_ids(selected_tuple, allow_empty=True)
    return SyncPlan(
        root=root,
        candidates=synthetic,
        selected_module_ids=selected_tuple,
        dependency_order=selected_tuple,
        sccs=tuple((module_id,) for module_id in selected_tuple),
        sync_plan_digest=str(evidence["sync_plan_digest"]),
        selection_digest=str(evidence["selection_digest"]),
    )
