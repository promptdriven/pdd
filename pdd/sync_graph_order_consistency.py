"""
Detect when sync ordering would differ between architecture.json and <include>-based graphs.

When ``architecture.json`` exists, agentic sync uses ``build_dep_graph_from_architecture``;
without it, ``build_dependency_graph`` from prompts drives order. This module compares the
two **subgraphs restricted to the current sync set** (using stripped module basenames) and
returns warnings so the switch is never silent.
"""
from __future__ import annotations

from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

from .sync_order import build_dependency_graph, extract_module_from_include


def _compare_id(module_name: str) -> str:
    """
    Map a sync basename to the same module id used in ``build_dependency_graph``.

    ``extract_module_from_include(name + '.prompt')`` handles ``foo_python``-style
    basenames. If that fails (e.g. ``crm_models`` / ``child`` with no fake suffix),
    fall back to the basename string so it still matches prompt filename stems.
    """
    s = extract_module_from_include(module_name + ".prompt")
    return s if s is not None else module_name


def _sync_compare_allowlist(
    modules_to_sync: List[str],
    dep_graph: Dict[str, List[str]],
    full_include: Dict[str, List[str]],
) -> Tuple[Set[str], List[str]]:
    """Returns (ids to compare, modules that cannot be aligned with the include scan)."""
    allow = {_compare_id(m) for m in modules_to_sync}
    skipped: List[str] = []
    graph_keys = set(full_include.keys())
    arch_ids = {_compare_id(k) for k in dep_graph} | {
        _compare_id(d) for vs in dep_graph.values() for d in vs
    }
    for m in modules_to_sync:
        cid = _compare_id(m)
        if extract_module_from_include(m + ".prompt") is None and cid not in graph_keys and cid not in arch_ids:
            skipped.append(m)
    return allow, skipped


def _edge_set_for_compare(
    dep_graph: Dict[str, List[str]],
    allow: Set[str],
) -> Set[Tuple[str, str]]:
    """Directed edges (src, dst) in compare-id space for nodes in ``allow``."""
    edges: Set[Tuple[str, str]] = set()
    for src, deps in dep_graph.items():
        ss = _compare_id(src)
        if ss not in allow:
            continue
        for d in deps:
            sd = _compare_id(d)
            if sd in allow and sd != ss:
                edges.add((ss, sd))
    return edges


def _edge_set_from_include_graph(
    full_include: Dict[str, List[str]],
    allow: Set[str],
) -> Set[Tuple[str, str]]:
    edges: Set[Tuple[str, str]] = set()
    for s in allow:
        for d in full_include.get(s, []):
            if d in allow and d != s:
                edges.add((s, d))
    return edges


def warnings_for_arch_vs_include_sync_order(
    *,
    dep_graph_from_architecture: Dict[str, List[str]],
    modules_to_sync: List[str],
    project_root: Path,
    prompts_dir: Optional[Path] = None,
) -> List[str]:
    """
    If architecture-driven edges differ from include-scan edges (same module subset), warn.

    Compare ids align ``build_dep_graph_from_architecture`` keys with
    ``build_dependency_graph`` (prompt filename stems), using the same rules as
    ``extract_module_from_include`` where possible, with a basename fallback.
    """
    warnings: List[str] = []

    pdir = prompts_dir if prompts_dir is not None else (project_root / "prompts")
    if not pdir.is_dir():
        warnings.append(
            f"Sync order check skipped: prompts directory not found at {pdir}, "
            "cannot build include-based graph for comparison."
        )
        return warnings

    full_include = build_dependency_graph(pdir)
    allow, skipped = _sync_compare_allowlist(
        modules_to_sync, dep_graph_from_architecture, full_include
    )
    if not allow:
        warnings.append(
            "Sync order check skipped: empty module sync set for architecture vs <include> comparison."
        )
        return warnings

    if skipped:
        warnings.append(
            "Sync order comparison: "
            f"{len(skipped)} module(s) could not be aligned with scanned prompts "
            f"({skipped!r}); edge diff applies only to the remaining modules. "
            "Without architecture.json, ordering for omitted names would follow <include> "
            "edges under prompts/."
        )

    arch_e = _edge_set_for_compare(dep_graph_from_architecture, allow)
    inc_e = _edge_set_from_include_graph(full_include, allow)

    only_arch = arch_e - inc_e
    only_inc = inc_e - arch_e
    if only_arch or only_inc:
        warnings.append(
            "Sync order source: using architecture.json for this run. "
            "The include-based graph (used when no architecture.json applies) "
            f"differs on {len(only_arch) + len(only_inc)} edge(s) within the sync set."
        )
        for a, b in sorted(only_arch)[:12]:
            warnings.append(
                f"  Only in architecture graph: {a!r} -> {b!r} "
                f"(no matching <include> dependency between these modules under {pdir})"
            )
        for a, b in sorted(only_inc)[:12]:
            warnings.append(
                f"  Only in <include> graph: {a!r} -> {b!r} "
                f"(not reflected in architecture.json dependencies for this sync set)"
            )
        if len(only_arch) + len(only_inc) > 24:
            warnings.append("  ... further edge differences omitted")

    return warnings
