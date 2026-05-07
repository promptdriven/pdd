"""Example showing how project-root resolution works via architecture_registry.

Demonstrates the tier precedence used by `find_project_root` and the
companion `find_git_toplevel` helper that powers the suppression of
false-positive remote-mismatch warnings in agentic_architecture.
"""

import sys
import tempfile
from pathlib import Path

# Prepend the worktree root so the in-tree `pdd` package wins over any
# already-installed copy that may not yet have the new symbols.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from pdd.architecture_registry import find_git_toplevel, find_project_root


def _touch(path: Path) -> None:
    """Create the file (and any missing parent directories)."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.touch()


def main() -> None:
    """Construct nested directory layouts and resolve their project roots."""

    print("PDD architecture_registry: project-root resolution")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmpdir:
        root = Path(tmpdir).resolve()

        # Layout: outer .git, inner project with .pddrc, deep cwd
        outer = root / "outer"
        outer.mkdir(parents=True)
        (outer / ".git").mkdir()  # outer is an unrelated git repo
        inner = outer / "projects" / "service-a"
        inner.mkdir(parents=True)
        _touch(inner / ".pddrc")  # Tier A marker
        deep_cwd = inner / "src" / "submodule"
        deep_cwd.mkdir(parents=True)

        print("\n[1] Nested Tier A wins over enclosing .git")
        print(f"    cwd                = {deep_cwd}")
        print(f"    find_project_root  = {find_project_root(deep_cwd)}")
        print(f"    find_git_toplevel  = {find_git_toplevel(deep_cwd)}")
        # find_project_root returns `inner` (innermost .pddrc / Tier A),
        # not `outer` (Tier C .git). The strict-descendant relationship
        # between project root and git toplevel lets _ensure_repo_context
        # suppress the remote-mismatch warning when running pdd generate
        # against an issue whose owner/repo differs from the outer remote.

        # Layout: outer PDD marker, inner real git repo
        outer_pdd = root / "outer-pdd"
        _touch(outer_pdd / ".pddrc")
        vendor_repo = outer_pdd / "vendor" / "repo"
        (vendor_repo / ".git").mkdir(parents=True)
        vendor_src = vendor_repo / "src"
        vendor_src.mkdir()
        print("\n[2] Inner .git wins over enclosing PDD marker")
        print(f"    cwd                = {vendor_src}")
        print(f"    find_project_root  = {find_project_root(vendor_src)}")

        # Layout: Tier B (sources/ + PRD)
        prd_project = root / "prd-only"
        (prd_project / "sources").mkdir(parents=True)
        _touch(prd_project / "PRD.md")
        print("\n[3] Tier B (sources/ + PRD/spec markdown)")
        print(f"    cwd                = {prd_project / 'sub'}")
        (prd_project / "sub").mkdir()
        print(f"    find_project_root  = {find_project_root(prd_project / 'sub')}")

        # Layout: only .git -> Tier C boundary
        git_only = root / "plain-repo"
        (git_only / ".git").mkdir(parents=True)
        print("\n[4] Tier C (.git) boundary")
        print(f"    cwd                = {git_only}")
        print(f"    find_project_root  = {find_project_root(git_only)}")

        # Layout: nothing -> resolves to start
        empty = root / "no-markers"
        empty.mkdir()
        print("\n[5] No markers -> returns the resolved start directory")
        print(f"    cwd                = {empty}")
        print(f"    find_project_root  = {find_project_root(empty)}")


if __name__ == "__main__":
    main()
