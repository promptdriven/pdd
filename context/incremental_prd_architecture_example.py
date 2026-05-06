"""
Example usage of the incremental_prd_architecture module: targeted PRD-driven
architecture updates with deterministic guards (rejecting unknown modules,
dangling dependencies, removals with remaining dependents, unsupported fields,
path traversal, and dependency cycles), atomic .bak/tempfile writes, and a
retry-with-feedback loop on invalid LLM patches.

Pairs with `pdd generate --incremental --experimental-prd <prd_file|issue-url>`.
"""

import json
import sys
from pathlib import Path
from unittest.mock import patch

# Add project root for direct execution. We use insert(0, ...) so this
# worktree's pdd package wins when an older version is also present in the
# active environment (e.g. an installed `pdd` package); sys.path.append put
# the installed copy first and broke direct runs of this example.
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.incremental_prd_architecture import (
    ArchitecturePatch,
    DependencyUpdate,
    ModuleModification,
    ModuleToAdd,
    apply_architecture_patch,
    run_incremental_prd_propagation,
)


def _module(filename, *, deps=None, description=None):
    """Build a minimal architecture entry for the examples."""
    return {
        "filename": filename,
        "reason": f"{filename} reason",
        "description": description or f"{filename} description",
        "dependencies": deps or [],
        "priority": 1,
        "filepath": f"src/{filename.replace('.prompt', '.py')}",
        "tags": ["module", "python"],
        "interface": {"type": "module"},
    }


# --- Example 1: Apply a valid patch directly (no LLM needed) -----------------
def example_apply_patch_directly():
    """Build an ArchitecturePatch in code and apply it deterministically."""
    raw = {
        "prd_files": ["docs/prd.md"],
        "modules": [
            _module("database_python.prompt"),
            _module("api_router_python.prompt", deps=["database_python.prompt"]),
        ],
    }
    patch = ArchitecturePatch(
        modules_to_add=[
            ModuleToAdd(
                filename="audit_logger_python.prompt",
                reason="Audit event emission for mutations",
                dependencies=["database_python.prompt"],
                interface={"type": "module"},
                requirements=["Emit audit events for API mutations."],
            )
        ],
        modules_to_modify=[
            ModuleModification(
                filename="api_router_python.prompt",
                changes={"description": "API routing with audit logging."},
                justification="PRD added audit logging.",
            )
        ],
        dependency_updates=[
            DependencyUpdate(
                source="api_router_python.prompt",
                add=["audit_logger_python.prompt"],
                justification="API router calls audit logger.",
            )
        ],
    )

    result = apply_architecture_patch(raw, patch)

    print(f"Modules after patch: {len(result.modules)}")
    print(f"Changed entries:     {result.changed_filenames}")
    print(f"prd_files preserved: {result.raw_architecture['prd_files']}")
    return result


# --- Example 2: Validators reject unsafe patches -----------------------------
def example_validators_reject_unsafe_patches():
    """Show three classes of rejections: unknown dep, cycle, dependents-on-removed."""
    raw = [_module("api_router_python.prompt", deps=["database_python.prompt"]),
           _module("database_python.prompt")]

    rejected = []

    # 2a. Unknown dependency target
    bad1 = ArchitecturePatch(dependency_updates=[
        DependencyUpdate(source="api_router_python.prompt",
                         add=["nonexistent_python.prompt"],
                         justification="forced bad")])
    try:
        apply_architecture_patch(raw, bad1)
    except ValueError as exc:
        rejected.append(("unknown dep", str(exc)))

    # 2b. New dependency cycle
    bad2 = ArchitecturePatch(dependency_updates=[
        DependencyUpdate(source="database_python.prompt",
                         add=["api_router_python.prompt"],
                         justification="would cycle")])
    try:
        apply_architecture_patch(raw, bad2)
    except ValueError as exc:
        rejected.append(("cycle", str(exc)))

    # 2c. Removal that leaves dependents
    bad3 = ArchitecturePatch(modules_to_remove=[
        {"filename": "database_python.prompt", "justification": "PRD removed it"}])
    try:
        apply_architecture_patch(raw, bad3)
    except ValueError as exc:
        rejected.append(("dangling dependents", str(exc)))

    for category, message in rejected:
        print(f"  rejected ({category}): {message}")
    return rejected


# --- Example 3: Full propagation flow with mocked LLMs -----------------------
def example_run_full_propagation(tmp_root):
    """Demonstrate the orchestrator with mocks for the three LLM seams."""
    docs = tmp_root / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Add audit logging.", encoding="utf-8")

    prompts = tmp_root / "prompts"
    prompts.mkdir()
    (prompts / "api_router_python.prompt").write_text(
        "<pdd-reason>routing</pdd-reason>\n"
        "<pdd-interface>{}</pdd-interface>\n\n"
        "## Requirements\n\n- Route incoming HTTP requests.\n",
        encoding="utf-8",
    )

    arch = tmp_root / "architecture.json"
    arch.write_text(json.dumps({
        "prd_files": ["docs/prd.md"],
        "modules": [_module("api_router_python.prompt")],
    }, indent=2), encoding="utf-8")

    fake_patch = ArchitecturePatch(
        modules_to_add=[ModuleToAdd(filename="audit_logger_python.prompt",
                                    reason="Audit logging",
                                    interface={"type": "module"},
                                    requirements=["Emit audit events."])],
        dependency_updates=[DependencyUpdate(
            source="api_router_python.prompt",
            add=["audit_logger_python.prompt"],
            justification="api_router calls audit_logger")],
    )

    with patch("pdd.incremental_prd_architecture._ask_llm_for_patch",
               return_value=(fake_patch, 0.25, "mock-patch-model")), \
         patch("pdd.incremental_prd_architecture.detect_change",
               return_value=([{"prompt_name": "api_router_python.prompt",
                              "change_instructions": "Add audit-logging note."}],
                             0.10, "mock-detect-model")), \
         patch("pdd.incremental_prd_architecture.change",
               return_value=("<pdd-reason>routing</pdd-reason>\n"
                             "<pdd-interface>{}</pdd-interface>\n\n"
                             "## Requirements\n\n- Route requests.\n- Audit mutations.\n",
                             0.20, "mock-change-model")):
        success, message, cost, model, changed = run_incremental_prd_propagation(
            "docs/prd.md",
            architecture_path=arch,
            prompts_dir=prompts,
            project_root=tmp_root,
            quiet=True,
        )

    print(f"  success={success}  cost=${cost:.2f}  model={model}")
    print(f"  message={message}")
    print(f"  changed_files={changed}")
    return success


# --- Example 4: Dry-run writes nothing ---------------------------------------
def example_dry_run(tmp_root):
    """Same setup as Example 3, but with dry_run=True. No files are written."""
    docs = tmp_root / "docs"
    docs.mkdir()
    (docs / "prd.md").write_text("Add caching layer.", encoding="utf-8")
    prompts = tmp_root / "prompts"
    prompts.mkdir()
    arch = tmp_root / "architecture.json"
    original = {"prd_files": ["docs/prd.md"],
                "modules": [_module("api_router_python.prompt")]}
    arch.write_text(json.dumps(original, indent=2), encoding="utf-8")

    fake_patch = ArchitecturePatch(modules_to_add=[ModuleToAdd(
        filename="cache_python.prompt", reason="Cache",
        interface={"type": "module"})])

    with patch("pdd.incremental_prd_architecture._ask_llm_for_patch",
               return_value=(fake_patch, 0.10, "mock")), \
         patch("pdd.incremental_prd_architecture.detect_change",
               return_value=([], 0.0, "mock")):
        success, _, _, _, _ = run_incremental_prd_propagation(
            "docs/prd.md", architecture_path=arch, prompts_dir=prompts,
            project_root=tmp_root, dry_run=True, quiet=True)

    after = json.loads(arch.read_text(encoding="utf-8"))
    snapshot = tmp_root / ".pdd" / "meta" / "prd_hashes.json"
    print(f"  success={success}  arch unchanged={after == original}  "
          f"snapshot written={snapshot.exists()}")


def main():
    import tempfile

    print("Example 1 — apply_architecture_patch directly")
    print("-" * 60)
    example_apply_patch_directly()

    print("\nExample 2 — validators reject unsafe patches")
    print("-" * 60)
    example_validators_reject_unsafe_patches()

    print("\nExample 3 — run_incremental_prd_propagation (mocked LLMs)")
    print("-" * 60)
    with tempfile.TemporaryDirectory() as tmp:
        example_run_full_propagation(Path(tmp))

    print("\nExample 4 — --dry-run writes nothing")
    print("-" * 60)
    with tempfile.TemporaryDirectory() as tmp:
        example_dry_run(Path(tmp))

    print("\nNext: run `pdd generate --incremental --experimental-prd docs/prd.md` "
          "(or a GitHub issue URL) on a real project.")


if __name__ == "__main__":
    main()
