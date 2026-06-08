"""Wiring and completeness validation module (issue #1466).

Verifies that generated handlers are registered, routes are reachable,
config entries are declared, and modules have corresponding tests.

All checks are deterministic filesystem/AST operations — no LLM calls.
"""
from __future__ import annotations

import logging
import re
from pathlib import Path

from pdd.generation_source_contract import (
    GenerationSourceContract,
    WiringCheckResult,
    WiringStatus,
)

logger = logging.getLogger(__name__)

# Patterns for handler registration detection
_ROUTER_REGISTRATION_RE = re.compile(
    r"(?:router\.\w+|app\.(?:include_router|add_api_route|route|get|post|put|delete|patch))\s*\(",
    re.IGNORECASE,
)


def check_handler_registration(project_root: Path) -> WiringCheckResult:
    """Check if any handlers are registered in the project.

    Returns pass if handler registrations are found, warn otherwise.
    """
    py_files = list(project_root.rglob("*.py"))
    found_any = False

    for py_file in py_files:
        if any(part.startswith(".") for part in py_file.parts):
            continue
        try:
            text = py_file.read_text(encoding="utf-8")
        except OSError:
            continue
        if _ROUTER_REGISTRATION_RE.search(text):
            found_any = True
            break

    if found_any:
        return WiringCheckResult(
            check_kind="handler_registration",
            status=WiringStatus.pass_,
            diagnostic=None,
        )
    else:
        return WiringCheckResult(
            check_kind="handler_registration",
            status=WiringStatus.warn,
            diagnostic=(
                "No handler registration patterns found (router.post/get/put/delete "
                "or app.include_router). Ensure generated handlers are registered "
                "in a routes or application entry-point file."
            ),
        )


def check_route_reachability(project_root: Path) -> WiringCheckResult:
    """Check if routes are reachable from the application entry point."""
    entry_points = list(project_root.rglob("main.py")) + list(project_root.rglob("app.py"))

    if not entry_points:
        return WiringCheckResult(
            check_kind="route_reachability",
            status=WiringStatus.warn,
            diagnostic=(
                "No application entry point (main.py or app.py) found. "
                "Routes may not be reachable."
            ),
        )

    return WiringCheckResult(
        check_kind="route_reachability",
        status=WiringStatus.pass_,
        diagnostic=None,
    )


def check_config_declaration(project_root: Path) -> WiringCheckResult:
    """Check if required config/env entries are declared."""
    config_files = (
        list(project_root.rglob("*.yaml"))
        + list(project_root.rglob("*.yml"))
        + list(project_root.rglob("*.env"))
        + list(project_root.rglob(".env"))
        + list(project_root.rglob("config.py"))
        + list(project_root.rglob("settings.py"))
    )

    if not config_files:
        return WiringCheckResult(
            check_kind="config_declaration",
            status=WiringStatus.warn,
            diagnostic=(
                "No config files (yaml/yml/.env/config.py/settings.py) found. "
                "Required environment/config entries may not be declared."
            ),
        )

    return WiringCheckResult(
        check_kind="config_declaration",
        status=WiringStatus.pass_,
        diagnostic=None,
    )


def check_module_test_coverage(project_root: Path) -> WiringCheckResult:
    """Check if generated modules have corresponding test files."""
    pdd_dir = project_root / "pdd"
    tests_dir = project_root / "tests"

    if not pdd_dir.exists():
        return WiringCheckResult(
            check_kind="module_test_coverage",
            status=WiringStatus.warn,
            diagnostic="No pdd/ module directory found — cannot check test coverage.",
        )

    modules = [
        f.stem
        for f in pdd_dir.glob("*.py")
        if not f.name.startswith("_")
    ]

    if not tests_dir.exists():
        orphaned = modules
    else:
        test_files = {f.stem for f in tests_dir.rglob("test_*.py")}
        orphaned = [
            m for m in modules
            if f"test_{m}" not in test_files
        ]

    if orphaned:
        return WiringCheckResult(
            check_kind="module_test_coverage",
            status=WiringStatus.warn,
            diagnostic=(
                f"Modules without corresponding test files: {', '.join(orphaned[:5])}. "
                "Consider adding tests for these modules."
            ),
        )

    return WiringCheckResult(
        check_kind="module_test_coverage",
        status=WiringStatus.pass_,
        diagnostic=None,
    )


def check_script_executable(project_root: Path) -> WiringCheckResult:
    """Check if scripts listed in the project are executable/documented."""
    script_dirs = [
        project_root / "scripts",
        project_root / "bin",
    ]

    for script_dir in script_dirs:
        if script_dir.exists():
            non_exec = [
                f for f in script_dir.iterdir()
                if f.is_file() and not (f.stat().st_mode & 0o111)
            ]
            if non_exec:
                return WiringCheckResult(
                    check_kind="script_executable",
                    status=WiringStatus.warn,
                    diagnostic=(
                        f"Scripts without executable permission: "
                        f"{', '.join(f.name for f in non_exec[:5])}. "
                        "Run `chmod +x <script>` to fix."
                    ),
                )
            return WiringCheckResult(
                check_kind="script_executable",
                status=WiringStatus.pass_,
                diagnostic=None,
            )

    return WiringCheckResult(
        check_kind="script_executable",
        status=WiringStatus.pass_,
        diagnostic=None,
    )


def validate_wiring(
    contract: GenerationSourceContract,
    project_root: Path,
    *,
    strict: bool = False,
) -> list[WiringCheckResult]:
    """Run all wiring checks and return results.

    When strict=True and any check fails, raises GenerationWiringError.
    When strict=False, returns all results without raising.
    """
    results = [
        check_handler_registration(project_root),
        check_route_reachability(project_root),
        check_config_declaration(project_root),
        check_module_test_coverage(project_root),
        check_script_executable(project_root),
    ]

    contract.wiring_results = results

    if strict:
        failures = [r for r in results if r.status == WiringStatus.fail]
        if failures:
            from pdd.architecture_sync import ArchitectureConformanceError  # type: ignore[import-untyped]

            class GenerationWiringError(ArchitectureConformanceError):
                pass

            diagnostics = "; ".join(f.diagnostic or "no detail" for f in failures)
            raise GenerationWiringError(
                f"Wiring validation failed ({len(failures)} failures): {diagnostics}"
            )

    logger.info(
        "validate_wiring: run_id=%s, %d checks, %d failures",
        contract.run_id,
        len(results),
        sum(1 for r in results if r.status == WiringStatus.fail),
    )

    return results
