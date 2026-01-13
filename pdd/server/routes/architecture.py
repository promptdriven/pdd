"""
REST API endpoints for architecture.json validation operations.

Provides endpoints for validating architecture changes before saving,
detecting circular dependencies, missing references, and other structural issues.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Set

from fastapi import APIRouter
from pydantic import BaseModel, Field


router = APIRouter(prefix="/api/v1/architecture", tags=["architecture"])


class ArchitectureModule(BaseModel):
    """Schema for an architecture module."""

    reason: str
    description: str
    dependencies: List[str]
    priority: int
    filename: str
    filepath: str
    tags: List[str] = Field(default_factory=list)
    interface: Optional[Dict[str, Any]] = None


class ValidationError(BaseModel):
    """Validation error that blocks saving."""

    type: str  # circular_dependency, missing_dependency, invalid_field
    message: str
    modules: List[str]  # Affected module filenames


class ValidationWarning(BaseModel):
    """Validation warning that is informational only."""

    type: str  # duplicate_dependency, orphan_module
    message: str
    modules: List[str]


class ValidateArchitectureRequest(BaseModel):
    """Request body for architecture validation."""

    modules: List[ArchitectureModule]


class ValidationResult(BaseModel):
    """Result of architecture validation."""

    valid: bool  # True if no errors (warnings are OK)
    errors: List[ValidationError]
    warnings: List[ValidationWarning]


def _detect_circular_dependencies(modules: List[ArchitectureModule]) -> List[List[str]]:
    """
    Detect circular dependencies using DFS with recursion stack.

    Returns a list of cycles, where each cycle is a list of module filenames.
    """
    # Build adjacency graph: module -> list of modules it depends on
    graph: Dict[str, Set[str]] = {}
    all_filenames: Set[str] = set()

    for module in modules:
        all_filenames.add(module.filename)
        graph[module.filename] = set(module.dependencies)

    cycles: List[List[str]] = []
    visited: Set[str] = set()
    rec_stack: Set[str] = set()

    def dfs(node: str, path: List[str]) -> None:
        """DFS to detect cycles."""
        if node in rec_stack:
            # Found cycle - extract the cycle from path
            try:
                cycle_start = path.index(node)
                cycle = path[cycle_start:] + [node]
                cycles.append(cycle)
            except ValueError:
                pass
            return

        if node in visited or node not in graph:
            return

        visited.add(node)
        rec_stack.add(node)
        path.append(node)

        for dep in graph.get(node, set()):
            if dep in all_filenames:  # Only follow edges to known modules
                dfs(dep, path)

        path.pop()
        rec_stack.remove(node)

    # Run DFS from each unvisited node
    for filename in all_filenames:
        if filename not in visited:
            dfs(filename, [])

    return cycles


def _validate_architecture(modules: List[ArchitectureModule]) -> ValidationResult:
    """Validate architecture and return errors and warnings."""
    errors: List[ValidationError] = []
    warnings: List[ValidationWarning] = []

    # Build set of all filenames
    all_filenames = {m.filename for m in modules}

    # Check for circular dependencies
    cycles = _detect_circular_dependencies(modules)
    for cycle in cycles:
        errors.append(
            ValidationError(
                type="circular_dependency",
                message=f"Circular dependency detected: {' -> '.join(cycle)}",
                modules=cycle,
            )
        )

    # Check for missing dependencies
    for module in modules:
        for dep in module.dependencies:
            if dep not in all_filenames:
                errors.append(
                    ValidationError(
                        type="missing_dependency",
                        message=f"Module '{module.filename}' depends on "
                        f"non-existent module '{dep}'",
                        modules=[module.filename, dep],
                    )
                )

    # Check for invalid/missing required fields
    for module in modules:
        if not module.filename or not module.filename.strip():
            errors.append(
                ValidationError(
                    type="invalid_field",
                    message="Module has empty filename",
                    modules=[module.filename or "(unnamed)"],
                )
            )
        if not module.filepath or not module.filepath.strip():
            errors.append(
                ValidationError(
                    type="invalid_field",
                    message=f"Module '{module.filename}' has empty filepath",
                    modules=[module.filename],
                )
            )
        if not module.description or not module.description.strip():
            errors.append(
                ValidationError(
                    type="invalid_field",
                    message=f"Module '{module.filename}' has empty description",
                    modules=[module.filename],
                )
            )

    # Check for duplicate dependencies (warning)
    for module in modules:
        if len(module.dependencies) != len(set(module.dependencies)):
            # Find the duplicates
            seen: Set[str] = set()
            duplicates: List[str] = []
            for dep in module.dependencies:
                if dep in seen:
                    duplicates.append(dep)
                seen.add(dep)
            warnings.append(
                ValidationWarning(
                    type="duplicate_dependency",
                    message=f"Module '{module.filename}' has duplicate dependencies: "
                    f"{', '.join(duplicates)}",
                    modules=[module.filename],
                )
            )

    # Check for orphan modules (warning)
    # Build set of modules that are depended upon
    depended_upon: Set[str] = set()
    for module in modules:
        depended_upon.update(module.dependencies)

    for module in modules:
        if not module.dependencies and module.filename not in depended_upon:
            warnings.append(
                ValidationWarning(
                    type="orphan_module",
                    message=f"Module '{module.filename}' has no dependencies "
                    f"and is not depended upon by any other module",
                    modules=[module.filename],
                )
            )

    return ValidationResult(
        valid=len(errors) == 0,
        errors=errors,
        warnings=warnings,
    )


@router.post("/validate", response_model=ValidationResult)
async def validate_architecture(request: ValidateArchitectureRequest) -> ValidationResult:
    """
    Validate architecture for structural issues.

    Checks for:
    - Circular dependencies (error)
    - Missing dependencies (error)
    - Invalid/missing required fields (error)
    - Duplicate dependencies (warning)
    - Orphan modules (warning)

    Returns validation result with valid flag, errors, and warnings.
    Errors block saving (valid=False), warnings are informational (valid=True).
    """
    return _validate_architecture(request.modules)
