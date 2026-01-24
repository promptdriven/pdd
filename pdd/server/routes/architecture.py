"""
REST API endpoints for architecture.json validation and sync operations.

Provides endpoints for:
- Validating architecture changes before saving
- Detecting circular dependencies, missing references, and structural issues
- Syncing architecture.json from prompt file metadata tags
- Generating architecture from a GitHub issue URL
"""

from __future__ import annotations

import re
import json
from pathlib import Path
from typing import Any, Dict, List, Optional, Set

from fastapi import APIRouter
from pydantic import BaseModel, Field

from pdd.architecture_sync import (
    ARCHITECTURE_JSON_PATH,
    sync_all_prompts_to_architecture,
    update_architecture_from_prompt,
    get_architecture_entry_for_prompt,
    generate_tags_from_architecture,
    has_pdd_tags,
)


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


class SyncRequest(BaseModel):
    """Request body for sync-from-prompts operation."""

    filenames: Optional[List[str]] = None  # None = sync all prompts
    dry_run: bool = False


class SyncResult(BaseModel):
    """Result of sync-from-prompts operation."""

    success: bool
    updated_count: int
    skipped_count: int = 0
    results: List[Dict[str, Any]]
    validation: ValidationResult
    errors: List[str] = Field(default_factory=list)


class GenerateTagsRequest(BaseModel):
    """Request body for generate-tags-for-prompt operation."""

    prompt_filename: str  # e.g., "llm_invoke_python.prompt"


class GenerateTagsResult(BaseModel):
    """Result of generate-tags-for-prompt operation."""

    success: bool
    tags: Optional[str] = None  # Generated XML tags or None if not found
    has_existing_tags: bool = False  # True if prompt already has PDD tags
    architecture_entry: Optional[Dict[str, Any]] = None  # The full architecture entry
    error: Optional[str] = None


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


@router.post("/sync-from-prompts", response_model=SyncResult)
async def sync_from_prompts(request: SyncRequest) -> SyncResult:
    """
    Sync architecture.json from prompt file metadata tags.

    This endpoint reads PDD metadata tags (<pdd-reason>, <pdd-interface>,
    <pdd-dependency>) from prompt files and updates the corresponding entries
    in architecture.json.

    Prompts are the source of truth - tags in prompts override architecture.json.
    Validation is lenient - missing tags are OK, only updates fields with tags.

    Request body:
        {
            "filenames": ["llm_invoke_python.prompt", ...] | null,
            "dry_run": false
        }

    If filenames is null, syncs ALL prompt files.
    If dry_run is true, validates changes without writing.

    Returns:
        {
            "success": bool,  // True if no errors and validation passed
            "updated_count": int,  // Number of modules updated
            "skipped_count": int,  // Number of modules skipped (no prompt file)
            "results": [
                {
                    "filename": "...",
                    "success": bool,
                    "updated": bool,
                    "changes": {"reason": {"old": ..., "new": ...}, ...}
                },
                ...
            ],
            "validation": {
                "valid": bool,
                "errors": [...],  // Circular deps, missing deps, etc.
                "warnings": [...]  // Duplicates, orphans, etc.
            },
            "errors": [str, ...]  // Sync operation errors
        }
    """
    try:
        # Perform sync operation
        if request.filenames is None:
            # Sync all prompts
            sync_result = sync_all_prompts_to_architecture(dry_run=request.dry_run)
        else:
            # Sync specific prompts
            results = []
            updated_count = 0
            errors_list = []

            for filename in request.filenames:
                result = update_architecture_from_prompt(filename, dry_run=request.dry_run)
                results.append({
                    'filename': filename,
                    'success': result['success'],
                    'updated': result['updated'],
                    'changes': result['changes'],
                    'error': result.get('error')
                })

                if result['success'] and result['updated']:
                    updated_count += 1
                elif not result['success']:
                    errors_list.append(f"{filename}: {result['error']}")

            sync_result = {
                'success': len(errors_list) == 0,
                'updated_count': updated_count,
                'skipped_count': 0,
                'results': results,
                'errors': errors_list
            }

        # Load updated architecture and validate
        arch_path = Path(ARCHITECTURE_JSON_PATH)
        arch_data = json.loads(arch_path.read_text(encoding='utf-8'))
        modules = [ArchitectureModule(**mod) for mod in arch_data]
        validation_result = _validate_architecture(modules)

        # Overall success: sync succeeded AND validation passed
        overall_success = sync_result['success'] and validation_result.valid

        return SyncResult(
            success=overall_success,
            updated_count=sync_result['updated_count'],
            skipped_count=sync_result.get('skipped_count', 0),
            results=sync_result['results'],
            validation=validation_result,
            errors=sync_result.get('errors', [])
        )

    except Exception as e:
        # Return error result
        return SyncResult(
            success=False,
            updated_count=0,
            skipped_count=0,
            results=[],
            validation=ValidationResult(valid=True, errors=[], warnings=[]),
            errors=[f"Unexpected error: {str(e)}"]
        )


@router.post("/generate-tags-for-prompt", response_model=GenerateTagsResult)
async def generate_tags_for_prompt(request: GenerateTagsRequest) -> GenerateTagsResult:
    """
    Generate PDD metadata tags for a prompt from architecture.json.

    This is the reverse direction of sync-from-prompts: it reads the architecture.json
    entry for a prompt and generates XML tags (<pdd-reason>, <pdd-interface>,
    <pdd-dependency>) that can be injected into the prompt file.

    Request body:
        {
            "prompt_filename": "llm_invoke_python.prompt"
        }

    Returns:
        {
            "success": bool,
            "tags": "<pdd-reason>...</pdd-reason>\\n<pdd-interface>...</pdd-interface>\\n...",
            "has_existing_tags": false,  // True if prompt already has PDD tags
            "architecture_entry": {...},  // The full architecture entry (for preview)
            "error": "Error message if failed"
        }
    """
    try:
        # Get architecture entry for this prompt
        entry = get_architecture_entry_for_prompt(request.prompt_filename)

        if entry is None:
            return GenerateTagsResult(
                success=False,
                tags=None,
                has_existing_tags=False,
                architecture_entry=None,
                error=f"No architecture entry found for '{request.prompt_filename}'"
            )

        # Check if the prompt file already has PDD tags
        prompts_dir = Path.cwd() / "prompts"
        prompt_path = prompts_dir / request.prompt_filename
        existing_tags = False

        if prompt_path.exists():
            prompt_content = prompt_path.read_text(encoding='utf-8')
            existing_tags = has_pdd_tags(prompt_content)

        # Generate tags from architecture entry
        tags = generate_tags_from_architecture(entry)

        return GenerateTagsResult(
            success=True,
            tags=tags if tags else None,
            has_existing_tags=existing_tags,
            architecture_entry=entry,
            error=None
        )

    except Exception as e:
        return GenerateTagsResult(
            success=False,
            tags=None,
            has_existing_tags=False,
            architecture_entry=None,
            error=f"Error generating tags: {str(e)}"
        )


# ============================================================================
# Generate Architecture from GitHub Issue
# ============================================================================

_GITHUB_ISSUE_RE = re.compile(
    r"(?:https?://)?(?:www\.)?github\.com/([^/]+)/([^/]+)/issues/(\d+)"
)


class GenerateFromIssueRequest(BaseModel):
    """Request body for generating architecture from a GitHub issue URL."""

    issue_url: str = Field(..., description="GitHub issue URL (e.g., https://github.com/owner/repo/issues/42)")
    verbose: bool = Field(False, description="Enable verbose output")
    quiet: bool = Field(False, description="Suppress non-error output")
    timeout_adder: float = Field(0.0, description="Additional seconds to add to each step's timeout")


class GenerateFromIssueResult(BaseModel):
    """Result of triggering architecture generation from a GitHub issue."""

    success: bool
    message: str
    job_id: Optional[str] = None


@router.post("/generate-from-issue", response_model=GenerateFromIssueResult)
async def generate_from_issue(request: GenerateFromIssueRequest) -> GenerateFromIssueResult:
    """
    Generate architecture from a GitHub issue URL.

    Validates the URL, then spawns `pdd generate <issue_url>` in a terminal
    window to run the agentic architecture workflow. The frontend can poll
    the spawned job status via /api/v1/commands/spawned-jobs/{job_id}/status.

    This mirrors how `pdd bug <url>` and `pdd change <url>` trigger their
    respective agentic workflows from the web interface.
    """
    # Validate URL format
    if not _GITHUB_ISSUE_RE.search(request.issue_url):
        return GenerateFromIssueResult(
            success=False,
            message=f"Invalid GitHub issue URL: {request.issue_url}",
            job_id=None,
        )

    try:
        from .commands import (
            _build_pdd_command_args,
            _spawned_jobs,
            get_project_root,
            get_server_port,
        )
        from ..terminal_spawner import TerminalSpawner
        import time
        import uuid

        project_root = get_project_root()
        server_port = get_server_port()

        # Build options dict
        options: Dict[str, Any] = {}
        if request.verbose:
            options["verbose"] = True
        if request.quiet:
            options["quiet"] = True

        # Build command args: pdd generate <issue_url>
        args = {"prompt_file": request.issue_url}
        cmd_args = _build_pdd_command_args("generate", args, options)
        cmd_str = " ".join(cmd_args)

        # Generate job ID
        job_id = f"spawned-{int(time.time() * 1000)}-{uuid.uuid4().hex[:8]}"

        # Track the job
        from datetime import datetime, timezone as tz
        _spawned_jobs[job_id] = {
            "job_id": job_id,
            "command": "generate",
            "status": "running",
            "started_at": datetime.now(tz.utc).isoformat(),
            "completed_at": None,
            "exit_code": None,
        }

        # Spawn terminal
        spawned = TerminalSpawner.spawn(
            cmd_str,
            working_dir=str(project_root),
            job_id=job_id,
            server_port=server_port,
        )

        if not spawned:
            del _spawned_jobs[job_id]
            return GenerateFromIssueResult(
                success=False,
                message="Failed to spawn terminal for architecture generation",
                job_id=None,
            )

        return GenerateFromIssueResult(
            success=True,
            message=f"Architecture generation started for {request.issue_url}",
            job_id=job_id,
        )

    except Exception as e:
        return GenerateFromIssueResult(
            success=False,
            message=f"Error starting architecture generation: {str(e)}",
            job_id=None,
        )
