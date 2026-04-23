"""
REST API endpoints for architecture.json validation and sync operations.

Provides endpoints for:
- Validating architecture changes before saving
- Detecting circular dependencies, missing references, and structural issues
- Syncing architecture.json from prompt file metadata tags
- Generating architecture from a GitHub issue URL
"""

from __future__ import annotations

import asyncio
import re
import json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any, Dict, List, Optional

from fastapi import APIRouter
from pydantic import BaseModel, Field

from pdd.load_prompt_template import load_prompt_template
from pdd.agentic_common import run_agentic_task

from pdd.architecture_registry import extract_modules
from pdd.architecture_sync import (
    get_architecture_entry_for_prompt,
    generate_tags_from_architecture,
    has_pdd_tags,
    sync_prompts_to_architecture,
    validate_architecture_modules,
)


router = APIRouter(prefix="/api/v1/architecture", tags=["architecture"])

_rearrange_executor = ThreadPoolExecutor(max_workers=2)


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
    group: Optional[str] = None


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


class RearrangeRequest(BaseModel):
    """Request body for agentic graph layout rearrangement."""

    architecture_path: str = Field(
        "architecture.json",
        description="Path to the architecture file, relative to project root"
    )


class RearrangeResult(BaseModel):
    """Result of agentic graph rearrangement."""

    success: bool
    modules: Optional[List[Dict[str, Any]]] = None
    message: Optional[str] = None
    error: Optional[str] = None


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
    raw_result = validate_architecture_modules(
        [module.model_dump() for module in request.modules]
    )
    return ValidationResult(**raw_result)


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
        sync_result = sync_prompts_to_architecture(
            filenames=request.filenames,
            dry_run=request.dry_run,
        )
        return SyncResult(**sync_result)

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


# ============================================================================
# Agentic Graph Layout Rearrangement
# ============================================================================

@router.post("/rearrange", response_model=RearrangeResult)
async def rearrange_graph_layout(request: RearrangeRequest) -> RearrangeResult:
    """
    Use an agentic workflow to assign logical swimlane positions to all modules.

    Runs arrange_graph_layout_LLM.prompt via run_agentic_task. The agent reads
    the specified architecture file and any PRD from the project root, reasons
    about the architecture's logical structure, assigns swimlane positions,
    and writes the updated file in-place. Returns the updated modules array.
    """
    try:
        from .commands import get_project_root
        project_root = get_project_root()

        arch_path = project_root / request.architecture_path
        if not arch_path.exists():
            return RearrangeResult(
                success=False,
                error=f"{request.architecture_path} not found"
            )

        # Snapshot the original file so we can restore it after the LLM runs.
        # Re-arrange is treated as an in-memory-only operation: positions are
        # returned to the frontend but the file on disk is kept as-is.  The
        # user must explicitly click Save to persist them.  This ensures that
        # clicking Discard truly reverts everything, including the on-disk file.
        original_content = arch_path.read_text(encoding="utf-8")

        template = load_prompt_template("arrange_graph_layout_LLM")
        # Use str.replace instead of .format() to avoid escaping issues with
        # any literal {} characters in the prompt body.
        instruction = (template
            .replace("{project_root}", str(project_root))
            .replace("{architecture_path}", str(arch_path))
        )

        loop = asyncio.get_running_loop()
        success, output, cost_usd, provider = await loop.run_in_executor(
            _rearrange_executor,
            lambda: run_agentic_task(
                instruction=instruction,
                cwd=project_root,
                label="arrange_graph_layout",
            )
        )

        if not success:
            return RearrangeResult(success=False, error=f"Agent failed: {output[:500]}")

        updated_content = arch_path.read_text(encoding="utf-8")
        updated_modules = extract_modules(json.loads(updated_content))
        if not updated_modules:
            return RearrangeResult(
                success=False,
                error="Updated architecture file contains no valid modules"
            )

        # Restore original file — positions live in the frontend state only
        # until the user explicitly saves them.
        arch_path.write_text(original_content, encoding="utf-8")

        return RearrangeResult(
            success=True,
            modules=updated_modules,
            message=output.strip(),
        )

    except json.JSONDecodeError as e:
        return RearrangeResult(
            success=False,
            error=f"Updated architecture file has invalid JSON: {str(e)}"
        )
    except Exception as e:
        return RearrangeResult(success=False, error=f"Rearrange failed: {str(e)}")
