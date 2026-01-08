"""
REST API endpoints for file operations.

Provides endpoints for browsing, reading, and writing files in the project
directory with proper security validation.
"""

from __future__ import annotations

import base64
import hashlib
from datetime import datetime
from pathlib import Path
from typing import Annotated, List, Literal, Optional

from fastapi import APIRouter, Depends, HTTPException, Query

try:
    from rich.console import Console
    console = Console()
except ImportError:
    class Console:
        def print(self, *args, **kwargs):
            import builtins
            builtins.print(*args)
    console = Console()

from ..models import FileContent, FileMetadata, FileTreeNode, WriteFileRequest, WriteResult
from ..security import PathValidator, SecurityError

# Binary file extensions
BINARY_EXTENSIONS = {
    ".png", ".jpg", ".jpeg", ".gif", ".bmp", ".ico", ".webp",
    ".pdf", ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx",
    ".zip", ".tar", ".gz", ".rar", ".7z",
    ".exe", ".dll", ".so", ".dylib",
    ".pyc", ".pyo", ".class",
    ".mp3", ".mp4", ".wav", ".avi", ".mov",
    ".ttf", ".otf", ".woff", ".woff2",
}

# Default chunk size for large files
DEFAULT_CHUNK_SIZE = 100000

router = APIRouter(prefix="/api/v1/files", tags=["files"])

# Dependency injection placeholder - will be overridden by app
_path_validator: Optional[PathValidator] = None


def get_path_validator() -> PathValidator:
    """Dependency to get the PathValidator instance."""
    if _path_validator is None:
        raise RuntimeError("PathValidator not configured")
    return _path_validator


def set_path_validator(validator: PathValidator) -> None:
    """Configure the PathValidator instance."""
    global _path_validator
    _path_validator = validator


def _is_binary_file(path: Path) -> bool:
    """Check if a file is binary based on extension or content."""
    if path.suffix.lower() in BINARY_EXTENSIONS:
        return True
    # Try reading first bytes to detect binary content
    try:
        with open(path, "rb") as f:
            chunk = f.read(8192)
            if b"\x00" in chunk:
                return True
    except Exception:
        pass
    return False


def _build_file_tree(
    path: Path,
    project_root: Path,
    depth: int,
    current_depth: int = 0
) -> FileTreeNode:
    """Recursively build a file tree structure."""
    relative_path = path.relative_to(project_root)
    stat_info = path.stat()

    if path.is_dir():
        children = None
        if current_depth < depth:
            try:
                entries = sorted(path.iterdir(), key=lambda p: (not p.is_dir(), p.name.lower()))
                children = [
                    _build_file_tree(entry, project_root, depth, current_depth + 1)
                    for entry in entries
                    if not entry.name.startswith(".")  # Skip hidden files
                ]
            except PermissionError:
                children = []

        return FileTreeNode(
            name=path.name,
            path=str(relative_path),
            type="directory",
            children=children,
            mtime=datetime.fromtimestamp(stat_info.st_mtime),
        )
    else:
        return FileTreeNode(
            name=path.name,
            path=str(relative_path),
            type="file",
            size=stat_info.st_size,
            mtime=datetime.fromtimestamp(stat_info.st_mtime),
        )


@router.get("/tree", response_model=FileTreeNode)
async def get_file_tree(
    path: Annotated[str, Query(description="Path relative to project root")] = "",
    depth: Annotated[int, Query(description="Maximum recursion depth", ge=1, le=10)] = 3,
    validator: PathValidator = Depends(get_path_validator),
):
    """
    Get directory structure as a tree.

    Returns metadata only, not file contents.
    """
    try:
        if path:
            abs_path = validator.validate(path)
        else:
            abs_path = validator.project_root

        if not abs_path.exists():
            raise HTTPException(status_code=404, detail=f"Path not found: {path}")

        if not abs_path.is_dir():
            raise HTTPException(status_code=400, detail=f"Not a directory: {path}")

        return _build_file_tree(abs_path, validator.project_root, depth)

    except SecurityError as e:
        raise HTTPException(status_code=403, detail=e.message)


@router.get("/content", response_model=FileContent)
async def get_file_content(
    path: Annotated[str, Query(description="File path relative to project root")],
    encoding: Annotated[Literal["utf-8", "base64"], Query(description="Content encoding")] = "utf-8",
    chunk: Annotated[Optional[int], Query(description="Chunk index for large files", ge=0)] = None,
    chunk_size: Annotated[int, Query(description="Chunk size in bytes")] = DEFAULT_CHUNK_SIZE,
    validator: PathValidator = Depends(get_path_validator),
):
    """
    Read file content.

    Binary files are returned as base64. Large files support chunked responses.
    Includes SHA-256 checksum for verification.
    """
    try:
        abs_path = validator.validate(path)

        if not abs_path.exists():
            raise HTTPException(status_code=404, detail=f"File not found: {path}")

        if abs_path.is_dir():
            raise HTTPException(status_code=400, detail=f"Cannot read directory: {path}")

        file_size = abs_path.stat().st_size
        is_binary = _is_binary_file(abs_path)

        # Determine encoding
        # If base64 is explicitly requested, treat as binary to ensure consistent return type
        treat_as_binary = is_binary or encoding == "base64"
        
        # Read file content
        content_bytes = b""
        sha256_hash = hashlib.sha256()

        # Always open in binary mode to support seeking and accurate byte chunking
        with open(abs_path, "rb") as f:
            if chunk is not None:
                f.seek(chunk * chunk_size)
                content_bytes = f.read(chunk_size)
            else:
                content_bytes = f.read()
        
        sha256_hash.update(content_bytes)

        if treat_as_binary:
            content = base64.b64encode(content_bytes).decode("ascii")
            actual_encoding = "base64"
        else:
            try:
                content = content_bytes.decode("utf-8")
                actual_encoding = "utf-8"
            except UnicodeDecodeError:
                # Fallback for binary content or split multi-byte characters in chunk
                content = base64.b64encode(content_bytes).decode("ascii")
                actual_encoding = "base64"
                # Update is_binary flag since we forced binary encoding
                is_binary = True

        # Calculate chunking info
        total_chunks = None
        chunk_index = None
        if chunk is not None:
            if chunk_size > 0:
                total_chunks = (file_size + chunk_size - 1) // chunk_size
            else:
                total_chunks = 1
            chunk_index = chunk

        return FileContent(
            path=path,
            content=content,
            encoding=actual_encoding,
            size=len(content_bytes),  # Size of the actual bytes returned
            is_binary=is_binary,
            chunk_index=chunk_index,
            total_chunks=total_chunks,
            checksum=sha256_hash.hexdigest(),
        )

    except SecurityError as e:
        raise HTTPException(status_code=403, detail=e.message)


@router.post("/write", response_model=WriteResult)
async def write_file(
    request: WriteFileRequest,
    validator: PathValidator = Depends(get_path_validator),
):
    """
    Write content to a file.

    Creates parent directories if needed.
    """
    try:
        abs_path = validator.validate(request.path)

        # Create parent directories if requested
        if request.create_parents:
            abs_path.parent.mkdir(parents=True, exist_ok=True)

        # Decode and write content
        if request.encoding == "base64":
            content_bytes = base64.b64decode(request.content)
            with open(abs_path, "wb") as f:
                f.write(content_bytes)
        else:
            with open(abs_path, "w", encoding="utf-8") as f:
                f.write(request.content)

        stat_info = abs_path.stat()
        return WriteResult(
            success=True,
            path=request.path,
            mtime=datetime.fromtimestamp(stat_info.st_mtime),
        )

    except SecurityError as e:
        raise HTTPException(status_code=403, detail=e.message)
    except Exception as e:
        return WriteResult(
            success=False,
            path=request.path,
            error=str(e),
        )


@router.get("/metadata", response_model=List[FileMetadata])
async def get_file_metadata(
    paths: Annotated[List[str], Query(description="List of paths to check")],
    validator: PathValidator = Depends(get_path_validator),
):
    """
    Get metadata for multiple files.

    Batch endpoint for checking file existence and properties.
    """
    results = []
    for path in paths:
        try:
            abs_path = validator.validate(path)
            if abs_path.exists():
                stat_info = abs_path.stat()
                results.append(FileMetadata(
                    path=path,
                    exists=True,
                    size=stat_info.st_size,
                    mtime=datetime.fromtimestamp(stat_info.st_mtime),
                    is_directory=abs_path.is_dir(),
                ))
            else:
                results.append(FileMetadata(path=path, exists=False))
        except SecurityError:
            results.append(FileMetadata(path=path, exists=False))

    return results