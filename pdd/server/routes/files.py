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
) -> Optional[FileTreeNode]:
    """Recursively build a file tree structure."""
    relative_path = path.relative_to(project_root)

    # Handle broken symlinks - use lstat to not follow symlinks
    try:
        stat_info = path.stat()
    except (FileNotFoundError, OSError):
        # Broken symlink or inaccessible file - skip it
        return None

    if path.is_dir():
        children = None
        if current_depth < depth:
            try:
                entries = sorted(path.iterdir(), key=lambda p: (not p.is_dir(), p.name.lower()))
                children = [
                    node for node in (
                        _build_file_tree(entry, project_root, depth, current_depth + 1)
                        for entry in entries
                        if not entry.name.startswith(".")  # Skip hidden files
                    )
                    if node is not None  # Skip broken symlinks
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


# Known language suffixes for prompt files (e.g., "calculator_python.prompt")
# IMPORTANT: Sorted by length (longest first) so more specific suffixes match before shorter ones
# (e.g., "typescriptreact" must match before "typescript", "javascript" before "java")
# This list covers languages from data/language_format.csv.
# Users can add custom languages to the CSV; they'll be detected via the _is_known_language fallback.
KNOWN_LANGUAGES = sorted([
    # Core languages
    "python", "typescriptreact", "javascriptreact", "typescript", "javascript",
    "java", "go", "rust", "cpp", "c", "csharp", "ruby", "swift", "kotlin",
    # Scripting & systems
    "php", "scala", "perl", "bash", "shell", "powershell", "lua",
    "haskell", "dart", "elixir", "clojure", "julia", "erlang",
    "fortran", "nim", "ocaml", "groovy", "coffeescript", "r",
    "zig", "mojo", "solidity",
    # Frontend / templating
    "svelte", "vue", "scss", "sass", "less",
    "jinja", "handlebars", "pug", "ejs", "twig",
    # Data / config / query
    "sql", "graphql", "protobuf", "terraform", "hcl",
    "html", "css", "makefile", "prisma", "lean", "nix",
    "glsl", "wgsl", "starlark", "dockerfile",
], key=len, reverse=True)

# Map language to file extensions
LANGUAGE_EXTENSIONS = {
    "python": [".py"],
    "typescript": [".ts", ".tsx"],
    "typescriptreact": [".tsx"],
    "javascript": [".js", ".jsx"],
    "javascriptreact": [".jsx"],
    "java": [".java"],
    "go": [".go"],
    "rust": [".rs"],
    "cpp": [".cpp", ".cc", ".cxx"],
    "c": [".c"],
    "csharp": [".cs"],
    "ruby": [".rb"],
    "swift": [".swift"],
    "kotlin": [".kt"],
    "php": [".php"],
    "scala": [".scala"],
    "perl": [".pl"],
    "lua": [".lua"],
    "haskell": [".hs"],
    "dart": [".dart"],
    "elixir": [".ex", ".exs"],
    "clojure": [".clj"],
    "julia": [".jl"],
    "erlang": [".erl"],
    "nim": [".nim"],
    "ocaml": [".ml"],
    "groovy": [".groovy"],
    "prisma": [".prisma"],
    "lean": [".lean"],
    "zig": [".zig"],
    "mojo": [".mojo"],
    "solidity": [".sol"],
    "svelte": [".svelte"],
    "vue": [".vue"],
    "scss": [".scss"],
    "sass": [".sass"],
    "less": [".less"],
    "jinja": [".jinja2", ".jinja", ".j2"],
    "handlebars": [".hbs", ".handlebars"],
    "pug": [".pug"],
    "ejs": [".ejs"],
    "twig": [".twig"],
    "graphql": [".graphql", ".gql"],
    "protobuf": [".proto"],
    "terraform": [".tf"],
    "hcl": [".hcl"],
    "nix": [".nix"],
    "glsl": [".glsl"],
    "wgsl": [".wgsl"],
    "starlark": [".bzl"],
    "dockerfile": [".dockerfile", "Dockerfile"],
    # Web languages
    "html": [".html", ".htm"],
    "css": [".css"],
    "makefile": ["Makefile", ".mk"],
}


def load_pddrc(project_root: Path) -> dict:
    """
    Load .pddrc configuration file if it exists.

    Returns parsed YAML config or empty dict.
    """
    import fnmatch
    pddrc_path = project_root / ".pddrc"
    if not pddrc_path.exists():
        return {}

    try:
        import yaml
        with open(pddrc_path) as f:
            return yaml.safe_load(f) or {}
    except Exception:
        return {}


def match_context(prompt_path: str, pddrc: dict) -> tuple:
    """
    Match a prompt path to a context in .pddrc and return context name and defaults.

    Args:
        prompt_path: Relative path to prompt file (e.g., "prompts/calculator_python.prompt")
        pddrc: Parsed .pddrc configuration

    Returns:
        Tuple of (context_name, defaults_dict)
    """
    import fnmatch

    contexts = pddrc.get("contexts", {})

    # Try each context in order (order matters for matching)
    for context_name, context_config in contexts.items():
        paths = context_config.get("paths", [])
        defaults = context_config.get("defaults", {})

        for pattern in paths:
            if fnmatch.fnmatch(prompt_path, pattern):
                return context_name, defaults

    # Return default context if exists, otherwise empty
    default_context = contexts.get("default", {})
    return "default", default_context.get("defaults", {})


def parse_prompt_stem(stem: str) -> tuple:
    """
    Parse sync_basename and language from prompt stem.

    Case-insensitive language matching to handle both:
    - "calculator_python" -> ("calculator", "python")
    - "calculator_Python" -> ("calculator", "python")
    - "simple_math_TypeScript" -> ("simple_math", "typescript")
    - "ui_components_TypeScriptReact" -> ("ui_components", "typescriptreact")
    - "unknown" -> ("unknown", None)

    Uses KNOWN_LANGUAGES (sorted longest-first) for matching, with a fallback
    to _is_known_language() which checks the language_format.csv for custom languages.
    """
    stem_lower = stem.lower()
    # Primary: check against hardcoded list (sorted longest-first for correct matching)
    for lang in KNOWN_LANGUAGES:
        suffix = f"_{lang}"
        if stem_lower.endswith(suffix):
            # Return the basename portion and normalized lowercase language
            return stem[:-len(suffix)], lang

    # Fallback: try CSV-based language detection for languages not in hardcoded list
    if "_" in stem:
        parts = stem_lower.split("_")
        # Try progressively longer suffixes (from right) to find a known language
        # e.g., for "my_app_newlang": try "newlang", then "app_newlang"
        for i in range(len(parts) - 1, 0, -1):
            candidate = "_".join(parts[i:])
            try:
                from ...construct_paths import _is_known_language
                if _is_known_language(candidate):
                    return stem[:-(len(candidate) + 1)], candidate
            except (ImportError, Exception):
                break

    return stem, None


@router.get("/prompts")
async def list_prompt_files(
    validator: PathValidator = Depends(get_path_validator),
):
    """
    List all .prompt files in the project.

    Returns a list of prompt files with their related dev-unit files
    (code, tests, examples) if they exist.

    Uses .pddrc configuration if available to determine correct paths.

    Each result includes:
    - prompt: Full path to .prompt file
    - sync_basename: Basename for sync command (without language suffix)
    - language: Detected language (e.g., "python")
    - code, test, example: Paths to related files if they exist
    """
    project_root = validator.project_root
    prompts_dir = project_root / "prompts"

    # Load .pddrc for context-specific paths
    pddrc = load_pddrc(project_root)

    results = []

    # Find all .prompt files using set to avoid duplicates
    prompt_files = set()

    # 1. prompts/ directory (recursive)
    if prompts_dir.exists():
        prompt_files.update(prompts_dir.rglob("*.prompt"))

    # 2. Project root
    prompt_files.update(project_root.glob("*.prompt"))

    # 3. Check prompts_dir from contexts
    for context_name, context_config in pddrc.get("contexts", {}).items():
        defaults = context_config.get("defaults", {})
        custom_prompts_dir = defaults.get("prompts_dir")
        if custom_prompts_dir:
            custom_path = project_root / custom_prompts_dir
            if custom_path.exists():
                prompt_files.update(custom_path.rglob("*.prompt"))

    for prompt_path in sorted(prompt_files):
        relative_path = str(prompt_path.relative_to(project_root))
        full_stem = prompt_path.stem  # e.g., "calculator_python"

        # Parse language suffix to get sync_basename
        sync_basename, language = parse_prompt_stem(full_stem)  # e.g., ("calculator", "python")

        # Get context-specific paths from .pddrc
        context_name, context_defaults = match_context(relative_path, pddrc)

        # Extract subdirectory structure from prompt path
        # e.g., "prompts/server/click_executor_python.prompt" -> "server"
        prompt_subdir = ""
        prompts_base = context_defaults.get("prompts_dir", "prompts")
        # Check if prompt is under the prompts base directory
        if relative_path.startswith(prompts_base + "/"):
            # Get path after prompts base, excluding the filename
            after_base = relative_path[len(prompts_base) + 1:]
            if "/" in after_base:
                prompt_subdir = "/".join(after_base.split("/")[:-1])
        elif "/" in relative_path:
            # For prompts not in a prompts/ directory, check if there's a subdirectory
            # e.g., "server/click_executor_python.prompt" -> "server"
            parts = relative_path.split("/")
            if len(parts) > 1:
                prompt_subdir = "/".join(parts[:-1])

        # Get file extensions for this language
        extensions = LANGUAGE_EXTENSIONS.get(language, [".py", ".ts", ".js", ".java"]) if language else [".py", ".ts", ".tsx", ".js", ".jsx", ".java"]

        # Try to find related files (code, test, example)
        # Include prompt_subdir in sync_basename so pdd sync can find the correct prompt
        # when there are multiple prompts with the same name in different subdirectories
        full_sync_basename = f"{prompt_subdir}/{sync_basename}" if prompt_subdir else sync_basename
        related = {
            "prompt": relative_path,
            "sync_basename": full_sync_basename,  # For sync command: "frontend/app/admin/page"
            "language": language,            # Detected language: "python"
            "context": context_name,         # Matched .pddrc context name
        }

        # Helper to substitute placeholders in path templates
        def substitute_path_template(template: str) -> str:
            """Replace {name} and {language} placeholders in path template."""
            result = template.replace("{name}", sync_basename)
            if language:
                result = result.replace("{language}", language)
            return result

        # ===== CODE FILE DETECTION =====
        # Use outputs.code.path or generate_output_path from .pddrc if available
        code_dirs = []
        explicit_code_path = None

        # Priority 0: Check new 'outputs' format (Issue #237)
        # Format: outputs: { code: { path: "app/layout.tsx" } }
        outputs_config = context_defaults.get("outputs", {})
        if outputs_config and isinstance(outputs_config, dict):
            code_output = outputs_config.get("code", {})
            if code_output and isinstance(code_output, dict):
                explicit_code_path = code_output.get("path")

        # If explicit path is set, substitute placeholders and check it directly
        if explicit_code_path:
            resolved_code_path = substitute_path_template(explicit_code_path)
            code_path = project_root / resolved_code_path
            if code_path.exists():
                related["code"] = str(code_path.relative_to(project_root))

        # Priority 1: .pddrc generate_output_path (legacy format)
        if "code" not in related:
            pddrc_code_dir = context_defaults.get("generate_output_path")
            if pddrc_code_dir:
                # Strip trailing slash
                pddrc_code_dir = pddrc_code_dir.rstrip("/")
                code_dirs.append(pddrc_code_dir)

            # Priority 2: Default locations
            code_dirs.extend(["src", ""])  # Empty string for project root

            for code_dir in code_dirs:
                for ext in extensions:
                    # Try with subdirectory first, then without
                    paths_to_try = []
                    if code_dir:
                        if prompt_subdir:
                            paths_to_try.append(project_root / code_dir / prompt_subdir / f"{sync_basename}{ext}")
                        paths_to_try.append(project_root / code_dir / f"{sync_basename}{ext}")
                    else:
                        if prompt_subdir:
                            paths_to_try.append(project_root / prompt_subdir / f"{sync_basename}{ext}")
                        paths_to_try.append(project_root / f"{sync_basename}{ext}")

                    for code_path in paths_to_try:
                        if code_path.exists():
                            related["code"] = str(code_path.relative_to(project_root))
                            break
                    if "code" in related:
                        break
                if "code" in related:
                    break

        # ===== TEST FILE DETECTION =====
        # Use outputs.test.path or test_output_path from .pddrc if available
        test_dirs = []
        explicit_test_path = None

        # Check new 'outputs' format first (Issue #237)
        if outputs_config and isinstance(outputs_config, dict):
            test_output = outputs_config.get("test", {})
            if test_output and isinstance(test_output, dict):
                explicit_test_path = test_output.get("path")

        # If explicit path is set, substitute placeholders and check it directly
        if explicit_test_path:
            resolved_test_path = substitute_path_template(explicit_test_path)
            test_path = project_root / resolved_test_path
            if test_path.exists():
                related["test"] = str(test_path.relative_to(project_root))

        # Legacy format: test_output_path
        if "test" not in related:
            pddrc_test_dir = context_defaults.get("test_output_path")
            if pddrc_test_dir:
                pddrc_test_dir = pddrc_test_dir.rstrip("/")
                test_dirs.append(pddrc_test_dir)

            test_dirs.extend(["tests", "test", ""])  # Empty string for project root
            test_prefixes = ["test_", ""]
            # Include .test and .spec suffixes common in Jest/TypeScript projects
            test_suffixes = [".test", ".spec", "", "_test"]

            # For non-executable languages (schema/config), tests are usually in Python/TS
            # These languages don't have native test frameworks, so tests are written in
            # general-purpose languages like Python or TypeScript
            NON_EXECUTABLE_LANGUAGES = {
                "prisma", "sql", "graphql", "protobuf", "terraform", "hcl",
                "html", "css", "makefile", "dockerfile", "nix", "starlark",
                "glsl", "wgsl", "scss", "sass", "less", "pug", "ejs", "twig",
                "handlebars", "jinja",
            }

            # Determine test file extensions to search
            if language and language.lower() in NON_EXECUTABLE_LANGUAGES:
                # For config/schema languages, search for Python and TypeScript test files
                test_extensions = [".py", ".ts", ".tsx", ".js", ".jsx"]
            else:
                # For executable languages, use language-specific extensions first,
                # then add Python/TypeScript as fallbacks
                test_extensions = list(extensions) + [".py", ".ts"]
                # Dedupe while preserving order
                test_extensions = list(dict.fromkeys(test_extensions))

            for test_dir in test_dirs:
                found = False
                for prefix in test_prefixes:
                    for suffix in test_suffixes:
                        # Skip invalid combination (no prefix and no suffix with just basename)
                        if not prefix and not suffix:
                            continue
                        for ext in test_extensions:
                            test_name = f"{prefix}{sync_basename}{suffix}{ext}"
                            # Try with subdirectory first, then without
                            paths_to_try = []
                            if test_dir:
                                if prompt_subdir:
                                    paths_to_try.append(project_root / test_dir / prompt_subdir / test_name)
                                paths_to_try.append(project_root / test_dir / test_name)
                            else:
                                if prompt_subdir:
                                    paths_to_try.append(project_root / prompt_subdir / test_name)
                                paths_to_try.append(project_root / test_name)

                            for test_path in paths_to_try:
                                if test_path.exists():
                                    related["test"] = str(test_path.relative_to(project_root))
                                    found = True
                                    break
                            if found:
                                break
                        if found:
                            break
                    if found:
                        break
                if found:
                    break

        # ===== EXAMPLE FILE DETECTION =====
        # Use outputs.example.path or example_output_path from .pddrc if available
        example_dirs = []
        explicit_example_path = None

        # Check new 'outputs' format first (Issue #237)
        if outputs_config and isinstance(outputs_config, dict):
            example_output = outputs_config.get("example", {})
            if example_output and isinstance(example_output, dict):
                explicit_example_path = example_output.get("path")

        # If explicit path is set, substitute placeholders and check it directly
        if explicit_example_path:
            resolved_example_path = substitute_path_template(explicit_example_path)
            example_path = project_root / resolved_example_path
            if example_path.exists():
                related["example"] = str(example_path.relative_to(project_root))

        # Legacy format: example_output_path
        if "example" not in related:
            pddrc_example_dir = context_defaults.get("example_output_path")
            if pddrc_example_dir:
                pddrc_example_dir = pddrc_example_dir.rstrip("/")
                example_dirs.append(pddrc_example_dir)

            example_dirs.extend(["examples", ""])  # Empty string for project root

            for example_dir in example_dirs:
                for ext in extensions:
                    example_name = f"{sync_basename}_example{ext}"
                    # Try with subdirectory first, then without
                    paths_to_try = []
                    if example_dir:
                        if prompt_subdir:
                            paths_to_try.append(project_root / example_dir / prompt_subdir / example_name)
                        paths_to_try.append(project_root / example_dir / example_name)
                    else:
                        if prompt_subdir:
                            paths_to_try.append(project_root / prompt_subdir / example_name)
                        paths_to_try.append(project_root / example_name)

                    for example_path in paths_to_try:
                        if example_path.exists():
                            related["example"] = str(example_path.relative_to(project_root))
                            break
                    if "example" in related:
                        break
                if "example" in related:
                    break

        results.append(related)

    return results


@router.get("/prompts/changed")
async def list_changed_prompt_files(
    base_branch: Annotated[str, Query(description="Base branch to compare against")] = "main",
    validator: PathValidator = Depends(get_path_validator),
):
    """
    List prompt files that have been changed on the current branch compared to base.

    Uses git diff to find .prompt files that are new or modified.

    Returns:
        List of changed prompt file paths (relative to project root)
    """
    import subprocess

    project_root = validator.project_root

    try:
        # Get the merge-base between current branch and base branch
        merge_base_result = subprocess.run(
            ["git", "merge-base", "HEAD", base_branch],
            cwd=project_root,
            capture_output=True,
            text=True,
        )

        if merge_base_result.returncode != 0:
            # If merge-base fails (e.g., no common ancestor), compare directly
            merge_base = base_branch
        else:
            merge_base = merge_base_result.stdout.strip()

        # Get list of changed files (including added, modified)
        diff_result = subprocess.run(
            ["git", "diff", "--name-only", "--diff-filter=ACMR", merge_base, "HEAD"],
            cwd=project_root,
            capture_output=True,
            text=True,
        )

        if diff_result.returncode != 0:
            raise HTTPException(
                status_code=500,
                detail=f"Failed to get git diff: {diff_result.stderr}"
            )

        # Also get staged and unstaged changes (for uncommitted work)
        status_result = subprocess.run(
            ["git", "status", "--porcelain"],
            cwd=project_root,
            capture_output=True,
            text=True,
        )

        changed_files = set()

        # Parse committed changes
        for line in diff_result.stdout.strip().split("\n"):
            if line and line.endswith(".prompt"):
                changed_files.add(line)

        # Parse uncommitted changes (staged and unstaged)
        if status_result.returncode == 0:
            for line in status_result.stdout.strip().split("\n"):
                if line and len(line) > 3:
                    # Format: XY filename (X=staged, Y=unstaged)
                    file_path = line[3:].strip()
                    # Handle renamed files (format: "old -> new")
                    if " -> " in file_path:
                        file_path = file_path.split(" -> ")[1]
                    if file_path.endswith(".prompt"):
                        changed_files.add(file_path)

        return {"changed_prompts": sorted(changed_files), "base_branch": base_branch}

    except FileNotFoundError:
        raise HTTPException(
            status_code=500,
            detail="Git is not installed or not in PATH"
        )
    except Exception as e:
        raise HTTPException(
            status_code=500,
            detail=f"Error getting changed prompts: {str(e)}"
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