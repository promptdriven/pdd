"""
Include Resolver Module

This module is responsible for safely resolving file paths referenced in prompt files,
reading their content, and providing simple token estimation. It acts as a security
boundary by enforcing root directory constraints to prevent path traversal attacks.
"""

import os
from pathlib import Path
from typing import Union, List, Any
from dataclasses import dataclass, field
from src.backend.models.findings import Finding, Severity, Evidence

class PathSecurityError(Exception):
    """Raised when a resolved path attempts to traverse outside the security root."""
    pass

class FileLoadError(Exception):
    """Raised when a file cannot be read due to missing file, permissions, or encoding."""
    pass

@dataclass
class ResolutionResult:
    total_tokens: int = 0
    resolved_files: List[str] = field(default_factory=list)
    findings: List[Finding] = field(default_factory=list)

class IncludeResolver:
    """
    Handles the safe resolution and reading of files included in prompts.
    """

    def __init__(self, root_path: Union[str, Path] = None):
        """
        Initialize the resolver with a security root.

        Args:
            root_path: The directory that acts as the security boundary. 
                       Files outside this directory cannot be resolved.
                       Defaults to the current working directory.
        """
        if root_path is None:
            self.root_path = Path.cwd().resolve()
        else:
            self.root_path = Path(root_path).resolve()

    def resolve_path(self, file_path: str, base_dir: Union[str, Path]) -> Path:
        """
        Resolves a relative file path against a base directory and enforces security constraints.

        Args:
            file_path: The relative path string found in the include tag.
            base_dir: The directory of the file currently being processed.

        Returns:
            Path: The absolute, normalized path to the file.

        Raises:
            PathSecurityError: If the resolved path is outside the root_path.
        """
        base_path = Path(base_dir).resolve()
        
        # Combine and resolve to get the absolute path, removing .. components
        try:
            # We use os.path.join logic via pathlib to handle the join
            target_path = (base_path / file_path).resolve()
        except RuntimeError:
            # Can happen with infinite loops in symlinks, though rare
            raise PathSecurityError(f"Could not resolve path: {file_path}")

        # Security Check: Ensure target_path starts with root_path
        # is_relative_to is available in Python 3.9+. 
        # For broader compatibility, we can check common path prefix.
        try:
            target_path.relative_to(self.root_path)
        except ValueError:
            raise PathSecurityError(
                f"Security violation: Attempted to access '{target_path}' "
                f"which is outside the security root '{self.root_path}'."
            )

        return target_path

    def read_content(self, file_path: Union[str, Path]) -> str:
        """
        Safely opens and reads the content of a file.

        Args:
            file_path: The absolute path to the file (usually obtained via self.resolve).

        Returns:
            str: The content of the file.

        Raises:
            FileLoadError: If the file is missing, unreadable, or has encoding issues.
        """
        path_obj = Path(file_path)

        if not path_obj.exists():
            raise FileLoadError(f"File not found: {path_obj}")
        
        if not path_obj.is_file():
            raise FileLoadError(f"Path is not a file: {path_obj}")

        try:
            # Defaulting to utf-8, but handling errors gracefully
            with open(path_obj, 'r', encoding='utf-8', errors='replace') as f:
                return f.read()
        except PermissionError:
            raise FileLoadError(f"Permission denied: {path_obj}")
        except OSError as e:
            raise FileLoadError(f"OS Error reading file {path_obj}: {str(e)}")
        except Exception as e:
            raise FileLoadError(f"Unexpected error reading {path_obj}: {str(e)}")

    @staticmethod
    def estimate_tokens(text: str) -> int:
        """
        Estimates the number of tokens in a string using a simple heuristic.
        
        Heuristic: len(text) / 4.
        
        Args:
            text: The string to estimate.

        Returns:
            int: The estimated token count.
        """
        if not text:
            return 0
        return int(len(text) / 4)

    def resolve(self, parsed_prompt: Any, base_path: str) -> ResolutionResult:
        """
        Resolves includes in a parsed prompt.
        """
        result = ResolutionResult()
        # Handle base_path: if it's a file, get parent dir
        path_obj = Path(base_path)
        base_dir = path_obj.parent if path_obj.suffix or path_obj.is_file() else path_obj
        
        if not hasattr(parsed_prompt, 'tags'):
            return result

        for tag in parsed_prompt.tags:
            if tag.name == 'include':
                file_ref = tag.content.strip()
                try:
                    target = self.resolve_path(file_ref, base_dir)
                    content = self.read_content(target)
                    tokens = self.estimate_tokens(content)
                    result.total_tokens += tokens
                    result.resolved_files.append(str(target))
                except (PathSecurityError, FileLoadError) as e:
                    result.findings.append(Finding(
                        rule_id="include_error",
                        severity=Severity.ERROR,
                        title="Include Resolution Failed",
                        message=str(e),
                        evidence=Evidence(line_start=tag.start_line, line_end=tag.end_line)
                    ))
        return result
