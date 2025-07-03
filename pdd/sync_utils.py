"""
sync_utils.py
~~~~~~~~~~~~

Defensive file operation utilities for sync operations.
Provides safe file reading and existence checking with proper error handling.
"""

from pathlib import Path
from typing import Optional, Tuple
from rich.console import Console

console = Console()


def safe_read_file(file_path: Path, context: str = "") -> Tuple[bool, Optional[str]]:
    """
    Safely read a file with proper error handling.
    
    Args:
        file_path: Path to the file to read
        context: Context description for error messages
    
    Returns:
        Tuple of (success: bool, content: Optional[str])
    """
    try:
        if not file_path.exists():
            return False, None
        
        content = file_path.read_text(encoding='utf-8', errors='ignore')
        return True, content
        
    except Exception as e:
        console.print(f"[red]Error reading {context} file {file_path}: {e}[/red]")
        return False, None


def ensure_file_exists_for_operation(file_path: Path, operation: str) -> bool:
    """
    Ensure a file exists before attempting an operation on it.
    
    Args:
        file_path: Path to the file that should exist
        operation: Description of the operation being attempted
    
    Returns:
        True if file exists, False otherwise
    """
    if not file_path.exists():
        console.print(f"[red]Cannot perform {operation}: file {file_path} does not exist[/red]")
        return False
    return True


def validate_file_paths(paths: dict, required_files: list = None) -> dict:
    """
    Validate that expected file paths exist and are accessible.
    
    Args:
        paths: Dict mapping file types to Path objects
        required_files: List of file types that must exist (optional)
    
    Returns:
        Dict mapping file types to validation results
    """
    validation = {}
    required_files = required_files or []
    
    for file_type, file_path in paths.items():
        exists = file_path.exists() if isinstance(file_path, Path) else Path(file_path).exists()
        validation[file_type] = {
            'exists': exists,
            'required': file_type in required_files,
            'path': str(file_path)
        }
        
        if file_type in required_files and not exists:
            console.print(f"[yellow]Warning: Required {file_type} file missing: {file_path}[/yellow]")
    
    return validation


def create_missing_directories(file_path: Path) -> bool:
    """
    Create parent directories for a file path if they don't exist.
    
    Args:
        file_path: Path to a file whose parent directories should be created
    
    Returns:
        True if directories exist or were created successfully, False otherwise
    """
    try:
        file_path.parent.mkdir(parents=True, exist_ok=True)
        return True
    except Exception as e:
        console.print(f"[red]Error creating directories for {file_path}: {e}[/red]")
        return False