#!/usr/bin/env python3
"""
Fix external imports in generated example files.

This module provides functionality to automatically fix generated examples
that have external imports by replacing them with inline function definitions.
"""

import re
import os
from typing import Optional, Tuple


def fix_external_imports_in_content(content: str, original_code: str) -> Tuple[str, bool]:
    """
    Fix external imports in generated example content by replacing them with inline definitions.
    
    Args:
        content: The generated example content
        original_code: The original code module content
        
    Returns:
        Tuple of (fixed_content, was_fixed)
    """
    was_fixed = False
    
    # Pattern to match external imports like "from module_name import function_name"
    external_import_pattern = r'from\s+(\w+)\s+import\s+(\w+)'
    
    # Also fix double "def" syntax errors and other common issues
    content = re.sub(r'def\s+def\s+', 'def ', content)
    was_fixed = was_fixed or bool(re.search(r'def\s+def\s+', content))
    
    matches = list(re.finditer(external_import_pattern, content))
    
    for match in matches:
        module_name = match.group(1)
        function_name = match.group(2)
        
        # Skip standard library imports
        if module_name in ['os', 'sys', 'json', 'datetime', 'pathlib', 'typing', 'collections', 'itertools']:
            continue
            
        # Extract the function definition from original code
        function_def = _extract_function_definition(original_code, function_name)
        
        if function_def:
            # Replace the import with the inline function definition
            content = content.replace(match.group(0), function_def)
            was_fixed = True
        else:
            # If we can't find the function definition, replace with a comment
            content = content.replace(
                match.group(0), 
                f"# {function_name} function definition (import from {module_name} removed)"
            )
            was_fixed = True
    
    return content, was_fixed


def _extract_function_definition(code: str, function_name: str) -> Optional[str]:
    """
    Extract a function definition from code.
    
    Args:
        code: The code to search in
        function_name: The name of the function to extract
        
    Returns:
        The function definition or None if not found
    """
    # Pattern to match function definitions
    pattern = rf'(def\s+{re.escape(function_name)}\s*\([^)]*\)\s*->[^:]*:.*?)(?=\n\ndef|\nclass|\Z)'
    
    match = re.search(pattern, code, re.DOTALL)
    if match:
        return match.group(1).strip()
    
    # Fallback: simpler pattern without return type annotation
    pattern = rf'(def\s+{re.escape(function_name)}\s*\([^)]*\)\s*:.*?)(?=\n\ndef|\nclass|\Z)'
    match = re.search(pattern, code, re.DOTALL)
    if match:
        return match.group(1).strip()
    
    return None


def fix_example_file(file_path: str, original_code_path: str) -> bool:
    """
    Fix external imports in an example file.
    
    Args:
        file_path: Path to the example file to fix
        original_code_path: Path to the original code file
        
    Returns:
        True if the file was fixed, False otherwise
    """
    if not os.path.exists(file_path):
        print(f"Error: Example file not found at {file_path}")
        return False
        
    if not os.path.exists(original_code_path):
        print(f"Error: Original code file not found at {original_code_path}")
        return False
    
    # Read the example file
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Read the original code
    with open(original_code_path, 'r', encoding='utf-8') as f:
        original_code = f.read()
    
    # Fix external imports
    fixed_content, was_fixed = fix_external_imports_in_content(content, original_code)
    
    if was_fixed:
        # Write the fixed content back
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(fixed_content)
        print(f"Successfully fixed external imports in {file_path}")
        return True
    else:
        print(f"No external imports found in {file_path}")
        return False


if __name__ == "__main__":
    # Example usage
    import sys
    
    if len(sys.argv) != 3:
        print("Usage: python fix_external_imports.py <example_file> <original_code_file>")
        sys.exit(1)
    
    example_file = sys.argv[1]
    original_code_file = sys.argv[2]
    
    fix_example_file(example_file, original_code_file)
