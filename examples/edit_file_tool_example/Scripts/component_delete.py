#!/usr/bin/env python3
"""
Component Delete Script

Simple script to completely remove a component and all its associated files:
1. Remove main module file from edit_file_tool/
2. Remove example file from examples/
3. Remove test file from tests/
4. Remove PDD meta files from .pdd/meta/
5. Remove make_creation directory for the component
6. Preserve prompt files in prompts/ (protected folder)
"""

import argparse
import os
import shutil
import sys
from pathlib import Path

def delete_component_files(base_name: str, dry_run: bool = False):
    """
    Completely delete all files for a specific component.
    
    Removes:
    - edit_file_tool/{base_name}*.py
    - examples/{base_name}*.py  
    - tests/test_{base_name}*.py
    - .pdd/meta/{base_name}_python*.json
    - make_creation/{base_name}/ (entire directory)
    - prompts/{base_name}_python.prompt (PRESERVED - protected folder)
    """
    print(f"[INFO] {'[DRY RUN] ' if dry_run else ''}Deleting component '{base_name}'...")
    total_deleted = 0
    
    # Define target directories and their file patterns
    delete_targets = [
        {
            'dir': 'edit_file_tool',
            'prefix': base_name,
            'description': 'module files',
            'extensions': ['.py']
        },
        {
            'dir': 'examples', 
            'prefix': base_name,
            'description': 'example files',
            'extensions': ['.py']
        },
        {
            'dir': 'tests',
            'prefix': f'test_{base_name}',
            'description': 'test files',
            'extensions': ['.py']
        },
        {
            'dir': '.pdd/meta',
            'prefix': f'{base_name}_python',
            'description': 'PDD meta files',
            'extensions': ['.json', '.yaml', '.yml']  # Any meta file extensions
        }
    ]
    
    # Delete files in directories
    for target in delete_targets:
        dir_path = target['dir']
        prefix = target['prefix']
        description = target['description']
        extensions = target['extensions']
        
        # Skip if directory doesn't exist
        if not os.path.exists(dir_path):
            continue
            
        try:
            # Get all files in the directory
            all_files = os.listdir(dir_path)
            
            # Find files that match our component pattern
            matching_files = []
            for f in all_files:
                if f.startswith(prefix):
                    # Check if it has one of the expected extensions or no extension filter
                    if not extensions or any(f.endswith(ext) for ext in extensions):
                        matching_files.append(f)
            
            if not matching_files:
                continue
                
            print(f"[INFO] {'[DRY RUN] ' if dry_run else ''}Found {len(matching_files)} {description} in '{dir_path}'")
            
            # Delete each file
            for filename in matching_files:
                file_path = os.path.join(dir_path, filename)
                try:
                    if dry_run:
                        print(f"[DRY RUN] Would delete: {file_path}")
                    else:
                        os.remove(file_path)
                        print(f"[SUCCESS] Deleted: {file_path}")
                    total_deleted += 1
                except OSError as e:
                    print(f"[WARN] Could not delete '{file_path}': {e}")
                    
        except OSError as e:
            print(f"[ERROR] Could not process directory '{dir_path}': {e}")
    
    # Delete make_creation directory for this component
    make_creation_dir = os.path.join("make_creation", base_name)
    if os.path.exists(make_creation_dir):
        try:
            if dry_run:
                print(f"[DRY RUN] Would delete directory: {make_creation_dir}")
                # Count files that would be deleted
                for root, dirs, files in os.walk(make_creation_dir):
                    total_deleted += len(files)
            else:
                shutil.rmtree(make_creation_dir)
                print(f"[SUCCESS] Deleted directory: {make_creation_dir}")
                total_deleted += 1
        except OSError as e:
            print(f"[WARN] Could not delete directory '{make_creation_dir}': {e}")
    
    # Skip deleting prompt files to preserve prompts/ folder
    prompt_file = f"prompts/{base_name}_python.prompt"
    if os.path.exists(prompt_file):
        print(f"[INFO] Preserving prompt file: {prompt_file} (prompts/ folder protected)")
            
    if total_deleted > 0:
        print(f"[SUCCESS] {'[DRY RUN] ' if dry_run else ''}Component deletion {'would delete' if dry_run else 'completed'} - {'would delete' if dry_run else 'deleted'} {total_deleted} files/directories")
    else:
        print(f"[INFO] No files found for component '{base_name}'")

def main():
    """Main function."""
    parser = argparse.ArgumentParser(
        description='Delete all files for a PDD component'
    )
    parser.add_argument(
        'component_name', 
        help='Name of the component to delete (e.g., utils, cli)'
    )
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='Show what would be deleted without actually deleting'
    )
    parser.add_argument(
        '--force',
        action='store_true',
        help='Skip confirmation prompt'
    )
    
    args = parser.parse_args()
    
    # Extract base component name (remove .py if present)
    base_name = args.component_name
    if base_name.endswith('.py'):
        base_name = base_name[:-3]
    
    print(f"[INFO] Component deletion script for: {base_name}")
    
    # Show what will be deleted
    if not args.dry_run and not args.force:
        print(f"\n[WARNING] This will permanently delete ALL files for component '{base_name}'")
        print("Files that will be deleted:")
        print(f"  - edit_file_tool/{base_name}*.py")
        print(f"  - examples/{base_name}*.py")
        print(f"  - tests/test_{base_name}*.py")
        print(f"  - .pdd/meta/{base_name}_python*")
        print(f"  - make_creation/{base_name}/ (entire directory)")
        print(f"  - prompts/{base_name}_python.prompt (PRESERVED - protected)")
        print()
        
        response = input("Are you sure you want to delete these files? (y/N): ").lower().strip()
        if response != 'y':
            print("[INFO] Component deletion cancelled.")
            sys.exit(0)
    
    # Delete the component
    delete_component_files(base_name, dry_run=args.dry_run)
    
    if args.dry_run:
        print(f"[INFO] Dry run completed for component '{base_name}'. Use --force to actually delete.")
    else:
        print(f"[INFO] Component '{base_name}' deleted successfully.")

if __name__ == "__main__":
    main()