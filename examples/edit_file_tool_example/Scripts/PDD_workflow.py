#!/usr/bin/env python3
"""
Optimized PDD Workflow Script

Simple workflow to:
1. Take a component name
2. Run PDD sync with --force flag
3. Create cmd_(component).txt command log
4. Clean up temporary files
5. Ensure __init__.py exists
"""

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path

# Configuration
EXECUTION_MODE = 'execute'  # Set to 'print' to show commands without executing
ENABLE_LOGGING = False  # Set to False to disable sync log file creation
ENABLE_COST_TRACKING = False  # Set to True to enable cost tracking by default
USE_INFISICAL = False  # Set to False to run pdd directly without infisical wrapper

# Read ENABLE_TAGGING from environment variable (set by Makefile)
ENABLE_TAGGING = os.environ.get('ENABLE_TAGGING', 'no').lower() == 'yes'


def ensure_init_file():
    """Ensure edit_file_tool directory has __init__.py for proper package structure."""
    edit_file_tool_dir = "edit_file_tool"
    os.makedirs(edit_file_tool_dir, exist_ok=True)
    
    init_file_path = os.path.join(edit_file_tool_dir, "__init__.py")
    if not os.path.exists(init_file_path):
        try:
            with open(init_file_path, 'w', encoding='utf-8') as f:
                f.write('"""Edit File Tool Package"""\n')
            print(f"[INFO] Created __init__.py in {edit_file_tool_dir}")
        except IOError as e:
            print(f"[WARN] Could not create __init__.py: {e}")


def create_cmd_file(component_name: str, cmd_executed: list, exit_code: int, log_file: str = None):
    """Create cmd_(module).txt file to track the command executed."""
    # Ensure make_creation/component_name directory exists
    cmd_dir = os.path.join("make_creation", component_name)
    os.makedirs(cmd_dir, exist_ok=True)
    
    cmd_file = os.path.join(cmd_dir, f"cmd_{component_name}.txt")
    try:
        with open(cmd_file, 'w', encoding='utf-8') as f:
            f.write(f"# Component: {component_name}\n")
            f.write(f"# Commands are intended to be run from the project root.\n")
            f.write(f"# PHASE 0: Clean existing files enabled - deleted existing component files\n")
            f.write(f"# Using prompt file: 'prompts/{component_name}_python.prompt'\n")
            f.write(f"\n")
            f.write(f"# PHASE 1: PDD Sync - Complete Workflow\n")
            f.write(f"# Uses the pdd sync command to automatically execute the complete PDD workflow.\n")
            f.write(f"# This includes auto-deps, generate, example, crash, verify, test, fix, and update phases.\n")
            
            # Build the command string in the expected format
            cmd_str = ' '.join(cmd_executed)
            if log_file:
                cmd_str += f' > "{log_file}" 2>&1'
            f.write(f"{cmd_str}\n")
            
        print(f"[INFO] Created command log: {cmd_file}")
    except IOError as e:
        print(f"[WARN] Could not create command log file '{cmd_file}': {e}")


def cleanup_component_files(base_name: str):
    """
    Clean up temporary/versioned files for a specific component.
    
    Keeps only the final files:
    - edit_file_tool/{base_name}.py
    - examples/{base_name}_example.py  
    - tests/test_{base_name}.py
    
    Also cleans up PDD meta files:
    - .pdd/meta/{base_name}_python_*.json
    """
    print(f"[INFO] Running cleanup for component '{base_name}'...")
    total_deleted = 0
    
    # Define target directories and their protected files
    cleanup_targets = [
        {
            'dir': 'edit_file_tool',
            'prefix': base_name,
            'protected': f'{base_name}.py',
            'description': 'module files'
        },
        {
            'dir': 'examples', 
            'prefix': base_name,
            'protected': f'{base_name}_example.py',
            'description': 'example files'
        },
        {
            'dir': 'tests',
            'prefix': f'test_{base_name}',
            'protected': f'test_{base_name}.py', 
            'description': 'test files'
        },
        {
            'dir': '.pdd/meta',
            'prefix': f'{base_name}_python',
            'protected': None,  # No protected files in meta - delete all matching
            'description': 'PDD meta files'
        }
    ]
    
    for target in cleanup_targets:
        dir_path = target['dir']
        prefix = target['prefix']
        protected_file = target['protected']
        description = target['description']
        
        # Skip if directory doesn't exist
        if not os.path.exists(dir_path):
            continue
            
        try:
            # Get all files in the directory
            all_files = os.listdir(dir_path)
            
            # Find files that match our component pattern
            if dir_path == '.pdd/meta':
                # For PDD meta files, match any extension (json, etc.)
                matching_files = [f for f in all_files if f.startswith(prefix)]
            else:
                # For code directories, only match .py files
                matching_files = [f for f in all_files if f.startswith(prefix) and f.endswith('.py')]
            
            # Filter out the protected file (if any)
            if protected_file:
                files_to_delete = [f for f in matching_files if f != protected_file]
            else:
                # No protected files - delete all matching
                files_to_delete = matching_files
            
            if not files_to_delete:
                continue
                
            print(f"[INFO] Found {len(files_to_delete)} temporary {description} in '{dir_path}'")
            
            # Delete each file
            for filename in files_to_delete:
                file_path = os.path.join(dir_path, filename)
                try:
                    os.remove(file_path)
                    print(f"[SUCCESS] Deleted: {file_path}")
                    total_deleted += 1
                except OSError as e:
                    print(f"[WARN] Could not delete '{file_path}': {e}")
                    
        except OSError as e:
            print(f"[ERROR] Could not process directory '{dir_path}': {e}")
            
    if total_deleted > 0:
        print(f"[SUCCESS] Cleanup completed - deleted {total_deleted} temporary files")
    else:
        print(f"[INFO] No temporary files found for component '{base_name}'")


def run_pdd_sync(component_name: str, log_file: str = None, enable_cost_tracking: bool = False) -> int:
    """Run PDD sync command and return exit code."""
    print(f"[INFO] Running PDD sync for component '{component_name}'...")
    
    # Build PDD command - with or without infisical wrapper
    if USE_INFISICAL:
        cmd = ["infisical", "run", "--", "pdd", "--local", "--force"]
    else:
        cmd = ["pdd", "--local", "--force"]
    
    # Add cost tracking if enabled
    if enable_cost_tracking:
        # Ensure make_creation/component_name directory exists
        cost_dir = os.path.join("make_creation", component_name)
        os.makedirs(cost_dir, exist_ok=True)
        
        cost_file = os.path.join(cost_dir, f"cost_{component_name}.csv")
        cmd.extend(["--output-cost", cost_file])  # Remove quotes from actual command
        print(f"[INFO] Cost tracking enabled. Output will be saved to: {cost_file}")
    
    # Add sync and component name (sync comes before component in expected format)
    cmd.extend(["sync", component_name])  # Remove quotes from actual command
    
    try:
        if log_file:
            print(f"[INFO] Logging sync output to: {log_file}")
            # Redirect both stdout and stderr to log file
            with open(log_file, 'w', encoding='utf-8') as f:
                result = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, check=False)
        else:
            result = subprocess.run(cmd, check=False)
        
        return result.returncode
    except FileNotFoundError:
        print("[ERROR] 'pdd' command not found. Make sure PDD is installed and in PATH.")
        return 1
    except Exception as e:
        print(f"[ERROR] Failed to run PDD sync: {e}")
        return 1


def main():
    """Main workflow function."""
    parser = argparse.ArgumentParser(
        description='Optimized PDD workflow: sync component and cleanup'
    )
    parser.add_argument(
        'component_name', 
        help='Name of the component to build (e.g., utils, cli)'
    )
    parser.add_argument(
        '--clean', '--override',
        action='store_true',
        help='Delete existing component files before building (for Makefile compatibility)'
    )
    parser.add_argument(
        '--no-cleanup', 
        action='store_true',
        help='Skip cleanup of temporary files after sync'
    )
    parser.add_argument(
        '--print-only',
        action='store_true', 
        help='Print commands that would be executed without running them'
    )
    parser.add_argument(
        '--no-log',
        action='store_true',
        help='Disable creation of sync log file'
    )
    parser.add_argument(
        '--enable-cost-tracking',
        action='store_true',
        help='Enable cost tracking and save to make_creation/module/cost_(module).csv'
    )
    
    args = parser.parse_args()
    
    # Extract base component name (remove .py if present)
    base_name = args.component_name
    if base_name.endswith('.py'):
        base_name = base_name[:-3]
    
    print(f"[INFO] Starting PDD workflow for component: {base_name}")
    
    # 1. Validate prompt file exists
    prompt_file = f"prompts/{base_name}_python.prompt"
    if not os.path.exists(prompt_file):
        print(f"[ERROR] Prompt file not found: {prompt_file}")
        sys.exit(1)
    
    # 2. Ensure __init__.py exists
    ensure_init_file()
    
    # 3. Setup logging if enabled
    log_file = None
    if (ENABLE_LOGGING and not args.no_log):
        logs_dir = "logs"
        os.makedirs(logs_dir, exist_ok=True)
        log_file = os.path.join(logs_dir, f"{base_name}_sync.txt")
    
    # 4. Determine execution mode
    execution_mode = 'print' if args.print_only else EXECUTION_MODE
    
    if execution_mode == 'print':
        print(f"[INFO] Print mode - showing commands that would be executed:")
        cost_tracking_enabled = args.enable_cost_tracking or ENABLE_COST_TRACKING
        
        # Build command display in expected format
        if USE_INFISICAL:
            cmd_display = f'infisical run -- pdd --local --force'
        else:
            cmd_display = f'pdd --local --force'
        if cost_tracking_enabled:
            cost_file = os.path.join("make_creation", base_name, f"cost_{base_name}.csv")
            cmd_display += f' --output-cost "{cost_file}"'
        cmd_display += f' sync "{base_name}"'
        
        if log_file:
            cmd_display += f' > "{log_file}" 2>&1'
            
        print(f"Command: {cmd_display}")
        
        if log_file:
            print(f"Logging: Output would be saved to {log_file}")
        if cost_tracking_enabled:
            cost_file = os.path.join("make_creation", base_name, f"cost_{base_name}.csv")
            print(f"Cost tracking: Would be saved to {cost_file}")
        if not args.no_cleanup:
            print(f"Cleanup: Remove temporary files for component '{base_name}'")
        cmd_log_path = os.path.join("make_creation", base_name, f"cmd_{base_name}.txt")
        print(f"Command log: {cmd_log_path} would be created")
        print(f"[INFO] Print mode enabled. No commands executed.")
        return
    
    # 5. Run PDD sync
    cost_tracking_enabled = args.enable_cost_tracking or ENABLE_COST_TRACKING
    sync_exit_code = run_pdd_sync(base_name, log_file, cost_tracking_enabled)
    
    # 5.1. Create command log file with quotes for display purposes
    if USE_INFISICAL:
        cmd_executed_display = ["infisical", "run", "--", "pdd", "--local", "--force"]
    else:
        cmd_executed_display = ["pdd", "--local", "--force"]
    if cost_tracking_enabled:
        cost_file = os.path.join("make_creation", base_name, f"cost_{base_name}.csv")
        cmd_executed_display.extend(["--output-cost", f'"{cost_file}"'])
    cmd_executed_display.extend(["sync", f'"{base_name}"'])
    create_cmd_file(base_name, cmd_executed_display, sync_exit_code, log_file)

    
    if sync_exit_code == 0:
        print(f"[SUCCESS] PDD sync completed successfully for '{base_name}'")
        if log_file:
            print(f"[INFO] Sync log saved to: {log_file}")
    else:
        print(f"[ERROR] PDD sync failed (exit code {sync_exit_code}) for '{base_name}'")
        if log_file:
            print(f"[INFO] Check sync log for details: {log_file}")
    
    # 6. Cleanup temporary files (unless disabled)
    if not args.no_cleanup:
        cleanup_component_files(base_name)
    
    # 7. Exit with same code as sync
    if sync_exit_code != 0:
        sys.exit(sync_exit_code)
    
    print(f"[INFO] PDD workflow completed successfully for '{base_name}'")


if __name__ == "__main__":
    main()