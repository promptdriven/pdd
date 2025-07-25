"""
Python Environment Detector

Detects the host shell's Python environment (conda, venv, poetry, pipenv, etc.)
and returns the appropriate Python executable for subprocess calls.

This ensures that PDD operations use the same Python environment as the shell
that launched PDD, rather than the uv tools environment where PDD is installed.
"""

import os
import sys
import shutil
from pathlib import Path
from typing import Optional


def detect_host_python_executable() -> str:
    """
    Detect the host shell's Python executable.
    
    This function checks for various virtual environment indicators
    and returns the appropriate Python executable path.
    
    Returns:
        str: Path to the Python executable that should be used for subprocess calls.
             Falls back to sys.executable if no host environment is detected.
    
    Detection order:
    1. VIRTUAL_ENV (works for venv, virtualenv, poetry, pipenv)
    2. CONDA_PREFIX (conda-specific)
    3. PATH resolution with shutil.which('python')
    4. sys.executable (fallback)
    """
    
    # Check for virtual environment (venv, virtualenv, poetry, pipenv)
    virtual_env = os.environ.get('VIRTUAL_ENV')
    if virtual_env:
        # Try common Python executable locations within the virtual environment
        for python_name in ['python', 'python3']:
            # Unix-like systems
            venv_python = Path(virtual_env) / 'bin' / python_name
            if venv_python.is_file():
                return str(venv_python)
            
            # Windows
            venv_python = Path(virtual_env) / 'Scripts' / f'{python_name}.exe'
            if venv_python.is_file():
                return str(venv_python)
    
    # Check for conda environment
    conda_prefix = os.environ.get('CONDA_PREFIX')
    if conda_prefix:
        # Try common Python executable locations within conda environment
        for python_name in ['python', 'python3']:
            # Unix-like systems
            conda_python = Path(conda_prefix) / 'bin' / python_name
            if conda_python.is_file():
                return str(conda_python)
            
            # Windows
            conda_python = Path(conda_prefix) / f'{python_name}.exe'
            if conda_python.is_file():
                return str(conda_python)
    
    # Use PATH resolution as fallback (respects shell's PATH modifications)
    which_python = shutil.which('python')
    if which_python and Path(which_python).resolve() != Path(sys.executable).resolve():
        # Only use if it's different from the current sys.executable
        # This helps detect when we're in a different environment
        return which_python
    
    # Try python3 as well
    which_python3 = shutil.which('python3')
    if which_python3 and Path(which_python3).resolve() != Path(sys.executable).resolve():
        return which_python3
    
    # Final fallback to current executable
    return sys.executable


def get_environment_info() -> dict:
    """
    Get detailed information about the current Python environment.
    
    Returns:
        dict: Dictionary containing environment information for debugging
    """
    return {
        'sys_executable': sys.executable,
        'detected_executable': detect_host_python_executable(),
        'virtual_env': os.environ.get('VIRTUAL_ENV'),
        'conda_prefix': os.environ.get('CONDA_PREFIX'), 
        'conda_default_env': os.environ.get('CONDA_DEFAULT_ENV'),
        'poetry_active': os.environ.get('POETRY_ACTIVE'),
        'pipenv_active': os.environ.get('PIPENV_ACTIVE'),
        'which_python': shutil.which('python'),
        'which_python3': shutil.which('python3'),
        'path': os.environ.get('PATH', '').split(os.pathsep)[:3],  # First 3 PATH entries
    }


def is_in_virtual_environment() -> bool:
    """
    Check if we're currently running in any kind of virtual environment.
    
    Returns:
        bool: True if in a virtual environment, False otherwise
    """
    return bool(
        os.environ.get('VIRTUAL_ENV') or 
        os.environ.get('CONDA_PREFIX') or
        os.environ.get('POETRY_ACTIVE') or
        os.environ.get('PIPENV_ACTIVE')
    )


def get_environment_type() -> str:
    """
    Determine the type of virtual environment we're in.
    
    Returns:
        str: Type of environment ('conda', 'venv', 'poetry', 'pipenv', 'system', 'unknown')
    """
    if os.environ.get('CONDA_PREFIX'):
        return 'conda'
    elif os.environ.get('POETRY_ACTIVE'):
        return 'poetry'
    elif os.environ.get('PIPENV_ACTIVE'):
        return 'pipenv'
    elif os.environ.get('VIRTUAL_ENV'):
        return 'venv'
    elif is_in_virtual_environment():
        return 'unknown'
    else:
        return 'system'


if __name__ == '__main__':
    # Demo/test functionality
    print("Python Environment Detection")
    print("=" * 40)
    
    env_info = get_environment_info()
    for key, value in env_info.items():
        print(f"{key}: {value}")
    
    print()
    print(f"Environment type: {get_environment_type()}")
    print(f"In virtual environment: {is_in_virtual_environment()}")
    print(f"Detected Python executable: {detect_host_python_executable()}")