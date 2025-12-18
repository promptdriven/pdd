"""Tests for setup_tool.py"""

import subprocess
import tempfile
from pathlib import Path
import pytest
from pdd.setup_tool import create_api_env_script


def test_create_api_env_script_with_special_characters_bash():
    """
    Test that API keys with special shell characters are properly escaped
    when generating bash/zsh shell scripts.
    
    This test will fail with the current implementation (no escaping) and
    pass after fixing with shlex.quote().
    """
    # Simulate a Gemini API key that might contain special characters
    # These are realistic characters that could appear in API keys or be accidentally
    # included when copy-pasting
    test_keys = {
        'GEMINI_API_KEY': 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash'
    }
    
    # Generate the script
    script_content = create_api_env_script(test_keys, 'bash')
    
    # Write to a temporary file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.sh', delete=False) as f:
        f.write(script_content)
        script_path = Path(f.name)
    
    try:
        # Try to parse/validate the script by running it with bash -n (syntax check)
        # This will fail if the script has parsing errors
        result = subprocess.run(
            ['bash', '-n', str(script_path)],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        # The script should parse without errors
        assert result.returncode == 0, (
            f"Generated script has syntax errors: {result.stderr}\n"
            f"Script content:\n{script_content}"
        )
        
        # Additionally, try to source it in a subprocess to ensure it can be executed
        # We'll check the exit code but not the actual env vars (since they're set in subprocess)
        result = subprocess.run(
            ['bash', '-c', f'source {script_path} && exit 0'],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        assert result.returncode == 0, (
            f"Generated script cannot be sourced: {result.stderr}\n"
            f"Script content:\n{script_content}"
        )
        
    finally:
        # Clean up
        script_path.unlink()


def test_create_api_env_script_with_special_characters_zsh():
    """Test that API keys with special characters work in zsh scripts."""
    test_keys = {
        'GEMINI_API_KEY': 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash'
    }
    
    script_content = create_api_env_script(test_keys, 'zsh')
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.sh', delete=False) as f:
        f.write(script_content)
        script_path = Path(f.name)
    
    try:
        # Test zsh syntax
        result = subprocess.run(
            ['zsh', '-n', str(script_path)],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        assert result.returncode == 0, (
            f"Generated zsh script has syntax errors: {result.stderr}\n"
            f"Script content:\n{script_content}"
        )
    finally:
        script_path.unlink()


def test_create_api_env_script_with_common_problematic_characters():
    """
    Test with various common problematic characters that might appear in API keys.
    
    Characters tested:
    - Double quotes: "
    - Single quotes: '
    - Dollar signs: $ (variable expansion)
    - Backticks: ` (command substitution)
    - Backslashes: \\ (escaping)
    - Spaces: (should be handled)
    - Parentheses: () (might be interpreted)
    """
    problematic_key = 'key"with\'many$special`characters\\and spaces(too)'
    test_keys = {
        'GEMINI_API_KEY': problematic_key
    }
    
    # Test all common shells
    for shell in ['bash', 'zsh', 'sh']:
        script_content = create_api_env_script(test_keys, shell)
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.sh', delete=False) as f:
            f.write(script_content)
            script_path = Path(f.name)
        
        try:
            # Use bash/sh for sh, bash for bash, zsh for zsh
            shell_cmd = 'sh' if shell == 'sh' else shell
            result = subprocess.run(
                [shell_cmd, '-n', str(script_path)],
                capture_output=True,
                text=True,
                timeout=5
            )
            
            assert result.returncode == 0, (
                f"Generated {shell} script has syntax errors: {result.stderr}\n"
                f"Script content:\n{script_content}"
            )
        finally:
            script_path.unlink()


def test_create_api_env_script_preserves_key_value():
    """
    Test that after proper escaping, the key value can still be correctly
    extracted when the script is sourced.
    """
    original_key = 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash'
    test_keys = {
        'GEMINI_API_KEY': original_key
    }
    
    script_content = create_api_env_script(test_keys, 'bash')
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.sh', delete=False) as f:
        f.write(script_content)
        script_path = Path(f.name)
    
    try:
        # Source the script and extract the value
        # We'll use a Python subprocess to avoid shell escaping issues in our test
        result = subprocess.run(
            ['bash', '-c', f'source {script_path} && python3 -c "import os; print(os.environ.get(\'GEMINI_API_KEY\', \'\'))"'],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        assert result.returncode == 0, (
            f"Failed to source script and read env var: {result.stderr}\n"
            f"Script content:\n{script_content}"
        )
        
        extracted_key = result.stdout.strip()
        assert extracted_key == original_key, (
            f"Key value was corrupted during escaping.\n"
            f"Original: {repr(original_key)}\n"
            f"Extracted: {repr(extracted_key)}\n"
            f"Script content:\n{script_content}"
        )
    finally:
        script_path.unlink()


def test_create_api_env_script_with_normal_key():
    """
    Test that normal keys (without special characters) still work correctly.
    This ensures our fix doesn't break existing functionality.
    """
    normal_key = 'AIzaSyAbCdEf1234567890_normal_key_value'
    test_keys = {
        'OPENAI_API_KEY': normal_key,
        'GEMINI_API_KEY': normal_key
    }
    
    script_content = create_api_env_script(test_keys, 'bash')
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.sh', delete=False) as f:
        f.write(script_content)
        script_path = Path(f.name)
    
    try:
        result = subprocess.run(
            ['bash', '-n', str(script_path)],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        assert result.returncode == 0, (
            f"Normal key failed syntax check: {result.stderr}\n"
            f"Script content:\n{script_content}"
        )
        
        # Verify values can be extracted
        result = subprocess.run(
            ['bash', '-c', f'source {script_path} && python3 -c "import os; print(os.environ.get(\'OPENAI_API_KEY\', \'\')); print(os.environ.get(\'GEMINI_API_KEY\', \'\'))"'],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        assert result.returncode == 0
        extracted_keys = result.stdout.strip().split('\n')
        assert extracted_keys[0] == normal_key
        assert extracted_keys[1] == normal_key
    finally:
        script_path.unlink()

