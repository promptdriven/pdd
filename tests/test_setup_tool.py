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


def _shell_available(shell: str) -> bool:
    """Check if a shell is available on the system"""
    try:
        result = subprocess.run(
            ['which', shell],
            capture_output=True,
            timeout=2
        )
        return result.returncode == 0
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return False


def test_create_api_env_script_with_special_characters_fish():
    """
    Test that API keys with special characters work in fish shell scripts.
    
    This test verifies that shlex.quote() works correctly with fish shell.
    Fish is not POSIX-compliant, so there may be edge cases where POSIX-style
    quoting doesn't work as expected.
    """
    if not _shell_available('fish'):
        pytest.skip("fish shell not available")
    
    test_keys = {
        'GEMINI_API_KEY': 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash'
    }
    
    script_content = create_api_env_script(test_keys, 'fish')
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.fish', delete=False) as f:
        f.write(script_content)
        script_path = Path(f.name)
    
    try:
        # Fish doesn't have a -n syntax check flag like bash/zsh
        # So we'll try to source it and see if it works
        result = subprocess.run(
            ['fish', '-c', f'source {script_path}; exit 0'],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        assert result.returncode == 0, (
            f"Generated fish script has syntax/execution errors: {result.stderr}\n"
            f"Script content:\n{script_content}"
        )
    finally:
        script_path.unlink()


def test_create_api_env_script_preserves_key_value_fish():
    """
    Test that fish shell correctly preserves key values with special characters.
    
    This is critical because fish has different quoting rules than POSIX shells,
    and shlex.quote() may not handle all cases correctly.
    """
    if not _shell_available('fish'):
        pytest.skip("fish shell not available")
    
    original_key = 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash'
    test_keys = {
        'GEMINI_API_KEY': original_key
    }
    
    script_content = create_api_env_script(test_keys, 'fish')
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.fish', delete=False) as f:
        f.write(script_content)
        script_path = Path(f.name)
    
    try:
        # Source the script and extract the value using fish
        result = subprocess.run(
            ['fish', '-c', f'source {script_path}; python3 -c "import os; print(os.environ.get(\'GEMINI_API_KEY\', \'\'))"'],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        assert result.returncode == 0, (
            f"Failed to source fish script and read env var: {result.stderr}\n"
            f"Script content:\n{script_content}"
        )
        
        extracted_key = result.stdout.strip()
        assert extracted_key == original_key, (
            f"Key value was corrupted during escaping in fish shell.\n"
            f"Original: {repr(original_key)}\n"
            f"Extracted: {repr(extracted_key)}\n"
            f"Script content:\n{script_content}\n"
            f"This indicates shlex.quote() may not work correctly with fish shell."
        )
    finally:
        script_path.unlink()


def test_create_api_env_script_with_special_characters_csh():
    """
    Test that API keys with special characters work in csh/tcsh shell scripts.
    
    WARNING: csh/tcsh have fundamentally different quoting rules than POSIX shells.
    shlex.quote() uses POSIX single-quote syntax which may not work correctly
    in csh/tcsh, especially with:
    - Variables containing $ (variable expansion still occurs in single quotes)
    - Complex backslash sequences
    - Certain special characters
    
    This test will help identify if shlex.quote() works correctly with csh/tcsh.
    """
    # Try csh first, then tcsh
    shell_cmd = None
    shell_name = None
    for shell in ['csh', 'tcsh']:
        if _shell_available(shell):
            shell_cmd = shell
            shell_name = shell
            break
    
    if not shell_cmd:
        pytest.skip("csh/tcsh not available")
    
    test_keys = {
        'GEMINI_API_KEY': 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash'
    }
    
    script_content = create_api_env_script(test_keys, shell_name)
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.csh', delete=False) as f:
        f.write(script_content)
        script_path = Path(f.name)
    
    try:
        # csh/tcsh don't have a -n flag, so we'll try to source it
        # Use -f to prevent reading .cshrc/.tcshrc which might interfere
        result = subprocess.run(
            [shell_cmd, '-f', '-c', f'source {script_path}; exit 0'],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        assert result.returncode == 0, (
            f"Generated {shell_name} script has syntax/execution errors: {result.stderr}\n"
            f"Script content:\n{script_content}\n"
            f"This may indicate that shlex.quote() doesn't work correctly with {shell_name}."
        )
    finally:
        script_path.unlink()


def test_create_api_env_script_preserves_key_value_csh():
    """
    Test that csh/tcsh correctly preserves key values with special characters.
    
    This is critical because csh/tcsh have fundamentally different quoting rules:
    - Single quotes in csh do NOT prevent variable expansion ($var still expands)
    - Backslash escaping works differently
    - The quoting mechanism is incompatible with POSIX
    
    This test will likely reveal issues with using shlex.quote() for csh/tcsh.
    """
    # Try csh first, then tcsh
    shell_cmd = None
    shell_name = None
    for shell in ['csh', 'tcsh']:
        if _shell_available(shell):
            shell_cmd = shell
            shell_name = shell
            break
    
    if not shell_cmd:
        pytest.skip("csh/tcsh not available")
    
    original_key = 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash'
    test_keys = {
        'GEMINI_API_KEY': original_key
    }
    
    script_content = create_api_env_script(test_keys, shell_name)
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.csh', delete=False) as f:
        f.write(script_content)
        script_path = Path(f.name)
    
    try:
        # Source the script and extract the value using csh/tcsh
        # Use -f to prevent reading .cshrc/.tcshrc
        result = subprocess.run(
            [shell_cmd, '-f', '-c', f'source {script_path}; python3 -c "import os; print(os.environ.get(\'GEMINI_API_KEY\', \'\'))"'],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        assert result.returncode == 0, (
            f"Failed to source {shell_name} script and read env var: {result.stderr}\n"
            f"Script content:\n{script_content}"
        )
        
        extracted_key = result.stdout.strip()
        assert extracted_key == original_key, (
            f"Key value was corrupted during escaping in {shell_name} shell.\n"
            f"Original: {repr(original_key)}\n"
            f"Extracted: {repr(extracted_key)}\n"
            f"Script content:\n{script_content}\n"
            f"This indicates shlex.quote() does NOT work correctly with {shell_name}.\n"
            f"csh/tcsh have different quoting rules than POSIX shells."
        )
    finally:
        script_path.unlink()


def test_create_api_env_script_csh_variable_expansion_issue():
    """
    Test a specific csh/tcsh issue: variable expansion in single quotes.
    
    In csh/tcsh, single quotes do NOT prevent variable expansion.
    This means a key containing $HOME will expand to the actual home directory
    path, which is incorrect behavior.
    
    This test demonstrates the fundamental incompatibility between
    POSIX-style quoting (shlex.quote) and csh/tcsh.
    """
    # Try csh first, then tcsh
    shell_cmd = None
    shell_name = None
    for shell in ['csh', 'tcsh']:
        if _shell_available(shell):
            shell_cmd = shell
            shell_name = shell
            break
    
    if not shell_cmd:
        pytest.skip("csh/tcsh not available")
    
    # Create a key that contains $HOME to test variable expansion
    # In POSIX shells, this should be preserved as-is
    # In csh/tcsh, this might expand to the actual home directory
    test_key = 'api_key_with_$HOME_in_it'
    test_keys = {
        'GEMINI_API_KEY': test_key
    }
    
    script_content = create_api_env_script(test_keys, shell_name)
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.csh', delete=False) as f:
        f.write(script_content)
        script_path = Path(f.name)
    
    try:
        # Source the script and extract the value
        result = subprocess.run(
            [shell_cmd, '-f', '-c', f'source {script_path}; python3 -c "import os; print(os.environ.get(\'GEMINI_API_KEY\', \'\'))"'],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        assert result.returncode == 0, (
            f"Failed to source {shell_name} script: {result.stderr}\n"
            f"Script content:\n{script_content}"
        )
        
        extracted_key = result.stdout.strip()
        # This test will likely FAIL, demonstrating the issue
        assert extracted_key == test_key, (
            f"Variable expansion occurred in {shell_name} despite single quotes!\n"
            f"Expected: {repr(test_key)}\n"
            f"Got: {repr(extracted_key)}\n"
            f"Script content:\n{script_content}\n"
            f"This proves that shlex.quote() (POSIX single quotes) does NOT work\n"
            f"correctly with csh/tcsh, which expand variables even in single quotes."
        )
    finally:
        script_path.unlink()


def test_create_api_env_script_fish_edge_cases():
    """
    Test fish shell with various edge cases that might reveal quoting issues.
    
    Fish shell, while often compatible with POSIX-style quoting, may have
    edge cases with certain character combinations.
    """
    if not _shell_available('fish'):
        pytest.skip("fish shell not available")
    
    edge_cases = [
        'key with spaces',
        "key'with'single'quotes",
        'key"with"double"quotes',
        'key$with$dollars',
        'key\\with\\backslashes',
        'key`with`backticks',
        'key(with)parentheses',
        'key[with]brackets',
        'key{with}braces',
        'key;with;semicolons',
        'key|with|pipes',
        'key&with&ampersands',
        'key<with>redirects',
        'key\nwith\nnewlines',
        'key\twith\ttabs',
    ]
    
    for i, test_key in enumerate(edge_cases):
        test_keys = {
            'TEST_API_KEY': test_key
        }
        
        script_content = create_api_env_script(test_keys, 'fish')
        
        with tempfile.NamedTemporaryFile(mode='w', suffix=f'.fish', delete=False) as f:
            f.write(script_content)
            script_path = Path(f.name)
        
        try:
            # Try to source it
            result = subprocess.run(
                ['fish', '-c', f'source {script_path}; python3 -c "import os; print(os.environ.get(\'TEST_API_KEY\', \'\'))"'],
                capture_output=True,
                text=True,
                timeout=5
            )
            
            if result.returncode != 0:
                pytest.fail(
                    f"Fish shell failed with edge case {i+1}: {repr(test_key)}\n"
                    f"Error: {result.stderr}\n"
                    f"Script content:\n{script_content}"
                )
            
            extracted_key = result.stdout.strip()
            if extracted_key != test_key:
                pytest.fail(
                    f"Fish shell corrupted value for edge case {i+1}: {repr(test_key)}\n"
                    f"Expected: {repr(test_key)}\n"
                    f"Got: {repr(extracted_key)}\n"
                    f"Script content:\n{script_content}"
                )
        finally:
            script_path.unlink()

