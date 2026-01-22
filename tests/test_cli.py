import sys
import types
import pytest
from unittest.mock import MagicMock, patch
import importlib

# We need to mock the dependencies BEFORE importing pdd.cli to ensure isolation
# and to capture the side effects of the module-level code.

@pytest.fixture
def mock_pdd_dependencies():
    """
    Sets up mocks for all modules that pdd.cli imports.
    This prevents actual imports and allows us to verify interactions.
    """
    # Create a dictionary of modules to mock
    modules_to_mock = [
        'pdd.core',
        'pdd.core.cli',
        'pdd.commands',
        'pdd.commands.templates',
        'pdd.auto_update',
        'pdd.code_generator_main',
        'pdd.context_generator_main',
        'pdd.cmd_test_main',
        'pdd.fix_main',
        'pdd.split_main',
        'pdd.change_main',
        'pdd.update_main',
        'pdd.sync_main',
        'pdd.auto_deps_main',
        'pdd.detect_change_main',
        'pdd.conflicts_main',
        'pdd.bug_main',
        'pdd.crash_main',
        'pdd.trace_main',
        'pdd.agentic_test',
        'pdd.preprocess_main',
        'pdd.construct_paths',
        'pdd.fix_verification_main',
        'pdd.core.errors',
        'pdd.install_completion',
        'pdd.core.utils',
    ]

    mock_modules = {}
    original_modules = {}

    # Setup mocks
    for mod_name in modules_to_mock:
        if mod_name in sys.modules:
            original_modules[mod_name] = sys.modules[mod_name]
        
        mock_mod = MagicMock()
        sys.modules[mod_name] = mock_mod
        mock_modules[mod_name] = mock_mod

    # Specific setup for attributes accessed in pdd.cli
    # pdd.core.cli.cli
    mock_modules['pdd.core.cli'].cli = MagicMock(name='cli_group')
    mock_modules['pdd.core.cli'].process_commands = MagicMock(name='process_commands')
    
    # pdd.commands.register_commands
    mock_modules['pdd.commands'].register_commands = MagicMock(name='register_commands')

    # Setup dummy attributes for re-exports to verify they are passed through
    mock_modules['pdd.commands.templates'].templates_group = "mock_templates_group"
    mock_modules['pdd.auto_update'].auto_update = "mock_auto_update"
    mock_modules['pdd.code_generator_main'].code_generator_main = "mock_code_generator_main"
    # ... (we can check existence for others, explicit values help debugging)

    yield mock_modules

    # Teardown: Restore original modules
    for mod_name in modules_to_mock:
        if mod_name in original_modules:
            sys.modules[mod_name] = original_modules[mod_name]
        else:
            del sys.modules[mod_name]
            
    # Also remove pdd.cli from sys.modules so it gets re-imported cleanly next time
    if 'pdd.cli' in sys.modules:
        del sys.modules['pdd.cli']


def test_cli_registers_commands_on_import(mock_pdd_dependencies):
    """
    Test that importing pdd.cli calls register_commands(cli).
    """
    # Arrange
    mock_cli_group = mock_pdd_dependencies['pdd.core.cli'].cli
    mock_register = mock_pdd_dependencies['pdd.commands'].register_commands

    # Act
    # Ensure pdd.cli is not in sys.modules so import triggers execution
    if 'pdd.cli' in sys.modules:
        del sys.modules['pdd.cli']
    import pdd.cli

    # Assert
    mock_register.assert_called_once_with(mock_cli_group)


def test_cli_re_exports_symbols(mock_pdd_dependencies):
    """
    Test that pdd.cli re-exports the expected symbols from submodules.
    """
    # Arrange
    # Define the list of expected exports based on the code under test
    expected_exports = [
        'templates_group',
        'auto_update',
        'code_generator_main',
        'context_generator_main',
        'cmd_test_main',
        'fix_main',
        'split_main',
        'change_main',
        'update_main',
        'sync_main',
        'auto_deps_main',
        'detect_change_main',
        'conflicts_main',
        'bug_main',
        'crash_main',
        'trace_main',
        'agentic_test_main',
        'preprocess_main',
        'construct_paths',
        'fix_verification_main',
        'console',
        'install_completion',
        '_should_show_onboarding_reminder',
        'process_commands'
    ]

    # Act
    if 'pdd.cli' in sys.modules:
        del sys.modules['pdd.cli']
    import pdd.cli

    # Assert
    for symbol in expected_exports:
        assert hasattr(pdd.cli, symbol), f"pdd.cli is missing re-export: {symbol}"


def test_cli_main_execution_logic(mock_pdd_dependencies):
    """
    Test the logic that would run under if __name__ == \"__main__\":
    Since we cannot easily invoke __main__ directly without subprocesses,
    we verify the components that would be called are present and correct.
    """
    # Arrange
    mock_cli_group = mock_pdd_dependencies['pdd.core.cli'].cli
    
    # Act
    if 'pdd.cli' in sys.modules:
        del sys.modules['pdd.cli']
    import pdd.cli

    # Assert
    # We verify that the 'cli' object imported into pdd.cli is indeed the one we mocked.
    # This confirms that if `cli()` were called in main, it would be our mock.
    assert pdd.cli.cli is mock_cli_group
    
    # If we were to simulate main:
    with patch.object(pdd.cli, 'cli') as mocked_main_cli:
        # We can't easily trigger the if block without executing the file as a script.
        # But we can verify the object is callable.
        assert callable(pdd.cli.cli)