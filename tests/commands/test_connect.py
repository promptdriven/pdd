"""
Test Plan for pdd/commands/connect.py

1.  **Unit Tests (Pytest)**:
    The `connect` command is primarily an orchestration layer that configures and launches a Uvicorn server.
    The logic involves parsing CLI arguments, applying security checks, configuring the environment, and invoking external libraries (`uvicorn`, `webbrowser`).

    We will test the following scenarios using `click.testing.CliRunner` and `unittest.mock`:

    -   **Dependency Check**: Verify the command fails gracefully if `uvicorn` is not installed.
    -   **Default Execution**: Verify correct default values (port 9876, localhost), browser opening, and successful server startup.
    -   **Configuration Options**:
        -   `--no-browser`: Verify browser does not open.
        -   `--frontend-url`: Verify custom URL is used for browser and CORS.
        -   `--port` / `--host`: Verify arguments passed to Uvicorn.
    -   **Smart Port Detection**:
        -   **Port Available**: Verify command uses the requested port when available.
        -   **Default Port In Use**: Verify auto-detection finds next available port.
        -   **User-Specified Port In Use**: Verify error and exit when user explicitly specifies an unavailable port.
        -   **All Ports In Range Unavailable**: Verify error when no ports are available.
    -   **Security Logic**:
        -   **Remote with Token**: Verify allowing remote connections with a token proceeds without confirmation and binds to 0.0.0.0 if host was default.
        -   **Remote without Token (Confirmed)**: Verify warning is displayed and user confirmation allows proceeding.
        -   **Remote without Token (Denied)**: Verify user denial aborts execution.
        -   **Host Binding Warning**: Verify warning when binding to non-localhost without `--allow-remote`.
    -   **Error Handling**:
        -   **App Creation Failure**: Verify graceful exit if `create_app` fails.
        -   **Server Runtime Error**: Verify graceful exit if `uvicorn.run` throws an exception.
        -   **Keyboard Interrupt**: Verify clean shutdown message on Ctrl+C.

2.  **Z3 Formal Verification**:
    -   **Analysis**: The logic in this module is imperative, relying heavily on side effects (IO, network binding, process execution) and external library behavior. The conditional logic is simple (boolean flags).
    -   **Conclusion**: Z3 is not suitable for this type of code. Formal verification is best applied to complex algorithmic logic, state machines, or constraint solving. Here, the complexity lies in integration and configuration, which is best covered by standard unit tests with mocking. Therefore, no Z3 tests are included.
"""

import os
import sys
from unittest.mock import MagicMock, patch
import pytest
from click.testing import CliRunner

# Import the command under test
# We assume the package structure allows this import based on the file path provided
from pdd.commands.connect import connect

@pytest.fixture
def mock_dependencies():
    """
    Fixture to mock external dependencies: uvicorn, webbrowser, create_app, and cloud.
    Returns a dictionary of mocks for verification.
    """
    with patch("pdd.commands.connect.uvicorn") as mock_uvicorn, \
         patch("pdd.commands.connect.webbrowser") as mock_webbrowser, \
         patch("pdd.commands.connect.create_app") as mock_create_app:

        # Setup default mock behaviors
        mock_uvicorn.run.return_value = None
        mock_create_app.return_value = MagicMock(name="FastAPIApp")

        yield {
            "uvicorn": mock_uvicorn,
            "webbrowser": mock_webbrowser,
            "create_app": mock_create_app
        }


@pytest.fixture
def mock_dependencies_with_cloud():
    """
    Fixture with cloud authentication mocked.
    Returns a dictionary of mocks for verification.
    """
    with patch("pdd.commands.connect.uvicorn") as mock_uvicorn, \
         patch("pdd.commands.connect.webbrowser") as mock_webbrowser, \
         patch("pdd.commands.connect.create_app") as mock_create_app, \
         patch("pdd.core.cloud.CloudConfig.get_jwt_token") as mock_get_jwt:

        # Setup default mock behaviors
        mock_uvicorn.run.return_value = None
        mock_create_app.return_value = MagicMock(name="FastAPIApp")
        mock_get_jwt.return_value = None  # Not authenticated by default

        yield {
            "uvicorn": mock_uvicorn,
            "webbrowser": mock_webbrowser,
            "create_app": mock_create_app,
            "get_jwt_token": mock_get_jwt
        }

def test_connect_missing_uvicorn():
    """Test that the command fails if uvicorn is not installed."""
    # Simulate uvicorn being None (ImportError handled in module)
    with patch("pdd.commands.connect.uvicorn", None):
        runner = CliRunner()
        result = runner.invoke(connect)
        
        assert result.exit_code == 1
        assert "Error: 'uvicorn' is not installed" in result.output

def test_connect_defaults(mock_dependencies):
    """Test execution with default arguments."""
    runner = CliRunner()
    with runner.isolated_filesystem():
        with patch("pdd.commands.connect.is_port_available", return_value=True):
            result = runner.invoke(connect)

            assert result.exit_code == 0
            assert "Starting PDD server on http://127.0.0.1:9876" in result.output

            # Verify create_app called with current directory
            mock_dependencies["create_app"].assert_called_once()

            # Verify browser opened
            mock_dependencies["webbrowser"].open.assert_called_with("http://127.0.0.1:9876")

            # Verify uvicorn run
            mock_dependencies["uvicorn"].run.assert_called_once()
            call_kwargs = mock_dependencies["uvicorn"].run.call_args[1]
            assert call_kwargs["host"] == "127.0.0.1"
            assert call_kwargs["port"] == 9876


def test_connect_local_only_flag(mock_dependencies):
    """Test --local-only flag skips cloud registration."""
    runner = CliRunner()
    with runner.isolated_filesystem():
        with patch("pdd.commands.connect.is_port_available", return_value=True):
            result = runner.invoke(connect, ["--local-only"])

            assert result.exit_code == 0
            assert "Running in local-only mode (--local-only flag set)" in result.output
            assert "Starting PDD server on http://127.0.0.1:9876" in result.output

            # Should still run the server
            mock_dependencies["uvicorn"].run.assert_called_once()

def test_connect_no_browser(mock_dependencies):
    """Test --no-browser flag."""
    runner = CliRunner()
    result = runner.invoke(connect, ["--no-browser"])
    
    assert result.exit_code == 0
    mock_dependencies["webbrowser"].open.assert_not_called()

def test_connect_custom_host_port(mock_dependencies):
    """Test custom host and port arguments."""
    runner = CliRunner()
    result = runner.invoke(connect, ["--host", "localhost", "--port", "8000"])
    
    assert result.exit_code == 0
    assert "Starting PDD server on http://localhost:8000" in result.output
    
    call_kwargs = mock_dependencies["uvicorn"].run.call_args[1]
    assert call_kwargs["host"] == "localhost"
    assert call_kwargs["port"] == 8000

def test_connect_custom_frontend_url(mock_dependencies):
    """Test --frontend-url option."""
    custom_url = "http://my-custom-frontend.com"
    runner = CliRunner()
    result = runner.invoke(connect, ["--frontend-url", custom_url])
    
    assert result.exit_code == 0
    assert f"Frontend: {custom_url}" in result.output
    
    # Verify browser opens custom URL
    mock_dependencies["webbrowser"].open.assert_called_with(custom_url)
    
    # Verify custom URL added to CORS origins
    call_kwargs = mock_dependencies["create_app"].call_args[1]
    assert custom_url in call_kwargs["config"].allowed_origins

def test_connect_allow_remote_with_token(mock_dependencies):
    """
    Test --allow-remote with --token.
    Should proceed without confirmation and bind to 0.0.0.0 if host is default.
    """
    runner = CliRunner()
    
    # Patch os.environ to verify token setting
    with patch.dict(os.environ, {}, clear=True):
        result = runner.invoke(connect, ["--allow-remote", "--token", "secret123"])
        
        assert result.exit_code == 0
        assert "Binding to 0.0.0.0 to allow remote connections" in result.output
        
        # Verify host changed to 0.0.0.0
        call_kwargs = mock_dependencies["uvicorn"].run.call_args[1]
        assert call_kwargs["host"] == "0.0.0.0"
        
        # Verify token set in env
        assert os.environ.get("PDD_ACCESS_TOKEN") == "secret123"

def test_connect_allow_remote_no_token_confirmed(mock_dependencies):
    """
    Test --allow-remote without token, user confirms warning.
    """
    runner = CliRunner()
    
    # Simulate user typing 'y'
    result = runner.invoke(connect, ["--allow-remote"], input="y\n")
    
    assert result.exit_code == 0
    assert "SECURITY WARNING" in result.output
    assert "Binding to 0.0.0.0" in result.output
    
    # Should proceed to run uvicorn
    mock_dependencies["uvicorn"].run.assert_called_once()

def test_connect_allow_remote_no_token_denied(mock_dependencies):
    """
    Test --allow-remote without token, user denies warning.
    """
    runner = CliRunner()
    
    # Simulate user typing 'n'
    result = runner.invoke(connect, ["--allow-remote"], input="n\n")
    
    assert result.exit_code == 1
    assert "SECURITY WARNING" in result.output
    assert "Aborted" in result.output or result.exit_code != 0
    
    # Should NOT run uvicorn
    mock_dependencies["uvicorn"].run.assert_not_called()

def test_connect_host_warning(mock_dependencies):
    """
    Test warning when binding to non-localhost without --allow-remote.
    """
    runner = CliRunner()
    result = runner.invoke(connect, ["--host", "192.168.1.5"])
    
    assert result.exit_code == 0
    assert "Warning: Binding to 192.168.1.5 without --allow-remote flag" in result.output
    
    # Should still run
    mock_dependencies["uvicorn"].run.assert_called_once()

def test_connect_create_app_failure(mock_dependencies):
    """Test handling of create_app failure."""
    mock_dependencies["create_app"].side_effect = Exception("Config Error")
    
    runner = CliRunner()
    result = runner.invoke(connect)
    
    assert result.exit_code == 1
    assert "Failed to initialize server: Config Error" in result.output

def test_connect_uvicorn_failure(mock_dependencies):
    """Test handling of uvicorn runtime failure."""
    mock_dependencies["uvicorn"].run.side_effect = Exception("Port in use")
    
    runner = CliRunner()
    result = runner.invoke(connect)
    
    assert result.exit_code == 1
    assert "Server error: Port in use" in result.output

def test_connect_keyboard_interrupt(mock_dependencies):
    """Test graceful shutdown on KeyboardInterrupt."""
    mock_dependencies["uvicorn"].run.side_effect = KeyboardInterrupt()

    runner = CliRunner()
    result = runner.invoke(connect)

    assert result.exit_code == 0
    assert "Server stopping..." in result.output
    assert "Goodbye!" in result.output


# =============================================================================
# Smart Port Detection Tests
# =============================================================================

from pdd.commands.connect import is_port_available, find_available_port


def test_is_port_available_free_port():
    """Test is_port_available returns True for a free port."""
    # Use a high port that's unlikely to be in use
    with patch("pdd.commands.connect.socket.socket") as mock_socket:
        mock_sock_instance = MagicMock()
        mock_socket.return_value.__enter__.return_value = mock_sock_instance
        mock_sock_instance.bind.return_value = None  # No exception = success

        result = is_port_available(59999)
        assert result is True


def test_is_port_available_port_in_use():
    """Test is_port_available returns False when port is in use."""
    with patch("pdd.commands.connect.socket.socket") as mock_socket:
        mock_sock_instance = MagicMock()
        mock_socket.return_value.__enter__.return_value = mock_sock_instance
        mock_sock_instance.bind.side_effect = OSError("Address already in use")

        result = is_port_available(9876)
        assert result is False


def test_find_available_port_first_available():
    """Test find_available_port returns first available port."""
    def mock_is_available(port, host="127.0.0.1"):
        # Simulate: 9876 in use, 9877 available
        return port != 9876

    with patch("pdd.commands.connect.is_port_available", side_effect=mock_is_available):
        result = find_available_port(9876, 9880)
        assert result == 9877


def test_find_available_port_none_available():
    """Test find_available_port returns None when all ports in use."""
    with patch("pdd.commands.connect.is_port_available", return_value=False):
        result = find_available_port(9876, 9880)
        assert result is None


def test_connect_default_port_in_use_auto_detect(mock_dependencies):
    """Test auto-detection of available port when default is in use."""
    def mock_is_available(port, host="127.0.0.1"):
        # Default port 9876 in use, 9877 available
        return port != 9876

    with patch("pdd.commands.connect.is_port_available", side_effect=mock_is_available):
        runner = CliRunner()
        with runner.isolated_filesystem():
            result = runner.invoke(connect)

            assert result.exit_code == 0
            assert "Port 9876 is in use" in result.output
            assert "Using port 9877 instead" in result.output

            # Verify uvicorn called with detected port
            call_kwargs = mock_dependencies["uvicorn"].run.call_args[1]
            assert call_kwargs["port"] == 9877


def test_connect_user_specified_port_in_use_error(mock_dependencies):
    """Test error when user explicitly specifies a port that's in use."""
    with patch("pdd.commands.connect.is_port_available", return_value=False):
        runner = CliRunner()
        with runner.isolated_filesystem():
            # User explicitly specifies --port
            result = runner.invoke(connect, ["--port", "8080"])

            assert result.exit_code == 1
            assert "Error: Port 8080 is already in use" in result.output
            assert "Please specify a different port" in result.output

            # Should NOT run uvicorn
            mock_dependencies["uvicorn"].run.assert_not_called()


def test_connect_all_ports_in_range_unavailable(mock_dependencies):
    """Test error when no ports in the auto-detection range are available."""
    with patch("pdd.commands.connect.is_port_available", return_value=False), \
         patch("pdd.commands.connect.find_available_port", return_value=None):
        runner = CliRunner()
        with runner.isolated_filesystem():
            result = runner.invoke(connect)

            assert result.exit_code == 1
            assert "No available ports found" in result.output

            # Should NOT run uvicorn
            mock_dependencies["uvicorn"].run.assert_not_called()


def test_connect_port_available_uses_requested(mock_dependencies):
    """Test that available port is used without auto-detection message."""
    with patch("pdd.commands.connect.is_port_available", return_value=True):
        runner = CliRunner()
        with runner.isolated_filesystem():
            result = runner.invoke(connect)

            assert result.exit_code == 0
            # Should NOT show port detection messages
            assert "Port 9876 is in use" not in result.output
            assert "Using port" not in result.output

            # Verify uvicorn called with default port
            call_kwargs = mock_dependencies["uvicorn"].run.call_args[1]
            assert call_kwargs["port"] == 9876