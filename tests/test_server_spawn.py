"""
Regression tests for spawned terminal job completion callback port.

Issue: When pdd connect auto-detects a different port (because default 9876 is busy),
the spawned terminal callback uses the hardcoded port 9876 instead of the actual
server port, causing the callback to fail silently.
"""
import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path


def test_create_app_with_custom_port_configures_commands_router():
    """
    Regression test: create_app with custom port should configure the
    commands router to use that port for spawned terminal callbacks.

    Bug: commands.py had its own _server_port = 9876 that was never updated,
    so spawned terminal callbacks always used port 9876 even when the server
    was running on a different port.
    """
    from pdd.server.app import create_app, get_server_port
    from pdd.server.models import ServerConfig
    from pdd.server.routes.commands import get_server_port as commands_get_server_port

    custom_port = 9999
    config = ServerConfig(port=custom_port)

    app = create_app(Path("/tmp/test"), config=config)

    # The app.py get_server_port should return the custom port
    assert get_server_port() == custom_port, \
        f"app.py get_server_port() should return {custom_port}, got {get_server_port()}"

    # CRITICAL: The commands.py get_server_port must ALSO return the custom port
    # This is what the spawn_terminal endpoint uses for the callback URL
    assert commands_get_server_port() == custom_port, \
        f"commands.py get_server_port() must return the configured port {custom_port}, " \
        f"not the default 9876. Got {commands_get_server_port()}"


def test_spawn_terminal_uses_configured_port():
    """
    Test that spawn_terminal endpoint generates callback URL with correct port.
    """
    from fastapi.testclient import TestClient
    from pdd.server.app import create_app
    from pdd.server.models import ServerConfig

    custom_port = 8888
    config = ServerConfig(port=custom_port)

    app = create_app(Path.cwd(), config=config)
    client = TestClient(app)

    # Patch TerminalSpawner via app.py's own module reference to avoid
    # sys.modules identity issues when server conftest cleans pdd.server.* modules
    import pdd.server.app as app_mod
    with patch.object(app_mod.commands, 'TerminalSpawner') as mock_spawner:
        mock_spawner.spawn.return_value = True

        response = client.post("/api/v1/commands/spawn-terminal", json={
            "command": "sync",
            "args": {"basename": "test"},
            "options": {}
        })

        # Verify spawn was called with the correct port
        assert mock_spawner.spawn.called, "TerminalSpawner.spawn should have been called"
        call_kwargs = mock_spawner.spawn.call_args[1]
        assert call_kwargs.get('server_port') == custom_port, \
            f"Expected server_port={custom_port}, got {call_kwargs.get('server_port')}"


def test_default_port_still_works():
    """
    Sanity check: When no custom port is specified, default 9876 should be used.
    """
    from pdd.server.app import create_app, get_server_port
    from pdd.server.routes.commands import get_server_port as commands_get_server_port

    # Create app without custom config (uses defaults)
    app = create_app(Path("/tmp/test"))

    # Both should return the default port
    assert get_server_port() == 9876, \
        f"Default port should be 9876, got {get_server_port()}"
    assert commands_get_server_port() == 9876, \
        f"commands.py default port should be 9876, got {commands_get_server_port()}"
