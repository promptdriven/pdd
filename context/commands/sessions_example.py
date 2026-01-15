import asyncio
import sys
from unittest.mock import MagicMock, patch
from click.testing import CliRunner
from rich.console import Console

# In a real scenario, you would import directly from the package:
# from pdd.commands.sessions import sessions

# For this standalone example, we will mock the dependencies that the module expects
# before importing the module itself, or we assume the module is available in the path.
# Since we cannot easily replicate the entire 'pdd' package structure here,
# we will demonstrate how to test/invoke the commands assuming the module is imported.

# --- MOCKING DEPENDENCIES START ---
# We need to mock the internal pdd modules that sessions.py imports
sys.modules["pdd"] = MagicMock()
sys.modules["pdd.core"] = MagicMock()
sys.modules["pdd.core.cloud"] = MagicMock()
sys.modules["pdd.remote_session"] = MagicMock()
sys.modules["pdd.utils"] = MagicMock()

# Mock CloudConfig
mock_cloud_config = MagicMock()
mock_cloud_config.get_jwt_token.return_value = "fake-jwt-token-123"
sys.modules["pdd.core.cloud"].CloudConfig = mock_cloud_config

# Mock RemoteSessionManager
mock_session_manager = MagicMock()


# Define a dummy session object structure - using new API field names
class DummySession:
    def __init__(self, session_id, project_name, cloud_url, status, last_heartbeat):
        self.session_id = session_id
        self.project_name = project_name
        self.cloud_url = cloud_url
        self.status = status
        self.last_heartbeat = last_heartbeat

    def dict(self):
        return self.__dict__


# Setup mock return values
fake_sessions = [
    DummySession("sess_abc123", "my-project", "https://pdd.dev/connect/abc123", "active", "2 mins ago"),
    DummySession("sess_xyz789", "demo-app", "https://pdd.dev/connect/xyz789", "stale", "2 days ago")
]


# Async mock for list_sessions
async def mock_list_sessions(token):
    return fake_sessions


# Async mock for get_session
async def mock_get_session(token, session_id):
    for s in fake_sessions:
        if s.session_id == session_id:
            return s
    return None


mock_session_manager.list_sessions = mock_list_sessions
mock_session_manager.get_session = mock_get_session
sys.modules["pdd.remote_session"].RemoteSessionManager = mock_session_manager


# Mock handle_error
def mock_handle_error(e):
    print(f"Error handled: {e}")


sys.modules["pdd.utils"].handle_error = mock_handle_error
# --- MOCKING DEPENDENCIES END ---

# Now we can import the module code provided in the prompt.
# In a real project, this would just be: from pdd.commands.sessions import sessions
# Here, we assume the code provided in <code_module> is saved as 'sessions_module.py'
try:
    import sessions_module as sessions_cmd
except ImportError:
    # Fallback if running directly where the file might be named differently
    # This block is just for the sake of the example runner finding the code
    pass


def run_example():
    """
    Demonstrates how to invoke the 'sessions' CLI commands programmatically.
    This is useful for testing or integration scripts.
    """
    console = Console()
    runner = CliRunner()

    console.print("[bold green]=== PDD Sessions Command Example ===[/bold green]")
    console.print("This script mocks the backend API calls to demonstrate CLI output.\n")

    # 1. List Sessions (Table Output)
    console.print("[bold blue]1. Running 'sessions list' (Table format)[/bold blue]")
    result_table = runner.invoke(sessions_cmd.sessions, ["list"])

    if result_table.exit_code == 0:
        print(result_table.output)
    else:
        console.print("[red]Command failed![/red]")
        print(result_table.output)

    # 2. List Sessions (JSON Output)
    console.print("[bold blue]2. Running 'sessions list --json'[/bold blue]")
    result_json = runner.invoke(sessions_cmd.sessions, ["list", "--json"])

    if result_json.exit_code == 0:
        print(result_json.output)
    else:
        console.print("[red]Command failed![/red]")

    # 3. Session Info (Specific ID)
    target_id = "sess_abc123"
    console.print(f"[bold blue]3. Running 'sessions info {target_id}'[/bold blue]")
    result_info = runner.invoke(sessions_cmd.sessions, ["info", target_id])

    if result_info.exit_code == 0:
        print(result_info.output)
    else:
        console.print("[red]Command failed![/red]")

    # 4. Session Info (Not Found)
    missing_id = "sess_missing"
    console.print(f"[bold blue]4. Running 'sessions info {missing_id}' (Expect Not Found)[/bold blue]")
    result_missing = runner.invoke(sessions_cmd.sessions, ["info", missing_id])

    print(result_missing.output)


if __name__ == "__main__":
    # Patching asyncio.run to work in this script if needed, though the module uses it internally.
    # The module calls asyncio.run() inside the command functions.
    # Since we mocked the async methods on the manager, the module's asyncio.run call will execute our sync mocks wrapped in async.

    # We need to ensure the module uses the mocked objects we set up in sys.modules
    # If the module was already imported before mocks, we'd need to reload it.
    # For this standalone example, the import happens after mocks.

    if 'sessions_module' in sys.modules or 'sessions_cmd' in locals():
        run_example()
    else:
        print("Error: Could not import the sessions module. Please ensure the code is saved as 'sessions_module.py' in the same directory.")
