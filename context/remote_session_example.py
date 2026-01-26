import asyncio
import os
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

# --- Setup for Example Context ---
# Ensure we can import the pdd package relative to this script
project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

# Import the module to be demonstrated
from pdd.remote_session import (
    RemoteSessionManager,
    RemoteSessionError,
    SessionInfo,
    CommandInfo,
    get_active_session_manager,
    set_active_session_manager
)

# Mock CloudConfig to avoid needing real cloud endpoints/credentials for this example
# In a real application, you would configure your environment variables instead.
with patch("pdd.remote_session.CloudConfig") as MockCloudConfig:
    # Setup mock return values for endpoint URLs
    MockCloudConfig.get_endpoint_url.side_effect = lambda endpoint: f"https://api.pdd.example.com/{endpoint}"

    async def main():
        print("=== PDD Remote Session Manager Example ===\n")

        # 1. Initialize the Manager
        # In a real app, this token comes from CloudConfig.get_jwt_token()
        jwt_token = "ey_mock_jwt_token_example"
        project_path = Path("/home/user/projects/my-app")
        manager = RemoteSessionManager(jwt_token=jwt_token, project_path=project_path)

        # Set as the global active manager (optional, but good practice for singletons)
        set_active_session_manager(manager)
        print(f"Manager initialized. Active global manager: {get_active_session_manager() is not None}")

        # 2. Register a Session
        # The cloud generates the access URL - no public URL, host, or port needed
        print("\n--- Registering Session ---")

        mock_register_response = {
            "sessionId": "sess_12345_abcde",
            "cloudUrl": "https://pdd.dev/connect/sess_12345_abcde"
        }

        # We patch httpx.AsyncClient within the context of the register method
        with patch("httpx.AsyncClient") as MockClient:
            mock_instance = MockClient.return_value.__aenter__.return_value
            mock_instance.post.return_value = MagicMock(
                status_code=200,
                json=lambda: mock_register_response
            )

            try:
                # New API: register() returns the cloud URL, no parameters needed
                cloud_url = await manager.register(session_name="My Remote Dev Session")
                print(f"Session registered successfully!")
                print(f"Cloud URL: {cloud_url}")
                print(f"Session ID: {manager.session_id}")
            except RemoteSessionError as e:
                print(f"Registration failed: {e}")
                return

        # 3. Start Heartbeat
        # This runs in the background to keep the session alive in the cloud
        # Key features:
        # - First heartbeat is sent IMMEDIATELY on startup (prevents early timeout)
        # - Uses 5-second delay after first heartbeat, then 30-second intervals
        # - 3 retries with exponential backoff on network errors
        # - Automatic JWT token refresh on 401 errors
        print("\n--- Starting Heartbeat ---")
        manager.start_heartbeat()
        print("Heartbeat task started in background.")
        print("  - Sends first heartbeat immediately")
        print("  - Retries 3 times with exponential backoff on errors")
        print("  - Auto-refreshes JWT token on 401 (expiration)")

        # Simulate some runtime...
        await asyncio.sleep(0.1)

        # 3b. Token Refresh Example (handled automatically by heartbeat/polling)
        # The manager's _refresh_token() method is called automatically when
        # heartbeat or get_pending_commands() receives a 401 response.
        # This uses the Firebase refresh token stored in the system keyring.
        print("\n--- Token Refresh (automatic on 401) ---")
        print("Token refresh is automatic - no manual intervention needed.")
        print("If the JWT expires (~1 hour), the manager will:")
        print("  1. Detect 401 error from cloud API")
        print("  2. Call _refresh_token() to get new JWT")
        print("  3. Retry the failed request with new token")

        # 4. List Active Sessions
        # This is a static method to see what sessions are available for this user
        print("\n--- Listing Sessions ---")

        mock_list_response = {
            "sessions": [
                {
                    "sessionId": "sess_12345_abcde",
                    "cloudUrl": "https://pdd.dev/connect/sess_12345_abcde",
                    "projectName": "my-app",
                    "projectPath": "/home/user/projects/my-app",
                    "createdAt": "2023-10-27T10:00:00Z",
                    "lastHeartbeat": "2023-10-27T10:05:00Z",
                    "status": "active",
                    "metadata": {"platform": "Linux"}
                },
                {
                    "sessionId": "sess_98765_zyxwv",
                    "cloudUrl": "https://pdd.dev/connect/sess_98765_zyxwv",
                    "projectName": "legacy-api",
                    "projectPath": "/var/www/legacy",
                    "createdAt": "2023-10-26T15:30:00Z",
                    "lastHeartbeat": "2023-10-26T15:35:00Z",
                    "status": "stale",
                    "metadata": {"platform": "Darwin"}
                }
            ]
        }

        with patch("httpx.AsyncClient") as MockClient:
            mock_instance = MockClient.return_value.__aenter__.return_value
            mock_instance.get.return_value = MagicMock(
                status_code=200,
                json=lambda: mock_list_response
            )

            try:
                sessions = await RemoteSessionManager.list_sessions(jwt_token)
                for s in sessions:
                    print(f"- [{s.status.upper()}] {s.project_name} ({s.session_id})")
                    print(f"  Cloud URL: {s.cloud_url}")
            except RemoteSessionError as e:
                print(f"Failed to list sessions: {e}")

        # 5. Cleanup / Deregister
        # Always clean up when the application shuts down
        print("\n--- Deregistering Session ---")

        with patch("httpx.AsyncClient") as MockClient:
            mock_instance = MockClient.return_value.__aenter__.return_value
            mock_instance.request.return_value = MagicMock(status_code=200)

            await manager.deregister()
            print("Session deregistered and heartbeat stopped.")

            # Verify internal state is cleared
            if manager.session_id is None:
                print("Manager state cleared successfully.")

    if __name__ == "__main__":
        asyncio.run(main())
