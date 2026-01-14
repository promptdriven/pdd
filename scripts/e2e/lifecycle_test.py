"""
Full lifecycle E2E test for PDD Connect remote sessions.

This script tests the complete remote session lifecycle:
1. Register session
2. Send heartbeat
3. List sessions (verify session appears)
4. Deregister session
5. Verify session removed
"""

import asyncio
import httpx
import sys
import os
import socket
import platform
from pathlib import Path
from typing import Dict, Any, Optional

# Import validation helpers
try:
    from scripts.e2e.validation_helpers import (
        validate_register_response,
        validate_list_sessions_response,
        validate_heartbeat_response,
        validate_deregister_response,
        print_validation_result
    )
except ImportError:
    # If running as module, adjust import
    from validation_helpers import (
        validate_register_response,
        validate_list_sessions_response,
        validate_heartbeat_response,
        validate_deregister_response,
        print_validation_result
    )


class RemoteSessionLifecycleTest:
    """
    End-to-end lifecycle test for remote sessions.
    """

    def __init__(
        self,
        jwt_token: str,
        cloud_url: str,
        project_path: str = "/tmp/pdd_e2e_test",
        session_name: Optional[str] = None,
        verbose: bool = True
    ):
        """
        Initialize the lifecycle test.

        Args:
            jwt_token: JWT authentication token
            cloud_url: Base URL for cloud functions
            project_path: Path to test project directory
            session_name: Optional custom session name
            verbose: If True, print progress messages
        """
        self.jwt_token = jwt_token
        self.cloud_url = cloud_url
        self.project_path = project_path
        self.session_name = session_name or "e2e-lifecycle-test"
        self.verbose = verbose
        self.session_id: Optional[str] = None
        self.cloud_session_url: Optional[str] = None

    def _print(self, message: str, symbol: str = ""):
        """Print message if verbose mode is enabled."""
        if self.verbose:
            prefix = f"{symbol} " if symbol else ""
            print(f"{prefix}{message}")

    def _get_metadata(self) -> Dict[str, Any]:
        """Get system metadata for session registration."""
        return {
            "hostname": socket.gethostname(),
            "platform": platform.system(),
            "platformRelease": platform.release(),
            "pythonVersion": sys.version.split()[0],
            "testMode": "e2e"
        }

    async def register_session(self) -> bool:
        """
        Step 1: Register a new remote session.

        Returns:
            bool: True if registration succeeded
        """
        self._print("\n" + "="*60)
        self._print("STEP 1: Register Session", "🔹")
        self._print("="*60)

        endpoint = f"{self.cloud_url}/registerSession"
        headers = {
            "Authorization": f"Bearer {self.jwt_token}",
            "Content-Type": "application/json"
        }
        payload = {
            "projectPath": self.project_path,
            "sessionName": self.session_name,
            "metadata": self._get_metadata()
        }

        self._print(f"Endpoint: {endpoint}")
        self._print(f"Project: {self.project_path}")
        self._print(f"Session name: {self.session_name}")

        try:
            async with httpx.AsyncClient(timeout=30.0) as client:
                response = await client.post(
                    endpoint,
                    json=payload,
                    headers=headers
                )

                if response.status_code >= 400:
                    self._print(f"Registration failed: {response.status_code}", "❌")
                    self._print(f"Response: {response.text}")
                    return False

                data = response.json()

                # Validate response
                is_valid, error = validate_register_response(data)
                if not is_valid:
                    self._print(f"Invalid response: {error}", "❌")
                    return False

                # Store session details
                self.session_id = data["sessionId"]
                self.cloud_session_url = data["cloudUrl"]

                self._print(f"Session ID: {self.session_id}", "✅")
                self._print(f"Cloud URL: {self.cloud_session_url}", "✅")
                self._print("Registration successful!", "✅")
                return True

        except httpx.RequestError as e:
            self._print(f"Network error: {str(e)}", "❌")
            return False
        except Exception as e:
            self._print(f"Unexpected error: {str(e)}", "❌")
            return False

    async def send_heartbeat(self) -> bool:
        """
        Step 2: Send a heartbeat to keep the session alive.

        Returns:
            bool: True if heartbeat succeeded
        """
        self._print("\n" + "="*60)
        self._print("STEP 2: Send Heartbeat", "🔹")
        self._print("="*60)

        if not self.session_id:
            self._print("No session ID - register first", "❌")
            return False

        endpoint = f"{self.cloud_url}/heartbeatSession"
        headers = {
            "Authorization": f"Bearer {self.jwt_token}",
            "Content-Type": "application/json"
        }
        payload = {"sessionId": self.session_id}

        self._print(f"Endpoint: {endpoint}")
        self._print(f"Session ID: {self.session_id}")

        try:
            async with httpx.AsyncClient(timeout=10.0) as client:
                response = await client.post(
                    endpoint,
                    json=payload,
                    headers=headers
                )

                if response.status_code >= 400:
                    self._print(f"Heartbeat failed: {response.status_code}", "❌")
                    self._print(f"Response: {response.text}")
                    return False

                # Response may be empty or contain success message
                if response.text:
                    data = response.json()
                    is_valid, error = validate_heartbeat_response(data)
                    if not is_valid:
                        self._print(f"Invalid response: {error}", "❌")
                        return False

                self._print("Heartbeat sent successfully!", "✅")
                return True

        except httpx.RequestError as e:
            self._print(f"Network error: {str(e)}", "❌")
            return False
        except Exception as e:
            self._print(f"Unexpected error: {str(e)}", "❌")
            return False

    async def list_sessions(self) -> Optional[list]:
        """
        Step 3: List all sessions and verify our session appears.

        Returns:
            list: List of sessions if successful, None otherwise
        """
        self._print("\n" + "="*60)
        self._print("STEP 3: List Sessions", "🔹")
        self._print("="*60)

        endpoint = f"{self.cloud_url}/listSessions"
        headers = {
            "Authorization": f"Bearer {self.jwt_token}",
            "Content-Type": "application/json"
        }

        self._print(f"Endpoint: {endpoint}")

        try:
            async with httpx.AsyncClient(timeout=30.0) as client:
                response = await client.get(endpoint, headers=headers)

                if response.status_code >= 400:
                    self._print(f"List failed: {response.status_code}", "❌")
                    self._print(f"Response: {response.text}")
                    return None

                data = response.json()

                # Validate response
                is_valid, error = validate_list_sessions_response(data)
                if not is_valid:
                    self._print(f"Invalid response: {error}", "❌")
                    return None

                sessions = data["sessions"]
                self._print(f"Found {len(sessions)} session(s)", "✅")

                # Verify our session is in the list
                if self.session_id:
                    found = any(s["sessionId"] == self.session_id for s in sessions)
                    if found:
                        self._print(f"Our session {self.session_id} found in list", "✅")
                    else:
                        self._print(f"Our session {self.session_id} NOT found in list", "⚠️")
                        # This is a warning, not a failure - session might have been cleaned up

                # Print session details
                for session in sessions:
                    self._print(
                        f"  - {session['sessionId'][:20]}... "
                        f"({session['projectName']}) [{session['status']}]"
                    )

                return sessions

        except httpx.RequestError as e:
            self._print(f"Network error: {str(e)}", "❌")
            return None
        except Exception as e:
            self._print(f"Unexpected error: {str(e)}", "❌")
            return None

    async def deregister_session(self) -> bool:
        """
        Step 4: Deregister the session.

        Returns:
            bool: True if deregistration succeeded
        """
        self._print("\n" + "="*60)
        self._print("STEP 4: Deregister Session", "🔹")
        self._print("="*60)

        if not self.session_id:
            self._print("No session ID - nothing to deregister", "⚠️")
            return True  # Not a failure

        endpoint = f"{self.cloud_url}/deregisterSession"
        headers = {
            "Authorization": f"Bearer {self.jwt_token}",
            "Content-Type": "application/json"
        }
        payload = {"sessionId": self.session_id}

        self._print(f"Endpoint: {endpoint}")
        self._print(f"Session ID: {self.session_id}")

        try:
            async with httpx.AsyncClient(timeout=10.0) as client:
                response = await client.request(
                    "DELETE",
                    endpoint,
                    json=payload,
                    headers=headers
                )

                if response.status_code >= 400:
                    self._print(f"Deregister failed: {response.status_code}", "❌")
                    self._print(f"Response: {response.text}")
                    return False

                # Response may be empty or contain success message
                if response.text:
                    data = response.json()
                    is_valid, error = validate_deregister_response(data)
                    if not is_valid:
                        self._print(f"Invalid response: {error}", "❌")
                        return False

                self._print("Session deregistered successfully!", "✅")
                return True

        except httpx.RequestError as e:
            self._print(f"Network error: {str(e)}", "❌")
            return False
        except Exception as e:
            self._print(f"Unexpected error: {str(e)}", "❌")
            return False

    async def verify_cleanup(self) -> bool:
        """
        Step 5: Verify the session has been removed from the list.

        Returns:
            bool: True if session is no longer in the list
        """
        self._print("\n" + "="*60)
        self._print("STEP 5: Verify Cleanup", "🔹")
        self._print("="*60)

        sessions = await self.list_sessions()
        if sessions is None:
            self._print("Failed to list sessions for verification", "❌")
            return False

        # Check if our session is still in the list
        if self.session_id:
            found = any(s["sessionId"] == self.session_id for s in sessions)
            if found:
                self._print(f"Session {self.session_id} still in list after deregister", "❌")
                return False
            else:
                self._print(f"Session {self.session_id} successfully removed", "✅")

        return True

    async def run_full_lifecycle(self) -> bool:
        """
        Run the complete lifecycle test.

        Returns:
            bool: True if all steps passed
        """
        self._print("\n" + "="*80)
        self._print("PDD CONNECT REMOTE SESSION - FULL LIFECYCLE TEST", "🚀")
        self._print("="*80)
        self._print(f"Cloud URL: {self.cloud_url}")
        self._print(f"Project: {self.project_path}")
        self._print(f"Session name: {self.session_name}")

        try:
            # Step 1: Register
            if not await self.register_session():
                self._print("\n❌ FAILED: Registration", "")
                return False

            # Step 2: Heartbeat
            if not await self.send_heartbeat():
                self._print("\n❌ FAILED: Heartbeat", "")
                # Try to cleanup before failing
                await self.deregister_session()
                return False

            # Step 3: List sessions
            sessions = await self.list_sessions()
            if sessions is None:
                self._print("\n❌ FAILED: List sessions", "")
                # Try to cleanup before failing
                await self.deregister_session()
                return False

            # Verify our session is in the list
            if self.session_id:
                found = any(s["sessionId"] == self.session_id for s in sessions)
                if not found:
                    self._print("\n❌ FAILED: Session not found in list", "")
                    return False

            # Step 4: Deregister
            if not await self.deregister_session():
                self._print("\n❌ FAILED: Deregister", "")
                return False

            # Step 5: Verify cleanup
            if not await self.verify_cleanup():
                self._print("\n❌ FAILED: Verification", "")
                return False

            # All steps passed!
            self._print("\n" + "="*80)
            self._print("✅ ALL TESTS PASSED - Full lifecycle completed successfully!", "🎉")
            self._print("="*80)
            return True

        except KeyboardInterrupt:
            self._print("\n\nTest interrupted by user", "⚠️")
            # Try to cleanup
            if self.session_id:
                self._print("Attempting cleanup...")
                await self.deregister_session()
            return False

        except Exception as e:
            self._print(f"\n❌ UNEXPECTED ERROR: {str(e)}", "")
            # Try to cleanup
            if self.session_id:
                self._print("Attempting cleanup...")
                await self.deregister_session()
            return False


async def run_lifecycle_test(
    jwt_token: str,
    cloud_url: str,
    project_path: str = "/tmp/pdd_e2e_test",
    session_name: Optional[str] = None,
    verbose: bool = True
) -> bool:
    """
    Convenience function to run the lifecycle test.

    Args:
        jwt_token: JWT authentication token
        cloud_url: Base URL for cloud functions
        project_path: Path to test project directory
        session_name: Optional custom session name
        verbose: If True, print progress messages

    Returns:
        bool: True if test passed
    """
    test = RemoteSessionLifecycleTest(
        jwt_token=jwt_token,
        cloud_url=cloud_url,
        project_path=project_path,
        session_name=session_name,
        verbose=verbose
    )
    return await test.run_full_lifecycle()


def main():
    """CLI interface for lifecycle test."""
    import argparse

    parser = argparse.ArgumentParser(
        description="E2E lifecycle test for PDD Connect remote sessions"
    )
    parser.add_argument(
        "--jwt-token",
        help="JWT token (or set PDD_JWT_TOKEN env var)"
    )
    parser.add_argument(
        "--cloud-url",
        help="Cloud functions URL (or set PDD_CLOUD_URL env var)"
    )
    parser.add_argument(
        "--local",
        action="store_true",
        help="Use local emulator configuration"
    )
    parser.add_argument(
        "--staging",
        action="store_true",
        help="Use staging configuration"
    )
    parser.add_argument(
        "--project-path",
        default="/tmp/pdd_e2e_test",
        help="Test project path"
    )
    parser.add_argument(
        "--session-name",
        help="Custom session name"
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Suppress progress messages"
    )

    args = parser.parse_args()

    # Determine configuration
    if args.local:
        jwt_token = "mock-jwt-token-for-local-testing"
        cloud_url = os.environ.get(
            "LOCAL_CLOUD_URL",
            "http://localhost:5555/prompt-driven-development/us-central1"
        )
        # Set emulator environment variables
        os.environ["FUNCTIONS_EMULATOR"] = "true"
        os.environ["FIRESTORE_EMULATOR_HOST"] = "localhost:8080"
    elif args.staging:
        jwt_token = os.environ.get("PDD_JWT_TOKEN")
        cloud_url = os.environ.get(
            "STAGING_CLOUD_URL",
            "https://us-central1-prompt-driven-development-stg.cloudfunctions.net"
        )
    else:
        jwt_token = args.jwt_token or os.environ.get("PDD_JWT_TOKEN")
        cloud_url = args.cloud_url or os.environ.get("PDD_CLOUD_URL")

    # Validate required args
    if not jwt_token:
        print("Error: JWT token required (--jwt-token, PDD_JWT_TOKEN env var, or --local)", file=sys.stderr)
        sys.exit(1)

    if not cloud_url:
        print("Error: Cloud URL required (--cloud-url, PDD_CLOUD_URL env var, or --local/--staging)", file=sys.stderr)
        sys.exit(1)

    # Run test
    verbose = not args.quiet

    try:
        success = asyncio.run(run_lifecycle_test(
            jwt_token=jwt_token,
            cloud_url=cloud_url,
            project_path=args.project_path,
            session_name=args.session_name,
            verbose=verbose
        ))

        sys.exit(0 if success else 1)

    except KeyboardInterrupt:
        print("\n\nInterrupted by user", file=sys.stderr)
        sys.exit(130)
    except Exception as e:
        print(f"\n❌ Fatal error: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
