"""
Concurrent sessions E2E test for PDD Connect.

This script tests registering and managing multiple concurrent sessions:
1. Register N sessions in parallel
2. List sessions and verify all N appear
3. Send heartbeats to all sessions in parallel
4. Deregister all sessions in parallel
5. Verify all sessions removed
"""

import asyncio
import httpx
import sys
import os
import socket
import platform
from typing import List, Dict, Any, Optional

# Import validation helpers
try:
    from scripts.e2e.validation_helpers import (
        validate_register_response,
        validate_list_sessions_response
    )
except ImportError:
    from validation_helpers import (
        validate_register_response,
        validate_list_sessions_response
    )


class ConcurrentSessionsTest:
    """
    Test for managing multiple concurrent remote sessions.
    """

    def __init__(
        self,
        jwt_token: str,
        cloud_url: str,
        num_sessions: int = 5,
        base_project_path: str = "/tmp/pdd_e2e_concurrent",
        session_prefix: str = "e2e-concurrent",
        verbose: bool = True
    ):
        """
        Initialize the concurrent sessions test.

        Args:
            jwt_token: JWT authentication token
            cloud_url: Base URL for cloud functions
            num_sessions: Number of sessions to create
            base_project_path: Base path for test projects
            session_prefix: Prefix for session names
            verbose: If True, print progress messages
        """
        self.jwt_token = jwt_token
        self.cloud_url = cloud_url
        self.num_sessions = num_sessions
        self.base_project_path = base_project_path
        self.session_prefix = session_prefix
        self.verbose = verbose
        self.session_ids: List[str] = []
        self.cloud_urls: List[str] = []

    def _print(self, message: str, symbol: str = ""):
        """Print message if verbose mode is enabled."""
        if self.verbose:
            prefix = f"{symbol} " if symbol else ""
            print(f"{prefix}{message}")

    def _get_metadata(self, session_index: int) -> Dict[str, Any]:
        """Get system metadata for session registration."""
        return {
            "hostname": socket.gethostname(),
            "platform": platform.system(),
            "platformRelease": platform.release(),
            "pythonVersion": sys.version.split()[0],
            "testMode": "e2e-concurrent",
            "sessionIndex": session_index
        }

    async def register_single_session(self, session_index: int) -> Optional[Dict[str, str]]:
        """
        Register a single session.

        Args:
            session_index: Index of the session (0 to num_sessions-1)

        Returns:
            dict: Session info (sessionId, cloudUrl) or None if failed
        """
        endpoint = f"{self.cloud_url}/registerSession"
        headers = {
            "Authorization": f"Bearer {self.jwt_token}",
            "Content-Type": "application/json"
        }
        payload = {
            "projectPath": f"{self.base_project_path}/session-{session_index}",
            "sessionName": f"{self.session_prefix}-{session_index}",
            "metadata": self._get_metadata(session_index)
        }

        try:
            async with httpx.AsyncClient(timeout=30.0) as client:
                response = await client.post(
                    endpoint,
                    json=payload,
                    headers=headers
                )

                if response.status_code >= 400:
                    self._print(
                        f"  Session {session_index}: Registration failed ({response.status_code})",
                        "❌"
                    )
                    return None

                data = response.json()

                # Validate response
                is_valid, error = validate_register_response(data)
                if not is_valid:
                    self._print(f"  Session {session_index}: Invalid response - {error}", "❌")
                    return None

                self._print(f"  Session {session_index}: Registered ({data['sessionId'][:16]}...)", "✅")
                return data

        except Exception as e:
            self._print(f"  Session {session_index}: Error - {str(e)}", "❌")
            return None

    async def register_all_sessions(self) -> bool:
        """
        Register all sessions in parallel.

        Returns:
            bool: True if all registrations succeeded
        """
        self._print("\n" + "="*60)
        self._print(f"STEP 1: Register {self.num_sessions} Sessions in Parallel", "🔹")
        self._print("="*60)

        # Create tasks for parallel registration
        tasks = [
            self.register_single_session(i)
            for i in range(self.num_sessions)
        ]

        # Execute in parallel
        results = await asyncio.gather(*tasks)

        # Collect successful registrations
        self.session_ids = []
        self.cloud_urls = []
        for result in results:
            if result:
                self.session_ids.append(result["sessionId"])
                self.cloud_urls.append(result["cloudUrl"])

        success_count = len(self.session_ids)
        self._print(
            f"\nRegistered {success_count}/{self.num_sessions} sessions successfully",
            "✅" if success_count == self.num_sessions else "⚠️"
        )

        return success_count == self.num_sessions

    async def list_and_verify_sessions(self) -> bool:
        """
        List all sessions and verify our sessions appear.

        Returns:
            bool: True if all our sessions are found
        """
        self._print("\n" + "="*60)
        self._print("STEP 2: List Sessions and Verify All Present", "🔹")
        self._print("="*60)

        endpoint = f"{self.cloud_url}/listSessions"
        headers = {
            "Authorization": f"Bearer {self.jwt_token}",
            "Content-Type": "application/json"
        }

        try:
            async with httpx.AsyncClient(timeout=30.0) as client:
                response = await client.get(endpoint, headers=headers)

                if response.status_code >= 400:
                    self._print(f"List failed: {response.status_code}", "❌")
                    return False

                data = response.json()

                # Validate response
                is_valid, error = validate_list_sessions_response(data)
                if not is_valid:
                    self._print(f"Invalid response: {error}", "❌")
                    return False

                sessions = data["sessions"]
                self._print(f"Total sessions found: {len(sessions)}")

                # Verify all our sessions are present
                found_count = 0
                for session_id in self.session_ids:
                    found = any(s["sessionId"] == session_id for s in sessions)
                    if found:
                        found_count += 1
                        self._print(f"  {session_id[:20]}... found", "✅")
                    else:
                        self._print(f"  {session_id[:20]}... NOT found", "❌")

                success = found_count == len(self.session_ids)
                self._print(
                    f"\nFound {found_count}/{len(self.session_ids)} of our sessions",
                    "✅" if success else "❌"
                )

                return success

        except Exception as e:
            self._print(f"Error: {str(e)}", "❌")
            return False

    async def send_heartbeat_single(self, session_id: str, index: int) -> bool:
        """
        Send heartbeat for a single session.

        Args:
            session_id: Session ID
            index: Session index for logging

        Returns:
            bool: True if heartbeat succeeded
        """
        endpoint = f"{self.cloud_url}/heartbeatSession"
        headers = {
            "Authorization": f"Bearer {self.jwt_token}",
            "Content-Type": "application/json"
        }
        payload = {"sessionId": session_id}

        try:
            async with httpx.AsyncClient(timeout=10.0) as client:
                response = await client.post(
                    endpoint,
                    json=payload,
                    headers=headers
                )

                if response.status_code >= 400:
                    self._print(f"  Session {index}: Heartbeat failed ({response.status_code})", "❌")
                    return False

                self._print(f"  Session {index}: Heartbeat sent ({session_id[:16]}...)", "✅")
                return True

        except Exception as e:
            self._print(f"  Session {index}: Error - {str(e)}", "❌")
            return False

    async def send_all_heartbeats(self) -> bool:
        """
        Send heartbeats to all sessions in parallel.

        Returns:
            bool: True if all heartbeats succeeded
        """
        self._print("\n" + "="*60)
        self._print(f"STEP 3: Send Heartbeats to {len(self.session_ids)} Sessions", "🔹")
        self._print("="*60)

        # Create tasks for parallel heartbeats
        tasks = [
            self.send_heartbeat_single(session_id, i)
            for i, session_id in enumerate(self.session_ids)
        ]

        # Execute in parallel
        results = await asyncio.gather(*tasks)

        success_count = sum(results)
        self._print(
            f"\nSent {success_count}/{len(self.session_ids)} heartbeats successfully",
            "✅" if success_count == len(self.session_ids) else "⚠️"
        )

        return success_count == len(self.session_ids)

    async def deregister_single_session(self, session_id: str, index: int) -> bool:
        """
        Deregister a single session.

        Args:
            session_id: Session ID
            index: Session index for logging

        Returns:
            bool: True if deregistration succeeded
        """
        endpoint = f"{self.cloud_url}/deregisterSession"
        headers = {
            "Authorization": f"Bearer {self.jwt_token}",
            "Content-Type": "application/json"
        }
        payload = {"sessionId": session_id}

        try:
            async with httpx.AsyncClient(timeout=10.0) as client:
                response = await client.request(
                    "DELETE",
                    endpoint,
                    json=payload,
                    headers=headers
                )

                if response.status_code >= 400:
                    self._print(f"  Session {index}: Deregister failed ({response.status_code})", "❌")
                    return False

                self._print(f"  Session {index}: Deregistered ({session_id[:16]}...)", "✅")
                return True

        except Exception as e:
            self._print(f"  Session {index}: Error - {str(e)}", "❌")
            return False

    async def deregister_all_sessions(self) -> bool:
        """
        Deregister all sessions in parallel.

        Returns:
            bool: True if all deregistrations succeeded
        """
        self._print("\n" + "="*60)
        self._print(f"STEP 4: Deregister {len(self.session_ids)} Sessions", "🔹")
        self._print("="*60)

        # Create tasks for parallel deregistration
        tasks = [
            self.deregister_single_session(session_id, i)
            for i, session_id in enumerate(self.session_ids)
        ]

        # Execute in parallel
        results = await asyncio.gather(*tasks)

        success_count = sum(results)
        self._print(
            f"\nDeregistered {success_count}/{len(self.session_ids)} sessions successfully",
            "✅" if success_count == len(self.session_ids) else "⚠️"
        )

        return success_count == len(self.session_ids)

    async def verify_all_removed(self) -> bool:
        """
        Verify all sessions have been removed.

        Returns:
            bool: True if all sessions are removed
        """
        self._print("\n" + "="*60)
        self._print("STEP 5: Verify All Sessions Removed", "🔹")
        self._print("="*60)

        endpoint = f"{self.cloud_url}/listSessions"
        headers = {
            "Authorization": f"Bearer {self.jwt_token}",
            "Content-Type": "application/json"
        }

        try:
            async with httpx.AsyncClient(timeout=30.0) as client:
                response = await client.get(endpoint, headers=headers)

                if response.status_code >= 400:
                    self._print(f"List failed: {response.status_code}", "❌")
                    return False

                data = response.json()
                sessions = data.get("sessions", [])

                # Check if any of our sessions still exist
                remaining = [
                    sid for sid in self.session_ids
                    if any(s["sessionId"] == sid for s in sessions)
                ]

                if remaining:
                    self._print(f"{len(remaining)} session(s) still present:", "❌")
                    for sid in remaining:
                        self._print(f"  - {sid}")
                    return False
                else:
                    self._print("All sessions successfully removed", "✅")
                    return True

        except Exception as e:
            self._print(f"Error: {str(e)}", "❌")
            return False

    async def run_concurrent_test(self) -> bool:
        """
        Run the complete concurrent sessions test.

        Returns:
            bool: True if all steps passed
        """
        self._print("\n" + "="*80)
        self._print("PDD CONNECT REMOTE SESSION - CONCURRENT SESSIONS TEST", "🚀")
        self._print("="*80)
        self._print(f"Cloud URL: {self.cloud_url}")
        self._print(f"Number of sessions: {self.num_sessions}")
        self._print(f"Session prefix: {self.session_prefix}")

        try:
            # Step 1: Register all sessions
            if not await self.register_all_sessions():
                self._print("\n❌ FAILED: Registration", "")
                # Try to cleanup
                if self.session_ids:
                    self._print("Attempting cleanup of registered sessions...")
                    await self.deregister_all_sessions()
                return False

            # Step 2: List and verify
            if not await self.list_and_verify_sessions():
                self._print("\n❌ FAILED: Verification", "")
                # Try to cleanup
                await self.deregister_all_sessions()
                return False

            # Step 3: Send heartbeats
            if not await self.send_all_heartbeats():
                self._print("\n❌ FAILED: Heartbeats", "")
                # Try to cleanup
                await self.deregister_all_sessions()
                return False

            # Step 4: Deregister all
            if not await self.deregister_all_sessions():
                self._print("\n❌ FAILED: Deregistration", "")
                return False

            # Step 5: Verify cleanup
            if not await self.verify_all_removed():
                self._print("\n❌ FAILED: Cleanup verification", "")
                return False

            # All steps passed!
            self._print("\n" + "="*80)
            self._print(
                f"✅ ALL TESTS PASSED - {self.num_sessions} concurrent sessions handled successfully!",
                "🎉"
            )
            self._print("="*80)
            return True

        except KeyboardInterrupt:
            self._print("\n\nTest interrupted by user", "⚠️")
            # Try to cleanup
            if self.session_ids:
                self._print("Attempting cleanup...")
                await self.deregister_all_sessions()
            return False

        except Exception as e:
            self._print(f"\n❌ UNEXPECTED ERROR: {str(e)}", "")
            # Try to cleanup
            if self.session_ids:
                self._print("Attempting cleanup...")
                await self.deregister_all_sessions()
            return False


async def run_concurrent_test(
    jwt_token: str,
    cloud_url: str,
    num_sessions: int = 5,
    verbose: bool = True
) -> bool:
    """
    Convenience function to run the concurrent sessions test.

    Args:
        jwt_token: JWT authentication token
        cloud_url: Base URL for cloud functions
        num_sessions: Number of sessions to create
        verbose: If True, print progress messages

    Returns:
        bool: True if test passed
    """
    test = ConcurrentSessionsTest(
        jwt_token=jwt_token,
        cloud_url=cloud_url,
        num_sessions=num_sessions,
        verbose=verbose
    )
    return await test.run_concurrent_test()


def main():
    """CLI interface for concurrent sessions test."""
    import argparse

    parser = argparse.ArgumentParser(
        description="E2E concurrent sessions test for PDD Connect"
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
        "--num-sessions",
        type=int,
        default=5,
        help="Number of concurrent sessions to create (default: 5)"
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
        print("Error: JWT token required", file=sys.stderr)
        sys.exit(1)

    if not cloud_url:
        print("Error: Cloud URL required", file=sys.stderr)
        sys.exit(1)

    # Run test
    verbose = not args.quiet

    try:
        success = asyncio.run(run_concurrent_test(
            jwt_token=jwt_token,
            cloud_url=cloud_url,
            num_sessions=args.num_sessions,
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
