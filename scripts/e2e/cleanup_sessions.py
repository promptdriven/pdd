"""
Session cleanup utility for E2E testing.

This module provides utilities to clean up all remote sessions for a user,
ensuring no stale sessions remain after testing.
"""

import asyncio
import httpx
import sys
import os
from typing import List, Dict, Any


async def list_all_sessions(jwt_token: str, cloud_url: str) -> List[Dict[str, Any]]:
    """
    List all sessions for the authenticated user.

    Args:
        jwt_token: JWT authentication token
        cloud_url: Base URL for cloud functions

    Returns:
        List of session dictionaries

    Raises:
        httpx.HTTPStatusError: If API request fails
    """
    endpoint = f"{cloud_url}/listSessions"
    headers = {
        "Authorization": f"Bearer {jwt_token}",
        "Content-Type": "application/json"
    }

    async with httpx.AsyncClient(timeout=30.0) as client:
        response = await client.get(endpoint, headers=headers)
        response.raise_for_status()
        data = response.json()
        return data.get("sessions", [])


async def deregister_session(jwt_token: str, cloud_url: str, session_id: str) -> bool:
    """
    Deregister a single session.

    Args:
        jwt_token: JWT authentication token
        cloud_url: Base URL for cloud functions
        session_id: Session ID to deregister

    Returns:
        bool: True if deregistration succeeded

    Raises:
        httpx.HTTPStatusError: If API request fails
    """
    endpoint = f"{cloud_url}/deregisterSession"
    headers = {
        "Authorization": f"Bearer {jwt_token}",
        "Content-Type": "application/json"
    }
    payload = {"sessionId": session_id}

    async with httpx.AsyncClient(timeout=10.0) as client:
        response = await client.request(
            "DELETE",
            endpoint,
            json=payload,
            headers=headers
        )
        response.raise_for_status()
        return True


async def cleanup_all_sessions(
    jwt_token: str,
    cloud_url: str,
    verbose: bool = True,
    dry_run: bool = False
) -> Dict[str, Any]:
    """
    Clean up all sessions for the authenticated user.

    Args:
        jwt_token: JWT authentication token
        cloud_url: Base URL for cloud functions
        verbose: If True, print progress messages
        dry_run: If True, list sessions but don't deregister

    Returns:
        dict: Cleanup summary with counts and any errors
    """
    # List all sessions
    if verbose:
        print(f"Fetching sessions from {cloud_url}...")

    try:
        sessions = await list_all_sessions(jwt_token, cloud_url)
    except httpx.HTTPStatusError as e:
        error_msg = f"Failed to list sessions: {e.response.status_code} {e.response.text}"
        if verbose:
            print(f"❌ {error_msg}")
        return {
            "success": False,
            "error": error_msg,
            "sessions_found": 0,
            "sessions_cleaned": 0,
            "failed": []
        }
    except Exception as e:
        error_msg = f"Network error: {str(e)}"
        if verbose:
            print(f"❌ {error_msg}")
        return {
            "success": False,
            "error": error_msg,
            "sessions_found": 0,
            "sessions_cleaned": 0,
            "failed": []
        }

    num_sessions = len(sessions)
    if verbose:
        print(f"Found {num_sessions} session(s) to clean up")

    if num_sessions == 0:
        if verbose:
            print("✅ No sessions to clean up")
        return {
            "success": True,
            "sessions_found": 0,
            "sessions_cleaned": 0,
            "failed": []
        }

    # Dry run mode - just list sessions
    if dry_run:
        if verbose:
            print("\n🔍 Dry run mode - sessions would be cleaned:")
            for session in sessions:
                session_id = session.get("sessionId", "unknown")
                project_name = session.get("projectName", "unknown")
                status = session.get("status", "unknown")
                print(f"  - {session_id} ({project_name}) [{status}]")
        return {
            "success": True,
            "sessions_found": num_sessions,
            "sessions_cleaned": 0,
            "dry_run": True,
            "sessions": sessions
        }

    # Deregister each session
    cleaned = 0
    failed = []

    for session in sessions:
        session_id = session.get("sessionId", "unknown")
        project_name = session.get("projectName", "unknown")

        try:
            await deregister_session(jwt_token, cloud_url, session_id)
            cleaned += 1
            if verbose:
                print(f"  ✅ Deregistered: {session_id} ({project_name})")

        except httpx.HTTPStatusError as e:
            error = f"{session_id}: {e.response.status_code} {e.response.text}"
            failed.append(error)
            if verbose:
                print(f"  ❌ Failed to deregister {session_id}: {e.response.status_code}")

        except Exception as e:
            error = f"{session_id}: {str(e)}"
            failed.append(error)
            if verbose:
                print(f"  ❌ Failed to deregister {session_id}: {e}")

    # Print summary
    if verbose:
        print(f"\n{'='*60}")
        print(f"Cleanup Summary:")
        print(f"  Sessions found: {num_sessions}")
        print(f"  Successfully cleaned: {cleaned}")
        print(f"  Failed: {len(failed)}")
        if failed:
            print(f"\nFailed sessions:")
            for error in failed:
                print(f"  - {error}")

    return {
        "success": len(failed) == 0,
        "sessions_found": num_sessions,
        "sessions_cleaned": cleaned,
        "failed": failed
    }


async def cleanup_sessions_by_prefix(
    jwt_token: str,
    cloud_url: str,
    prefix: str,
    verbose: bool = True,
    dry_run: bool = False
) -> Dict[str, Any]:
    """
    Clean up sessions matching a specific project name prefix.

    Useful for cleaning up only test sessions without affecting real sessions.

    Args:
        jwt_token: JWT authentication token
        cloud_url: Base URL for cloud functions
        prefix: Project name prefix to match (e.g., "e2e-test")
        verbose: If True, print progress messages
        dry_run: If True, list sessions but don't deregister

    Returns:
        dict: Cleanup summary
    """
    # List all sessions
    if verbose:
        print(f"Fetching sessions matching prefix '{prefix}'...")

    try:
        all_sessions = await list_all_sessions(jwt_token, cloud_url)
    except Exception as e:
        error_msg = f"Failed to list sessions: {str(e)}"
        if verbose:
            print(f"❌ {error_msg}")
        return {
            "success": False,
            "error": error_msg,
            "sessions_found": 0,
            "sessions_cleaned": 0,
            "failed": []
        }

    # Filter sessions by prefix
    matching_sessions = [
        s for s in all_sessions
        if s.get("projectName", "").startswith(prefix)
    ]

    num_sessions = len(matching_sessions)
    if verbose:
        print(f"Found {num_sessions} session(s) matching prefix '{prefix}'")
        print(f"(Total sessions: {len(all_sessions)})")

    if num_sessions == 0:
        if verbose:
            print("✅ No matching sessions to clean up")
        return {
            "success": True,
            "sessions_found": 0,
            "sessions_cleaned": 0,
            "failed": []
        }

    # Use the main cleanup function with filtered sessions
    if dry_run:
        if verbose:
            print("\n🔍 Dry run mode - sessions would be cleaned:")
            for session in matching_sessions:
                session_id = session.get("sessionId", "unknown")
                project_name = session.get("projectName", "unknown")
                status = session.get("status", "unknown")
                print(f"  - {session_id} ({project_name}) [{status}]")
        return {
            "success": True,
            "sessions_found": num_sessions,
            "sessions_cleaned": 0,
            "dry_run": True,
            "sessions": matching_sessions
        }

    # Deregister matching sessions
    cleaned = 0
    failed = []

    for session in matching_sessions:
        session_id = session.get("sessionId", "unknown")
        project_name = session.get("projectName", "unknown")

        try:
            await deregister_session(jwt_token, cloud_url, session_id)
            cleaned += 1
            if verbose:
                print(f"  ✅ Deregistered: {session_id} ({project_name})")

        except Exception as e:
            error = f"{session_id}: {str(e)}"
            failed.append(error)
            if verbose:
                print(f"  ❌ Failed to deregister {session_id}: {e}")

    # Print summary
    if verbose:
        print(f"\n{'='*60}")
        print(f"Cleanup Summary (prefix: '{prefix}'):")
        print(f"  Matching sessions found: {num_sessions}")
        print(f"  Successfully cleaned: {cleaned}")
        print(f"  Failed: {len(failed)}")

    return {
        "success": len(failed) == 0,
        "sessions_found": num_sessions,
        "sessions_cleaned": cleaned,
        "failed": failed
    }


def main():
    """CLI interface for session cleanup."""
    import argparse

    parser = argparse.ArgumentParser(
        description="Clean up PDD Connect remote sessions"
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
        "--prefix",
        help="Only clean up sessions with this project name prefix"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="List sessions but don't delete them"
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Suppress progress messages"
    )

    args = parser.parse_args()

    # Get JWT token
    jwt_token = args.jwt_token or os.environ.get("PDD_JWT_TOKEN")
    if not jwt_token:
        print("Error: JWT token required (--jwt-token or PDD_JWT_TOKEN env var)", file=sys.stderr)
        sys.exit(1)

    # Get cloud URL
    cloud_url = args.cloud_url or os.environ.get("PDD_CLOUD_URL")
    if not cloud_url:
        print("Error: Cloud URL required (--cloud-url or PDD_CLOUD_URL env var)", file=sys.stderr)
        sys.exit(1)

    # Run cleanup
    verbose = not args.quiet

    try:
        if args.prefix:
            result = asyncio.run(cleanup_sessions_by_prefix(
                jwt_token,
                cloud_url,
                args.prefix,
                verbose=verbose,
                dry_run=args.dry_run
            ))
        else:
            result = asyncio.run(cleanup_all_sessions(
                jwt_token,
                cloud_url,
                verbose=verbose,
                dry_run=args.dry_run
            ))

        # Exit with appropriate code
        if result["success"]:
            sys.exit(0)
        else:
            sys.exit(1)

    except KeyboardInterrupt:
        print("\n\nInterrupted by user", file=sys.stderr)
        sys.exit(130)
    except Exception as e:
        print(f"\n❌ Unexpected error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
