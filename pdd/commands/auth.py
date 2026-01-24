from __future__ import annotations

import asyncio
import base64
import json
import os
import sys
import time
from pathlib import Path
from typing import Optional, Dict, Any

import click
from rich.console import Console

# Internal imports
try:
    from ..auth_service import (
        get_auth_status,
        logout as service_logout,
        verify_auth,
        JWT_CACHE_FILE,
    )
    from ..get_jwt_token import (
        get_jwt_token,
        AuthError,
        NetworkError,
        TokenError,
        UserCancelledError,
        RateLimitError,
    )
except ImportError:
    pass

console = Console()

# Constants
PDD_ENV = os.environ.get("PDD_ENV", "local")


def _load_firebase_api_key() -> str:
    """Load the Firebase API key from environment or .env files."""
    # 1. Check direct env var
    env_key = os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY")
    if env_key:
        return env_key

    # 2. Check .env files in current directory
    candidates = [Path(".env"), Path(".env.local")]
    
    for candidate in candidates:
        if candidate.exists():
            try:
                content = candidate.read_text(encoding="utf-8")
                for line in content.splitlines():
                    if line.strip().startswith("NEXT_PUBLIC_FIREBASE_API_KEY="):
                        return line.split("=", 1)[1].strip().strip('"').strip("'")
            except Exception:
                continue
                
    return ""


def _get_client_id() -> Optional[str]:
    """Get the GitHub Client ID for the current environment."""
    return os.environ.get(f"GITHUB_CLIENT_ID_{PDD_ENV.upper()}") or os.environ.get("GITHUB_CLIENT_ID")


def _decode_jwt_payload(token: str) -> Dict[str, Any]:
    """Decode JWT payload without verification to extract claims."""
    try:
        # JWT is header.payload.signature
        parts = token.split(".")
        if len(parts) != 3:
            return {}
        
        payload = parts[1]
        # Add padding if needed
        padding = len(payload) % 4
        if padding:
            payload += "=" * (4 - padding)
            
        decoded = base64.urlsafe_b64decode(payload)
        return json.loads(decoded)
    except Exception:
        return {}


@click.group("auth")
def auth_group():
    """Manage PDD Cloud authentication."""
    pass


@auth_group.command("login")
@click.option(
    "--browser/--no-browser",
    default=None,
    help="Control browser opening (auto-detect if not specified)"
)
def login(browser: Optional[bool]):
    """Authenticate with PDD Cloud via GitHub."""

    api_key = _load_firebase_api_key()
    if not api_key:
        console.print("[red]Error: NEXT_PUBLIC_FIREBASE_API_KEY not found.[/red]")
        console.print("Please set it in your environment or .env file.")
        sys.exit(1)

    client_id = _get_client_id()
    app_name = "PDD CLI"

    async def run_login():
        try:
            # Import remote session detection
            from ..core.remote_session import should_skip_browser

            # Determine if browser should be skipped
            skip_browser, reason = should_skip_browser(explicit_flag=browser)

            if skip_browser:
                console.print(f"[yellow]Note: {reason}[/yellow]")
                console.print("[yellow]Please open the authentication URL manually in a browser.[/yellow]")

            # Pass no_browser parameter to get_jwt_token
            token = await get_jwt_token(
                firebase_api_key=api_key,
                github_client_id=client_id,
                app_name=app_name,
                no_browser=skip_browser
            )
            
            if not token:
                console.print("[red]Authentication failed: No token received.[/red]")
                sys.exit(1)
                
            # Decode token to get expiration
            payload = _decode_jwt_payload(token)
            expires_at = payload.get("exp")

            # Validate expires_at is a valid numeric timestamp (Issue #379)
            # If missing or invalid, use 1-hour fallback (matches _cache_jwt() pattern)
            if not isinstance(expires_at, (int, float)) or expires_at <= 0:
                expires_at = time.time() + 3600  # 1-hour fallback
                console.print("[yellow]Warning: Token missing expiration, using 1-hour default.[/yellow]")

            # Ensure cache directory exists
            if not JWT_CACHE_FILE.parent.exists():
                JWT_CACHE_FILE.parent.mkdir(parents=True, exist_ok=True)
            
            # Save token and expiration to cache
            # We store id_token for retrieval and expires_at for auth_service checks
            cache_data = {
                "id_token": token,
                "expires_at": expires_at
            }
            
            JWT_CACHE_FILE.write_text(json.dumps(cache_data))
            
            console.print("[green]Successfully authenticated to PDD Cloud.[/green]")
            
        except AuthError as e:
            console.print(f"[red]Authentication failed: {e}[/red]")
            sys.exit(1)
        except NetworkError as e:
            console.print(f"[red]Network error: {e}[/red]")
            sys.exit(1)
        except TokenError as e:
            console.print(f"[red]Token error: {e}[/red]")
            sys.exit(1)
        except UserCancelledError:
            console.print("[yellow]Authentication cancelled by user.[/yellow]")
            sys.exit(1)
        except RateLimitError as e:
            console.print(f"[red]Rate limit exceeded: {e}[/red]")
            sys.exit(1)
        except Exception as e:
            console.print(f"[red]An unexpected error occurred: {e}[/red]")
            sys.exit(1)

    asyncio.run(run_login())


@auth_group.command("status")
@click.option(
    "--verify",
    is_flag=True,
    default=False,
    help="Verify authentication by attempting to refresh the token"
)
def status(verify: bool):
    """Check current authentication status.

    By default, shows the current auth state based on cached credentials.
    Use --verify to actually test if authentication will work.
    """
    auth_status = get_auth_status()

    if not auth_status.get("authenticated"):
        console.print("[yellow]Not authenticated.[/yellow]")
        console.print("Run: [bold]pdd auth login[/bold]")
        sys.exit(1)

    username = "Unknown"
    expires_in_minutes = None

    # If we have a cached token, try to extract user info
    if auth_status.get("cached") and JWT_CACHE_FILE.exists():
        try:
            data = json.loads(JWT_CACHE_FILE.read_text())
            token = data.get("id_token")
            if token:
                payload = _decode_jwt_payload(token)
                username = payload.get("email") or payload.get("sub") or "Unknown"

            # Calculate time remaining
            expires_at = auth_status.get("expires_at")
            if expires_at:
                expires_in_minutes = int((expires_at - time.time()) / 60)
        except Exception:
            pass

        # Token is cached and valid
        console.print(f"Authenticated as: [bold green]{username}[/bold green]")
        if expires_in_minutes is not None:
            console.print(f"Token expires in: {expires_in_minutes} minutes")
        sys.exit(0)

    else:
        # Only refresh token exists, JWT expired or missing
        # Try to get username from expired token if it exists
        if JWT_CACHE_FILE.exists():
            try:
                data = json.loads(JWT_CACHE_FILE.read_text())
                token = data.get("id_token")
                if token:
                    payload = _decode_jwt_payload(token)
                    username = payload.get("email") or payload.get("sub") or "Unknown"
            except Exception:
                pass

        if not verify:
            # Show warning that token may fail
            console.print(f"Session for: [bold yellow]{username}[/bold yellow] (token expired, will refresh on next use)")
            console.print("[yellow]⚠ If cloud operations fail, run:[/yellow] [bold]pdd auth login[/bold]")
            sys.exit(0)
        else:
            # Actually verify by attempting refresh
            console.print("Verifying authentication...")

            async def do_verify():
                return await verify_auth()

            result = asyncio.run(do_verify())

            if result.get("valid"):
                verified_username = result.get("username") or username
                console.print(f"[green]✓[/green] Authenticated as: [bold green]{verified_username}[/bold green]")
                console.print("[green]Token refreshed successfully.[/green]")
                sys.exit(0)
            else:
                error = result.get("error", "Unknown error")
                console.print(f"[red]✗ Authentication verification failed:[/red] {error}")
                if result.get("needs_reauth"):
                    console.print("Run: [bold]pdd auth logout && pdd auth login[/bold]")
                sys.exit(1)


@auth_group.command("logout")
def logout_cmd():
    """Log out of PDD Cloud."""
    success, error = service_logout()
    if success:
        console.print("Logged out of PDD Cloud.")
    else:
        console.print(f"[red]Failed to logout: {error}[/red]")
        # We don't exit with 1 here as partial logout might have occurred
        # and the user is effectively logged out locally anyway.


@auth_group.command("token")
@click.option("--format", "output_format", type=click.Choice(["raw", "json"]), default="raw", help="Output format.")
def token_cmd(output_format: str):
    """Print the current authentication token."""

    token_str = None
    expires_at = None

    # Attempt to read valid token from cache
    if JWT_CACHE_FILE.exists():
        try:
            data = json.loads(JWT_CACHE_FILE.read_text())
            cached_token = data.get("id_token")
            cached_exp = data.get("expires_at")

            # Simple expiry check
            if cached_token and cached_exp and cached_exp > time.time():
                token_str = cached_token
                expires_at = cached_exp
        except Exception:
            pass

    if not token_str:
        # Removed err=True because rich.console.Console.print does not support it
        console.print("[red]No valid token available. Please login.[/red]")
        sys.exit(1)

    if output_format == "json":
        output = {
            "token": token_str,
            "expires_at": expires_at
        }
        console.print_json(data=output)
    else:
        console.print(token_str)


@auth_group.command("clear-cache")
def clear_cache():
    """Clear the JWT token cache.

    This is useful when:
    - Switching between environments (staging vs production)
    - Experiencing authentication issues
    - JWT token audience mismatch errors

    After clearing the cache, you'll need to re-authenticate
    with 'pdd auth login' or source the appropriate environment
    setup script (e.g., setup_staging_env.sh).
    """
    if not JWT_CACHE_FILE.exists():
        console.print("[yellow]No JWT cache found at ~/.pdd/jwt_cache[/yellow]")
        console.print("Nothing to clear.")
        return

    try:
        # Try to read cache before deleting to show what was cached
        cache_data = json.loads(JWT_CACHE_FILE.read_text())
        token = cache_data.get("id_token") or cache_data.get("jwt")
        if token:
            payload = _decode_jwt_payload(token)
            aud = payload.get("aud") or payload.get("firebase", {}).get("aud")
            exp = payload.get("exp")

            console.print("[dim]Cached token info:[/dim]")
            if aud:
                console.print(f"  Audience: {aud}")
            if exp:
                if exp > time.time():
                    time_remaining = int((exp - time.time()) / 60)
                    console.print(f"  Expires in: {time_remaining} minutes")
                else:
                    console.print("  Status: [red]Expired[/red]")
    except Exception:
        # If we can't read the cache, that's fine - just proceed with deletion
        pass

    # Delete the cache file
    try:
        JWT_CACHE_FILE.unlink()
        console.print("[green]✓[/green] JWT cache cleared successfully")
        console.print()
        console.print("[dim]To re-authenticate:[/dim]")
        console.print("  - For production: [bold]pdd auth login[/bold]")
        console.print("  - For staging: [bold]source setup_staging_env.sh[/bold]")
    except OSError as e:
        console.print(f"[red]Failed to clear cache: {e}[/red]")
        sys.exit(1)