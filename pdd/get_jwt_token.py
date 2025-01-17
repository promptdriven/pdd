import asyncio
import json
import os
import sys
import webbrowser
from http.server import BaseHTTPRequestHandler, HTTPServer
from typing import Optional, Tuple
from urllib.parse import parse_qs, urlparse
import secrets

import keyring
import requests
from rich.console import Console
from rich.prompt import Prompt

# Constants
KEYRING_SERVICE_NAME = "pdd_cli_firebase_auth"
FIREBASE_AUTH_DOMAIN = "https://identitytoolkit.googleapis.com/v1/accounts"
FIREBASE_REFRESH_TOKEN_URL = f"{FIREBASE_AUTH_DOMAIN}:token"
FIREBASE_SIGN_IN_WITH_IDP_URL = f"{FIREBASE_AUTH_DOMAIN}:signInWithIdp"
CALLBACK_PORT = 8080
CALLBACK_URL = "https://prompt-driven-development.firebaseapp.com/__/auth/handler"
FIREBASE_API_KEY = "AIzaSyC0w2jwRR82ZFgQs_YXJoEBqnnTH71X6BE"
GITHUB_CLIENT_ID = "Ov23liJ4eSm0y5W1L20u"
# Rich console for pretty printing
console = Console()

# Custom Exceptions
class AuthError(Exception):
    pass

class NetworkError(Exception):
    pass

class TokenError(Exception):
    pass

# Helper Functions
def get_stored_token() -> Optional[Tuple[str, str]]:
    """Retrieve stored Firebase ID token and refresh token from keyring."""
    id_token = keyring.get_password(KEYRING_SERVICE_NAME, "id_token")
    refresh_token = keyring.get_password(KEYRING_SERVICE_NAME, "refresh_token")
    return (id_token, refresh_token) if id_token and refresh_token else None

def store_tokens(id_token: str, refresh_token: str) -> None:
    """Store Firebase ID token and refresh token in keyring."""
    keyring.set_password(KEYRING_SERVICE_NAME, "id_token", id_token)
    keyring.set_password(KEYRING_SERVICE_NAME, "refresh_token", refresh_token)

def clear_tokens() -> None:
    """Clear stored Firebase tokens from keyring."""
    keyring.delete_password(KEYRING_SERVICE_NAME, "id_token")
    keyring.delete_password(KEYRING_SERVICE_NAME, "refresh_token")

def refresh_firebase_token(refresh_token: str, firebase_api_key: str) -> str:
    """Refresh Firebase ID token using refresh token."""
    payload = {
        "grant_type": "refresh_token",
        "refresh_token": refresh_token,
    }
    response = requests.post(
        f"{FIREBASE_REFRESH_TOKEN_URL}?key={firebase_api_key}",
        json=payload,
    )
    if response.status_code != 200:
        raise TokenError("Failed to refresh Firebase ID token")
    return response.json()["id_token"]

# OAuth Callback Server
class CallbackHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        """Handle the callback from GitHub"""
        query_components = parse_qs(urlparse(self.path).query)
        
        # Verify state parameter
        received_state = query_components.get('state', [None])[0]
        if received_state != self.server.expected_state:
            self.send_error(400, "State verification failed")
            return
            
        # Continue with existing code...
        code = query_components.get('code', [None])[0]
        if code:
            self.server.auth_code = code
            self.send_response(200)
            self.send_header('Content-type', 'text/html')
            self.end_headers()
            self.wfile.write(b"Authorization successful! You can close this window.")
        else:
            self.send_error(400, "No authorization code received")

async def start_callback_server() -> str:
    """Start a local server to handle OAuth callback."""
    server = HTTPServer(("localhost", CALLBACK_PORT), CallbackHandler)
    server.auth_code = None
    
    # Generate a random state parameter
    state = secrets.token_urlsafe(16)
    server.expected_state = state
    
    # Construct GitHub OAuth URL with state parameter
    github_oauth_url = (
        "https://github.com/login/oauth/authorize"
        f"?client_id={GITHUB_CLIENT_ID}"
        f"&redirect_uri={CALLBACK_URL}"
        f"&state={state}"
        "&scope=read:user"
    )
    
    webbrowser.open(github_oauth_url)
    
    console.print("[bold green]Waiting for GitHub authentication...[/bold green]")
    while not server.auth_code:
        server.handle_request()
    return server.auth_code

# Main Function
async def get_jwt_token(firebase_api_key: str, github_client_id: str) -> str:
    """
    Get a Firebase ID token using Firebase's built-in GitHub authentication provider.

    Args:
        firebase_api_key: Firebase Web API key
        github_client_id: OAuth client ID for GitHub app

    Returns:
        str: A valid Firebase ID token

    Raises:
        AuthError: If authentication fails
        NetworkError: If there are connectivity issues
        TokenError: If token exchange/refresh fails
    """
    # Check for existing valid token
    stored_tokens = get_stored_token()
    if stored_tokens:
        id_token, refresh_token = stored_tokens
        try:
            # Attempt to refresh token if expired
            id_token = refresh_firebase_token(refresh_token, firebase_api_key)
            store_tokens(id_token, refresh_token)
            return id_token
        except TokenError:
            console.print("[bold yellow]Stored token expired. Starting new authentication flow...[/bold yellow]")
            clear_tokens()

    # Start OAuth flow
    try:
        auth_code = await start_callback_server()
    except Exception as e:
        raise NetworkError(f"Failed to start local server: {e}")

    # Exchange auth code for Firebase ID token
    try:
        payload = {
            "postBody": f"code={auth_code}&providerId=github.com",
            "requestUri": CALLBACK_URL,
            "returnSecureToken": True,
            "client_id": github_client_id,
        }
        response = requests.post(
            f"{FIREBASE_SIGN_IN_WITH_IDP_URL}?key={firebase_api_key}",
            json=payload,
        )
        if response.status_code != 200:
            raise AuthError("Failed to authenticate with GitHub")
        data = response.json()
        id_token = data["idToken"]
        refresh_token = data["refreshToken"]
        store_tokens(id_token, refresh_token)
        return id_token
    except requests.exceptions.RequestException as e:
        raise NetworkError(f"Failed to exchange auth code: {e}")
    except KeyError:
        raise TokenError("Invalid response from Firebase")

# Example Usage
async def main():


    try:
        token = await get_jwt_token(
            firebase_api_key=FIREBASE_API_KEY,
            github_client_id=GITHUB_CLIENT_ID
        )
        console.print(f"[bold green]Successfully authenticated! Token: {token}[/bold green]")
    except AuthError as e:
        console.print(f"[bold red]Authentication failed: {e}[/bold red]")
    except NetworkError as e:
        console.print(f"[bold red]Network error: {e}[/bold red]")
    except TokenError as e:
        console.print(f"[bold red]Token error: {e}[/bold red]")

if __name__ == "__main__":
    asyncio.run(main())