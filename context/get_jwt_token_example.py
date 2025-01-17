import asyncio
import os
from pdd.get_jwt_token import get_jwt_token, AuthError, NetworkError, TokenError, UserCancelledError, RateLimitError

# Constants for the CLI application (replace with your actual values)
FIREBASE_API_KEY = os.environ.get("REACT_APP_FIREBASE_API_KEY")  # Your Firebase Web API key
GITHUB_CLIENT_ID = os.environ.get("GITHUB_CLIENT_ID")  # Your GitHub OAuth App's client ID
APP_NAME = "Prompt Driven Development"  # A unique name for your application

async def main():
    """
    Demonstrates how to use the get_jwt_token function to authenticate with Firebase using GitHub Device Flow.
    """
    print("Starting authentication process...")

    try:
        # Attempt to get a valid Firebase ID token
        token = await get_jwt_token(
            firebase_api_key=FIREBASE_API_KEY,
            github_client_id=GITHUB_CLIENT_ID,
            app_name=APP_NAME
        )

        print(f"Authentication successful! Firebase ID token: {token}")
        print("You can now use this token to make authenticated requests to your Firebase backend.")

    except AuthError as e:
        print(f"Authentication failed: {e}")
        if isinstance(e, UserCancelledError):
            print("The authentication process was cancelled by the user.")
    except NetworkError as e:
        print(f"Network error: {e}")
        print("Please check your internet connection and try again.")
    except TokenError as e:
        print(f"Token error: {e}")
        print("There was an issue with token exchange or refresh. Please try re-authenticating.")
    except RateLimitError as e:
        print(f"Rate limit exceeded: {e}")
        print("Too many authentication attempts. Please try again later.")

if __name__ == "__main__":
    asyncio.run(main())