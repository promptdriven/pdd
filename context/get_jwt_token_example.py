import asyncio
import os
from pathlib import Path
from pdd.get_jwt_token import get_jwt_token, AuthError, NetworkError, TokenError, UserCancelledError, RateLimitError

# Constants for the CLI application (replace with your actual values)
def _load_firebase_api_key(pdd_env: str) -> str:
    """Load the Firebase API key from the appropriate env file if not already set."""
    # If already in env, return it
    env_key = os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY")
    if env_key:
        return env_key

    # Choose env file based on target environment
    project_root = Path(__file__).resolve().parents[2]
    if pdd_env == "staging":
        candidate = project_root / "frontend" / ".env.staging"
    elif pdd_env == "prod":
        candidate = project_root / "frontend" / ".env.production"
    else:
        candidate = project_root / ".env"

    if candidate.exists():
        try:
            with candidate.open("r", encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if line.startswith("NEXT_PUBLIC_FIREBASE_API_KEY="):
                        return line.split("=", 1)[1].strip().strip('"').strip("'")
        except Exception:
            pass

    return ""

pdd_env = os.environ.get("PDD_ENV") or "local"
FIREBASE_API_KEY = _load_firebase_api_key(pdd_env)  # Your Firebase Web API key
GITHUB_CLIENT_ID = os.environ.get(f"GITHUB_CLIENT_ID_{pdd_env.upper()}") or os.environ.get("GITHUB_CLIENT_ID")  # Env-specific GitHub OAuth App client ID if provided
APP_NAME = "Prompt Driven Development"  # A unique name for your application

# Append environment to APP_NAME to isolate credentials and pick env-specific token vars
if pdd_env and pdd_env not in ["local", "prod"]:  # explicit envs get suffix
    APP_NAME = f"{APP_NAME} ({pdd_env})"
elif pdd_env == "staging":
    APP_NAME = f"{APP_NAME} (staging)"

# Target env-specific token variable (e.g., JWT_TOKEN_STAGING)
ENV_TOKEN_VAR = f"JWT_TOKEN_{pdd_env.upper()}"

async def main():
    """
    Demonstrates how to use the get_jwt_token function to authenticate with Firebase using GitHub Device Flow.
    """
    print("Starting authentication process...")

    if not FIREBASE_API_KEY:
        print("Error: NEXT_PUBLIC_FIREBASE_API_KEY is not set and could not be loaded for this environment.")
        print(f"Ensure the correct Firebase Web API key is available for PDD_ENV={pdd_env}.")
        return
    token = None  # Initialize token variable

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
        return  # Exit early on auth failure
    except NetworkError as e:
        print(f"Network error: {e}")
        print("Please check your internet connection and try again.")
        return  # Exit early on network failure
    except TokenError as e:
        print(f"Token error: {e}")
        print("There was an issue with token exchange or refresh. Please try re-authenticating.")
        return  # Exit early on token failure
    except RateLimitError as e:
        print(f"Rate limit exceeded: {e}")
        print("Too many authentication attempts. Please try again later.")
        return  # Exit early on rate limit failure

    # Only proceed if we have a valid token
    if token is None:
        print("Failed to obtain token. Exiting.")
        return

    # Replace the JWT token in .env with env-specific key plus a generic fallback
    env_file_path = ".env"
    new_token_line_specific = f"{ENV_TOKEN_VAR}={token}\n"
    new_token_line_generic = f"JWT_TOKEN={token}\n"

    # Read the existing lines from the .env file
    if os.path.exists(env_file_path):
        with open(env_file_path, "r") as file:
            lines = file.readlines()
    else:
        lines = []

    # Write the new token to the .env file, replacing the old ones if they exist
    with open(env_file_path, "w") as file:
        specific_replaced = False
        generic_replaced = False
        for line in lines:
            if line.startswith(f"{ENV_TOKEN_VAR}="):
                file.write(new_token_line_specific)
                specific_replaced = True
            elif line.startswith("JWT_TOKEN="):
                file.write(new_token_line_generic)
                generic_replaced = True
            else:
                file.write(line)
        if not specific_replaced:
            file.write(new_token_line_specific)
        if not generic_replaced:
            file.write(new_token_line_generic)

    print(f"{ENV_TOKEN_VAR} and JWT_TOKEN have been updated in {env_file_path}")

if __name__ == "__main__":
    asyncio.run(main())
