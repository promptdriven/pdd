import os
import json
import time
import requests
from pathlib import Path
from rich import print
from cryptography.fernet import Fernet

# Constants
HOME_DIR = Path.home()
PDD_DIR = HOME_DIR / ".pdd"
REFRESH_TOKEN_PATH = PDD_DIR / "refresh_token"
ID_TOKEN_PATH = PDD_DIR / "id_token"
ENCRYPTION_KEY_PATH = PDD_DIR / "encryption_key"
FIREBASE_API_KEY = "YOUR_FIREBASE_API_KEY"  # Replace with your Firebase API key
FIREBASE_REFRESH_URL = f"https://securetoken.googleapis.com/v1/token?key={FIREBASE_API_KEY}"

# Ensure the .pdd directory exists
PDD_DIR.mkdir(exist_ok=True)

# Load or generate encryption key
if not ENCRYPTION_KEY_PATH.exists():
    key = Fernet.generate_key()
    ENCRYPTION_KEY_PATH.write_bytes(key)
else:
    key = ENCRYPTION_KEY_PATH.read_bytes()

cipher_suite = Fernet(key)

def encrypt(data: str) -> bytes:
    """Encrypts a string using the cipher suite."""
    return cipher_suite.encrypt(data.encode())

def decrypt(data: bytes) -> str:
    """Decrypts bytes using the cipher suite."""
    return cipher_suite.decrypt(data).decode()

def get_jwt_token() -> str | None:
    """Fetches or refreshes a JWT token securely."""
    # Check if refresh token exists
    if not REFRESH_TOKEN_PATH.exists():
        print("[bold red]Error:[/bold red] No refresh token found. Please log in via GitHub at [link=https://prompt-driven-development.firebaseapp.com]PDD Cloud[/link].")
        return None

    # Read and decrypt the refresh token
    refresh_token = decrypt(REFRESH_TOKEN_PATH.read_bytes())

    # Check if ID token exists and is less than 50 minutes old
    if ID_TOKEN_PATH.exists():
        id_token_data = json.loads(decrypt(ID_TOKEN_PATH.read_bytes()))
        if time.time() - id_token_data['timestamp'] < 3000:  # 50 minutes in seconds
            return id_token_data['id_token']

    # Refresh the ID token
    try:
        response = requests.post(FIREBASE_REFRESH_URL, data={
            'grant_type': 'refresh_token',
            'refresh_token': refresh_token
        })
        response.raise_for_status()
        token_data = response.json()
        new_id_token = token_data['id_token']
        new_refresh_token = token_data['refresh_token']

        # Save the new tokens
        REFRESH_TOKEN_PATH.write_bytes(encrypt(new_refresh_token))
        ID_TOKEN_PATH.write_bytes(encrypt(json.dumps({
            'id_token': new_id_token,
            'timestamp': time.time()
        })))

        return new_id_token

    except requests.exceptions.RequestException as e:
        print(f"[bold red]Error:[/bold red] Failed to refresh token: {e}")
        return None

# Example usage
if __name__ == "__main__":
    token = get_jwt_token()
    if token:
        print(f"[bold green]JWT Token:[/bold green] {token}")