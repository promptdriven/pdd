import asyncio
os = __import__('os')
sys = __import__('sys')
from unittest.mock import MagicMock
from fastapi import FastAPI
from fastapi.testclient import TestClient

# --- Mocking Dependencies for Standalone Execution ---
# Since this module relies on specific internal 'pdd' modules and environment variables,
# we mock them here to make this example runnable without the full package structure.

# 1. Mock Environment Variables
os.environ["GITHUB_CLIENT_ID"] = "mock_github_client_id"
os.environ["NEXT_PUBLIC_FIREBASE_API_KEY"] = "mock_firebase_key"

# 2. Mock the 'pdd.get_jwt_token' module
# CRITICAL: Save originals BEFORE patching to avoid polluting sys.modules during pytest collection
# See context/pytest_isolation_example.py Pattern 7 for the correct approach
_saved = {}
_saved["pdd"] = sys.modules.get("pdd")
_saved["pdd.get_jwt_token"] = sys.modules.get("pdd.get_jwt_token")

sys.modules["pdd"] = MagicMock()
sys.modules["pdd.get_jwt_token"] = MagicMock()

# Mock specific classes/functions used in auth.py
mock_device_flow = MagicMock()
mock_device_flow.request_device_code.return_value = {
    "device_code": "mock_device_code",
    "user_code": "ABCD-1234",
    "verification_uri": "https://github.com/login/device",
    "expires_in": 900,
    "interval": 5
}
# Mock the polling function to simulate success immediately
async def mock_poll(*args):
    return "mock_github_token"
mock_device_flow.poll_for_token = mock_poll

sys.modules["pdd.get_jwt_token"].DeviceFlow = MagicMock(return_value=mock_device_flow)
sys.modules["pdd.get_jwt_token"].FirebaseAuthenticator = MagicMock()
sys.modules["pdd.get_jwt_token"]._cache_jwt = MagicMock()

# RESTORE originals immediately after setting up mocks
# This prevents polluting sys.modules for other test files during pytest collection
for key, original in _saved.items():
    if original is None:
        sys.modules.pop(key, None)
    else:
        sys.modules[key] = original

# --- Import the Module ---
# Assuming the module code is saved as 'auth_routes.py' in the same directory
try:
    from auth_routes import router as auth_router
except ImportError:
    # If running directly where the file might be named differently
    # This block is just for the example runner to find the code provided in the prompt
    import importlib.util
    spec = importlib.util.spec_from_file_location("auth_routes", "auth_routes.py")
    if spec and spec.loader:
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        auth_router = module.router
    else:
        # Fallback: create a dummy router if the file is not found to prevent crash during extraction
        from fastapi import APIRouter
        auth_router = APIRouter()

# --- Application Setup ---

app = FastAPI()
app.include_router(auth_router)

client = TestClient(app)

def run_example_flow():
    """Demonstrates the authentication flow using the TestClient."""
    print("--- 1. Check Initial Auth Status ---")
    response = client.get("/api/v1/auth/status")
    print(f"Status Code: {response.status_code}")
    print(f"Response: {response.json()}")
    # Expected: authenticated=False (unless you actually have a token cached locally)

    print("\n--- 2. Initiate Login (GitHub Device Flow) ---")
    # This triggers the background task and would normally open a browser
    response = client.post("/api/v1/auth/login")
    print(f"Status Code: {response.status_code}")
    data = response.json()
    print(f"Response: {data}")
    
    if data.get("success"):
        poll_id = data["poll_id"]
        print(f"\n[User Action Required] Go to {data['verification_uri']} and enter {data['user_code']}")
        
        print(f"\n--- 3. Poll Login Status (Poll ID: {poll_id}) ---")
        # In a real scenario, the frontend polls this every few seconds
        # Since we mocked the background task to run immediately, this might show pending or completed
        # depending on how fast the background task executes relative to this call.
        
        # Give the background task a moment to 'run' (in the test client context)
        import time
        time.sleep(0.1) 
        
        poll_response = client.get(f"/api/v1/auth/login/poll/{poll_id}")
        print(f"Poll Status: {poll_response.json()}")

    print("\n--- 4. Logout ---")
    response = client.post("/api/v1/auth/logout")
    print(f"Status Code: {response.status_code}")
    print(f"Response: {response.json()}")

    print("\n--- 5. Check Status After Logout ---")
    response = client.get("/api/v1/auth/status")
    print(f"Response: {response.json()}")

if __name__ == "__main__":
    run_example_flow()