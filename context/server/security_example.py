import uvicorn
from pathlib import Path
from fastapi import FastAPI, Depends, HTTPException
from fastapi.responses import JSONResponse

# Import the security module
# In a real project, this would be: from pdd.server.security import ...
# For this example, we assume the module is in the same directory or python path
from pdd.server.security import (
    PathValidator,
    configure_cors,
    create_token_dependency,
    SecurityLoggingMiddleware,
    SecurityError
)

# 1. Setup the application and basic configuration
app = FastAPI(title="Secure PDD Server Example")

# Define the project root (usually where your main script or project file is)
PROJECT_ROOT = Path(__file__).parent.resolve()

# Initialize the PathValidator
# We can optionally pass custom blacklist patterns
validator = PathValidator(
    project_root=PROJECT_ROOT,
    blacklist_patterns=[
        ".git", 
        ".env*", 
        "secrets.json", 
        "*.pem"
    ]
)

# 2. Configure Middleware
# Add logging middleware to track requests
app.add_middleware(SecurityLoggingMiddleware)

# Configure CORS to allow specific frontend origins
configure_cors(app, allowed_origins=["http://localhost:3000", "http://localhost:8080"])

# 3. Configure Authentication
# Create a dependency that requires a specific token
# In production, load this from an environment variable
API_TOKEN = "super-secret-dev-token"
auth_dependency = create_token_dependency(API_TOKEN)


# 4. Define Routes

@app.get("/public/status")
async def get_status():
    """A public endpoint that requires no authentication."""
    return {"status": "running", "mode": "secure"}


@app.get("/secure/data", dependencies=[Depends(auth_dependency)])
async def get_secure_data():
    """
    An endpoint protected by the token dependency.
    Requests without 'Authorization: Bearer super-secret-dev-token' will fail.
    """
    return {"data": "This is protected information", "secret_code": 12345}


@app.get("/files/read")
async def read_file(path: str, auth=Depends(auth_dependency)):
    """
    An endpoint that demonstrates safe file path handling.
    It uses PathValidator to prevent directory traversal attacks.
    """
    try:
        # Validate the user-provided path
        # This will raise SecurityError if the path tries to go up (../) 
        # or access blacklisted files (.env, .git)
        safe_path = validator.validate(path)
        
        # If we get here, the path is safe and absolute
        if not safe_path.exists():
            raise HTTPException(status_code=404, detail="File not found")
            
        if not safe_path.is_file():
            raise HTTPException(status_code=400, detail="Path is not a file")
            
        # In a real app, you might read the file content here
        return {
            "status": "success",
            "safe_path": str(safe_path),
            "message": "Path is valid and safe to access"
        }

    except SecurityError as e:
        # Handle security violations specifically
        # We return a 403 Forbidden for security issues
        return JSONResponse(
            status_code=403,
            content={
                "error": e.code,
                "message": e.message
            }
        )

# 5. Run the example
if __name__ == "__main__":
    print(f"Starting server with root: {PROJECT_ROOT}")
    print(f"Try accessing: http://127.0.0.1:8000/files/read?path=README.md")
    print(f"Try attacking: http://127.0.0.1:8000/files/read?path=../../etc/passwd")
    
    uvicorn.run(app, host="127.0.0.1", port=8000)