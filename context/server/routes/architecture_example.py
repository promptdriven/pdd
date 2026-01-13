import asyncio
import uvicorn
from fastapi import FastAPI
from fastapi.testclient import TestClient

# Assuming the module is saved as pdd/server/routes/architecture.py
# In a real app, you would use: from pdd.server.routes.architecture import router as architecture_router
# For this standalone example, we import from the local file context:
try:
    from architecture import (
        router as architecture_router,
        ArchitectureModule,
        ValidateArchitectureRequest,
        _validate_architecture,  # Importing internal function for direct demonstration
    )
except ImportError:
    # Fallback or mock for demonstration if the module is not present in the environment
    pass

def create_app() -> FastAPI:
    """Create the main FastAPI application and include the architecture router."""
    app = FastAPI(title="Architecture Validator Example")
    
    # Include the router defined in the module
    app.include_router(architecture_router)
    
    return app

def demonstrate_direct_validation():
    """
    Demonstrates how to use the validation logic directly (e.g., in a CLI tool or unit test)
    without spinning up the full HTTP server.
    """
    print("\n--- Direct Validation Logic Demo ---")

    # Scenario 1: A valid architecture
    valid_modules = [
        ArchitectureModule(
            filename="core.py",
            filepath="src/core.py",
            description="Core logic",
            reason="Base module",
            priority=10,
            dependencies=[]
        ),
        ArchitectureModule(
            filename="utils.py",
            filepath="src/utils.py",
            description="Utilities",
            reason="Helper functions",
            priority=5,
            dependencies=["core.py"]
        )
    ]
    
    result = _validate_architecture(valid_modules)
    print(f"Scenario 1 (Valid): Valid={result.valid}, Errors={len(result.errors)}")

    # Scenario 2: Circular Dependency
    circular_modules = [
        ArchitectureModule(
            filename="a.py",
            filepath="src/a.py",
            description="Module A",
            reason="A",
            priority=1,
            dependencies=["b.py"]
        ),
        ArchitectureModule(
            filename="b.py",
            filepath="src/b.py",
            description="Module B",
            reason="B",
            priority=1,
            dependencies=["a.py"]  # Cycle!
        )
    ]

    result = _validate_architecture(circular_modules)
    print(f"Scenario 2 (Circular): Valid={result.valid}")
    for err in result.errors:
        print(f"  [Error] {err.type}: {err.message}")

    # Scenario 3: Missing Dependency & Warnings
    broken_modules = [
        ArchitectureModule(
            filename="orphan.py",
            filepath="src/orphan.py",
            description="Lonely module",
            reason="Test",
            priority=1,
            dependencies=[]
        ),
        ArchitectureModule(
            filename="broken.py",
            filepath="src/broken.py",
            description="Broken links",
            reason="Test",
            priority=1,
            dependencies=["ghost.py", "ghost.py"] # Missing + Duplicate
        )
    ]

    result = _validate_architecture(broken_modules)
    print(f"Scenario 3 (Mixed): Valid={result.valid}")
    for err in result.errors:
        print(f"  [Error] {err.type}: {err.message}")
    for warn in result.warnings:
        print(f"  [Warning] {warn.type}: {warn.message}")


def demonstrate_api_usage():
    """
    Demonstrates how to call the endpoint via HTTP using TestClient.
    """
    print("\n--- API Endpoint Demo ---")
    
    app = create_app()
    client = TestClient(app)

    # Construct the request payload
    payload = {
        "modules": [
            {
                "filename": "api.py",
                "filepath": "src/api.py",
                "description": "API Layer",
                "reason": "Expose endpoints",
                "priority": 100,
                "dependencies": ["service.py"]
            },
            {
                "filename": "service.py",
                "filepath": "src/service.py",
                "description": "Business Logic",
                "reason": "Process data",
                "priority": 50,
                "dependencies": []
            }
        ]
    }

    response = client.post("/api/v1/architecture/validate", json=payload)
    
    if response.status_code == 200:
        data = response.json()
        print(f"API Response Status: {response.status_code}")
        print(f"Is Valid: {data['valid']}")
        print(f"Errors: {len(data['errors'])}")
        print(f"Warnings: {len(data['warnings'])}")
    else:
        print(f"Request failed: {response.text}")

if __name__ == "__main__":
    # 1. Show internal logic working
    try:
        demonstrate_direct_validation()
    except NameError:
        print("Architecture module not found, skipping direct validation demo.")

    # 2. Show API integration working
    try:
        demonstrate_api_usage()
    except Exception as e:
        print(f"API demo failed: {e}")
    
    # 3. To run the actual server, uncomment below:
    # uvicorn.run(create_app(), host="127.0.0.1", port=8000)