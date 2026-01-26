"""
Example usage of the pdd.server.routes module.

This example demonstrates how to import the routers exposed by the `pdd.server.routes` 
package and include them in a main FastAPI application.

In a real application, this code would typically reside in `pdd/server/main.py` or `pdd/server/app.py`.

Prerequisites:
    - The `pdd` package must be installed or available in the python path.
    - `fastapi` and `uvicorn` must be installed.
"""

import uvicorn
from fastapi import FastAPI, APIRouter

# In a real scenario, you would import directly from the package:
# from pdd.server.routes import files_router, commands_router, websocket_router

# --- Mocking the sub-modules for demonstration purposes ---
# In reality, these are defined in pdd/server/routes/files.py, etc.
mock_files_router = APIRouter(prefix="/files", tags=["files"])

@mock_files_router.get("/")
async def list_files():
    return {"message": "List of files"}

mock_commands_router = APIRouter(prefix="/commands", tags=["commands"])

@mock_commands_router.post("/exec")
async def exec_command():
    return {"message": "Command executed"}

mock_websocket_router = APIRouter(tags=["websocket"])

@mock_websocket_router.websocket("/ws")
async def websocket_endpoint():
    pass  # WebSocket logic would go here

# Simulating the __init__.py export
files_router = mock_files_router
commands_router = mock_commands_router
websocket_router = mock_websocket_router
# ----------------------------------------------------------


def create_app() -> FastAPI:
    """
    Factory function to create the FastAPI application.
    """
    app = FastAPI(
        title="PDD Server",
        description="Prompt Driven Development Server",
        version="1.0.0"
    )

    # Include the routers imported from the routes package
    # This keeps the main application file clean and modular
    app.include_router(files_router)
    app.include_router(commands_router)
    app.include_router(websocket_router)

    return app


def main() -> None:
    """
    Main entry point to run the server.
    """
    app = create_app()
    
    print("Starting PDD Server with the following routes:")
    for route in app.routes:
        if hasattr(route, "methods"):
            print(f" - {route.path} [{', '.join(route.methods)}]")
        else:
            print(f" - {route.path} [WebSocket]")

    # Run the server
    # In a real environment, you might use: uvicorn.run("pdd.server.main:app", reload=True)
    uvicorn.run(app, host="127.0.0.1", port=8000)


if __name__ == "__main__":
    main()