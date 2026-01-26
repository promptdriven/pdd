"""
Example usage of the PDD Server package.

This script demonstrates:
1. Setting up the server configuration
2. Initializing the Job Manager
3. Using the PathValidator for security
4. Creating and running the FastAPI application
"""

import asyncio
import threading
import time
import requests
from pathlib import Path
from rich.console import Console

# Import from the package
# In a real installation, this would be: from pdd.server import ...
# Assuming this script is running where 'pdd' is importable
try:
    from pdd.server import (
        create_app,
        run_server,
        JobManager,
        PathValidator,
        SecurityError,
        DEFAULT_HOST,
        DEFAULT_PORT
    )
except ImportError:
    # Fallback for local development if running from project root
    import sys
    sys.path.append(".")
    from pdd.server import (
        create_app,
        run_server,
        JobManager,
        PathValidator,
        SecurityError,
        DEFAULT_HOST,
        DEFAULT_PORT
    )

console = Console()

def demo_security_validation():
    """Demonstrates how to use the PathValidator component."""
    console.print("\n[bold blue]--- 1. Security Validation Demo ---[/bold blue]")
    
    project_root = Path.cwd() / "example_project"
    project_root.mkdir(exist_ok=True)
    
    # Create a dummy file inside the project
    (project_root / "safe_file.txt").write_text("I am safe.")
    
    validator = PathValidator(project_root=project_root)
    
    # Test 1: Valid Path
    try:
        safe_path = validator.validate("safe_file.txt")
        console.print(f"[green]✓ Valid path accepted:[/green] {safe_path}")
    except SecurityError as e:
        console.print(f"[red]✗ Unexpected error:[/red] {e}")

    # Test 2: Path Traversal Attempt
    try:
        # Attempt to go up directories
        validator.validate("../../etc/passwd")
    except SecurityError as e:
        console.print(f"[green]✓ Security caught traversal:[/green] {e}")

    # Cleanup
    import shutil
    if project_root.exists():
        shutil.rmtree(project_root)

async def demo_job_manager():
    """Demonstrates the JobManager functionality."""
    console.print("\n[bold blue]--- 2. Job Manager Demo ---[/bold blue]")
    
    # Define a simple mock executor
    async def mock_executor(job):
        await asyncio.sleep(0.5)
        return {"status": "success", "result": f"Processed {job.args.get('filename')}"}

    manager = JobManager(executor=mock_executor)
    
    # Submit a job
    console.print("Submitting background job...")
    job = await manager.submit(
        command="analyze",
        args={"filename": "main.py"}
    )
    
    console.print(f"Job ID: {job.id} | Status: {job.status}")
    
    # Wait for completion
    while job.status not in ["completed", "failed", "cancelled"]:
        await asyncio.sleep(0.1)
        
    console.print(f"Job Finished! Result: {job.result}")
    await manager.shutdown()

def run_server_thread(root_path: Path):
    """Helper to run the server in a thread."""
    run_server(
        project_root=root_path,
        host=DEFAULT_HOST,
        port=DEFAULT_PORT,
        log_level="error" # Quiet logs for demo
    )

def demo_server_interaction():
    """Demonstrates running the server and hitting an endpoint."""
    console.print("\n[bold blue]--- 3. Server Interaction Demo ---[/bold blue]")
    
    project_root = Path.cwd()
    
    # Start server in background thread
    server_thread = threading.Thread(
        target=run_server_thread,
        args=(project_root,),
        daemon=True
    )
    server_thread.start()
    
    # Wait for server startup
    console.print("Waiting for server to start...")
    time.sleep(2)
    
    base_url = f"http://{DEFAULT_HOST}:{DEFAULT_PORT}"
    
    try:
        # Hit the status endpoint
        response = requests.get(f"{base_url}/api/v1/status")
        if response.status_code == 200:
            data = response.json()
            console.print("[green]✓ Server is responding![/green]")
            console.print(f"   Version: {data.get('version')}")
            console.print(f"   Project Root: {data.get('project_root')}")
        else:
            console.print(f"[red]✗ Server returned error:[/red] {response.status_code}")
            
    except requests.exceptions.ConnectionError:
        console.print("[red]✗ Could not connect to server[/red]")

def main():
    # 1. Run synchronous security demo
    demo_security_validation()
    
    # 2. Run async job demo
    asyncio.run(demo_job_manager())
    
    # 3. Run server integration demo
    demo_server_interaction()
    
    console.print("\n[bold green]Demo Complete![/bold green]")

if __name__ == "__main__":
    main()