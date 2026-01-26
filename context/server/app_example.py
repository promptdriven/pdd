import sys
import asyncio
import threading
import time
import requests
from pathlib import Path
from rich.console import Console

# Adjust the path to ensure we can import the 'pdd' package
# Assuming this script is running in a directory where 'pdd' is a subdirectory or sibling
sys.path.append(str(Path(__file__).parent.parent))

try:
    # Import the server runner and app factory from the module
    from pdd.server.app import run_server, create_app, get_app_state
except ImportError as e:
    print(f"Error importing pdd.server.app: {e}")
    print("Ensure you are running this script from a location where the 'pdd' package is accessible.")
    sys.exit(1)

console = Console()

def start_server_in_thread(root_path: Path, host: str, port: int):
    """
    Helper to run the server in a separate thread so we can query it in the main thread.
    In a real scenario, you would just call run_server() directly.
    """
    console.print(f"[blue]Starting server thread for root: {root_path}[/blue]")
    # Note: uvicorn.run blocks, so we run it here
    run_server(
        project_root=root_path,
        host=host,
        port=port,
        log_level="warning", # Reduce noise for the example
        allowed_origins=["http://localhost:3000"]
    )

def main():
    """
    Demonstrates how to initialize and interact with the PDD Server application.
    """
    # 1. Define configuration
    HOST = "127.0.0.1"
    PORT = 9999
    PROJECT_ROOT = Path.cwd() / "example_project_root"
    
    # Create a dummy project root for testing
    PROJECT_ROOT.mkdir(exist_ok=True)
    (PROJECT_ROOT / "hello.txt").write_text("Hello from PDD Server!")

    # 2. Start the server
    # We run this in a thread to simulate the server running while we act as a client
    server_thread = threading.Thread(
        target=start_server_in_thread,
        args=(PROJECT_ROOT, HOST, PORT),
        daemon=True
    )
    server_thread.start()

    # Give the server a moment to spin up
    time.sleep(2)

    base_url = f"http://{HOST}:{PORT}"
    console.print(f"\n[bold]Interacting with server at {base_url}[/bold]\n")

    try:
        # 3. Check Server Status
        # This hits the /api/v1/status endpoint defined in create_app
        console.print("[yellow]1. Checking Server Status...[/yellow]")
        resp = requests.get(f"{base_url}/api/v1/status")
        
        if resp.status_code == 200:
            data = resp.json()
            console.print(f"   [green]Success![/green] Version: {data.get('version')}")
            console.print(f"   Project Root: {data.get('project_root')}")
            console.print(f"   Uptime: {data.get('uptime_seconds'):.2f}s")
        else:
            console.print(f"   [red]Failed:[/red] {resp.status_code} - {resp.text}")

        # 4. Test Security (Path Traversal)
        # The app uses PathValidator (via security.py) to block access outside root
        console.print("\n[yellow]2. Testing Security (Path Traversal)...[/yellow]")
        # Attempt to access a file outside the project root (e.g., system file)
        bad_path = "../../etc/passwd" 
        resp = requests.get(f"{base_url}/api/v1/files/content", params={"path": bad_path})
        
        if resp.status_code == 403:
            console.print(f"   [green]Security Active![/green] Server blocked access to '{bad_path}' (403 Forbidden)")
            console.print(f"   Response: {resp.json()}")
        else:
            console.print(f"   [red]Unexpected response:[/red] {resp.status_code}")

        # 5. Test Documentation Endpoint
        console.print("\n[yellow]3. Verifying Docs...[/yellow]")
        resp = requests.get(f"{base_url}/docs")
        if resp.status_code == 200:
            console.print("   [green]OpenAPI Docs are accessible.[/green]")
        else:
            console.print("   [red]Docs not found.[/red]")

    except requests.exceptions.ConnectionError:
        console.print("[bold red]Could not connect to server. Is it running?[/bold red]")
    except Exception as e:
        console.print(f"[bold red]An error occurred:[/bold red] {e}")
    finally:
        # Cleanup dummy directory
        import shutil
        if PROJECT_ROOT.exists():
            shutil.rmtree(PROJECT_ROOT)
        console.print("\n[blue]Example complete. Stopping server (daemon thread will exit).[/blue]")

if __name__ == "__main__":
    main()