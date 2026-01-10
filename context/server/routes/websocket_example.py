"""
WebSocket Routes Example for PDD Server

This example demonstrates how to use the WebSocket routes module for:
- Real-time job output streaming
- File system change monitoring
- Connection management
- Message protocol handling

Usage:
    python websocket_example.py

The example will:
1. Set up a mock FastAPI app with WebSocket routes
2. Create a test job and stream its output
3. Monitor file changes in a directory
4. Show proper message handling and error cases
"""

import asyncio
import json
import tempfile
import time
from pathlib import Path
from typing import Dict, Any, List, Optional

# Mock FastAPI app for demonstration
from fastapi import FastAPI, Depends
from fastapi.testclient import TestClient

# Since we're running as a standalone example, we need to handle imports
import sys

# Add the project root to Python path for imports
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

# Import the WebSocket module
try:
    from pdd.server.routes.websocket import (
        ConnectionManager,
        create_websocket_routes,
        emit_job_output,
        emit_job_progress,
        emit_job_complete,
        manager as global_manager,
        router,
        WSMessage
    )
except ImportError:
    # Fallback for standalone execution
    print("Warning: Running in standalone mode with mocked dependencies")
    
    class WSMessage:
        def __init__(self, type: str, data: Any):
            self.type = type
            self.data = data

    # Create a minimal mock of the module for demonstration
    class MockConnectionManager:
        def __init__(self):
            self.active_connections = []
            self.job_subscriptions = {}
            self.watch_subscriptions = []
        
        async def connect(self, websocket):
            self.active_connections.append(websocket)
        
        def disconnect(self, websocket, job_id=None):
            if websocket in self.active_connections:
                self.active_connections.remove(websocket)
        
        async def subscribe_to_job(self, websocket, job_id):
            self.job_subscriptions[job_id] = websocket
        
        async def subscribe_to_watch(self, websocket):
            self.watch_subscriptions.append(websocket)
        
        async def broadcast_job_message(self, job_id, message):
            print(f"[BROADCAST] Job {job_id}: {message.type}")
        
        async def broadcast_file_change(self, message):
            print(f"[BROADCAST] File change: {message.data}")
    
    global_manager = MockConnectionManager()
    router = None

    async def emit_job_output(job_id, stream, text):
        msg = WSMessage(type="job_output", data={"stream": stream, "text": text})
        await global_manager.broadcast_job_message(job_id, msg)

    async def emit_job_progress(job_id, current, total, status):
        msg = WSMessage(type="job_progress", data={"current": current, "total": total, "status": status})
        await global_manager.broadcast_job_message(job_id, msg)

    async def emit_job_complete(job_id, result, success, cost):
        msg = WSMessage(type="job_complete", data={"result": result, "success": success, "cost": cost})
        await global_manager.broadcast_job_message(job_id, msg)


# ============================================================================
# Mock Dependencies for Testing
# ============================================================================

class MockJobManager:
    """Mock JobManager for demonstration"""
    
    def __init__(self):
        self.jobs = {}
    
    def get_job(self, job_id):
        return self.jobs.get(job_id)
    
    async def cancel(self, job_id):
        job = self.get_job(job_id)
        if job:
            job.status = "CANCELLED"
            return True
        return False


class MockJob:
    """Mock Job for demonstration"""
    
    def __init__(self, job_id, status="RUNNING"):
        self.id = job_id
        self.status = status
        self.result = {"output": "Task completed successfully"}
        self.cost = 0.05


# ============================================================================
# Example WebSocket Client
# ============================================================================

class WebSocketClient:
    """Simulates a WebSocket client for testing"""
    
    def __init__(self, job_id=None, watch=False):
        self.job_id = job_id
        self.watch = watch
        self.messages = []
        self.connected = True
    
    async def send_text(self, data):
        """Simulate receiving a message"""
        try:
            message = json.loads(data)
            self.messages.append(message)
            print(f"[Client] Received: {message['type']}")
        except json.JSONDecodeError:
            raise Exception("Invalid JSON received")
    
    async def receive_text(self):
        """Simulate sending a message"""
        if self.job_id:
            # Send a cancel message after some delay
            await asyncio.sleep(0.5)
            return json.dumps({"type": "cancel"})
        elif self.watch:
            # Send subscription for file watching
            return json.dumps({"paths": ["./test_dir"]})
        return ""
    
    def close(self):
        self.connected = False


# ============================================================================
# Example Usage Functions
# ============================================================================

async def example_job_streaming():
    """Demonstrate job output streaming"""
    print("\n=== Job Streaming Example ===")
    
    # Setup
    job_manager = MockJobManager()
    job_id = "test-job-123"
    job_manager.jobs[job_id] = MockJob(job_id)
    
    # Create mock WebSocket client
    client = WebSocketClient(job_id=job_id)
    
    # Simulate connection
    await global_manager.connect(client)
    await global_manager.subscribe_to_job(client, job_id)
    
    # Simulate job output
    print("\n1. Streaming stdout:")
    await emit_job_output(job_id, "stdout", "Processing file...\n")
    
    print("\n2. Streaming stderr:")
    await emit_job_output(job_id, "stderr", "Warning: Low memory\n")
    
    print("\n3. Streaming progress:")
    await emit_job_progress(job_id, 1, 3, "Initializing")
    await asyncio.sleep(0.1)
    await emit_job_progress(job_id, 2, 3, "Processing")
    await asyncio.sleep(0.1)
    await emit_job_progress(job_id, 3, 3, "Completing")
    
    print("\n4. Job completion:")
    await emit_job_complete(
        job_id, 
        result={"files_processed": 10},
        success=True,
        cost=0.05
    )
    
    # Show received messages
    print(f"\nClient received {len(client.messages)} messages")
    for msg in client.messages:
        print(f"  - {msg['type']}: {msg.get('data', {})}")


async def example_file_watching():
    """Demonstrate file system watching"""
    print("\n=== File Watching Example ===")
    
    # Create temporary directory for testing
    with tempfile.TemporaryDirectory() as temp_dir:
        temp_path = Path(temp_dir)
        print(f"Created test directory: {temp_path}")
        
        # Setup mock client
        client = WebSocketClient(watch=True)
        await global_manager.connect(client)
        await global_manager.subscribe_to_watch(client)
        
        # Simulate file changes
        print("\n1. File created:")
        test_file = temp_path / "test.txt"
        test_file.write_text("Hello, World!")
        
        # Simulate watchdog event
        msg = WSMessage(
            type="file_change",
            data={
                "path": str(test_file),
                "event": "created",
                "timestamp": "2024-01-01T00:00:00Z"
            }
        )
        await global_manager.broadcast_file_change(msg)
        
        print("\n2. File modified:")
        test_file.write_text("Hello, Updated World!")
        
        msg = WSMessage(
            type="file_change",
            data={
                "path": str(test_file),
                "event": "modified",
                "timestamp": "2024-01-01T00:01:00Z"
            }
        )
        await global_manager.broadcast_file_change(msg)
        
        print("\n3. File deleted:")
        test_file.unlink()
        
        msg = WSMessage(
            type="file_change",
            data={
                "path": str(test_file),
                "event": "deleted",
                "timestamp": "2024-01-01T00:02:00Z"
            }
        )
        await global_manager.broadcast_file_change(msg)
        
        # Show received messages
        print(f"\nClient received {len(client.messages)} messages")
        for msg in client.messages:
            print(f"  - {msg['type']}: {msg.get('data', {})}")


async def example_connection_management():
    """Demonstrate connection management"""
    print("\n=== Connection Management Example ===")
    
    # Create multiple clients
    clients = [WebSocketClient(job_id=f"job-{i}") for i in range(3)]
    
    # Connect all clients
    for i, client in enumerate(clients):
        await global_manager.connect(client)
        await global_manager.subscribe_to_job(client, f"job-{i}")
        print(f"Connected client {i+1}")
    
    print(f"\nActive connections: {len(global_manager.active_connections)}")
    print(f"Job subscriptions: {len(global_manager.job_subscriptions)}")
    
    # Broadcast to specific job
    msg = WSMessage(type="test", data={"message": "Broadcast test"})
    await global_manager.broadcast_job_message("job-1", msg)
    
    # Disconnect one client
    global_manager.disconnect(clients[1])
    print(f"\nDisconnected client 1")
    print(f"Active connections: {len(global_manager.active_connections)}")
    
    # Disconnect all
    for client in clients:
        global_manager.disconnect(client)
    print(f"\nAll clients disconnected")


async def example_error_handling():
    """Demonstrate error handling"""
    print("\n=== Error Handling Example ===")
    
    # Test invalid job ID
    print("1. Testing invalid job ID:")
    try:
        # In a real system this might raise an error or just not broadcast
        await emit_job_output("invalid-job", "stdout", "test")
    except Exception as e:
        print(f"   Error: {e}")
    
    # Test malformed message
    print("\n2. Testing malformed message:")
    client = WebSocketClient()
    await global_manager.connect(client)
    
    # Simulate invalid JSON
    try:
        await client.send_text('{"type": "invalid"')
    except Exception as e:
        print(f"   Error: {e}")
    
    # Test connection closed
    print("\n3. Testing closed connection:")
    client.close()
    try:
        if not client.connected:
            raise Exception("Connection closed")
        await emit_job_output("test-job", "stdout", "test")
    except Exception as e:
        print(f"   Error: {e}")


# ============================================================================
# Main Example Runner
# ============================================================================

async def main():
    """Run all examples"""
    print("WebSocket Routes Example")
    print("=" * 50)
    
    try:
        await example_job_streaming()
        await example_file_watching()
        await example_connection_management()
        await example_error_handling()
    except Exception as e:
        print(f"\nExample failed: {e}")
        import traceback
        traceback.print_exc()
    finally:
        print("\nExample completed")


if __name__ == "__main__":
    # Run the example
    asyncio.run(main())