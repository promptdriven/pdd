import json
from datetime import datetime
from pydantic import ValidationError

# Assuming the module is importable as pdd.server.models
# If running locally next to the file, you might need to adjust imports
from pdd.server.models import (
    FileMetadata,
    CommandRequest,
    JobHandle,
    JobStatus,
    WSMessage,
    StdoutMessage,
    WriteFileRequest,
    ServerStatus
)

def example_usage():
    """Demonstrates the usage of PDD server models for validation and serialization."""
    print("=== PDD Server Models Example ===\n")

    # 1. File Metadata Example
    # ----------------------------------------------------------------
    print("--- 1. File Metadata Validation ---")
    try:
        # Valid file metadata
        file_meta = FileMetadata(
            path="src/main.py",
            exists=True,
            size=1024,
            mtime=datetime.now(),
            is_directory=False
        )
        print(f"Valid FileMetadata created: {file_meta.path}")
        print(f"JSON representation: {file_meta.model_dump_json()}")

        # Invalid path (traversal attempt)
        print("\nAttempting to create invalid path...")
        FileMetadata(
            path="../secret.txt",
            exists=True
        )
    except ValidationError as e:
        print(f"Caught expected validation error: {e.errors()[0]['msg']}")

    # 2. Command Request Example
    # ----------------------------------------------------------------
    print("\n--- 2. Command Request ---")
    cmd_req = CommandRequest(
        command="generate",
        args={"prompt": "Create a login form"},
        options={"model": "gpt-4", "temperature": 0.7}
    )
    
    # Accessing fields
    print(f"Command: {cmd_req.command}")
    print(f"Args: {cmd_req.args}")
    
    # Serialization to dict
    req_dict = cmd_req.model_dump()
    print(f"Serialized dict: {req_dict}")

    # 3. Job Handling Example
    # ----------------------------------------------------------------
    print("\n--- 3. Job Status & Handling ---")
    # Simulating a job creation response
    job = JobHandle(
        job_id="job-123-abc",
        status=JobStatus.QUEUED
    )
    
    print(f"Job ID: {job.job_id}")
    print(f"Status: {job.status.value}")
    print(f"Created at: {job.created_at.isoformat()}")

    # 4. WebSocket Messages (Polymorphism)
    # ----------------------------------------------------------------
    print("\n--- 4. WebSocket Messages ---")
    
    # Creating a specific message type
    stdout_msg = StdoutMessage(
        data="Compiling resources...",
        raw="\033[32mCompiling resources...\033[0m"
    )
    
    print(f"WS Message Type: {stdout_msg.type}")
    print(f"Content: {stdout_msg.data}")
    
    # Demonstrating generic WSMessage usage
    generic_msg = WSMessage(
        type="custom_event",
        data={"foo": "bar"}
    )
    print(f"Generic Message: {generic_msg.model_dump_json()}")

    # 5. Write File Request (Input Validation)
    # ----------------------------------------------------------------
    print("\n--- 5. Write File Request ---")
    write_req_data = {
        "path": "config/settings.json",
        "content": "{\"debug\": true}",
        "encoding": "utf-8",
        "create_parents": True
    }
    
    # Parse raw dictionary into model
    write_req = WriteFileRequest(**write_req_data)
    print(f"Parsed write request for: {write_req.path}")
    print(f"Create parents? {write_req.create_parents}")

    # 6. Server Status
    # ----------------------------------------------------------------
    print("\n--- 6. Server Status ---")
    status = ServerStatus(
        version="1.0.0",
        project_root="/home/user/projects/my-app",
        uptime_seconds=3600.5,
        active_jobs=2,
        connected_clients=5
    )
    
    # Pydantic v2 uses model_dump_json for serialization
    print(f"Server Status JSON: {status.model_dump_json(indent=2)}")

if __name__ == "__main__":
    example_usage()