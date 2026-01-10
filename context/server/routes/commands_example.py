import asyncio
import uvicorn
from fastapi import FastAPI
from fastapi.testclient import TestClient
from datetime import datetime
from typing import Dict, Any, Optional, List
from dataclasses import dataclass, field
from uuid import uuid4
from enum import Enum
from pydantic import BaseModel

# ============================================================================
# 1. MOCK DEPENDENCIES
# ============================================================================
# Since the module relies on external models and a JobManager, we mock them here
# to make this example self-contained and runnable.

# --- Mock Models (normally in ..models) ---
class JobStatus(str, Enum):
    QUEUED = "queued"
    RUNNING = "running"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"

class CommandRequest(BaseModel):
    command: str
    args: Dict[str, Any] = {}
    options: Dict[str, Any] = {}

class JobHandle(BaseModel):
    job_id: str
    status: JobStatus
    created_at: datetime

class JobResult(BaseModel):
    job_id: str
    status: JobStatus
    result: Optional[Any] = None
    error: Optional[str] = None
    cost: float = 0.0
    duration_seconds: float = 0.0
    completed_at: Optional[datetime] = None

# --- Mock JobManager (normally in ..jobs) ---
@dataclass
class MockJob:
    id: str
    command: str
    status: JobStatus = JobStatus.QUEUED
    created_at: datetime = field(default_factory=datetime.utcnow)
    started_at: Optional[datetime] = None
    completed_at: Optional[datetime] = None
    result: Optional[Any] = None
    error: Optional[str] = None
    cost: float = 0.0

class MockJobManager:
    def __init__(self):
        self.jobs: Dict[str, MockJob] = {}

    async def submit(self, command: str, args: Dict, options: Dict) -> MockJob:
        job_id = str(uuid4())
        job = MockJob(id=job_id, command=command)
        self.jobs[job_id] = job
        
        # Simulate async execution
        asyncio.create_task(self._run_job(job_id))
        return job

    async def _run_job(self, job_id: str):
        await asyncio.sleep(0.5)  # Simulate queue time
        job = self.jobs[job_id]
        job.status = JobStatus.RUNNING
        job.started_at = datetime.utcnow()
        
        await asyncio.sleep(1.0)  # Simulate work
        
        job.status = JobStatus.COMPLETED
        job.completed_at = datetime.utcnow()
        job.result = {"output": f"Executed {job.command} successfully"}
        job.cost = 0.05

    def get_job(self, job_id: str) -> Optional[MockJob]:
        return self.jobs.get(job_id)

    def get_all_jobs(self) -> Dict[str, MockJob]:
        return self.jobs

    async def cancel(self, job_id: str) -> bool:
        job = self.jobs.get(job_id)
        if job and job.status not in (JobStatus.COMPLETED, JobStatus.FAILED):
            job.status = JobStatus.CANCELLED
            return True
        return False

# ============================================================================
# 2. SETUP MODULE ENVIRONMENT
# ============================================================================
# We need to patch sys.modules so the router can import '..models' and '..jobs'
import sys
from types import ModuleType

# Create fake modules
models_mod = ModuleType("pdd.server.models")
models_mod.CommandRequest = CommandRequest
models_mod.JobHandle = JobHandle
models_mod.JobResult = JobResult
models_mod.JobStatus = JobStatus

jobs_mod = ModuleType("pdd.server.jobs")
jobs_mod.JobManager = MockJobManager

# Register them
sys.modules["pdd.server.models"] = models_mod
sys.modules["pdd.server.jobs"] = jobs_mod

# Now we can import the router module
from fastapi import APIRouter, Depends, HTTPException, Query

# --- RECREATING THE ROUTER LOGIC FOR DEMONSTRATION ---
# In a real scenario, you would do: from pdd.server.routes.commands import router, set_job_manager
router = APIRouter(prefix="/api/v1/commands", tags=["commands"])
_job_manager: Optional[MockJobManager] = None

def get_job_manager() -> MockJobManager:
    if _job_manager is None:
        raise RuntimeError("JobManager not configured")
    return _job_manager

def set_job_manager(manager: MockJobManager) -> None:
    global _job_manager
    _job_manager = manager

ALLOWED_COMMANDS = {
    "sync": "Synchronize prompts",
    "generate": "Generate code",
}

@router.post("/execute", response_model=JobHandle)
async def execute_command(request: CommandRequest, manager: MockJobManager = Depends(get_job_manager)):
    if request.command not in ALLOWED_COMMANDS:
        raise HTTPException(status_code=400, detail=f"Unknown command")
    job = await manager.submit(request.command, request.args, request.options)
    return JobHandle(job_id=job.id, status=job.status, created_at=job.created_at)

@router.get("/jobs/{job_id}", response_model=JobResult)
async def get_job_status(job_id: str, manager: MockJobManager = Depends(get_job_manager)):
    job = manager.get_job(job_id)
    if not job:
        raise HTTPException(status_code=404, detail="Job not found")
    
    duration = 0.0
    if job.started_at:
        end = job.completed_at or datetime.utcnow()
        duration = (end - job.started_at).total_seconds()

    return JobResult(
        job_id=job.id,
        status=job.status,
        result=job.result,
        error=job.error,
        cost=job.cost,
        duration_seconds=duration,
        completed_at=job.completed_at
    )

# ============================================================================
# 3. MAIN APPLICATION SETUP
# ============================================================================

def create_app() -> FastAPI:
    app = FastAPI()
    
    # 1. Initialize the JobManager
    manager = MockJobManager()
    
    # 2. Configure the router with the manager instance
    set_job_manager(manager)
    
    # 3. Include the router
    app.include_router(router)
    
    return app

async def run_example():
    """Demonstrates interacting with the API using TestClient."""
    app = create_app()
    client = TestClient(app)
    
    print("=== PDD Commands API Example ===\n")

    # 1. Submit a command
    print("1. Submitting 'generate' command...")
    payload = {
        "command": "generate",
        "args": {"prompt": "Create a login form"},
        "options": {"model": "gpt-4"}
    }
    response = client.post("/api/v1/commands/execute", json=payload)
    
    if response.status_code == 200:
        job_data = response.json()
        job_id = job_data["job_id"]
        print(f"   Success! Job ID: {job_id}")
        print(f"   Initial Status: {job_data['status']}")
    else:
        print(f"   Failed: {response.text}")
        return

    # 2. Poll for status
    print("\n2. Polling job status...")
    for _ in range(3):
        await asyncio.sleep(0.6) # Wait for mock job to progress
        resp = client.get(f"/api/v1/commands/jobs/{job_id}")
        status_data = resp.json()
        print(f"   Status: {status_data['status']}, Duration: {status_data['duration_seconds']:.2f}s")
        
        if status_data['status'] == "completed":
            print(f"   Result: {status_data['result']}")
            break

    # 3. Try an invalid command
    print("\n3. Testing invalid command validation...")
    bad_payload = {"command": "delete_database"}
    resp = client.post("/api/v1/commands/execute", json=bad_payload)
    print(f"   Status Code: {resp.status_code}")
    print(f"   Error: {resp.json()['detail']}")

if __name__ == "__main__":
    asyncio.run(run_example())