import asyncio
import sys
import os
import logging
from datetime import datetime

# Ensure the 'pdd' package is in the python path
# This assumes the script is running from 'pdd/context/' and the package root is 'pdd/'
# We use insert(0, ...) instead of append to ensure the local 'pdd' package takes precedence
# over any installed packages in the environment.
project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

from pdd.server.jobs import JobManager, Job, JobStatus

# Configure logging to capture internal module logs
logging.basicConfig(level=logging.ERROR)

async def mock_worker(job: Job) -> dict:
    """
    A custom executor function to simulate work without running actual CLI commands.
    
    In a real scenario, the JobManager uses 'ClickCommandExecutor' to run 
    PDD CLI commands. Here, we inject this mock to demonstrate the queuing logic.
    
    Args:
        job: The job instance containing args and options.
        
    Returns:
        A dictionary representing the result of the job.
    """
    # Extract parameters from job arguments
    duration = job.args.get("duration", 1.0)
    fail_job = job.args.get("fail", False)
    name = job.args.get("name", "Unknown")

    # Simulate processing time
    # We break the sleep into chunks to allow for cancellation checks if implemented deeply,
    # though the JobManager handles cancellation at the task level.
    await asyncio.sleep(duration)

    if fail_job:
        raise ValueError(f"Simulated failure for job: {name}")

    return {
        "message": f"Successfully processed {name}",
        "processed_items": 42,
        "cost": 0.005 * duration  # Simulated cost calculation
    }

async def main():
    print("=== PDD Job Manager Example ===\n")

    # 1. Initialize the JobManager
    # We set max_concurrent=2. This means if we submit 4 jobs, 
    # 2 will run immediately, and 2 will wait in the queue.
    manager = JobManager(max_concurrent=2, executor=mock_worker)

    # 2. Register Lifecycle Callbacks
    # These are useful for updating UIs, sending WebSocket messages, or logging.
    
    async def on_job_start(job: Job):
        print(f"✀ [START] Job {job.id[:6]} ({job.args['name']}) started.")

    async def on_job_complete(job: Job):
        symbol = "✅" if job.status == JobStatus.COMPLETED else "❌"
        print(f"{symbol} [DONE]  Job {job.id[:6]} finished: {job.status.value}")
        if job.error:
            print(f"   Error: {job.error}")

    manager.callbacks.on_start(on_job_start)
    manager.callbacks.on_complete(on_job_complete)

    print("--- Submitting Jobs ---")

    # 3. Submit a batch of jobs
    # Job A: 1.0s (Will run immediately)
    job_a = await manager.submit("test_cmd", args={"name": "Job A", "duration": 1.0})
    
    # Job B: 2.0s (Will run immediately)
    job_b = await manager.submit("test_cmd", args={"name": "Job B", "duration": 2.0})
    
    # Job C: 1.0s (Will be QUEUED because limit is 2)
    job_c = await manager.submit("test_cmd", args={"name": "Job C", "duration": 1.0})
    
    # Job D: 5.0s (Will be QUEUED, intended to be cancelled)
    job_d = await manager.submit("test_cmd", args={"name": "Job D", "duration": 5.0})
    
    # Job E: 0.5s (Will be QUEUED, intended to fail)
    job_e = await manager.submit("test_cmd", args={"name": "Job E", "duration": 0.5, "fail": True})

    print(f"Jobs submitted. Active jobs in manager: {len(manager.get_active_jobs())}")
    
    # 4. Demonstrate Cancellation
    # We cancel Job D while it is likely still in the queue (or just starting)
    print("\n--- Cancelling Job D ---")
    await asyncio.sleep(0.1) # Yield to let event loop process submissions
    
    was_cancelled = await manager.cancel(job_d.id)
    if was_cancelled:
        print(f"⚠️  Requested cancellation for Job D ({job_d.id[:6]})")

    # 5. Monitor Progress
    # We wait for jobs to process. 
    # Timeline:
    # T=0.0s: A(Run), B(Run), C(Queue), D(Queue), E(Queue)
    # T=0.1s: D Cancelled
    # T=1.0s: A finishes. C starts.
    # T=2.0s: B finishes. E starts. C finishes.
    # T=2.5s: E fails.
    
    print("\n--- Waiting for processing... ---")
    
    # Simple polling loop to wait until all jobs are done
    while True:
        active = manager.get_active_jobs()
        if not active:
            break
        await asyncio.sleep(0.5)

    print("\n--- All Jobs Finished ---")

    # 6. Inspect Results
    print("\nSummary:")
    all_jobs = manager.get_all_jobs()
    
    # Sort by creation time for cleaner output
    sorted_jobs = sorted(all_jobs.values(), key=lambda j: j.created_at)
    
    for job in sorted_jobs:
        name = job.args.get('name')
        cost_str = f"${job.cost:.4f}" if job.cost else "$-"
        print(f"Job {name:<6} | Status: {job.status.value:<10} | Cost: {cost_str} | ID: {job.id}")

    # 7. Cleanup
    # Removes jobs from memory that are completed and older than X seconds
    removed_count = manager.cleanup_old_jobs(max_age_seconds=0) # 0 to clear all completed
    print(f"\nCleaned up {removed_count} old jobs.")

    # Graceful shutdown (stops thread pools)
    await manager.shutdown()

if __name__ == "__main__":
    asyncio.run(main())