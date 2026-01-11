/**
 * useJobs - Custom hook for managing multiple concurrent job executions.
 *
 * Provides state management for tracking jobs, WebSocket connections for
 * real-time streaming, and notification handling.
 */

import { useState, useCallback, useRef, useEffect } from 'react';
import { api, JobHandle, CommandRequest } from '../api';

export type JobStatus = 'queued' | 'running' | 'completed' | 'failed' | 'cancelled';

export interface JobProgress {
  current: number;
  total: number;
  message: string;
}

export interface JobInfo {
  id: string;
  command: string;
  displayCommand: string;
  status: JobStatus;
  progress: JobProgress | null;
  output: string[];
  cost: number;
  startedAt: Date;
  completedAt: Date | null;
  error: string | null;
}

interface UseJobsOptions {
  onJobComplete?: (job: JobInfo, success: boolean) => void;
  maxOutputLines?: number;
}

// Safety limits - prevent resource exhaustion from too many LLM calls
const MAX_CONCURRENT_JOBS = 3;
const MAX_QUEUED_JOBS = 5;

export function useJobs(options: UseJobsOptions = {}) {
  const { onJobComplete, maxOutputLines = 1000 } = options;

  // Map of job ID -> JobInfo
  const [jobs, setJobs] = useState<Map<string, JobInfo>>(new Map());
  // Currently selected job for detail view
  const [selectedJobId, setSelectedJobId] = useState<string | null>(null);

  // Keep track of WebSocket connections
  const wsConnections = useRef<Map<string, WebSocket>>(new Map());

  // Ref to always get latest jobs state (avoids stale closure issues)
  const jobsRef = useRef<Map<string, JobInfo>>(jobs);
  jobsRef.current = jobs;

  // Cleanup WebSocket connections on unmount
  useEffect(() => {
    return () => {
      wsConnections.current.forEach((ws) => {
        if (ws.readyState === WebSocket.OPEN) {
          ws.close();
        }
      });
      wsConnections.current.clear();
    };
  }, []);

  /**
   * Add output line to a job, respecting max lines limit.
   */
  const addJobOutput = useCallback((jobId: string, line: string) => {
    setJobs((prev) => {
      const updated = new Map(prev);
      const job = updated.get(jobId);
      if (job) {
        const newOutput = [...job.output, line];
        // Trim if exceeds max lines
        if (newOutput.length > maxOutputLines) {
          newOutput.splice(0, newOutput.length - maxOutputLines);
        }
        updated.set(jobId, { ...job, output: newOutput });
      }
      return updated;
    });
  }, [maxOutputLines]);

  /**
   * Update job progress.
   */
  const updateJobProgress = useCallback((jobId: string, current: number, total: number, message: string) => {
    setJobs((prev) => {
      const updated = new Map(prev);
      const job = updated.get(jobId);
      if (job) {
        updated.set(jobId, {
          ...job,
          progress: { current, total, message },
          status: 'running',
        });
      }
      return updated;
    });
  }, []);

  /**
   * Mark job as completed.
   */
  const completeJob = useCallback((jobId: string, success: boolean, cost: number, result?: any) => {
    setJobs((prev) => {
      const updated = new Map(prev);
      const job = updated.get(jobId);
      if (job) {
        // Extract any buffered output from result (handles race condition where
        // job completes before WebSocket connects - output is in result.stdout/stderr)
        let finalOutput = [...job.output];
        if (result?.stdout && typeof result.stdout === 'string' && result.stdout.trim()) {
          // Only add if we haven't already received this output via streaming
          if (finalOutput.length === 0 || !finalOutput.includes(result.stdout)) {
            finalOutput.push(result.stdout);
          }
        }
        if (result?.stderr && typeof result.stderr === 'string' && result.stderr.trim()) {
          const stderrLine = `[stderr] ${result.stderr}`;
          if (!finalOutput.includes(stderrLine)) {
            finalOutput.push(stderrLine);
          }
        }

        const completedJob: JobInfo = {
          ...job,
          output: finalOutput,
          status: success ? 'completed' : 'failed',
          cost,
          completedAt: new Date(),
          error: success ? null : (result?.error || 'Job failed'),
        };
        updated.set(jobId, completedJob);
        // Trigger callback
        if (onJobComplete) {
          onJobComplete(completedJob, success);
        }
      }
      return updated;
    });

    // Close WebSocket connection
    const ws = wsConnections.current.get(jobId);
    if (ws && ws.readyState === WebSocket.OPEN) {
      ws.close();
    }
    wsConnections.current.delete(jobId);
  }, [onJobComplete]);

  /**
   * Submit a new job and start streaming its output.
   * Returns job ID on success, null on failure, or throws if limit exceeded.
   */
  const submitJob = useCallback(async (
    request: CommandRequest,
    displayCommand: string
  ): Promise<string | null> => {
    // SAFETY CHECK: Limit total jobs to prevent resource exhaustion
    const currentJobs = jobsRef.current;
    const activeCount = Array.from(currentJobs.values()).filter(
      j => j.status === 'queued' || j.status === 'running'
    ).length;

    if (activeCount >= MAX_QUEUED_JOBS) {
      throw new Error(`Too many jobs queued (${activeCount}/${MAX_QUEUED_JOBS}). Please wait for some to complete.`);
    }

    if (activeCount >= MAX_CONCURRENT_JOBS) {
      console.warn(`Warning: ${activeCount} jobs already running. New job will be queued.`);
    }

    try {
      // Submit the job via async API
      const handle: JobHandle = await api.executeCommand(request);
      const jobId = handle.job_id;

      // Create job info
      const jobInfo: JobInfo = {
        id: jobId,
        command: request.command,
        displayCommand,
        status: handle.status as JobStatus,
        progress: null,
        output: [],
        cost: 0,
        startedAt: new Date(),
        completedAt: null,
        error: null,
      };

      // Add to jobs map
      setJobs((prev) => {
        const updated = new Map(prev);
        updated.set(jobId, jobInfo);
        return updated;
      });

      // Select this job
      setSelectedJobId(jobId);

      // Connect WebSocket for real-time streaming
      const ws = api.connectToJobStream(jobId, {
        onStdout: (text) => addJobOutput(jobId, text),
        onStderr: (text) => addJobOutput(jobId, `[stderr] ${text}`),
        onProgress: (current, total, message) => updateJobProgress(jobId, current, total, message),
        onComplete: (success, result, cost) => completeJob(jobId, success, cost, result),
        onError: (error) => {
          console.error(`WebSocket error for job ${jobId}:`, error);
          completeJob(jobId, false, 0, { error: error.message });
        },
        onClose: () => {
          // Connection closed - use ref to get latest job state (not stale closure)
          const currentJob = jobsRef.current.get(jobId);
          if (currentJob && currentJob.status === 'running') {
            // Poll for final status
            api.getJobStatus(jobId).then((result) => {
              const success = result.status === 'completed';
              completeJob(jobId, success, result.cost || 0, result);
            }).catch(() => {
              // Assume failed if we can't get status
              completeJob(jobId, false, 0, { error: 'Connection lost' });
            });
          }
        },
      });

      wsConnections.current.set(jobId, ws);
      return jobId;
    } catch (error: any) {
      console.error('Failed to submit job:', error);
      return null;
    }
  }, [addJobOutput, updateJobProgress, completeJob]);

  /**
   * Cancel a running job.
   */
  const cancelJob = useCallback(async (jobId: string) => {
    try {
      // Send cancel via WebSocket if connected
      const ws = wsConnections.current.get(jobId);
      if (ws && ws.readyState === WebSocket.OPEN) {
        api.sendCancelRequest(ws);
      }

      // Also call the REST API to ensure cancellation
      await api.cancelJob(jobId);

      // Update local state
      setJobs((prev) => {
        const updated = new Map(prev);
        const job = updated.get(jobId);
        if (job) {
          updated.set(jobId, {
            ...job,
            status: 'cancelled',
            completedAt: new Date(),
          });
        }
        return updated;
      });
    } catch (error) {
      console.error('Failed to cancel job:', error);
    }
  }, []);

  /**
   * Remove a job from the list (for cleanup).
   */
  const removeJob = useCallback((jobId: string) => {
    setJobs((prev) => {
      const updated = new Map(prev);
      updated.delete(jobId);
      return updated;
    });

    // Close WebSocket if still open
    const ws = wsConnections.current.get(jobId);
    if (ws) {
      ws.close();
      wsConnections.current.delete(jobId);
    }

    // Deselect if this was selected
    setSelectedJobId((prev) => (prev === jobId ? null : prev));
  }, []);

  /**
   * Clear all completed/failed jobs.
   */
  const clearCompletedJobs = useCallback(() => {
    setJobs((prev) => {
      const updated = new Map(prev);
      for (const [id, job] of updated.entries()) {
        if (job.status === 'completed' || job.status === 'failed' || job.status === 'cancelled') {
          updated.delete(id);
        }
      }
      return updated;
    });
  }, []);

  /**
   * Add a spawned terminal job to the dashboard.
   * These jobs run in separate terminal windows, so we don't have WebSocket output.
   * They're marked as "running" until manually dismissed.
   */
  const addSpawnedJob = useCallback((displayCommand: string, command: string): string => {
    const jobId = `spawned-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;

    const jobInfo: JobInfo = {
      id: jobId,
      command,
      displayCommand,
      status: 'running',
      progress: null,
      output: [
        'Command running in separate terminal window.',
        '',
        'To stop: Close the terminal window',
        'When finished: Click "Done" or "Failed" below',
      ],
      cost: 0,
      startedAt: new Date(),
      completedAt: null,
      error: null,
    };

    setJobs((prev) => {
      const updated = new Map(prev);
      updated.set(jobId, jobInfo);
      return updated;
    });

    setSelectedJobId(jobId);
    return jobId;
  }, []);

  /**
   * Mark a spawned job as completed (user confirms it's done).
   */
  const markSpawnedJobDone = useCallback((jobId: string, success: boolean = true) => {
    setJobs((prev) => {
      const updated = new Map(prev);
      const job = updated.get(jobId);
      if (job) {
        updated.set(jobId, {
          ...job,
          status: success ? 'completed' : 'failed',
          completedAt: new Date(),
          output: [...job.output, success ? 'Marked as completed by user.' : 'Marked as failed by user.'],
        });
        if (onJobComplete) {
          onJobComplete({ ...job, status: success ? 'completed' : 'failed' }, success);
        }
      }
      return updated;
    });
  }, [onJobComplete]);

  // Derived state
  const activeJobs = Array.from(jobs.values()).filter(
    (j) => j.status === 'queued' || j.status === 'running'
  );
  const completedJobs = Array.from(jobs.values()).filter(
    (j) => j.status === 'completed' || j.status === 'failed' || j.status === 'cancelled'
  );
  const selectedJob = selectedJobId ? jobs.get(selectedJobId) || null : null;
  const isAnyJobRunning = activeJobs.length > 0;

  return {
    // State
    jobs,
    activeJobs,
    completedJobs,
    selectedJob,
    selectedJobId,
    isAnyJobRunning,

    // Actions
    submitJob,
    cancelJob,
    removeJob,
    clearCompletedJobs,
    setSelectedJobId,
    addSpawnedJob,
    markSpawnedJobDone,
  };
}

export default useJobs;
