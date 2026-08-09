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
  metadata?: {
    remote?: boolean;
    sessionId?: string;
    [key: string]: any;
  };
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

  // Ref to always get latest onJobComplete callback (avoids stale closure issues in polling)
  const onJobCompleteRef = useRef(onJobComplete);
  onJobCompleteRef.current = onJobComplete;

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
    setJobs((prev: Map<string, JobInfo>) => {
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
    setJobs((prev: Map<string, JobInfo>) => {
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
    setJobs((prev: Map<string, JobInfo>) => {
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
      (j: JobInfo) => j.status === 'queued' || j.status === 'running'
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
      setJobs((prev: Map<string, JobInfo>) => {
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
   * Handles both local jobs (WebSocket/REST) and remote jobs (cloud API).
   */
  const cancelJob = useCallback(async (jobId: string) => {
    try {
      const job = jobs.get(jobId);

      // Check if this is a remote job
      if (job?.metadata?.remote && job?.metadata?.sessionId) {
        // Remote job - use cloud API
        await api.cancelRemoteCommand({
          sessionId: job.metadata.sessionId,
          commandId: jobId,
        });

        // Update local state
        setJobs((prev: Map<string, JobInfo>) => {
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
        return;
      }

      // Local job - existing WebSocket/REST logic
      const ws = wsConnections.current.get(jobId);
      if (ws && ws.readyState === WebSocket.OPEN) {
        api.sendCancelRequest(ws);
      }

      // Also call the REST API to ensure cancellation
      await api.cancelJob(jobId);

      // Update local state
      setJobs((prev: Map<string, JobInfo>) => {
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
      throw error;
    }
  }, [jobs]);

  /**
   * Update the status and details of a spawned job.
   * Used for remote job polling to update job state when status changes.
   */
  const updateSpawnedJobStatus = useCallback((jobId: string, updates: Partial<JobInfo>) => {
    setJobs((prev: Map<string, JobInfo>) => {
      const updated = new Map(prev);
      const job = updated.get(jobId);
      if (job) {
        updated.set(jobId, { ...job, ...updates });
      }
      return updated;
    });
  }, []);

  /**
   * Remove a job from the list (for cleanup).
   */
  const removeJob = useCallback((jobId: string) => {
    setJobs((prev: Map<string, JobInfo>) => {
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
    setJobs((prev: Map<string, JobInfo>) => {
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
   * These jobs run in separate terminal windows with automatic completion tracking.
   * The terminal script calls back to the server when done.
   * For remote jobs, metadata should include { remote: true, sessionId: string }.
   */
  const addSpawnedJob = useCallback((
    displayCommand: string,
    command: string,
    serverJobId?: string,
    metadata?: { remote?: boolean; sessionId?: string; [key: string]: any }
  ): string => {
    // Use server-provided job ID if available, otherwise generate one
    const jobId = serverJobId || `spawned-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`;

    const jobInfo: JobInfo = {
      id: jobId,
      command,
      displayCommand,
      status: 'running',
      progress: null,
      output: [
        metadata?.remote
          ? 'Command running on remote session.'
          : 'Command running in separate terminal window.',
        '',
        'Status will update automatically when command completes.',
      ],
      cost: 0,
      startedAt: new Date(),
      completedAt: null,
      error: null,
      metadata,
    };

    setJobs((prev: Map<string, JobInfo>) => {
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
    setJobs((prev: Map<string, JobInfo>) => {
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

  /**
   * Manually mark any job with a final status (completed, failed, or cancelled).
   * Useful for remote jobs when automatic status detection isn't working.
   */
  const markJobStatus = useCallback((jobId: string, status: 'completed' | 'failed' | 'cancelled') => {
    setJobs((prev: Map<string, JobInfo>) => {
      const updated = new Map(prev);
      const job = updated.get(jobId);
      if (job) {
        const statusMessages: Record<string, string> = {
          completed: '✓ Manually marked as completed by user.',
          failed: '✗ Manually marked as failed by user.',
          cancelled: '⚠ Manually marked as cancelled by user.',
        };
        updated.set(jobId, {
          ...job,
          status,
          completedAt: new Date(),
          output: [...job.output, '', statusMessages[status]],
        });
        if (onJobComplete) {
          onJobComplete({ ...job, status }, status === 'completed');
        }
      }
      return updated;
    });
  }, [onJobComplete]);

  /**
   * Poll for spawned job status updates.
   * The terminal script calls back to the server when done, and we poll to detect it.
   */
  useEffect(() => {
    // Get spawned jobs that are still running (local, non-WebSocket jobs)
    // These are jobs added via addSpawnedJob - they don't have WebSocket connections
    // and aren't remote (remote jobs have their own polling below)
    const spawnedRunningJobs = (Array.from(jobs.values()) as JobInfo[]).filter(
      (j) => j.status === 'running' && !j.metadata?.remote && !wsConnections.current.has(j.id)
    );

    if (spawnedRunningJobs.length === 0) return;

    const pollInterval = setInterval(async () => {
      // Use jobsRef to get latest state (avoid stale closure)
      const currentJobs = jobsRef.current;
      const jobsToPoll = (Array.from(currentJobs.values()) as JobInfo[]).filter(
        (j) => j.status === 'running' && !j.metadata?.remote && !wsConnections.current.has(j.id)
      );

      for (const job of jobsToPoll) {
        try {
          const status = await api.getSpawnedJobStatus(job.id);
          if (status.status === 'completed' || status.status === 'failed') {
            // Auto-update job status
            const success = status.status === 'completed';
            let completedJobForCallback: { job: JobInfo; success: boolean } | null = null;

            setJobs((prev: Map<string, JobInfo>) => {
              const updated = new Map(prev);
              const currentJob = updated.get(job.id);
              if (currentJob && currentJob.status === 'running') {
                const completedJob: JobInfo = {
                  ...currentJob,
                  status: success ? 'completed' : 'failed',
                  completedAt: new Date(),
                  output: [
                    ...currentJob.output,
                    '',
                    success
                      ? `✓ Command completed successfully (exit code: ${status.exit_code || 0})`
                      : `✗ Command failed (exit code: ${status.exit_code || 1})`,
                  ],
                };
                updated.set(job.id, completedJob);
                completedJobForCallback = { job: completedJob, success };
              }
              return updated;
            });

            // Trigger callback outside setState using ref for latest callback
            if (completedJobForCallback && onJobCompleteRef.current) {
              onJobCompleteRef.current(completedJobForCallback.job, completedJobForCallback.success);
            }
          }
        } catch (e) {
          // Ignore polling errors - server might be temporarily unavailable
        }
      }
    }, 2000); // Poll every 2 seconds

    return () => clearInterval(pollInterval);
  }, [jobs]);

  /**
   * Poll for remote job status updates.
   * Remote jobs run on a different machine and we poll the cloud for status updates.
   * Uses jobsRef to always get the latest job state inside the polling callback.
   */
  useEffect(() => {
    // Check if there are any remote running jobs
    const remoteJobs = (Array.from(jobs.values()) as JobInfo[]).filter(
      (j) => j.metadata?.remote
    );
    const hasRemoteRunningJobs = remoteJobs.some(j => j.status === 'running');

    if (!hasRemoteRunningJobs) return;

    const pollInterval = setInterval(async () => {
      // Use jobsRef to get the LATEST jobs state (avoid stale closure)
      const currentJobs = jobsRef.current;
      const remoteRunningJobs = (Array.from(currentJobs.values()) as JobInfo[]).filter(
        (j) => j.metadata?.remote && j.status === 'running'
      );

      for (const job of remoteRunningJobs) {
        if (!job.metadata?.sessionId) continue;

        try {
          const status = await api.getRemoteCommandStatus(
            job.metadata.sessionId,
            job.id
          );

          console.log(`[Remote Poll] Job ${job.id}: cloud status = ${status?.status || 'null'}`);

          if (!status) {
            console.warn(`[Remote Poll] Job ${job.id}: no status returned from cloud`);
            continue;
          }

          // Update output if streaming - parse line by line
          if (status.status === 'processing' && status.response?.streaming) {
            setJobs((prev: Map<string, JobInfo>) => {
              const updated = new Map(prev);
              const currentJob = updated.get(job.id);
              if (currentJob && currentJob.status === 'running') {
                // Parse stdout and stderr into lines
                const newLines: string[] = [];
                if (status.response?.stdout) {
                  const stdoutLines = status.response.stdout.split('\n').filter((l: string) => l.trim());
                  newLines.push(...stdoutLines);
                }
                if (status.response?.stderr) {
                  const stderrLines = status.response.stderr.split('\n').filter((l: string) => l.trim());
                  newLines.push(...stderrLines.map((l: string) => `[stderr] ${l}`));
                }

                if (newLines.length > 0) {
                  // Replace the placeholder message with actual output
                  const isPlaceholder = currentJob.output.length <= 3 &&
                    currentJob.output.some((line: string) =>
                      line.includes('Command running') || line.includes('Status will update')
                    );

                  updated.set(job.id, {
                    ...currentJob,
                    output: isPlaceholder ? newLines : newLines,
                  });
                }
              }
              return updated;
            });
          }

          // Check for completion
          if (status.status === 'completed' || status.status === 'failed' || status.status === 'cancelled') {
            console.log(`[Remote Poll] Job ${job.id}: detected terminal status '${status.status}'`);
            const success = status.status === 'completed';
            const cancelled = status.status === 'cancelled';

            // Store completed job info to call callback outside setState
            let completedJobForCallback: { job: JobInfo; success: boolean } | null = null;

            setJobs((prev: Map<string, JobInfo>) => {
              const updated = new Map(prev);
              const currentJob = updated.get(job.id);
              // Allow update from running or queued status
              if (currentJob && (currentJob.status === 'running' || currentJob.status === 'queued')) {
                // Parse final output line by line
                const finalOutput: string[] = [];

                // Add final output from response, parsed line by line
                if (status.response?.stdout) {
                  const stdoutLines = status.response.stdout.split('\n').filter((l: string) => l.trim());
                  finalOutput.push(...stdoutLines);
                }
                if (status.response?.stderr) {
                  const stderrLines = status.response.stderr.split('\n').filter((l: string) => l.trim());
                  finalOutput.push(...stderrLines.map((l: string) => `[stderr] ${l}`));
                }

                // Add status message
                if (cancelled) {
                  finalOutput.push('', '⚠ Command was cancelled');
                } else if (success) {
                  finalOutput.push('', `✓ Command completed successfully`);
                } else {
                  finalOutput.push('', `✗ Command failed: ${status.response?.message || 'Unknown error'}`);
                }

                const completedJob: JobInfo = {
                  ...currentJob,
                  status: cancelled ? 'cancelled' : (success ? 'completed' : 'failed'),
                  completedAt: new Date(),
                  output: finalOutput.length > 0 ? finalOutput : currentJob.output,
                  cost: status.response?.cost || 0,
                  error: success ? null : (status.response?.message || 'Command failed'),
                };
                updated.set(job.id, completedJob);

                // Store for callback outside setState
                completedJobForCallback = { job: completedJob, success };
              }
              return updated;
            });

            // Trigger callback outside setState using ref for latest callback
            if (completedJobForCallback && onJobCompleteRef.current) {
              onJobCompleteRef.current(completedJobForCallback.job, completedJobForCallback.success);
            }
          }
        } catch (e) {
          // Ignore polling errors - cloud might be temporarily unavailable
          console.warn('Failed to poll remote job status:', e);
        }
      }
    }, 2000); // Poll every 2 seconds

    return () => clearInterval(pollInterval);
  }, [jobs]);

  // Derived state
  const activeJobs = Array.from(jobs.values()).filter(
    (j: JobInfo) => j.status === 'queued' || j.status === 'running'
  );
  const completedJobs = Array.from(jobs.values()).filter(
    (j: JobInfo) => j.status === 'completed' || j.status === 'failed' || j.status === 'cancelled'
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
    markJobStatus,
    updateSpawnedJobStatus,
  };
}

export default useJobs;
