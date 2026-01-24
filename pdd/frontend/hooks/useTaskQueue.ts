/**
 * useTaskQueue - Custom hook for managing a sequential task queue.
 *
 * Allows users to queue tasks for execution in sequence, with support for
 * auto-run mode (automatic progression) or manual mode (user-controlled).
 */

import { useState, useCallback, useEffect, useRef } from 'react';
import { PromptInfo } from '../api';
import { CommandType } from '../types';

export type TaskStatus = 'pending' | 'running' | 'completed' | 'failed' | 'skipped';
export type ExecutionMode = 'auto' | 'manual';

export interface TaskQueueItem {
  id: string;
  commandType: CommandType;  // Store enum for reconstruction
  prompt: PromptInfo;        // Required - needed to rebuild command
  rawOptions: Record<string, any>;  // Store _code, _test, _global_* for reconstruction
  displayCommand: string;
  status: TaskStatus;
  jobId?: string;
  createdAt: Date;
  startedAt?: Date;
  completedAt?: Date;
  error?: string;
}

export interface UseTaskQueueOptions {
  onTaskStart?: (task: TaskQueueItem) => void;
  onTaskComplete?: (task: TaskQueueItem, success: boolean) => void;
  onQueueComplete?: () => void;
}

const STORAGE_KEY = 'pdd-task-queue';
const MAX_QUEUE_SIZE = 50;

// Generate unique task ID
function generateTaskId(): string {
  return `task-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`;
}

export function useTaskQueue(options: UseTaskQueueOptions = {}) {
  const { onTaskStart, onTaskComplete, onQueueComplete } = options;

  // State
  const [tasks, setTasks] = useState<TaskQueueItem[]>([]);
  const [executionMode, setExecutionMode] = useState<ExecutionMode>('manual');
  const [isQueueRunning, setIsQueueRunning] = useState(false);
  const [isPaused, setIsPaused] = useState(false);

  // Ref to track current execution state without stale closures
  const stateRef = useRef({ tasks, executionMode, isQueueRunning, isPaused });
  stateRef.current = { tasks, executionMode, isQueueRunning, isPaused };

  // Ref for callbacks to avoid re-renders
  const callbacksRef = useRef({ onTaskStart, onTaskComplete, onQueueComplete });
  callbacksRef.current = { onTaskStart, onTaskComplete, onQueueComplete };

  // Function to submit a job - will be set by the parent component
  // Takes the full TaskQueueItem so it can reconstruct the command exactly
  const submitJobRef = useRef<((task: TaskQueueItem) => Promise<string | null>) | null>(null);

  // Load from localStorage on mount
  useEffect(() => {
    try {
      const saved = localStorage.getItem(STORAGE_KEY);
      if (saved) {
        const { tasks: savedTasks, executionMode: savedMode } = JSON.parse(saved);
        if (Array.isArray(savedTasks)) {
          // Only restore pending tasks, convert date strings back
          const restoredTasks = savedTasks
            .filter((t: any) => t.status === 'pending')
            .map((t: any) => ({
              ...t,
              createdAt: new Date(t.createdAt),
            }));
          setTasks(restoredTasks);
        }
        if (savedMode === 'auto' || savedMode === 'manual') {
          setExecutionMode(savedMode);
        }
      }
    } catch (e) {
      console.warn('Failed to restore task queue from localStorage:', e);
    }
  }, []);

  // Save to localStorage when tasks or mode changes
  useEffect(() => {
    try {
      const pendingTasks = tasks.filter(t => t.status === 'pending');
      localStorage.setItem(STORAGE_KEY, JSON.stringify({
        tasks: pendingTasks,
        executionMode,
      }));
    } catch (e) {
      console.warn('Failed to save task queue to localStorage:', e);
    }
  }, [tasks, executionMode]);

  /**
   * Add a new task to the queue.
   * Stores the raw inputs (commandType, prompt, rawOptions) so the command
   * can be reconstructed exactly like PromptSpace at execution time.
   */
  const addTask = useCallback((
    commandType: CommandType,
    prompt: PromptInfo,
    rawOptions: Record<string, any>,
    displayCommand: string
  ) => {
    const newTask: TaskQueueItem = {
      id: generateTaskId(),
      commandType,
      prompt,
      rawOptions,
      displayCommand,
      status: 'pending',
      createdAt: new Date(),
    };

    setTasks(prev => {
      if (prev.length >= MAX_QUEUE_SIZE) {
        console.warn(`Task queue is full (${MAX_QUEUE_SIZE} items). Cannot add more tasks.`);
        return prev;
      }
      return [...prev, newTask];
    });

    return newTask.id;
  }, []);

  /**
   * Remove a task from the queue.
   */
  const removeTask = useCallback((taskId: string) => {
    setTasks(prev => prev.filter(t => t.id !== taskId));
  }, []);

  /**
   * Reorder tasks in the queue (only pending tasks can be reordered).
   */
  const reorderTasks = useCallback((fromIndex: number, toIndex: number) => {
    setTasks(prev => {
      const newTasks = [...prev];
      // Only allow reordering pending tasks
      if (newTasks[fromIndex]?.status !== 'pending') {
        return prev;
      }
      const [removed] = newTasks.splice(fromIndex, 1);
      newTasks.splice(toIndex, 0, removed);
      return newTasks;
    });
  }, []);

  /**
   * Clear all tasks from the queue.
   */
  const clearQueue = useCallback(() => {
    setTasks([]);
    setIsQueueRunning(false);
    setIsPaused(false);
  }, []);

  /**
   * Clear only completed tasks.
   */
  const clearCompleted = useCallback(() => {
    setTasks(prev => prev.filter(t => t.status === 'pending' || t.status === 'running'));
  }, []);

  /**
   * Update a task in the queue.
   */
  const updateTask = useCallback((taskId: string, updates: Partial<TaskQueueItem>) => {
    setTasks(prev => prev.map(t =>
      t.id === taskId ? { ...t, ...updates } : t
    ));
  }, []);

  /**
   * Run the next pending task.
   */
  const runNextPendingTask = useCallback(async () => {
    const state = stateRef.current;

    if (state.isPaused) {
      return;
    }

    const nextTask = state.tasks.find(t => t.status === 'pending');
    if (!nextTask) {
      setIsQueueRunning(false);
      callbacksRef.current.onQueueComplete?.();
      return;
    }

    if (!submitJobRef.current) {
      console.error('submitJob function not set. Cannot run task.');
      return;
    }

    // Mark as running
    updateTask(nextTask.id, {
      status: 'running',
      startedAt: new Date()
    });

    callbacksRef.current.onTaskStart?.(nextTask);

    try {
      // Submit the job - pass the full task so command can be reconstructed
      const jobId = await submitJobRef.current(nextTask);

      if (jobId) {
        updateTask(nextTask.id, { jobId });
      } else {
        // Job submission failed
        updateTask(nextTask.id, {
          status: 'failed',
          completedAt: new Date(),
          error: 'Failed to submit job',
        });
        callbacksRef.current.onTaskComplete?.({ ...nextTask, status: 'failed' }, false);

        // Auto-pause queue on failure so user can investigate
        if (state.executionMode === 'auto' && state.isQueueRunning) {
          setIsPaused(true);
        }
      }
    } catch (e) {
      const error = e instanceof Error ? e.message : 'Unknown error';
      updateTask(nextTask.id, {
        status: 'failed',
        completedAt: new Date(),
        error,
      });
      callbacksRef.current.onTaskComplete?.({ ...nextTask, status: 'failed' }, false);

      // Auto-pause queue on failure so user can investigate
      if (state.executionMode === 'auto' && state.isQueueRunning) {
        setIsPaused(true);
      }
    }
  }, [updateTask]);

  /**
   * Handle job completion (called by useJobs onJobComplete).
   */
  const handleJobComplete = useCallback((jobId: string, success: boolean) => {
    const task = stateRef.current.tasks.find(t => t.jobId === jobId);
    if (!task) return;

    const newStatus: TaskStatus = success ? 'completed' : 'failed';
    updateTask(task.id, {
      status: newStatus,
      completedAt: new Date(),
      error: success ? undefined : 'Job failed',
    });

    callbacksRef.current.onTaskComplete?.({ ...task, status: newStatus }, success);

    const state = stateRef.current;
    if (state.executionMode === 'auto' && state.isQueueRunning && !state.isPaused) {
      if (success) {
        // Continue to next task on success
        setTimeout(() => runNextPendingTask(), 100);
      } else {
        // Auto-pause queue on failure so user can investigate
        setIsPaused(true);
      }
    }
  }, [updateTask, runNextPendingTask]);

  /**
   * Start the queue (begin running tasks).
   */
  const startQueue = useCallback(async () => {
    setIsQueueRunning(true);
    setIsPaused(false);
    await runNextPendingTask();
  }, [runNextPendingTask]);

  /**
   * Pause the queue (stop auto-progression).
   */
  const pauseQueue = useCallback(() => {
    setIsPaused(true);
  }, []);

  /**
   * Resume the queue after pausing.
   */
  const resumeQueue = useCallback(async () => {
    setIsPaused(false);
    // Only run next if we were running before and have pending tasks
    const hasRunning = stateRef.current.tasks.some(t => t.status === 'running');
    if (!hasRunning) {
      await runNextPendingTask();
    }
  }, [runNextPendingTask]);

  /**
   * Run the next task manually (for manual mode).
   */
  const runNextTask = useCallback(async () => {
    if (!isQueueRunning) {
      setIsQueueRunning(true);
    }
    setIsPaused(false);
    await runNextPendingTask();
  }, [runNextPendingTask, isQueueRunning]);

  /**
   * Skip a task.
   */
  const skipTask = useCallback((taskId: string) => {
    const task = stateRef.current.tasks.find(t => t.id === taskId);
    if (!task) return;

    updateTask(taskId, {
      status: 'skipped',
      completedAt: new Date()
    });
    callbacksRef.current.onTaskComplete?.({ ...task, status: 'skipped' }, false);

    // If this was the running task, move to next in auto mode
    if (task.status === 'running' || task.status === 'pending') {
      const state = stateRef.current;
      if (state.executionMode === 'auto' && state.isQueueRunning && !state.isPaused) {
        setTimeout(() => runNextPendingTask(), 100);
      }
    }
  }, [updateTask, runNextPendingTask]);

  /**
   * Retry a failed task.
   */
  const retryTask = useCallback((taskId: string) => {
    updateTask(taskId, {
      status: 'pending',
      jobId: undefined,
      startedAt: undefined,
      completedAt: undefined,
      error: undefined,
    });
  }, [updateTask]);

  /**
   * Set the function used to submit jobs (called by parent component).
   * The function receives the full task so it can reconstruct the command
   * exactly like PromptSpace does.
   */
  const setSubmitJob = useCallback((fn: (task: TaskQueueItem) => Promise<string | null>) => {
    submitJobRef.current = fn;
  }, []);

  // Derived state
  const pendingTasks = tasks.filter(t => t.status === 'pending');
  const completedTasks = tasks.filter(t => t.status === 'completed' || t.status === 'failed' || t.status === 'skipped');
  const runningTask = tasks.find(t => t.status === 'running') || null;
  const hasRunningTask = runningTask !== null;
  const progress = {
    total: tasks.length,
    completed: completedTasks.length,
    pending: pendingTasks.length,
    running: hasRunningTask ? 1 : 0,
  };

  return {
    // State
    tasks,
    executionMode,
    isQueueRunning,
    isPaused,
    runningTask,
    pendingTasks,
    completedTasks,
    progress,

    // Task management
    addTask,
    removeTask,
    reorderTasks,
    clearQueue,
    clearCompleted,
    skipTask,
    retryTask,

    // Execution control
    setExecutionMode,
    startQueue,
    pauseQueue,
    resumeQueue,
    runNextTask,

    // Integration
    handleJobComplete,
    setSubmitJob,
  };
}

export default useTaskQueue;
