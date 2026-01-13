/**
 * TaskQueueControls - Control bar for task queue execution.
 *
 * Provides execution mode toggle (Auto/Manual), start/pause/resume buttons,
 * and clear buttons.
 */

import React from 'react';
import { ExecutionMode } from '../hooks/useTaskQueue';

interface TaskQueueControlsProps {
  executionMode: ExecutionMode;
  isQueueRunning: boolean;
  isPaused: boolean;
  hasPendingTasks: boolean;
  hasCompletedTasks: boolean;
  hasAnyTasks: boolean;
  progress: {
    total: number;
    completed: number;
    pending: number;
    running: number;
  };
  onSetExecutionMode: (mode: ExecutionMode) => void;
  onStartQueue: () => void;
  onPauseQueue: () => void;
  onResumeQueue: () => void;
  onRunNextTask: () => void;
  onClearCompleted: () => void;
  onClearAll: () => void;
}

const TaskQueueControls: React.FC<TaskQueueControlsProps> = ({
  executionMode,
  isQueueRunning,
  isPaused,
  hasPendingTasks,
  hasCompletedTasks,
  hasAnyTasks,
  progress,
  onSetExecutionMode,
  onStartQueue,
  onPauseQueue,
  onResumeQueue,
  onRunNextTask,
  onClearCompleted,
  onClearAll,
}) => {
  return (
    <div className="space-y-3">
      {/* Execution Mode Toggle */}
      <div className="flex items-center justify-between">
        <span className="text-xs text-surface-400">Execution Mode</span>
        <div className="flex items-center bg-surface-800 rounded-lg p-0.5 border border-surface-700">
          <button
            onClick={() => onSetExecutionMode('auto')}
            className={`
              px-3 py-1 text-xs font-medium rounded-md transition-colors
              ${executionMode === 'auto'
                ? 'bg-accent-600 text-white'
                : 'text-surface-400 hover:text-white'
              }
            `}
          >
            Auto
          </button>
          <button
            onClick={() => onSetExecutionMode('manual')}
            className={`
              px-3 py-1 text-xs font-medium rounded-md transition-colors
              ${executionMode === 'manual'
                ? 'bg-accent-600 text-white'
                : 'text-surface-400 hover:text-white'
              }
            `}
          >
            Manual
          </button>
        </div>
      </div>

      {/* Progress */}
      {hasAnyTasks && (
        <div className="flex items-center justify-between text-xs">
          <span className="text-surface-400">Progress</span>
          <span className="text-surface-300">
            {progress.completed} / {progress.total} completed
          </span>
        </div>
      )}

      {/* Progress Bar */}
      {hasAnyTasks && progress.total > 0 && (
        <div className="h-1.5 bg-surface-700 rounded-full overflow-hidden">
          <div
            className="h-full bg-gradient-to-r from-accent-600 to-green-500 rounded-full transition-all duration-300"
            style={{ width: `${(progress.completed / progress.total) * 100}%` }}
          />
        </div>
      )}

      {/* Action Buttons */}
      <div className="flex items-center gap-2 flex-wrap">
        {/* Start / Pause / Resume buttons */}
        {executionMode === 'auto' && (
          <>
            {!isQueueRunning && hasPendingTasks && (
              <button
                onClick={onStartQueue}
                className="flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium bg-accent-600 text-white hover:bg-accent-500 rounded-lg transition-colors"
              >
                <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M14.752 11.168l-3.197-2.132A1 1 0 0010 9.87v4.263a1 1 0 001.555.832l3.197-2.132a1 1 0 000-1.664z" />
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
                </svg>
                Start Queue
              </button>
            )}
            {isQueueRunning && !isPaused && (
              <button
                onClick={onPauseQueue}
                className="flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium bg-yellow-600 text-white hover:bg-yellow-500 rounded-lg transition-colors"
              >
                <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M10 9v6m4-6v6m7-3a9 9 0 11-18 0 9 9 0 0118 0z" />
                </svg>
                Pause
              </button>
            )}
            {isQueueRunning && isPaused && (
              <button
                onClick={onResumeQueue}
                className="flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium bg-accent-600 text-white hover:bg-accent-500 rounded-lg transition-colors"
              >
                <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M14.752 11.168l-3.197-2.132A1 1 0 0010 9.87v4.263a1 1 0 001.555.832l3.197-2.132a1 1 0 000-1.664z" />
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
                </svg>
                Resume
              </button>
            )}
          </>
        )}

        {/* Manual mode: Run Next button */}
        {executionMode === 'manual' && hasPendingTasks && progress.running === 0 && (
          <button
            onClick={onRunNextTask}
            className="flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium bg-accent-600 text-white hover:bg-accent-500 rounded-lg transition-colors"
          >
            <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M13 5l7 7-7 7M5 5l7 7-7 7" />
            </svg>
            Run Next
          </button>
        )}

        {/* Clear buttons */}
        {hasCompletedTasks && (
          <button
            onClick={onClearCompleted}
            className="flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium bg-surface-700 text-surface-300 hover:bg-surface-600 rounded-lg transition-colors"
          >
            <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
            </svg>
            Clear Completed
          </button>
        )}

        {hasAnyTasks && (
          <button
            onClick={onClearAll}
            className="flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium text-red-400 bg-red-500/10 hover:bg-red-500/20 border border-red-500/20 rounded-lg transition-colors"
          >
            <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 7l-.867 12.142A2 2 0 0116.138 21H7.862a2 2 0 01-1.995-1.858L5 7m5 4v6m4-6v6m1-10V4a1 1 0 00-1-1h-4a1 1 0 00-1 1v3M4 7h16" />
            </svg>
            Clear All
          </button>
        )}
      </div>
    </div>
  );
};

export default TaskQueueControls;
