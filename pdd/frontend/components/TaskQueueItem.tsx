/**
 * TaskQueueItem - Displays a single task in the queue with status and actions.
 */

import React from 'react';
import { TaskQueueItem as TaskItem, TaskStatus } from '../hooks/useTaskQueue';

interface TaskQueueItemProps {
  task: TaskItem;
  index: number;
  onRemove: () => void;
  onSkip: () => void;
  onRetry: () => void;
  onRunNow: () => void;
  isDraggable: boolean;
  onDragStart?: (e: React.DragEvent) => void;
  onDragOver?: (e: React.DragEvent) => void;
  onDrop?: (e: React.DragEvent) => void;
  onDragEnd?: () => void;
}

/**
 * Format duration in human-readable format.
 */
function formatDuration(startedAt?: Date, completedAt?: Date): string {
  if (!startedAt) return '';
  const end = completedAt || new Date();
  const seconds = Math.floor((end.getTime() - startedAt.getTime()) / 1000);

  if (seconds < 60) return `${seconds}s`;
  const minutes = Math.floor(seconds / 60);
  const remainingSeconds = seconds % 60;
  if (minutes < 60) return `${minutes}m ${remainingSeconds}s`;
  const hours = Math.floor(minutes / 60);
  const remainingMinutes = minutes % 60;
  return `${hours}h ${remainingMinutes}m`;
}

/**
 * Get status badge styling.
 */
function getStatusStyle(status: TaskStatus): { bg: string; text: string; icon: string } {
  switch (status) {
    case 'pending':
      return { bg: 'bg-surface-500/20', text: 'text-surface-400', icon: 'clock' };
    case 'running':
      return { bg: 'bg-accent-500/20', text: 'text-accent-400', icon: 'spinner' };
    case 'completed':
      return { bg: 'bg-green-500/20', text: 'text-green-400', icon: 'check' };
    case 'failed':
      return { bg: 'bg-red-500/20', text: 'text-red-400', icon: 'x' };
    case 'skipped':
      return { bg: 'bg-yellow-500/20', text: 'text-yellow-400', icon: 'skip' };
    default:
      return { bg: 'bg-surface-500/20', text: 'text-surface-400', icon: 'question' };
  }
}

const TaskQueueItem: React.FC<TaskQueueItemProps> = ({
  task,
  index,
  onRemove,
  onSkip,
  onRetry,
  onRunNow,
  isDraggable,
  onDragStart,
  onDragOver,
  onDrop,
  onDragEnd,
}) => {
  // Safety check
  if (!task) {
    return null;
  }

  const statusStyle = getStatusStyle(task.status || 'pending');
  const isActive = task.status === 'running';
  const isPending = task.status === 'pending';
  const isFailed = task.status === 'failed';
  const isCompleted = task.status === 'completed' || task.status === 'skipped';

  return (
    <div
      draggable={isDraggable}
      onDragStart={onDragStart}
      onDragOver={onDragOver}
      onDrop={onDrop}
      onDragEnd={onDragEnd}
      className={`
        relative p-3 rounded-lg border transition-all duration-200
        ${isActive
          ? 'border-accent-500/50 bg-accent-500/10'
          : isCompleted
            ? 'border-surface-700/30 bg-surface-800/30 opacity-75'
            : 'border-surface-700/50 bg-surface-800/50 hover:border-surface-600'
        }
        ${isDraggable ? 'cursor-grab active:cursor-grabbing' : ''}
      `}
    >
      <div className="flex items-start gap-3">
        {/* Drag handle and index */}
        <div className="flex items-center gap-2 pt-0.5">
          {isDraggable ? (
            <div className="text-surface-500 hover:text-surface-400 cursor-grab">
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 8h16M4 16h16" />
              </svg>
            </div>
          ) : (
            <div className="w-4" />
          )}
          <span className="text-xs text-surface-500 font-mono w-4 text-center">
            {index + 1}
          </span>
        </div>

        {/* Task info */}
        <div className="flex-1 min-w-0">
          <div className="flex items-start justify-between gap-2">
            <h4 className="text-sm font-medium text-white truncate" title={task.displayCommand || 'Task'}>
              {task.displayCommand || 'Task'}
            </h4>
          </div>

          <div className="flex items-center gap-2 mt-1">
            {/* Status badge */}
            <span className={`inline-flex items-center gap-1 px-2 py-0.5 rounded-full text-xs font-medium ${statusStyle.bg} ${statusStyle.text}`}>
              {statusStyle.icon === 'spinner' && (
                <svg className="w-3 h-3 animate-spin" viewBox="0 0 24 24">
                  <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                  <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                </svg>
              )}
              {statusStyle.icon === 'check' && (
                <svg className="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
                </svg>
              )}
              {statusStyle.icon === 'x' && (
                <svg className="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
                </svg>
              )}
              {statusStyle.icon === 'clock' && (
                <svg className="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 8v4l3 3m6-3a9 9 0 11-18 0 9 9 0 0118 0z" />
                </svg>
              )}
              {statusStyle.icon === 'skip' && (
                <svg className="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M13 5l7 7-7 7M5 5l7 7-7 7" />
                </svg>
              )}
              {task.status}
            </span>

            {/* Duration */}
            {(isActive || isCompleted) && task.startedAt && (
              <span className="text-xs text-surface-500">
                {formatDuration(task.startedAt, task.completedAt)}
              </span>
            )}

            {/* Job ID if linked */}
            {task.jobId && (
              <span className="text-xs text-surface-600 font-mono">
                #{task.jobId.slice(-6)}
              </span>
            )}
          </div>

          {/* Error message */}
          {task.error && (
            <p className="text-xs text-red-400 mt-1 truncate" title={task.error}>
              {task.error}
            </p>
          )}
        </div>

        {/* Actions */}
        <div className="flex items-center gap-1">
          {isPending && (
            <>
              <button
                onClick={(e) => {
                  e.stopPropagation();
                  onRunNow();
                }}
                className="p-1.5 text-accent-400 hover:bg-accent-500/20 rounded transition-colors"
                title="Run now"
              >
                <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M14.752 11.168l-3.197-2.132A1 1 0 0010 9.87v4.263a1 1 0 001.555.832l3.197-2.132a1 1 0 000-1.664z" />
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
                </svg>
              </button>
              <button
                onClick={(e) => {
                  e.stopPropagation();
                  onSkip();
                }}
                className="p-1.5 text-yellow-400 hover:bg-yellow-500/20 rounded transition-colors"
                title="Skip this task"
              >
                <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M13 5l7 7-7 7M5 5l7 7-7 7" />
                </svg>
              </button>
            </>
          )}

          {isFailed && (
            <button
              onClick={(e) => {
                e.stopPropagation();
                onRetry();
              }}
              className="p-1.5 text-accent-400 hover:bg-accent-500/20 rounded transition-colors"
              title="Retry this task"
            >
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
              </svg>
            </button>
          )}

          {!isActive && (
            <button
              onClick={(e) => {
                e.stopPropagation();
                onRemove();
              }}
              className="p-1.5 text-surface-500 hover:text-red-400 hover:bg-red-500/20 rounded transition-colors"
              title="Remove from queue"
            >
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
              </svg>
            </button>
          )}
        </div>
      </div>

      {/* Running indicator */}
      {isActive && (
        <div className="mt-2 h-1 bg-surface-700 rounded-full overflow-hidden">
          <div className="h-full w-1/3 bg-gradient-to-r from-accent-600 to-accent-400 rounded-full animate-indeterminate" />
        </div>
      )}
    </div>
  );
};

export default TaskQueueItem;
