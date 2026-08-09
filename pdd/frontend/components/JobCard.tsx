/**
 * JobCard - Displays a single job with status, progress bar, and actions.
 */

import React from 'react';
import { JobInfo, JobStatus } from '../hooks/useJobs';

interface JobCardProps {
  job: JobInfo;
  isSelected: boolean;
  onSelect: () => void;
  onCancel: () => void;
  onRemove?: () => void;
  onMarkDone?: (success: boolean) => void;
  onMarkStatus?: (status: 'completed' | 'failed' | 'cancelled') => void;
}

/**
 * Format duration in human-readable format.
 */
function formatDuration(startedAt: Date, completedAt: Date | null): string {
  const end = completedAt || new Date();
  const seconds = Math.floor((end.getTime() - startedAt.getTime()) / 1000);

  if (seconds < 60) {
    return `${seconds}s`;
  }
  const minutes = Math.floor(seconds / 60);
  const remainingSeconds = seconds % 60;
  if (minutes < 60) {
    return `${minutes}m ${remainingSeconds}s`;
  }
  const hours = Math.floor(minutes / 60);
  const remainingMinutes = minutes % 60;
  return `${hours}h ${remainingMinutes}m`;
}

/**
 * Format relative time (e.g., "5m ago").
 */
function formatTimeAgo(date: Date): string {
  const seconds = Math.floor((new Date().getTime() - date.getTime()) / 1000);
  if (seconds < 60) return `${seconds}s ago`;
  const minutes = Math.floor(seconds / 60);
  if (minutes < 60) return `${minutes}m ago`;
  const hours = Math.floor(minutes / 60);
  if (hours < 24) return `${hours}h ago`;
  const days = Math.floor(hours / 24);
  return `${days}d ago`;
}

/**
 * Extract dev unit name from a display command string.
 * Looks for prompt filenames like "prompts/orders_Python.prompt" or module names.
 */
function extractDevUnitName(displayCommand: string): string | null {
  // Match prompts/MODULE_LANG.prompt pattern
  const promptMatch = displayCommand.match(/prompts\/([^_\s]+)/);
  if (promptMatch) return promptMatch[1];

  // Match MODULE_LANG.prompt pattern directly
  const fileMatch = displayCommand.match(/([a-zA-Z_]+)_[A-Za-z]+\.prompt/);
  if (fileMatch) return fileMatch[1];

  // Match -m MODULE or --module MODULE
  const moduleMatch = displayCommand.match(/(?:-m|--module)\s+(\S+)/);
  if (moduleMatch) return moduleMatch[1];

  return null;
}

/**
 * Get status badge styling.
 */
function getStatusStyle(status: JobStatus): { bg: string; text: string; icon: string } {
  switch (status) {
    case 'queued':
      return { bg: 'bg-yellow-500/20', text: 'text-yellow-400', icon: 'clock' };
    case 'running':
      return { bg: 'bg-accent-500/20', text: 'text-accent-400', icon: 'spinner' };
    case 'completed':
      return { bg: 'bg-green-500/20', text: 'text-green-400', icon: 'check' };
    case 'failed':
      return { bg: 'bg-red-500/20', text: 'text-red-400', icon: 'x' };
    case 'cancelled':
      return { bg: 'bg-surface-500/20', text: 'text-surface-400', icon: 'slash' };
    default:
      return { bg: 'bg-surface-500/20', text: 'text-surface-400', icon: 'question' };
  }
}

const JobCard: React.FC<JobCardProps> = ({
  job,
  isSelected,
  onSelect,
  onCancel,
  onRemove,
  onMarkDone,
  onMarkStatus,
}) => {
  const statusStyle = getStatusStyle(job.status);
  const isActive = job.status === 'queued' || job.status === 'running';
  const isSpawnedJob = job.id.startsWith('spawned-');
  const isRemoteJob = job.metadata?.remote === true;
  const devUnitName = extractDevUnitName(job.displayCommand);
  const progressPercent = job.progress
    ? Math.round((job.progress.current / job.progress.total) * 100)
    : null;

  return (
    <div
      onClick={onSelect}
      className={`
        relative p-4 rounded-xl border cursor-pointer transition-all duration-200
        ${isSelected
          ? 'border-accent-500 bg-accent-500/10 shadow-lg shadow-accent-500/10'
          : 'border-surface-700/50 bg-surface-800/50 hover:border-surface-600 hover:bg-surface-800/80'
        }
      `}
    >
      {/* Header: Command name and status */}
      <div className="flex items-start justify-between gap-2 mb-3">
        <div className="flex-1 min-w-0">
          <div className="flex items-center gap-2">
            <h3 className="text-sm font-medium text-white truncate" title={job.displayCommand}>
              {job.displayCommand}
            </h3>
            {devUnitName && (
              <span className="flex-shrink-0 px-2 py-0.5 rounded-md text-[10px] font-medium bg-purple-500/15 text-purple-300 border border-purple-500/25">
                {devUnitName}
              </span>
            )}
          </div>
          <div className="flex items-center gap-2 mt-1">
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
              {statusStyle.icon === 'slash' && (
                <svg className="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M18.364 18.364A9 9 0 005.636 5.636m12.728 12.728A9 9 0 015.636 5.636m12.728 12.728L5.636 5.636" />
                </svg>
              )}
              {job.status}
            </span>
            <span className="text-xs text-surface-500">
              {isActive
                ? formatDuration(job.startedAt, null)
                : job.completedAt
                  ? formatTimeAgo(job.completedAt)
                  : formatDuration(job.startedAt, null)
              }
            </span>
          </div>
        </div>

        {/* Cost display */}
        {job.cost > 0 && (
          <span className="text-xs text-surface-400 font-mono">
            ${job.cost.toFixed(3)}
          </span>
        )}
      </div>

      {/* Progress bar (only for running jobs with progress) */}
      {isActive && progressPercent !== null && (
        <div className="mb-3">
          <div className="flex items-center justify-between text-xs mb-1">
            <span className="text-surface-400 truncate max-w-[70%]">
              {job.progress?.message || 'Processing...'}
            </span>
            <span className="text-accent-400 font-medium">
              {progressPercent}%
            </span>
          </div>
          <div className="h-1.5 bg-surface-700 rounded-full overflow-hidden">
            <div
              className="h-full bg-gradient-to-r from-accent-600 to-accent-400 rounded-full transition-all duration-300"
              style={{ width: `${progressPercent}%` }}
            />
          </div>
        </div>
      )}

      {/* Indeterminate progress for running jobs without progress info */}
      {job.status === 'running' && progressPercent === null && (
        <div className="mb-3">
          <div className="h-1.5 bg-surface-700 rounded-full overflow-hidden">
            <div className="h-full w-1/3 bg-gradient-to-r from-accent-600 to-accent-400 rounded-full animate-indeterminate" />
          </div>
        </div>
      )}

      {/* Output preview (last line) */}
      {job.output.length > 0 && (
        <div className="mb-3 p-2 bg-surface-900/50 rounded-lg">
          <p className="text-xs text-surface-400 font-mono truncate">
            {job.output[job.output.length - 1]}
          </p>
        </div>
      )}

      {/* Actions */}
      <div className="flex items-center gap-2 flex-wrap">
        {/* Spawned LOCAL jobs (not remote) get Mark Done buttons and Dismiss */}
        {isActive && isSpawnedJob && !isRemoteJob && onMarkDone && (
          <>
            <button
              onClick={(e) => {
                e.stopPropagation();
                onMarkDone(true);
              }}
              className="px-3 py-1.5 text-xs font-medium text-green-400 bg-green-500/10 hover:bg-green-500/20 border border-green-500/20 rounded-lg transition-colors"
              title="Mark as successfully completed"
            >
              Done
            </button>
            <button
              onClick={(e) => {
                e.stopPropagation();
                onMarkDone(false);
              }}
              className="px-3 py-1.5 text-xs font-medium text-red-400 bg-red-500/10 hover:bg-red-500/20 border border-red-500/20 rounded-lg transition-colors"
              title="Mark as failed"
            >
              Failed
            </button>
            {onRemove && (
              <button
                onClick={(e) => {
                  e.stopPropagation();
                  onRemove();
                }}
                className="px-3 py-1.5 text-xs font-medium text-surface-400 bg-surface-700/50 hover:bg-surface-700 border border-surface-600/50 rounded-lg transition-colors"
                title="Remove from dashboard (close terminal to stop command)"
              >
                Dismiss
              </button>
            )}
          </>
        )}
        {/* Remote jobs get manual status buttons and Cancel Remote */}
        {isActive && isRemoteJob && onMarkStatus && (
          <>
            <button
              onClick={(e) => {
                e.stopPropagation();
                onMarkStatus('completed');
              }}
              className="px-3 py-1.5 text-xs font-medium text-green-400 bg-green-500/10 hover:bg-green-500/20 border border-green-500/20 rounded-lg transition-colors"
              title="Mark as successfully completed"
            >
              Done
            </button>
            <button
              onClick={(e) => {
                e.stopPropagation();
                onMarkStatus('failed');
              }}
              className="px-3 py-1.5 text-xs font-medium text-red-400 bg-red-500/10 hover:bg-red-500/20 border border-red-500/20 rounded-lg transition-colors"
              title="Mark as failed"
            >
              Failed
            </button>
            <button
              onClick={(e) => {
                e.stopPropagation();
                onMarkStatus('cancelled');
              }}
              className="px-3 py-1.5 text-xs font-medium text-surface-400 bg-surface-700/50 hover:bg-surface-700 border border-surface-600/50 rounded-lg transition-colors"
              title="Mark as cancelled"
            >
              Cancelled
            </button>
          </>
        )}
        {isActive && isRemoteJob && (
          <button
            onClick={(e) => {
              e.stopPropagation();
              // TODO: Cancel remote not fully implemented yet
              alert('Cancel Remote is not fully implemented yet. Use the manual status buttons above to mark the job status.');
            }}
            className="px-3 py-1.5 text-xs font-medium text-purple-400/50 bg-purple-500/5 border border-purple-500/10 rounded-lg cursor-not-allowed"
            title="Coming soon - use manual status buttons for now"
          >
            Cancel Remote (Coming Soon)
          </button>
        )}
        {/* Regular async jobs get Cancel button */}
        {isActive && !isSpawnedJob && !isRemoteJob && (
          <button
            onClick={(e) => {
              e.stopPropagation();
              onCancel();
            }}
            className="px-3 py-1.5 text-xs font-medium text-red-400 bg-red-500/10 hover:bg-red-500/20 border border-red-500/20 rounded-lg transition-colors"
          >
            Cancel
          </button>
        )}
        {!isActive && onRemove && (
          <button
            onClick={(e) => {
              e.stopPropagation();
              onRemove();
            }}
            className="px-3 py-1.5 text-xs font-medium text-surface-400 bg-surface-700/50 hover:bg-surface-700 border border-surface-600/50 rounded-lg transition-colors"
          >
            Remove
          </button>
        )}
        <button
          onClick={(e) => {
            e.stopPropagation();
            onSelect();
          }}
          className="px-3 py-1.5 text-xs font-medium text-accent-400 bg-accent-500/10 hover:bg-accent-500/20 border border-accent-500/20 rounded-lg transition-colors ml-auto"
        >
          {isSpawnedJob ? 'Details' : 'View Output'}
        </button>
      </div>
    </div>
  );
};

export default JobCard;
