/**
 * JobOutputPanel - Displays detailed output for a selected job.
 *
 * Features:
 * - Streaming output with auto-scroll
 * - Progress bar
 * - Copy output button
 * - Cancel/Close actions
 */

import React, { useRef, useEffect, useState } from 'react';
import { JobInfo } from '../hooks/useJobs';

interface JobOutputPanelProps {
  job: JobInfo;
  onCancel: () => void;
  onClose: () => void;
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

const JobOutputPanel: React.FC<JobOutputPanelProps> = ({
  job,
  onCancel,
  onClose,
}) => {
  const outputRef = useRef<HTMLDivElement>(null);
  const [autoScroll, setAutoScroll] = useState(true);
  const [copied, setCopied] = useState(false);
  const [duration, setDuration] = useState(formatDuration(job.startedAt, job.completedAt));

  const isActive = job.status === 'queued' || job.status === 'running';
  const progressPercent = job.progress
    ? Math.round((job.progress.current / job.progress.total) * 100)
    : null;

  // Update duration every second for active jobs
  useEffect(() => {
    if (!isActive) return;

    const interval = setInterval(() => {
      setDuration(formatDuration(job.startedAt, null));
    }, 1000);

    return () => clearInterval(interval);
  }, [isActive, job.startedAt]);

  // Auto-scroll to bottom when new output arrives
  useEffect(() => {
    if (autoScroll && outputRef.current) {
      outputRef.current.scrollTop = outputRef.current.scrollHeight;
    }
  }, [job.output, autoScroll]);

  // Detect manual scroll to disable auto-scroll
  const handleScroll = () => {
    if (!outputRef.current) return;
    const { scrollTop, scrollHeight, clientHeight } = outputRef.current;
    // If user scrolled up more than 50px from bottom, disable auto-scroll
    const isAtBottom = scrollHeight - scrollTop - clientHeight < 50;
    setAutoScroll(isAtBottom);
  };

  // Copy output to clipboard
  const handleCopy = async () => {
    const text = job.output.join('\n');
    try {
      await navigator.clipboard.writeText(text);
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    } catch (e) {
      console.error('Failed to copy:', e);
    }
  };

  return (
    <div className="flex flex-col h-full bg-surface-900 rounded-xl border border-surface-700/50 overflow-hidden">
      {/* Header */}
      <div className="flex items-center justify-between px-4 py-3 bg-surface-800/50 border-b border-surface-700/50">
        <div className="flex items-center gap-3 min-w-0">
          {/* Status indicator */}
          <div className={`w-2 h-2 rounded-full flex-shrink-0 ${
            job.status === 'running' ? 'bg-accent-400 animate-pulse' :
            job.status === 'queued' ? 'bg-yellow-400' :
            job.status === 'completed' ? 'bg-green-400' :
            job.status === 'failed' ? 'bg-red-400' :
            'bg-surface-400'
          }`} />
          <div className="min-w-0">
            <h3 className="text-sm font-medium text-white truncate">
              {job.displayCommand}
            </h3>
            <div className="flex items-center gap-2 text-xs text-surface-400">
              <span className="capitalize">{job.status}</span>
              <span>•</span>
              <span>{duration}</span>
              {job.cost > 0 && (
                <>
                  <span>•</span>
                  <span className="font-mono">${job.cost.toFixed(3)}</span>
                </>
              )}
            </div>
          </div>
        </div>

        {/* Actions */}
        <div className="flex items-center gap-2">
          <button
            onClick={handleCopy}
            className="px-3 py-1.5 text-xs font-medium text-surface-300 bg-surface-700/50 hover:bg-surface-700 border border-surface-600/50 rounded-lg transition-colors flex items-center gap-1.5"
            title="Copy output"
          >
            {copied ? (
              <>
                <svg className="w-3.5 h-3.5 text-green-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
                </svg>
                Copied
              </>
            ) : (
              <>
                <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M8 16H6a2 2 0 01-2-2V6a2 2 0 012-2h8a2 2 0 012 2v2m-6 12h8a2 2 0 002-2v-8a2 2 0 00-2-2h-8a2 2 0 00-2 2v8a2 2 0 002 2z" />
                </svg>
                Copy
              </>
            )}
          </button>

          {isActive && (
            <button
              onClick={onCancel}
              className="px-3 py-1.5 text-xs font-medium text-red-400 bg-red-500/10 hover:bg-red-500/20 border border-red-500/20 rounded-lg transition-colors"
            >
              Cancel
            </button>
          )}

          <button
            onClick={onClose}
            className="p-1.5 text-surface-400 hover:text-white hover:bg-surface-700 rounded-lg transition-colors"
            title="Close"
          >
            <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
            </svg>
          </button>
        </div>
      </div>

      {/* Progress bar */}
      {isActive && (
        <div className="px-4 py-2 bg-surface-800/30 border-b border-surface-700/30">
          {progressPercent !== null ? (
            <div>
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
          ) : (
            <div className="h-1.5 bg-surface-700 rounded-full overflow-hidden">
              <div className="h-full w-1/3 bg-gradient-to-r from-accent-600 to-accent-400 rounded-full animate-indeterminate" />
            </div>
          )}
        </div>
      )}

      {/* Output area */}
      <div
        ref={outputRef}
        onScroll={handleScroll}
        className="flex-1 overflow-auto p-4 font-mono text-sm"
      >
        {job.output.length === 0 ? (
          <div className="text-surface-500 text-center py-8">
            {isActive ? 'Waiting for output...' : 'No output'}
          </div>
        ) : (
          <pre className="whitespace-pre-wrap break-words text-surface-300">
            {job.output.map((line, i) => (
              <div
                key={i}
                className={`${
                  line.startsWith('[stderr]')
                    ? 'text-red-400'
                    : line.startsWith('>')
                      ? 'text-accent-400'
                      : ''
                }`}
              >
                {line}
              </div>
            ))}
          </pre>
        )}

        {/* Auto-scroll indicator */}
        {!autoScroll && job.output.length > 0 && (
          <button
            onClick={() => {
              setAutoScroll(true);
              if (outputRef.current) {
                outputRef.current.scrollTop = outputRef.current.scrollHeight;
              }
            }}
            className="fixed bottom-20 right-8 px-3 py-2 bg-accent-600 hover:bg-accent-500 text-white text-xs font-medium rounded-lg shadow-lg transition-colors flex items-center gap-2"
          >
            <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 14l-7 7m0 0l-7-7m7 7V3" />
            </svg>
            Scroll to bottom
          </button>
        )}
      </div>

      {/* Error message for failed jobs */}
      {job.status === 'failed' && job.error && (
        <div className="px-4 py-3 bg-red-500/10 border-t border-red-500/20">
          <div className="flex items-start gap-2">
            <svg className="w-4 h-4 text-red-400 flex-shrink-0 mt-0.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 8v4m0 4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
            </svg>
            <p className="text-sm text-red-400">{job.error}</p>
          </div>
        </div>
      )}

      {/* Success message */}
      {job.status === 'completed' && (
        <div className="px-4 py-3 bg-green-500/10 border-t border-green-500/20">
          <div className="flex items-center gap-2">
            <svg className="w-4 h-4 text-green-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
            </svg>
            <p className="text-sm text-green-400">Job completed successfully</p>
          </div>
        </div>
      )}
    </div>
  );
};

export default JobOutputPanel;
