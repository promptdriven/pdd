/**
 * JobDashboard - Main container for viewing all jobs.
 *
 * Layout:
 * - Collapsible panel showing active and recent jobs
 * - Split view with job list on left, selected job output on right
 */

import React, { useState } from 'react';
import { JobInfo } from '../hooks/useJobs';
import JobCard from './JobCard';
import JobOutputPanel from './JobOutputPanel';

// Batch operation tracking (for architecture prompt generation, etc.)
export interface BatchOperation {
  id: string;
  name: string;
  current: number;
  total: number;
  currentItem: string;
  status: 'running' | 'completed' | 'failed';
  startedAt: Date;
}

interface JobDashboardProps {
  activeJobs: JobInfo[];
  completedJobs: JobInfo[];
  selectedJob: JobInfo | null;
  onSelectJob: (jobId: string | null) => void;
  onCancelJob: (jobId: string) => void;
  onRemoveJob: (jobId: string) => void;
  onClearCompleted: () => void;
  // Mark spawned job as done
  onMarkSpawnedDone?: (jobId: string, success: boolean) => void;
  // Mark any job with manual status (for remote jobs)
  onMarkJobStatus?: (jobId: string, status: 'completed' | 'failed' | 'cancelled') => void;
  // Optional batch operation tracking
  batchOperation?: BatchOperation | null;
  onCancelBatchOperation?: () => void;
  // Visibility control - dashboard only shows when explicitly opened
  isVisible: boolean;
  onClose: () => void;
}

const JobDashboard: React.FC<JobDashboardProps> = ({
  activeJobs,
  completedJobs,
  selectedJob,
  onSelectJob,
  onCancelJob,
  onRemoveJob,
  onClearCompleted,
  onMarkSpawnedDone,
  onMarkJobStatus,
  batchOperation,
  onCancelBatchOperation,
  isVisible,
  onClose,
}) => {
  const [isCollapsed, setIsCollapsed] = useState(false);
  const hasJobs = activeJobs.length > 0 || completedJobs.length > 0;
  const hasBatchOp = batchOperation && batchOperation.status === 'running';

  // Only render when explicitly visible (controlled by Jobs button)
  if (!isVisible) {
    return null;
  }

  return (
    <div className="fixed bottom-12 left-0 right-0 z-50 pointer-events-none" data-job-dashboard>
      {/* Main dashboard panel - positioned above footer, max 60rem width, centered */}
      <div
        className={`
          pointer-events-auto mx-auto mb-2 bg-surface-900/95 backdrop-blur-lg rounded-2xl border border-surface-700/50 shadow-2xl
          transition-all duration-300 ease-in-out max-w-[60rem] mx-4 sm:mx-auto
          ${isCollapsed ? 'max-h-14' : 'max-h-[65vh]'}
        `}
        style={{ marginLeft: 'auto', marginRight: 'auto', width: 'calc(100% - 2rem)' }}
      >
        {/* Header bar with gold accent */}
        <div
          className="flex items-center justify-between px-4 py-3 border-b border-surface-700/50 cursor-pointer bg-gradient-to-r from-surface-800/80 to-surface-900/80"
          onClick={() => setIsCollapsed(!isCollapsed)}
        >
          <div className="flex items-center gap-3">
            {/* Toggle icon with gold accent when jobs active */}
            <div className={`w-7 h-7 rounded-lg flex items-center justify-center transition-all ${
              activeJobs.length > 0
                ? 'bg-[#FDCE49]/20 text-[#FDCE49]'
                : isCollapsed
                  ? 'bg-accent-500/20 text-accent-400'
                  : 'bg-surface-700 text-white'
            }`}>
              <svg
                className={`w-4 h-4 transition-transform duration-200 ${isCollapsed ? '' : 'rotate-180'}`}
                fill="none"
                stroke="currentColor"
                viewBox="0 0 24 24"
              >
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2.5} d="M5 15l7-7 7 7" />
              </svg>
            </div>

            <h2 className="text-base font-semibold text-white">
              Jobs
            </h2>

            {/* Batch operation badge */}
            {hasBatchOp && (
              <span className="px-2 py-0.5 text-xs font-medium bg-purple-500/20 text-purple-400 rounded-full flex items-center gap-1">
                <svg className="animate-spin h-3 w-3" viewBox="0 0 24 24">
                  <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                  <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                </svg>
                {batchOperation!.name}
              </span>
            )}

            {/* Active jobs badge with gold styling */}
            {activeJobs.length > 0 && (
              <span className="px-2.5 py-0.5 text-xs font-medium bg-[#FDCE49]/20 text-[#FDCE49] rounded-full flex items-center gap-1.5 animate-pulse">
                <span className="w-1.5 h-1.5 rounded-full bg-[#FDCE49]" />
                {activeJobs.length} running
              </span>
            )}

            {/* Completed jobs badge */}
            {completedJobs.length > 0 && (
              <span className="px-2 py-0.5 text-xs font-medium bg-surface-700 text-surface-400 rounded-full">
                {completedJobs.length} completed
              </span>
            )}
          </div>

          <div className="flex items-center gap-2" onClick={(e) => e.stopPropagation()}>
            {completedJobs.length > 0 && (
              <button
                onClick={onClearCompleted}
                className="px-3 py-1.5 text-xs font-medium text-surface-400 hover:text-white hover:bg-surface-700 rounded-lg transition-colors"
              >
                Clear completed
              </button>
            )}
            {/* Close button */}
            <button
              onClick={onClose}
              className="p-1.5 text-surface-400 hover:text-white hover:bg-surface-700 rounded-lg transition-colors"
              title="Close jobs panel"
            >
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
              </svg>
            </button>
          </div>
        </div>

        {/* Content (hidden when collapsed) - Single column with expandable cards */}
        {!isCollapsed && (
          <div className="overflow-y-auto p-4 max-h-[calc(65vh-3.5rem)]">
            {/* Batch operation section */}
            {hasBatchOp && batchOperation && (
              <div className="mb-4">
                <h3 className="text-xs font-medium text-purple-400 uppercase tracking-wider mb-3">
                  Batch Operation
                </h3>
                <div className="bg-surface-800/50 rounded-xl p-4 border border-purple-500/20">
                  <div className="flex items-center justify-between mb-2">
                    <span className="text-sm font-medium text-white">{batchOperation.name}</span>
                    {onCancelBatchOperation && (
                      <button
                        onClick={onCancelBatchOperation}
                        className="px-2 py-1 text-xs text-red-400 hover:text-red-300 hover:bg-red-500/10 rounded transition-colors"
                      >
                        Cancel
                      </button>
                    )}
                  </div>
                  <div className="flex items-center gap-2 text-xs text-surface-400 mb-2">
                    <span>{batchOperation.current} / {batchOperation.total}</span>
                    <span className="text-surface-600">•</span>
                    <span className="text-purple-400">{batchOperation.currentItem}</span>
                  </div>
                  {/* Progress bar */}
                  <div className="h-1.5 bg-surface-700 rounded-full overflow-hidden">
                    <div
                      className="h-full bg-gradient-to-r from-purple-500 to-accent-500 transition-all duration-300"
                      style={{ width: `${(batchOperation.current / batchOperation.total) * 100}%` }}
                    />
                  </div>
                </div>
              </div>
            )}

            {/* Active jobs section - Expandable cards */}
            {activeJobs.length > 0 && (
              <div className="mb-4">
                <h3 className="text-xs font-medium text-[#FDCE49] uppercase tracking-wider mb-3 flex items-center gap-2">
                  <span className="w-2 h-2 rounded-full bg-[#FDCE49] animate-pulse" />
                  Active Jobs
                </h3>
                <div className="space-y-2">
                  {activeJobs.map((job) => (
                    <div key={job.id} className="bg-surface-800/50 rounded-xl border border-surface-700/50 overflow-hidden">
                      <JobCard
                        job={job}
                        isSelected={selectedJob?.id === job.id}
                        onSelect={() => onSelectJob(selectedJob?.id === job.id ? null : job.id)}
                        onCancel={() => onCancelJob(job.id)}
                        onRemove={() => onRemoveJob(job.id)}
                        onMarkDone={onMarkSpawnedDone ? (success) => onMarkSpawnedDone(job.id, success) : undefined}
                        onMarkStatus={onMarkJobStatus ? (status) => onMarkJobStatus(job.id, status) : undefined}
                      />
                      {/* Inline output - indented 15% when expanded */}
                      {selectedJob?.id === job.id && (
                        <div className="border-t border-surface-700/50 bg-surface-900/50" style={{ marginLeft: '15%' }}>
                          <JobOutputPanel
                            job={job}
                            onCancel={() => onCancelJob(job.id)}
                            onClose={() => onSelectJob(null)}
                          />
                        </div>
                      )}
                    </div>
                  ))}
                </div>
              </div>
            )}

            {/* Completed jobs section - Expandable cards */}
            {completedJobs.length > 0 && (
              <div>
                <h3 className="text-xs font-medium text-surface-500 uppercase tracking-wider mb-3">
                  Recent Jobs
                </h3>
                <div className="space-y-2">
                  {completedJobs.slice(0, 10).map((job) => (
                    <div key={job.id} className="bg-surface-800/30 rounded-xl border border-surface-700/30 overflow-hidden">
                      <JobCard
                        job={job}
                        isSelected={selectedJob?.id === job.id}
                        onSelect={() => onSelectJob(selectedJob?.id === job.id ? null : job.id)}
                        onCancel={() => {}}
                        onRemove={() => onRemoveJob(job.id)}
                      />
                      {/* Inline output - indented 15% when expanded */}
                      {selectedJob?.id === job.id && (
                        <div className="border-t border-surface-700/50 bg-surface-900/50" style={{ marginLeft: '15%' }}>
                          <JobOutputPanel
                            job={job}
                            onCancel={() => {}}
                            onClose={() => onSelectJob(null)}
                          />
                        </div>
                      )}
                    </div>
                  ))}
                </div>
              </div>
            )}

            {/* Empty state */}
            {activeJobs.length === 0 && completedJobs.length === 0 && (
              <div className="text-center py-8">
                <svg
                  className="w-12 h-12 text-surface-600 mx-auto mb-3"
                  fill="none"
                  stroke="currentColor"
                  viewBox="0 0 24 24"
                >
                  <path
                    strokeLinecap="round"
                    strokeLinejoin="round"
                    strokeWidth={1.5}
                    d="M19 11H5m14 0a2 2 0 012 2v6a2 2 0 01-2 2H5a2 2 0 01-2-2v-6a2 2 0 012-2m14 0V9a2 2 0 00-2-2M5 11V9a2 2 0 012-2m0 0V5a2 2 0 012-2h6a2 2 0 012 2v2M7 7h10"
                  />
                </svg>
                <p className="text-surface-500 text-sm">No jobs yet</p>
                <p className="text-surface-600 text-xs mt-1">
                  Run a command to see it here
                </p>
              </div>
            )}
          </div>
        )}
      </div>
    </div>
  );
};

export default JobDashboard;
