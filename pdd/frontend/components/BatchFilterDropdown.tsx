/**
 * BatchFilterDropdown Component
 *
 * A dropdown for filtering and syncing prompts by batch (connected component).
 * Shows batch options with color indicators, module list, and a "Sync Batch" button.
 */

import React, { useState } from 'react';
import type { Batch } from '../lib/batchUtils';

interface BatchFilterDropdownProps {
  batches: Batch[];
  selectedBatch: Batch | null;
  onSelectBatch: (batch: Batch | null) => void;
  onSyncBatch?: (batch: Batch) => void;
  remainingCountByBatch?: Map<number, number>;
  disabled?: boolean;
  /** Show expanded view with module list (for sidebar) */
  showModuleList?: boolean;
}

const BatchFilterDropdown: React.FC<BatchFilterDropdownProps> = ({
  batches,
  selectedBatch,
  onSelectBatch,
  onSyncBatch,
  remainingCountByBatch = new Map(),
  disabled = false,
  showModuleList = false,
}) => {
  const [expandedBatchId, setExpandedBatchId] = useState<number | null>(null);

  // Don't show if only 1 or 0 batches (no point filtering)
  if (batches.length <= 1) return null;

  const selectedRemaining = selectedBatch
    ? remainingCountByBatch.get(selectedBatch.id) ?? selectedBatch.modules.length
    : 0;

  // Helper to extract display name from filename
  const getDisplayName = (filename: string) => {
    return filename.replace(/_[A-Za-z]+\.prompt$/, '').replace(/\.prompt$/, '');
  };

  // Compact view (for graph panel)
  if (!showModuleList) {
    return (
      <div className="flex items-center gap-2">
        {/* Batch Filter Dropdown */}
        <select
          value={selectedBatch?.id ?? 'all'}
          onChange={(e) => {
            if (e.target.value === 'all') {
              onSelectBatch(null);
            } else {
              const batch = batches.find(b => b.id === parseInt(e.target.value));
              onSelectBatch(batch || null);
            }
          }}
          disabled={disabled}
          className="px-3 py-1.5 bg-surface-800/50 border border-surface-600 rounded-lg text-sm text-white focus:outline-none focus:border-accent-500 disabled:opacity-50 disabled:cursor-not-allowed"
        >
          <option value="all">All Batches ({batches.length})</option>
          {batches.map(batch => (
            <option key={batch.id} value={batch.id}>
              {batch.name} ({batch.modules.length} modules)
            </option>
          ))}
        </select>

        {/* Batch color indicator */}
        {selectedBatch && (
          <div
            className="w-4 h-4 rounded-full border-2 border-white/20 flex-shrink-0"
            style={{ backgroundColor: selectedBatch.color }}
            title={`${selectedBatch.name}: ${selectedBatch.modules.length} modules`}
          />
        )}

        {/* Sync Batch Button */}
        {selectedBatch && onSyncBatch && (
          <button
            onClick={() => onSyncBatch(selectedBatch)}
            disabled={disabled || selectedRemaining === 0}
            className={`px-3 py-1.5 rounded-lg text-sm font-medium flex items-center gap-1.5 transition-colors ${
              disabled || selectedRemaining === 0
                ? 'bg-surface-700 text-surface-500 cursor-not-allowed'
                : 'bg-gradient-to-r from-[#FDCE49] to-[#DFA84A] hover:from-[#FFD966] hover:to-[#FDCE49] text-surface-900'
            }`}
          >
            <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
            </svg>
            Sync Batch ({selectedRemaining})
          </button>
        )}
      </div>
    );
  }

  // Expanded view with module list (for sidebar)
  return (
    <div className="space-y-2">
      {batches.map(batch => {
        const isExpanded = expandedBatchId === batch.id;
        const isSelected = selectedBatch?.id === batch.id;
        const remaining = remainingCountByBatch.get(batch.id) ?? batch.modules.length;

        return (
          <div
            key={batch.id}
            className={`rounded-lg border transition-colors ${
              isSelected
                ? 'border-accent-500 bg-accent-500/10'
                : 'border-surface-700 bg-surface-800/30 hover:border-surface-600'
            }`}
          >
            {/* Batch Header */}
            <div
              className="flex items-center gap-2 p-2 cursor-pointer"
              onClick={() => {
                onSelectBatch(isSelected ? null : batch);
                setExpandedBatchId(isExpanded ? null : batch.id);
              }}
            >
              {/* Batch color indicator */}
              <div
                className="w-3 h-3 rounded-full flex-shrink-0"
                style={{ backgroundColor: batch.color }}
              />

              {/* Batch name and count */}
              <div className="flex-1 min-w-0">
                <span className="text-sm text-white font-medium">{batch.name}</span>
                <span className="text-xs text-surface-400 ml-1.5">
                  ({batch.modules.length} modules)
                </span>
              </div>

              {/* Expand/collapse icon */}
              <svg
                className={`w-4 h-4 text-surface-400 transition-transform ${isExpanded ? 'rotate-180' : ''}`}
                fill="none"
                stroke="currentColor"
                viewBox="0 0 24 24"
              >
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
              </svg>
            </div>

            {/* Module List (expanded) */}
            {isExpanded && (
              <div className="border-t border-surface-700/50 p-2">
                <div className="max-h-32 overflow-y-auto space-y-1">
                  {batch.modules.map((module, idx) => (
                    <div
                      key={module.filename}
                      className="flex items-center gap-2 text-xs text-surface-300 py-0.5"
                    >
                      <span className="text-surface-500 w-4 text-right">{idx + 1}.</span>
                      <span className="truncate" title={module.filename}>
                        {getDisplayName(module.filename)}
                      </span>
                      <span className="text-surface-500 text-[10px]">P{module.priority}</span>
                    </div>
                  ))}
                </div>

                {/* Sync Batch Button */}
                {onSyncBatch && (
                  <button
                    onClick={(e) => {
                      e.stopPropagation();
                      onSyncBatch(batch);
                    }}
                    disabled={disabled || remaining === 0}
                    className={`mt-2 w-full px-3 py-1.5 rounded-lg text-xs font-medium flex items-center justify-center gap-1.5 transition-colors ${
                      disabled || remaining === 0
                        ? 'bg-surface-700 text-surface-500 cursor-not-allowed'
                        : 'bg-gradient-to-r from-[#FDCE49] to-[#DFA84A] hover:from-[#FFD966] hover:to-[#FDCE49] text-surface-900'
                    }`}
                  >
                    <svg className="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
                    </svg>
                    Sync {batch.name} ({remaining} remaining)
                  </button>
                )}
              </div>
            )}
          </div>
        );
      })}
    </div>
  );
};

export default BatchFilterDropdown;
