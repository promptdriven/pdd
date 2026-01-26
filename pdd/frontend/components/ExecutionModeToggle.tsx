import React from 'react';

interface ExecutionModeToggleProps {
  mode: 'local' | 'remote';
  onModeChange: (mode: 'local' | 'remote') => void;
  disabled?: boolean;
}

const ExecutionModeToggle: React.FC<ExecutionModeToggleProps> = ({
  mode,
  onModeChange,
  disabled = false,
}) => {
  return (
    <div className="flex items-center gap-1.5 sm:gap-2">
      <div
        className="flex bg-surface-800 border border-surface-700 rounded-lg p-0.5 sm:p-1"
        role="group"
        aria-label="Execution mode"
      >
        {/* Local Execution Button */}
        <button
          onClick={() => onModeChange('local')}
          disabled={disabled}
          className={`flex items-center gap-1.5 sm:gap-2 px-2 sm:px-3 py-1 sm:py-1.5 rounded-md text-xs sm:text-sm font-medium transition-all ${
            mode === 'local'
              ? 'bg-blue-500 text-white shadow-sm'
              : 'text-surface-400 hover:text-surface-200'
          } disabled:opacity-50 disabled:cursor-not-allowed`}
          title="Execute commands on this machine"
        >
          {/* Computer Icon */}
          <svg className="w-3.5 h-3.5 sm:w-4 sm:h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path
              strokeLinecap="round"
              strokeLinejoin="round"
              strokeWidth={2}
              d="M9.75 17L9 20l-1 1h8l-1-1-.75-3M3 13h18M5 17h14a2 2 0 002-2V5a2 2 0 00-2-2H5a2 2 0 00-2 2v10a2 2 0 002 2z"
            />
          </svg>
          <span>Local</span>
        </button>

        {/* Remote Control Button */}
        <button
          onClick={() => onModeChange('remote')}
          disabled={disabled}
          className={`flex items-center gap-1.5 sm:gap-2 px-2 sm:px-3 py-1 sm:py-1.5 rounded-md text-xs sm:text-sm font-medium transition-all ${
            mode === 'remote'
              ? 'bg-purple-500 text-white shadow-sm'
              : 'text-surface-400 hover:text-surface-200'
          } disabled:opacity-50 disabled:cursor-not-allowed`}
          title="Control a remote session via cloud"
        >
          {/* Cloud Icon */}
          <svg className="w-3.5 h-3.5 sm:w-4 sm:h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path
              strokeLinecap="round"
              strokeLinejoin="round"
              strokeWidth={2}
              d="M3 15a4 4 0 004 4h9a5 5 0 10-.1-9.999 5.002 5.002 0 10-9.78 2.096A4.001 4.001 0 003 15z"
            />
          </svg>
          <span>Remote</span>
        </button>
      </div>

      {/* Info tooltip - hide on small screens */}
      {mode === 'remote' && !disabled && (
        <span className="hidden sm:flex text-xs text-purple-400 items-center gap-1">
          <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path
              strokeLinecap="round"
              strokeLinejoin="round"
              strokeWidth={2}
              d="M13 16h-1v-4h-1m1-4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z"
            />
          </svg>
          Commands will execute on the selected remote session
        </span>
      )}
    </div>
  );
};

export default ExecutionModeToggle;
