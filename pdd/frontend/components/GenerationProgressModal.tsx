import React from 'react';
import { PromptGenerationResult } from '../api';
import { CheckIcon, SpinnerIcon } from './Icon';

interface GenerationProgressModalProps {
  isOpen: boolean;
  progress: { current: number; total: number; currentModule: string } | null;
  results: PromptGenerationResult[] | null;
  onClose: () => void;
  onCancel?: () => void;
}

const GenerationProgressModal: React.FC<GenerationProgressModalProps> = ({
  isOpen,
  progress,
  results,
  onClose,
  onCancel,
}) => {
  if (!isOpen) return null;

  const isComplete = results !== null && progress === null;
  const successCount = results?.filter(r => r.success).length || 0;
  const failCount = results?.filter(r => !r.success).length || 0;

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center">
      {/* Backdrop */}
      <div
        className="absolute inset-0 bg-black/60 backdrop-blur-sm"
        onClick={isComplete ? onClose : undefined}
      />

      {/* Modal */}
      <div className="relative glass rounded-2xl border border-surface-700/50 p-6 max-w-md w-full mx-4 shadow-2xl">
        {/* Header */}
        <div className="flex items-center justify-between mb-4">
          <h3 className="text-lg font-semibold text-white">
            {isComplete ? 'Generation Complete' : 'Generating Prompts'}
          </h3>
          {isComplete && (
            <button
              onClick={onClose}
              className="p-1.5 hover:bg-surface-700 rounded-lg transition-colors"
            >
              <svg className="w-5 h-5 text-surface-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
              </svg>
            </button>
          )}
        </div>

        {/* Progress State */}
        {progress && !isComplete && (
          <div className="space-y-4">
            {/* Progress bar */}
            <div className="relative h-2 bg-surface-700 rounded-full overflow-hidden">
              <div
                className="absolute left-0 top-0 h-full bg-gradient-to-r from-emerald-500 to-emerald-400 transition-all duration-300"
                style={{ width: `${(progress.current / progress.total) * 100}%` }}
              />
            </div>

            {/* Progress text */}
            <div className="flex items-center justify-between text-sm">
              <span className="text-surface-400">
                Generating prompt {progress.current} of {progress.total}
              </span>
              <span className="text-white font-medium">
                {Math.round((progress.current / progress.total) * 100)}%
              </span>
            </div>

            {/* Current module */}
            <div className="flex items-center gap-2 p-3 bg-surface-800/50 rounded-lg">
              <SpinnerIcon className="w-4 h-4 text-emerald-400 animate-spin" />
              <span className="text-sm text-surface-300 truncate">
                {progress.currentModule}
              </span>
            </div>

            {/* Stop button */}
            {onCancel && (
              <button
                onClick={onCancel}
                className="w-full px-4 py-2.5 bg-red-500/20 hover:bg-red-500/30 text-red-300 border border-red-500/30 rounded-xl font-medium transition-colors"
              >
                Stop Generation
              </button>
            )}
          </div>
        )}

        {/* Results State */}
        {isComplete && results && (
          <div className="space-y-4">
            {/* Summary */}
            <div className="flex items-center gap-4 p-3 bg-surface-800/50 rounded-lg">
              <div className="flex items-center gap-2">
                <div className="w-3 h-3 rounded-full bg-emerald-500" />
                <span className="text-sm text-surface-300">{successCount} succeeded</span>
              </div>
              {failCount > 0 && (
                <div className="flex items-center gap-2">
                  <div className="w-3 h-3 rounded-full bg-red-500" />
                  <span className="text-sm text-surface-300">{failCount} failed</span>
                </div>
              )}
            </div>

            {/* Results list */}
            <div className="max-h-64 overflow-y-auto space-y-2">
              {results.map((result, index) => (
                <div
                  key={index}
                  className={`flex items-start gap-2 p-2 rounded-lg ${
                    result.success ? 'bg-emerald-500/10' : 'bg-red-500/10'
                  }`}
                >
                  <div className="flex-shrink-0 mt-0.5">
                    {result.success ? (
                      <CheckIcon className="w-4 h-4 text-emerald-400" />
                    ) : (
                      <svg className="w-4 h-4 text-red-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                        <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
                      </svg>
                    )}
                  </div>
                  <div className="flex-1 min-w-0">
                    <span className={`text-sm ${result.success ? 'text-emerald-300' : 'text-red-300'}`}>
                      {result.module}.prompt
                    </span>
                    {result.error && (
                      <p className="text-xs text-red-400 mt-1 truncate">{result.error}</p>
                    )}
                  </div>
                </div>
              ))}
            </div>

            {/* Close button */}
            <button
              onClick={onClose}
              className="w-full px-4 py-2.5 bg-accent-600 hover:bg-accent-500 text-white rounded-xl font-medium transition-colors"
            >
              Close
            </button>
          </div>
        )}
      </div>
    </div>
  );
};

export default GenerationProgressModal;
