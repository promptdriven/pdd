import React, { useState } from 'react';
import { ArchitectureSyncResult, ArchitectureSyncModuleResult } from '../api';

interface SyncFromPromptModalProps {
  isOpen: boolean;
  isSyncing: boolean;
  result: ArchitectureSyncResult | null;
  onSync: () => void;
  onClose: () => void;
}

const SyncFromPromptModal: React.FC<SyncFromPromptModalProps> = ({
  isOpen,
  isSyncing,
  result,
  onSync,
  onClose,
}) => {
  const [showDetails, setShowDetails] = useState(false);

  if (!isOpen) return null;

  const hasValidationErrors = result && result.validation && !result.validation.valid;
  const hasResults = result !== null;

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center">
      {/* Backdrop */}
      <div
        className="absolute inset-0 bg-black/50 backdrop-blur-sm"
        onClick={!isSyncing ? onClose : undefined}
      />

      {/* Modal */}
      <div className="relative glass rounded-2xl border border-surface-700/50 w-full max-w-2xl max-h-[80vh] overflow-hidden flex flex-col shadow-2xl m-4">
        {/* Header */}
        <div className="flex items-center justify-between p-6 border-b border-surface-700/50">
          <div>
            <h2 className="text-xl font-semibold text-white flex items-center gap-2">
              <svg className="w-6 h-6 text-accent-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
              </svg>
              Sync from Prompts
            </h2>
            <p className="text-sm text-surface-400 mt-1">
              Update architecture.json from prompt metadata tags
            </p>
          </div>
          {!isSyncing && (
            <button
              onClick={onClose}
              className="p-2 hover:bg-surface-700 rounded-lg transition-colors"
            >
              <svg className="w-5 h-5 text-surface-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
              </svg>
            </button>
          )}
        </div>

        {/* Content */}
        <div className="flex-1 overflow-y-auto p-6">
          {!hasResults ? (
            // Pre-sync explanation
            <div className="space-y-4">
              <div className="bg-surface-800/50 border border-surface-700/50 rounded-lg p-4">
                <h3 className="text-sm font-medium text-white mb-2">What this does:</h3>
                <ul className="text-sm text-surface-300 space-y-1.5 list-disc list-inside">
                  <li>Scans all prompt files for metadata tags (<code className="text-accent-400">&lt;pdd-reason&gt;</code>, <code className="text-accent-400">&lt;pdd-interface&gt;</code>, <code className="text-accent-400">&lt;pdd-dependency&gt;</code>)</li>
                  <li>Updates corresponding entries in architecture.json</li>
                  <li>Validates the updated architecture for circular dependencies</li>
                  <li>Preserves fields not specified in tags (description, priority, tags)</li>
                </ul>
              </div>

              <div className="bg-blue-500/10 border border-blue-500/30 rounded-lg p-4 flex items-start gap-3">
                <svg className="w-5 h-5 text-blue-400 flex-shrink-0 mt-0.5" fill="currentColor" viewBox="0 0 20 20">
                  <path fillRule="evenodd" d="M18 10a8 8 0 11-16 0 8 8 0 0116 0zm-7-4a1 1 0 11-2 0 1 1 0 012 0zM9 9a1 1 0 000 2v3a1 1 0 001 1h1a1 1 0 100-2v-3a1 1 0 00-1-1H9z" clipRule="evenodd" />
                </svg>
                <div>
                  <h4 className="text-sm font-medium text-blue-300 mb-1">Source of Truth</h4>
                  <p className="text-sm text-blue-200/80">
                    Prompts are authoritative. Tags in prompt files will override what's in architecture.json.
                  </p>
                </div>
              </div>

              {isSyncing && (
                <div className="flex items-center justify-center gap-3 py-8">
                  <svg className="animate-spin h-8 w-8 text-accent-400" viewBox="0 0 24 24">
                    <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                    <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                  </svg>
                  <span className="text-surface-300">Syncing...</span>
                </div>
              )}
            </div>
          ) : (
            // Post-sync results
            <div className="space-y-4">
              {/* Summary */}
              <div className={`rounded-lg p-4 border ${
                result.success && result.validation.valid
                  ? 'bg-green-500/10 border-green-500/30'
                  : 'bg-red-500/10 border-red-500/30'
              }`}>
                <div className="flex items-start gap-3">
                  {result.success && result.validation.valid ? (
                    <svg className="w-6 h-6 text-green-400 flex-shrink-0" fill="currentColor" viewBox="0 0 20 20">
                      <path fillRule="evenodd" d="M10 18a8 8 0 100-16 8 8 0 000 16zm3.707-9.293a1 1 0 00-1.414-1.414L9 10.586 7.707 9.293a1 1 0 00-1.414 1.414l2 2a1 1 0 001.414 0l4-4z" clipRule="evenodd" />
                    </svg>
                  ) : (
                    <svg className="w-6 h-6 text-red-400 flex-shrink-0" fill="currentColor" viewBox="0 0 20 20">
                      <path fillRule="evenodd" d="M10 18a8 8 0 100-16 8 8 0 000 16zM8.707 7.293a1 1 0 00-1.414 1.414L8.586 10l-1.293 1.293a1 1 0 101.414 1.414L10 11.414l1.293 1.293a1 1 0 001.414-1.414L11.414 10l1.293-1.293a1 1 0 00-1.414-1.414L10 8.586 8.707 7.293z" clipRule="evenodd" />
                    </svg>
                  )}
                  <div className="flex-1">
                    <h3 className={`text-sm font-semibold mb-1 ${
                      result.success && result.validation.valid ? 'text-green-300' : 'text-red-300'
                    }`}>
                      {result.success && result.validation.valid
                        ? 'Sync Completed Successfully'
                        : hasValidationErrors
                        ? 'Validation Errors Detected'
                        : 'Sync Failed'}
                    </h3>
                    <p className={`text-sm ${
                      result.success && result.validation.valid ? 'text-green-200/80' : 'text-red-200/80'
                    }`}>
                      Updated {result.updated_count} module{result.updated_count !== 1 ? 's' : ''}
                      {result.skipped_count > 0 && `, skipped ${result.skipped_count}`}
                    </p>
                  </div>
                </div>
              </div>

              {/* Validation Errors */}
              {hasValidationErrors && (
                <div className="bg-red-500/10 border border-red-500/30 rounded-lg p-4">
                  <h4 className="text-sm font-medium text-red-300 mb-2">Validation Errors:</h4>
                  <ul className="text-sm text-red-200/80 space-y-1">
                    {result.validation.errors.map((err, i) => (
                      <li key={i} className="flex items-start gap-2">
                        <span className="text-red-400 flex-shrink-0">•</span>
                        <span>{err.message}</span>
                      </li>
                    ))}
                  </ul>
                </div>
              )}

              {/* Sync Errors */}
              {result.errors && result.errors.length > 0 && (
                <div className="bg-yellow-500/10 border border-yellow-500/30 rounded-lg p-4">
                  <h4 className="text-sm font-medium text-yellow-300 mb-2">Sync Warnings:</h4>
                  <ul className="text-sm text-yellow-200/80 space-y-1">
                    {result.errors.map((err, i) => (
                      <li key={i} className="flex items-start gap-2">
                        <span className="text-yellow-400 flex-shrink-0">•</span>
                        <span>{err}</span>
                      </li>
                    ))}
                  </ul>
                </div>
              )}

              {/* Details Toggle */}
              {result.results && result.results.length > 0 && (
                <button
                  onClick={() => setShowDetails(!showDetails)}
                  className="w-full px-4 py-2 bg-surface-700 hover:bg-surface-600 rounded-lg text-sm text-white flex items-center justify-between transition-colors"
                >
                  <span>{showDetails ? 'Hide' : 'Show'} Detailed Changes</span>
                  <svg className={`w-4 h-4 transition-transform ${showDetails ? 'rotate-180' : ''}`} fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                  </svg>
                </button>
              )}

              {/* Detailed Results */}
              {showDetails && result.results && (
                <div className="space-y-3 max-h-64 overflow-y-auto">
                  {result.results.map((moduleResult, idx) => (
                    <ModuleResultCard key={idx} result={moduleResult} />
                  ))}
                </div>
              )}
            </div>
          )}
        </div>

        {/* Footer */}
        <div className="flex items-center justify-end gap-3 p-6 border-t border-surface-700/50">
          {!hasResults ? (
            <>
              <button
                onClick={onClose}
                disabled={isSyncing}
                className="px-4 py-2 text-sm text-surface-300 hover:text-white transition-colors disabled:opacity-50"
              >
                Cancel
              </button>
              <button
                onClick={onSync}
                disabled={isSyncing}
                className="px-4 py-2 bg-accent-600 hover:bg-accent-500 text-white rounded-lg text-sm font-medium transition-colors disabled:opacity-50 disabled:cursor-not-allowed flex items-center gap-2"
              >
                {isSyncing && (
                  <svg className="animate-spin h-4 w-4" viewBox="0 0 24 24">
                    <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                    <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                  </svg>
                )}
                {isSyncing ? 'Syncing...' : 'Sync Now'}
              </button>
            </>
          ) : (
            <button
              onClick={onClose}
              className="px-4 py-2 bg-surface-700 hover:bg-surface-600 text-white rounded-lg text-sm font-medium transition-colors"
            >
              Close
            </button>
          )}
        </div>
      </div>
    </div>
  );
};

// Component to display individual module result
const ModuleResultCard: React.FC<{ result: ArchitectureSyncModuleResult }> = ({ result }) => {
  const [showChanges, setShowChanges] = useState(false);
  const hasChanges = result.changes && Object.keys(result.changes).length > 0;

  return (
    <div className="bg-surface-800/50 border border-surface-700/50 rounded-lg p-3">
      <div className="flex items-start justify-between mb-2">
        <div className="flex items-center gap-2">
          {result.success ? (
            result.updated ? (
              <svg className="w-4 h-4 text-green-400 flex-shrink-0" fill="currentColor" viewBox="0 0 20 20">
                <path fillRule="evenodd" d="M10 18a8 8 0 100-16 8 8 0 000 16zm3.707-9.293a1 1 0 00-1.414-1.414L9 10.586 7.707 9.293a1 1 0 00-1.414 1.414l2 2a1 1 0 001.414 0l4-4z" clipRule="evenodd" />
              </svg>
            ) : (
              <svg className="w-4 h-4 text-surface-400 flex-shrink-0" fill="currentColor" viewBox="0 0 20 20">
                <path fillRule="evenodd" d="M10 18a8 8 0 100-16 8 8 0 000 16zm0-2a6 6 0 100-12 6 6 0 000 12z" clipRule="evenodd" />
              </svg>
            )
          ) : (
            <svg className="w-4 h-4 text-red-400 flex-shrink-0" fill="currentColor" viewBox="0 0 20 20">
              <path fillRule="evenodd" d="M10 18a8 8 0 100-16 8 8 0 000 16zM8.707 7.293a1 1 0 00-1.414 1.414L8.586 10l-1.293 1.293a1 1 0 101.414 1.414L10 11.414l1.293 1.293a1 1 0 001.414-1.414L11.414 10l1.293-1.293a1 1 0 00-1.414-1.414L10 8.586 8.707 7.293z" clipRule="evenodd" />
            </svg>
          )}
          <span className="text-sm font-mono text-white">{result.filename}</span>
        </div>
        {hasChanges && (
          <button
            onClick={() => setShowChanges(!showChanges)}
            className="text-xs text-accent-400 hover:text-accent-300 flex items-center gap-1"
          >
            {showChanges ? 'Hide' : 'Show'} changes
            <svg className={`w-3 h-3 transition-transform ${showChanges ? 'rotate-180' : ''}`} fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
            </svg>
          </button>
        )}
      </div>

      <p className="text-xs text-surface-400">
        {result.updated ? `Updated: ${Object.keys(result.changes).join(', ')}` : result.error || 'No changes needed'}
      </p>

      {showChanges && hasChanges && (
        <div className="mt-3 pt-3 border-t border-surface-700/30 space-y-2">
          {Object.entries(result.changes).map(([field, change]) => {
            const typedChange = change as { old: unknown; new: unknown };
            return (
              <div key={field} className="text-xs">
                <div className="text-surface-400 font-medium mb-1">{field}:</div>
                <div className="bg-surface-900/50 rounded p-2 space-y-1">
                  <div className="flex items-start gap-2">
                    <span className="text-red-400 flex-shrink-0">-</span>
                    <span className="text-red-300/80 break-all">{JSON.stringify(typedChange.old).slice(0, 100)}{JSON.stringify(typedChange.old).length > 100 ? '...' : ''}</span>
                  </div>
                  <div className="flex items-start gap-2">
                    <span className="text-green-400 flex-shrink-0">+</span>
                    <span className="text-green-300/80 break-all">{JSON.stringify(typedChange.new).slice(0, 100)}{JSON.stringify(typedChange.new).length > 100 ? '...' : ''}</span>
                  </div>
                </div>
              </div>
            );
          })}
        </div>
      )}
    </div>
  );
};

export default SyncFromPromptModal;
