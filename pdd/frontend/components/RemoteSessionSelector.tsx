import React, { useState } from 'react';
import { RemoteSessionInfo } from '../api';

interface RemoteSessionSelectorProps {
  sessions: RemoteSessionInfo[];
  selectedSessionId: string | null;
  onSelectSession: (sessionId: string | null) => void;
  disabled?: boolean;
  error?: string | null;
  onRefresh?: () => void;
}

const RemoteSessionSelector: React.FC<RemoteSessionSelectorProps> = ({
  sessions,
  selectedSessionId,
  onSelectSession,
  disabled = false,
  error = null,
  onRefresh,
}) => {
  const [showDebug, setShowDebug] = useState(false);
  const selectedSession = sessions.find(s => s.sessionId === selectedSessionId);

  const formatRelativeTime = (timestamp: string): string => {
    try {
      const date = new Date(timestamp);
      const now = new Date();
      const diff = now.getTime() - date.getTime();
      const minutes = Math.floor(diff / 60000);
      const hours = Math.floor(diff / 3600000);

      if (minutes < 1) return 'just now';
      if (minutes < 60) return `${minutes}m ago`;
      if (hours < 24) return `${hours}h ago`;
      return `${Math.floor(hours / 24)}d ago`;
    } catch {
      return 'unknown';
    }
  };

  return (
    <div className="flex flex-col gap-1.5">
      <div className="flex flex-col md:flex-row items-start md:items-center gap-1.5 md:gap-2">
        <label className="text-xs sm:text-sm text-surface-300 font-medium whitespace-nowrap">
          Session:
        </label>

        <select
          value={selectedSessionId || ''}
          onChange={e => onSelectSession(e.target.value || null)}
          disabled={disabled || sessions.length === 0}
          className="w-full md:w-48 lg:w-56 px-2 sm:px-3 py-1 sm:py-1.5 bg-surface-800 border border-surface-700 rounded-lg text-xs sm:text-sm text-surface-200 focus:outline-none focus:border-blue-500 disabled:opacity-50 disabled:cursor-not-allowed"
        >
          <option value="">-- Select Session --</option>
          {sessions.map(session => (
            <option key={session.sessionId} value={session.sessionId}>
              {session.projectName} @ {session.metadata.hostname}
              {session.status === 'stale' ? ' (offline)' : ''}
            </option>
          ))}
        </select>

        {/* Status indicator */}
        {sessions.length === 0 && !error && (
          <span className="text-xs text-surface-500">No sessions</span>
        )}

        {/* Error indicator */}
        {error && (
          <span className="text-xs text-red-400">
            ⚠️ Error loading sessions
          </span>
        )}

        {/* Debug toggle button */}
        <button
          onClick={() => setShowDebug(!showDebug)}
          className="ml-2 px-2 py-0.5 text-xs text-surface-400 hover:text-surface-200 border border-surface-700 hover:border-surface-500 rounded transition-colors"
          title="Toggle debug info"
        >
          {showDebug ? '🔍 Hide Debug' : '🔍 Debug'}
        </button>

        {/* Refresh button */}
        {onRefresh && (
          <button
            onClick={onRefresh}
            className="ml-1 px-2 py-0.5 text-xs text-surface-400 hover:text-surface-200 border border-surface-700 hover:border-surface-500 rounded transition-colors"
            title="Refresh sessions"
          >
            🔄
          </button>
        )}

        {/* Selected session info - show inline on larger screens */}
        {selectedSession && (
          <div className="w-full md:w-auto mt-1.5 md:mt-0 md:ml-2 flex items-center gap-2 text-xs text-surface-400">
            {/* Status badge */}
            <span
              className={`flex items-center gap-1.5 px-2 py-0.5 rounded-full text-xs font-medium ${
                selectedSession.status === 'active'
                  ? 'bg-green-500/10 text-green-400 border border-green-500/20'
                  : 'bg-yellow-500/10 text-yellow-400 border border-yellow-500/20'
              }`}
            >
              <span
                className={`w-1.5 h-1.5 rounded-full ${
                  selectedSession.status === 'active'
                    ? 'bg-green-400'
                    : 'bg-yellow-400 animate-pulse'
                }`}
              />
              {selectedSession.status === 'active' ? 'Active' : 'Offline'}
            </span>

            {/* Last seen - hide on small screens */}
            <span className="hidden lg:inline text-xs text-surface-400">
              {formatRelativeTime(selectedSession.lastHeartbeat)}
            </span>

            {/* Project path tooltip - hide on small screens */}
            <span
              className="hidden xl:inline text-xs text-surface-500 truncate max-w-[150px] lg:max-w-[200px]"
              title={selectedSession.projectPath}
            >
              {selectedSession.projectPath}
            </span>
          </div>
        )}
      </div>

      {/* Stale session warning banner */}
      {selectedSession && selectedSession.status === 'stale' && (
        <div className="mt-2 p-2 bg-yellow-500/10 border border-yellow-500/20 rounded-lg">
          <div className="flex items-start gap-2">
            <svg className="w-4 h-4 text-yellow-400 flex-shrink-0 mt-0.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
            </svg>
            <div>
              <p className="text-xs font-medium text-yellow-400">Session Offline</p>
              <p className="text-xs text-yellow-200/70 mt-0.5">
                This session has not sent a heartbeat recently. The remote machine may not be running.
                Commands submitted may not be executed.
              </p>
            </div>
          </div>
        </div>
      )}

      {/* Debug panel */}
      {showDebug && (
        <div className="mt-2 p-3 bg-surface-900/50 border border-surface-700 rounded-lg text-xs">
          <div className="font-semibold text-surface-300 mb-2">🔍 Debug Information</div>

          <div className="space-y-1 text-surface-400">
            <div className="flex gap-2">
              <span className="text-surface-500 min-w-[100px]">Sessions:</span>
              <span>{sessions.length} found</span>
            </div>

            {error && (
              <div className="flex gap-2">
                <span className="text-surface-500 min-w-[100px]">Error:</span>
                <span className="text-red-400 flex-1 break-words">{error}</span>
              </div>
            )}

            <div className="flex gap-2">
              <span className="text-surface-500 min-w-[100px]">Last Fetch:</span>
              <span>{new Date().toLocaleTimeString()}</span>
            </div>

            <div className="mt-2 pt-2 border-t border-surface-700">
              <div className="text-surface-500 mb-1">Troubleshooting:</div>
              <ul className="list-disc list-inside space-y-0.5 text-surface-400">
                {error?.includes('Not authenticated') && (
                  <li>Not authenticated. Run: pdd auth login</li>
                )}
                {error?.includes('401') || error?.includes('403') && (
                  <li>JWT token expired or invalid. Try: source setup_staging_env.sh</li>
                )}
                {error?.includes('timeout') || error?.includes('network') && (
                  <li>Network issue. Check cloud connectivity.</li>
                )}
                {!error && sessions.length === 0 && (
                  <li>No sessions found. Start one with: pdd connect</li>
                )}
              </ul>
            </div>
          </div>
        </div>
      )}
    </div>
  );
};

export default RemoteSessionSelector;
