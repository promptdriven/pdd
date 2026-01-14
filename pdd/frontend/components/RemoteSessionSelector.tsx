import React from 'react';
import { RemoteSessionInfo } from '../api';

interface RemoteSessionSelectorProps {
  sessions: RemoteSessionInfo[];
  selectedSessionId: string | null;
  onSelectSession: (sessionId: string | null) => void;
  disabled?: boolean;
}

const RemoteSessionSelector: React.FC<RemoteSessionSelectorProps> = ({
  sessions,
  selectedSessionId,
  onSelectSession,
  disabled = false,
}) => {
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
    <div className="flex flex-col gap-2">
      <div className="flex items-center gap-2">
        <label className="text-sm text-surface-300 font-medium">
          Remote Session:
        </label>

        <select
          value={selectedSessionId || ''}
          onChange={e => onSelectSession(e.target.value || null)}
          disabled={disabled || sessions.length === 0}
          className="flex-1 px-3 py-1.5 bg-surface-800 border border-surface-700 rounded-lg text-sm text-surface-200 focus:outline-none focus:border-blue-500 disabled:opacity-50 disabled:cursor-not-allowed"
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
        {sessions.length === 0 && (
          <span className="text-xs text-surface-500">No sessions</span>
        )}
      </div>

      {/* Selected session info */}
      {selectedSession && (
        <div className="flex items-center gap-2 px-3 py-2 bg-surface-800/50 rounded-lg border border-surface-700/50">
          {/* Status badge */}
          <span
            className={`flex items-center gap-1.5 px-2 py-1 rounded-full text-xs font-medium ${
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

          {/* Last seen */}
          <span className="text-xs text-surface-400">
            Last seen: {formatRelativeTime(selectedSession.lastHeartbeat)}
          </span>

          {/* Project path tooltip */}
          <span
            className="text-xs text-surface-500 ml-auto"
            title={selectedSession.projectPath}
          >
            {selectedSession.projectPath.length > 30
              ? `...${selectedSession.projectPath.slice(-27)}`
              : selectedSession.projectPath}
          </span>
        </div>
      )}
    </div>
  );
};

export default RemoteSessionSelector;
