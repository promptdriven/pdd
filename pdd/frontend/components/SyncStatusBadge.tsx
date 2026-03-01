import React, { useEffect, useState } from 'react';
import { api, SyncStatus, SyncStatusType } from '../api';

interface SyncStatusBadgeProps {
  basename: string;
  language: string;
  refreshTrigger?: number;  // Increment to trigger refresh
  className?: string;
}

interface StatusConfig {
  color: string;
  bgColor: string;
  borderColor: string;
  icon: React.ReactNode;
  label: string;
  description: string;
}

const STATUS_CONFIG: Record<SyncStatusType, StatusConfig> = {
  in_sync: {
    color: 'text-green-400',
    bgColor: 'bg-green-500/10',
    borderColor: 'border-green-500/30',
    icon: (
      <svg className="w-3 h-3" fill="none" viewBox="0 0 24 24" stroke="currentColor">
        <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
      </svg>
    ),
    label: 'Synced',
    description: 'Prompt and code are in sync',
  },
  prompt_changed: {
    color: 'text-yellow-400',
    bgColor: 'bg-yellow-500/10',
    borderColor: 'border-yellow-500/30',
    icon: (
      <svg className="w-3 h-3" fill="none" viewBox="0 0 24 24" stroke="currentColor">
        <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 10l7-7m0 0l7 7m-7-7v18" />
      </svg>
    ),
    label: 'Prompt Changed',
    description: 'Prompt was edited since last sync',
  },
  code_changed: {
    color: 'text-orange-400',
    bgColor: 'bg-orange-500/10',
    borderColor: 'border-orange-500/30',
    icon: (
      <svg className="w-3 h-3" fill="none" viewBox="0 0 24 24" stroke="currentColor">
        <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 14l-7 7m0 0l-7-7m7 7V3" />
      </svg>
    ),
    label: 'Code Changed',
    description: 'Code was edited externally',
  },
  conflict: {
    color: 'text-red-400',
    bgColor: 'bg-red-500/10',
    borderColor: 'border-red-500/30',
    icon: (
      <svg className="w-3 h-3" fill="none" viewBox="0 0 24 24" stroke="currentColor">
        <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
      </svg>
    ),
    label: 'Conflict',
    description: 'Both prompt and code have changes',
  },
  never_synced: {
    color: 'text-surface-400',
    bgColor: 'bg-surface-500/10',
    borderColor: 'border-surface-500/30',
    icon: (
      <svg className="w-3 h-3" fill="none" viewBox="0 0 24 24" stroke="currentColor">
        <circle cx="12" cy="12" r="9" strokeWidth={2} />
      </svg>
    ),
    label: 'Not Synced',
    description: 'No sync history exists',
  },
};

const SyncStatusBadge: React.FC<SyncStatusBadgeProps> = ({
  basename,
  language,
  refreshTrigger,
  className = '',
}) => {
  const [status, setStatus] = useState<SyncStatus | null>(null);
  const [isLoading, setIsLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    const fetchStatus = async () => {
      if (!basename || !language) {
        setIsLoading(false);
        return;
      }

      setIsLoading(true);
      setError(null);

      try {
        const result = await api.getSyncStatus(basename, language);
        setStatus(result);
      } catch (e: any) {
        console.error('Failed to fetch sync status:', e);
        setError(e.message || 'Failed to load');
      } finally {
        setIsLoading(false);
      }
    };

    fetchStatus();
  }, [basename, language, refreshTrigger]);

  if (isLoading) {
    return (
      <div className={`inline-flex items-center gap-1.5 px-2 py-1 rounded text-[10px] sm:text-xs bg-surface-700/50 text-surface-400 ${className}`}>
        <svg className="animate-spin h-3 w-3" viewBox="0 0 24 24">
          <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
          <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
        </svg>
        <span className="hidden sm:inline">Loading...</span>
      </div>
    );
  }

  if (error || !status) {
    return (
      <div
        className={`inline-flex items-center gap-1.5 px-2 py-1 rounded text-[10px] sm:text-xs bg-surface-700/50 text-surface-500 ${className}`}
        title={error || 'Status unavailable'}
      >
        <svg className="w-3 h-3" fill="none" viewBox="0 0 24 24" stroke="currentColor">
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M8.228 9c.549-1.165 2.03-2 3.772-2 2.21 0 4 1.343 4 3 0 1.4-1.278 2.575-3.006 2.907-.542.104-.994.54-.994 1.093m0 3h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
        </svg>
        <span className="hidden sm:inline">Unknown</span>
      </div>
    );
  }

  const config = STATUS_CONFIG[status.status];

  // Build tooltip content
  let tooltipParts = [config.description];
  if (status.last_sync_timestamp) {
    const date = new Date(status.last_sync_timestamp);
    tooltipParts.push(`Last sync: ${date.toLocaleString()}`);
  }
  if (status.last_sync_command) {
    tooltipParts.push(`Command: ${status.last_sync_command}`);
  }

  return (
    <div
      className={`inline-flex items-center gap-1.5 px-2 py-1 rounded border text-[10px] sm:text-xs transition-colors ${config.color} ${config.bgColor} ${config.borderColor} ${className}`}
      title={tooltipParts.join('\n')}
    >
      {config.icon}
      <span className="hidden sm:inline font-medium">{config.label}</span>
    </div>
  );
};

export default SyncStatusBadge;
