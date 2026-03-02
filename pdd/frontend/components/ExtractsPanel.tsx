import React, { useState, useEffect, useCallback } from 'react';
import { api, ExtractMetadata, ExtractContent, ExtractListResponse } from '../api';
import { SpinnerIcon, ChevronUpIcon, ChevronDownIcon } from './Icon';

function formatTimestamp(ts: string | null): string {
  if (!ts) return 'Unknown';
  try {
    const date = new Date(ts);
    const now = new Date();
    const diffMs = now.getTime() - date.getTime();
    const diffMins = Math.floor(diffMs / 60000);
    if (diffMins < 1) return 'Just now';
    if (diffMins < 60) return `${diffMins}m ago`;
    const diffHours = Math.floor(diffMins / 60);
    if (diffHours < 24) return `${diffHours}h ago`;
    const diffDays = Math.floor(diffHours / 24);
    if (diffDays < 7) return `${diffDays}d ago`;
    return date.toLocaleDateString();
  } catch {
    return ts;
  }
}

interface ExtractRowProps {
  extract: ExtractMetadata;
}

const ExtractRow: React.FC<ExtractRowProps> = ({ extract }) => {
  const [expanded, setExpanded] = useState(false);
  const [content, setContent] = useState<string | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const handleToggle = useCallback(async () => {
    if (expanded) {
      setExpanded(false);
      return;
    }
    setExpanded(true);
    if (content !== null) return; // already fetched

    setLoading(true);
    setError(null);
    try {
      const result = await api.getExtract(extract.cache_key);
      setContent(result.content);
    } catch (e) {
      setError(e instanceof Error ? e.message : 'Failed to load extract content');
    } finally {
      setLoading(false);
    }
  }, [expanded, content, extract.cache_key]);

  const freshnessLabel = extract.is_fresh === true ? 'Fresh' : extract.is_fresh === false ? 'Stale' : 'Unknown';
  const freshnessColor =
    extract.is_fresh === true
      ? 'bg-green-500/20 text-green-400 border-green-500/30'
      : extract.is_fresh === false
      ? 'bg-yellow-500/20 text-yellow-400 border-yellow-500/30'
      : 'bg-surface-600/30 text-surface-400 border-surface-500/30';

  return (
    <div className="border border-surface-700/50 rounded-lg overflow-hidden">
      <button
        onClick={handleToggle}
        className="w-full flex items-center gap-3 p-3 text-left hover:bg-surface-800/50 transition-colors"
      >
        <div className="flex-1 min-w-0">
          <p className="text-sm font-medium text-white truncate" title={extract.source_path}>
            {extract.source_path || 'Unknown source'}
          </p>
          <p className="text-xs text-surface-400 truncate mt-0.5" title={extract.query}>
            {extract.query || 'No query'}
          </p>
        </div>
        <span className="text-xs text-surface-500 whitespace-nowrap">
          {formatTimestamp(extract.timestamp)}
        </span>
        <span className={`text-xs px-2 py-0.5 rounded-full border whitespace-nowrap ${freshnessColor}`}>
          {freshnessLabel}
        </span>
        {expanded ? (
          <ChevronUpIcon className="w-4 h-4 text-surface-400 flex-shrink-0" />
        ) : (
          <ChevronDownIcon className="w-4 h-4 text-surface-400 flex-shrink-0" />
        )}
      </button>

      {expanded && (
        <div className="border-t border-surface-700/50 p-3 bg-surface-900/50">
          {loading && (
            <div className="flex items-center gap-2 text-surface-400 text-sm py-2">
              <SpinnerIcon className="w-4 h-4 animate-spin" />
              Loading content...
            </div>
          )}
          {error && (
            <p className="text-sm text-red-400">{error}</p>
          )}
          {content !== null && (
            <pre className="text-xs text-surface-300 whitespace-pre-wrap break-words max-h-80 overflow-y-auto font-mono leading-relaxed">
              {content}
            </pre>
          )}
        </div>
      )}
    </div>
  );
};

const ExtractsPanel: React.FC = () => {
  const [data, setData] = useState<ExtractListResponse | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  const loadExtracts = useCallback(async () => {
    setLoading(true);
    setError(null);
    try {
      const result = await api.listExtracts();
      setData(result);
    } catch (e) {
      setError(e instanceof Error ? e.message : 'Failed to load extracts');
    } finally {
      setLoading(false);
    }
  }, []);

  useEffect(() => {
    loadExtracts();
  }, [loadExtracts]);

  if (loading) {
    return (
      <div className="flex flex-col items-center justify-center py-12">
        <SpinnerIcon className="w-6 h-6 text-accent-400 animate-spin" />
        <p className="mt-3 text-surface-400 text-sm">Loading cached extracts...</p>
      </div>
    );
  }

  if (error) {
    return (
      <div className="flex flex-col items-center justify-center py-12 gap-3">
        <p className="text-red-400 text-sm">{error}</p>
        <button
          onClick={loadExtracts}
          className="px-3 py-1.5 bg-accent-600 hover:bg-accent-500 text-white rounded-lg text-sm transition-colors"
        >
          Retry
        </button>
      </div>
    );
  }

  if (!data || data.total === 0) {
    return (
      <div className="flex flex-col items-center justify-center py-12 text-center">
        <svg className="w-10 h-10 text-surface-600 mb-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={1.5} d="M20 7l-8-4-8 4m16 0l-8 4m8-4v10l-8 4m0-10L4 7m8 4v10M4 7v10l8 4" />
        </svg>
        <p className="text-surface-400 text-sm">No cached extracts yet.</p>
        <p className="text-surface-500 text-xs mt-1 max-w-sm">
          Extracts are created automatically when you use{' '}
          <code className="text-accent-400">&lt;include query="..."&gt;</code>{' '}
          tags in your prompt files.
        </p>
      </div>
    );
  }

  return (
    <div>
      {/* Summary bar */}
      <div className="flex items-center gap-3 mb-4 text-sm">
        <span className="text-surface-300">
          <span className="font-medium text-white">{data.total}</span> cached extract{data.total !== 1 ? 's' : ''}
        </span>
        {data.stale_count > 0 && (
          <span className="text-yellow-400">
            {data.stale_count} stale
          </span>
        )}
      </div>

      {/* Extract list */}
      <div className="space-y-2">
        {data.extracts.map((extract) => (
          <ExtractRow key={extract.cache_key} extract={extract} />
        ))}
      </div>
    </div>
  );
};

export default ExtractsPanel;
