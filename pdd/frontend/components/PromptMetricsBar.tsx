import React from 'react';
import { TokenMetrics } from '../api';

interface PromptMetricsBarProps {
  rawMetrics: TokenMetrics | null;
  processedMetrics: TokenMetrics | null;
  viewMode: 'raw' | 'processed';
  onViewModeChange: (mode: 'raw' | 'processed') => void;
  isLoading: boolean;
  preprocessingError?: string | null;
  timeValue?: number;  // Reasoning allocation (0-1), default 0.25
}

const PromptMetricsBar: React.FC<PromptMetricsBarProps> = ({
  rawMetrics,
  processedMetrics,
  viewMode,
  onViewModeChange,
  isLoading,
  preprocessingError,
  timeValue = 0.25,
}) => {
  const currentMetrics = viewMode === 'processed' ? processedMetrics : rawMetrics;

  // Determine context usage color
  const getUsageColor = (percent: number): string => {
    if (percent < 50) return 'text-green-400';
    if (percent < 75) return 'text-yellow-400';
    if (percent < 90) return 'text-orange-400';
    return 'text-red-400';
  };

  // Get progress bar color class
  const getBarColor = (percent: number): string => {
    if (percent < 50) return 'bg-green-500';
    if (percent < 75) return 'bg-yellow-500';
    if (percent < 90) return 'bg-orange-500';
    return 'bg-red-500';
  };

  // Format cost
  const formatCost = (cost: number): string => {
    if (cost < 0.0001) return `$${cost.toFixed(6)}`;
    if (cost < 0.01) return `$${cost.toFixed(4)}`;
    if (cost < 1) return `$${cost.toFixed(3)}`;
    return `$${cost.toFixed(2)}`;
  };

  // Format token count
  const formatTokens = (count: number): string => {
    if (count >= 1000000) return `${(count / 1000000).toFixed(1)}M`;
    if (count >= 1000) return `${(count / 1000).toFixed(1)}K`;
    return count.toString();
  };

  // Format model name for display
  const formatModelName = (model: string): string => {
    // Extract just the model name without provider prefix
    const parts = model.split('/');
    const name = parts[parts.length - 1];
    // Truncate if too long
    return name.length > 20 ? name.substring(0, 17) + '...' : name;
  };

  return (
    <div className="flex flex-col sm:flex-row sm:items-center justify-between px-3 sm:px-4 py-2 sm:py-2.5 bg-surface-800/30 border-b border-surface-700/50 gap-2 sm:gap-4">
      {/* Left side: View toggle */}
      <div className="flex items-center gap-2">
        <span className="text-[10px] sm:text-xs text-surface-400">View:</span>
        <div className="flex rounded-lg overflow-hidden border border-surface-600/50">
          <button
            onClick={() => onViewModeChange('raw')}
            className={`px-2 sm:px-3 py-1 text-[10px] sm:text-xs font-medium transition-all duration-200 ${
              viewMode === 'raw'
                ? 'bg-accent-600 text-white'
                : 'bg-surface-700/50 text-surface-300 hover:bg-surface-600'
            }`}
          >
            Raw
          </button>
          <button
            onClick={() => onViewModeChange('processed')}
            disabled={!processedMetrics && !preprocessingError}
            className={`px-2 sm:px-3 py-1 text-[10px] sm:text-xs font-medium transition-all duration-200 ${
              viewMode === 'processed'
                ? 'bg-accent-600 text-white'
                : 'bg-surface-700/50 text-surface-300 hover:bg-surface-600'
            } ${!processedMetrics && !preprocessingError ? 'opacity-50 cursor-not-allowed' : ''}`}
            title={preprocessingError ? `Error: ${preprocessingError}` : 'View processed prompt with includes expanded'}
          >
            Processed
          </button>
        </div>
        {preprocessingError && viewMode === 'processed' && (
          <span className="text-[10px] sm:text-xs text-red-400 ml-1 sm:ml-2 truncate max-w-[100px] sm:max-w-none" title={preprocessingError}>
            Error
          </span>
        )}
      </div>

      {/* Right side: Metrics - responsive layout */}
      <div className="flex items-center gap-3 sm:gap-5 flex-wrap">
        {isLoading ? (
          <div className="flex items-center gap-1.5 text-surface-400 text-[10px] sm:text-xs">
            <svg className="animate-spin h-3 w-3" viewBox="0 0 24 24">
              <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
              <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
            </svg>
            Analyzing...
          </div>
        ) : currentMetrics ? (
          <>
            {/* Token count */}
            <div className="flex items-center gap-1.5">
              <span className="text-[10px] sm:text-xs text-surface-400">Tokens:</span>
              <span className="text-xs sm:text-sm font-mono text-white">
                {formatTokens(currentMetrics.token_count)}
              </span>
            </div>

            {/* Context usage */}
            <div className="flex items-center gap-1.5">
              <span className="text-[10px] sm:text-xs text-surface-400 hidden sm:inline">Context:</span>
              <div className="flex items-center gap-1">
                <div className="w-12 sm:w-16 h-1.5 sm:h-2 bg-surface-700 rounded-full overflow-hidden">
                  <div
                    className={`h-full transition-all ${getBarColor(currentMetrics.context_usage_percent)}`}
                    style={{ width: `${Math.min(currentMetrics.context_usage_percent, 100)}%` }}
                  />
                </div>
                <span className={`text-xs sm:text-sm font-mono ${getUsageColor(currentMetrics.context_usage_percent)}`}>
                  {currentMetrics.context_usage_percent.toFixed(0)}%
                </span>
              </div>
            </div>

            {/* Cost estimate */}
            {currentMetrics.cost_estimate && (
              <div className="flex items-center gap-1.5">
                <span className="text-[10px] sm:text-xs text-surface-400 hidden sm:inline">Cost:</span>
                <span className="text-xs sm:text-sm font-mono text-green-400">
                  {formatCost(currentMetrics.cost_estimate.input_cost)}
                </span>
              </div>
            )}

            {/* Thinking/Reasoning allocation */}
            <div className="flex items-center gap-1.5">
              <span className="text-[10px] sm:text-xs text-surface-400 hidden sm:inline">Thinking:</span>
              <div className="flex items-center gap-1">
                <div className="w-12 sm:w-16 h-1.5 sm:h-2 bg-surface-700 rounded-full overflow-hidden">
                  <div
                    className="h-full transition-all bg-gradient-to-r from-purple-500 to-blue-500"
                    style={{ width: `${Math.min(timeValue * 100, 100)}%` }}
                  />
                </div>
                <span className="text-xs sm:text-sm font-mono text-purple-400">
                  {Math.round(timeValue * 100)}%
                </span>
              </div>
            </div>
          </>
        ) : (
          <span className="text-[10px] sm:text-xs text-surface-500">No metrics</span>
        )}
      </div>
    </div>
  );
};

export default PromptMetricsBar;
