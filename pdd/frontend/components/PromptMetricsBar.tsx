import React from 'react';
import { TokenMetrics, ModelInfo } from '../api';
import ModelSelector from './ModelSelector';

interface PromptMetricsBarProps {
  rawMetrics: TokenMetrics | null;
  processedMetrics: TokenMetrics | null;
  viewMode: 'raw' | 'processed';
  onViewModeChange: (mode: 'raw' | 'processed') => void;
  isLoading: boolean;
  preprocessingError?: string | null;
  timeValue?: number;  // Reasoning allocation (0-1), default 0.25
  // Code-to-prompt ratio props
  promptLineCount?: number;
  codeLineCount?: number;
  // Context distribution props (can be derived from selectedModel)
  contextLimit?: number;  // Model context limit (default 200K)
  maxThinkingTokens?: number;  // Max thinking budget (default 128K for Claude)
  // Model selection props
  selectedModel?: ModelInfo | null;
  onModelChange?: (model: ModelInfo | null) => void;
}

const PromptMetricsBar: React.FC<PromptMetricsBarProps> = ({
  rawMetrics,
  processedMetrics,
  viewMode,
  onViewModeChange,
  isLoading,
  preprocessingError,
  timeValue = 0.25,
  promptLineCount,
  codeLineCount,
  contextLimit: contextLimitProp,
  maxThinkingTokens: maxThinkingTokensProp,
  selectedModel,
  onModelChange,
}) => {
  const currentMetrics = viewMode === 'processed' ? processedMetrics : rawMetrics;

  // Context distribution calculations
  // Priority: selectedModel > backend-provided > prop > default
  const contextLimit = selectedModel?.context_limit || currentMetrics?.context_limit || contextLimitProp || 200000;
  // Max thinking tokens from model, or fall back to contextLimit-based default
  const maxThinkingTokens = selectedModel?.max_thinking_tokens || maxThinkingTokensProp || (contextLimit >= 200000 ? 128000 : 32000);
  const thinkingBudget = Math.floor(timeValue * maxThinkingTokens);
  const inputTokens = currentMetrics?.token_count || 0;
  const outputCapacity = Math.max(0, contextLimit - inputTokens - thinkingBudget);
  const isOutputWarning = outputCapacity < 20000;  // Less than 20K for output

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

  // Calculate distribution percentages for the bar
  const totalBudget = contextLimit;
  const inputPercent = (inputTokens / totalBudget) * 100;
  const thinkingPercent = (thinkingBudget / totalBudget) * 100;
  const outputPercent = (outputCapacity / totalBudget) * 100;

  return (
    <div className="bg-surface-800/30 border-b border-surface-700/50">
      {/* Main metrics row */}
      <div className="flex flex-col sm:flex-row sm:items-center justify-between px-3 sm:px-4 py-2 sm:py-2.5 gap-2 sm:gap-4">
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
        {/* Model selector */}
        {onModelChange && (
          <div className="hidden sm:block ml-2">
            <ModelSelector
              selectedModel={selectedModel || null}
              onModelChange={onModelChange}
            />
          </div>
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

            {/* Thinking/Reasoning allocation - shows token count */}
            <div className="flex items-center gap-1.5" title={`${formatTokens(thinkingBudget)} thinking tokens (${Math.round(timeValue * 100)}% of ${formatTokens(maxThinkingTokens)} max)`}>
              <span className="text-[10px] sm:text-xs text-surface-400 hidden sm:inline">Thinking:</span>
              <div className="flex items-center gap-1">
                <div className="w-12 sm:w-16 h-1.5 sm:h-2 bg-surface-700 rounded-full overflow-hidden">
                  <div
                    className="h-full transition-all bg-gradient-to-r from-purple-500 to-blue-500"
                    style={{ width: `${Math.min(timeValue * 100, 100)}%` }}
                  />
                </div>
                <span className="text-xs sm:text-sm font-mono text-purple-400">
                  {formatTokens(thinkingBudget)}
                </span>
              </div>
            </div>

            {/* Code:Prompt ratio */}
            {promptLineCount !== undefined && promptLineCount > 0 && codeLineCount !== undefined && (
              <div className="flex items-center gap-1.5" title={`${codeLineCount} lines of code / ${promptLineCount} lines of prompt`}>
                <span className="text-[10px] sm:text-xs text-surface-400 hidden sm:inline">Code:Prompt:</span>
                <span className={`text-xs sm:text-sm font-mono ${
                  codeLineCount / promptLineCount >= 1 ? 'text-blue-400' : 'text-orange-400'
                }`}>
                  {(codeLineCount / promptLineCount).toFixed(1)}x
                </span>
                <span className="text-[10px] text-surface-500 hidden md:inline">
                  ({codeLineCount}/{promptLineCount})
                </span>
              </div>
            )}
          </>
        ) : (
          <span className="text-[10px] sm:text-xs text-surface-500">No metrics</span>
        )}
      </div>
      </div>

      {/* Context Distribution Bar */}
      {currentMetrics && (
        <div className="px-3 sm:px-4 pb-2">
          <div className="flex items-center gap-2">
            <span className="text-[10px] text-surface-500 w-16 sm:w-20 flex-shrink-0">
              {formatTokens(contextLimit)} ctx
            </span>
            <div className="flex-1 h-2 sm:h-2.5 bg-surface-700/50 rounded-full overflow-hidden flex">
              {/* Input tokens (blue) */}
              <div
                className="h-full bg-blue-500 transition-all"
                style={{ width: `${Math.min(inputPercent, 100)}%` }}
                title={`Input: ${formatTokens(inputTokens)} tokens (${inputPercent.toFixed(1)}%)`}
              />
              {/* Thinking budget (purple) */}
              <div
                className="h-full bg-purple-500 transition-all"
                style={{ width: `${Math.min(thinkingPercent, 100 - inputPercent)}%` }}
                title={`Thinking: ${formatTokens(thinkingBudget)} tokens (${thinkingPercent.toFixed(1)}%)`}
              />
              {/* Output capacity (green/orange based on warning) */}
              <div
                className={`h-full transition-all ${isOutputWarning ? 'bg-orange-500/50' : 'bg-green-500/30'}`}
                style={{ width: `${Math.max(outputPercent, 0)}%` }}
                title={`Output capacity: ${formatTokens(outputCapacity)} tokens (${outputPercent.toFixed(1)}%)`}
              />
            </div>
          </div>
          {/* Legend */}
          <div className="flex items-center gap-3 mt-1 text-[9px] sm:text-[10px] text-surface-500">
            <div className="flex items-center gap-1">
              <div className="w-2 h-2 rounded-sm bg-blue-500" />
              <span>Input {formatTokens(inputTokens)}</span>
            </div>
            <div className="flex items-center gap-1">
              <div className="w-2 h-2 rounded-sm bg-purple-500" />
              <span>Thinking {formatTokens(thinkingBudget)}</span>
            </div>
            <div className="flex items-center gap-1">
              <div className={`w-2 h-2 rounded-sm ${isOutputWarning ? 'bg-orange-500' : 'bg-green-500/50'}`} />
              <span className={isOutputWarning ? 'text-orange-400' : ''}>
                Output {formatTokens(outputCapacity)}
                {isOutputWarning && ' (low)'}
              </span>
            </div>
          </div>
        </div>
      )}
    </div>
  );
};

export default PromptMetricsBar;
