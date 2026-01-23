import React from 'react';
import { TokenMetrics, ModelInfo } from '../api';
import { formatCost } from '../lib/format';

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
  // Model selection props (resolved model passed from parent)
  selectedModel?: ModelInfo | null;
  // Code/Test/Example/Preview/Diff button props
  showCodePanel?: boolean;
  onToggleCodePanel?: () => void;
  hasCodeFile?: boolean;
  showTestPanel?: boolean;
  onToggleTestPanel?: () => void;
  hasTestFile?: boolean;
  showExamplePanel?: boolean;
  onToggleExamplePanel?: () => void;
  hasExampleFile?: boolean;
  showPreview?: boolean;
  onTogglePreview?: () => void;
  onShowDiff?: () => void;
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
  showCodePanel,
  onToggleCodePanel,
  hasCodeFile,
  showTestPanel,
  onToggleTestPanel,
  hasTestFile,
  showExamplePanel,
  onToggleExamplePanel,
  hasExampleFile,
  showPreview,
  onTogglePreview,
  onShowDiff,
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
        {/* Left side: View toggle and action buttons */}
      <div className="flex items-center gap-3">
        <span className="text-xs sm:text-sm font-bold text-white">View</span>
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
          <span className="text-[10px] sm:text-xs text-red-400 truncate max-w-[100px] sm:max-w-none" title={preprocessingError}>
            Error
          </span>
        )}

        {/* Separator */}
        <div className="h-4 w-px bg-surface-600/50 hidden sm:block" />

        {/* Code/Preview/Diff buttons - moved here from path bar */}
        {onToggleCodePanel && (
          <button
            onClick={onToggleCodePanel}
            disabled={!hasCodeFile}
            className={`flex items-center gap-1.5 px-2.5 py-1 rounded-lg text-xs font-medium transition-all duration-200 ${
              !hasCodeFile
                ? 'bg-surface-700/30 text-surface-500 cursor-not-allowed'
                : showCodePanel
                ? 'bg-blue-600 text-white'
                : 'bg-surface-700/50 text-surface-300 hover:bg-surface-600 hover:text-white'
            }`}
            title={!hasCodeFile ? 'No code file available' : showCodePanel ? 'Hide code panel' : 'Show code side-by-side'}
          >
            <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M10 20l4-16m4 4l4 4-4 4M6 16l-4-4 4-4" />
            </svg>
            <span className="hidden sm:inline">Code</span>
          </button>
        )}
        {onToggleTestPanel && (
          <button
            onClick={onToggleTestPanel}
            disabled={!hasTestFile}
            className={`flex items-center gap-1.5 px-2.5 py-1 rounded-lg text-xs font-medium transition-all duration-200 ${
              !hasTestFile
                ? 'bg-surface-700/30 text-surface-500 cursor-not-allowed'
                : showTestPanel
                ? 'bg-yellow-600 text-white'
                : 'bg-surface-700/50 text-surface-300 hover:bg-surface-600 hover:text-white'
            }`}
            title={!hasTestFile ? 'No test file available' : showTestPanel ? 'Hide test panel' : 'Show test side-by-side'}
          >
            <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5H7a2 2 0 00-2 2v12a2 2 0 002 2h10a2 2 0 002-2V7a2 2 0 00-2-2h-2M9 5a2 2 0 002 2h2a2 2 0 002-2M9 5a2 2 0 012-2h2a2 2 0 012 2m-6 9l2 2 4-4" />
            </svg>
            <span className="hidden sm:inline">Test</span>
          </button>
        )}
        {onToggleExamplePanel && (
          <button
            onClick={onToggleExamplePanel}
            disabled={!hasExampleFile}
            className={`flex items-center gap-1.5 px-2.5 py-1 rounded-lg text-xs font-medium transition-all duration-200 ${
              !hasExampleFile
                ? 'bg-surface-700/30 text-surface-500 cursor-not-allowed'
                : showExamplePanel
                ? 'bg-green-600 text-white'
                : 'bg-surface-700/50 text-surface-300 hover:bg-surface-600 hover:text-white'
            }`}
            title={!hasExampleFile ? 'No example file available' : showExamplePanel ? 'Hide example panel' : 'Show example side-by-side'}
          >
            <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 6.253v13m0-13C10.832 5.477 9.246 5 7.5 5S4.168 5.477 3 6.253v13C4.168 18.477 5.754 18 7.5 18s3.332.477 4.5 1.253m0-13C13.168 5.477 14.754 5 16.5 5c1.747 0 3.332.477 4.5 1.253v13C19.832 18.477 18.247 18 16.5 18c-1.746 0-3.332.477-4.5 1.253" />
            </svg>
            <span className="hidden sm:inline">Example</span>
          </button>
        )}
        {onTogglePreview && (
          <button
            onClick={onTogglePreview}
            className={`flex items-center gap-1.5 px-2.5 py-1 rounded-lg text-xs font-medium transition-all duration-200 ${
              showPreview
                ? 'bg-accent-600 text-white'
                : 'bg-surface-700/50 text-surface-300 hover:bg-surface-600 hover:text-white'
            }`}
            title={showPreview ? 'Show source code' : 'Show rendered preview'}
          >
            <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              {showPreview ? (
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M10 20l4-16m4 4l4 4-4 4M6 16l-4-4 4-4" />
              ) : (
                <>
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M15 12a3 3 0 11-6 0 3 3 0 016 0z" />
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M2.458 12C3.732 7.943 7.523 5 12 5c4.478 0 8.268 2.943 9.542 7-1.274 4.057-5.064 7-9.542 7-4.477 0-8.268-2.943-9.542-7z" />
                </>
              )}
            </svg>
            <span className="hidden sm:inline">{showPreview ? 'Source' : 'Preview'}</span>
          </button>
        )}
        {onShowDiff && (
          <button
            onClick={onShowDiff}
            disabled={!hasCodeFile}
            className={`flex items-center gap-1.5 px-2.5 py-1 rounded-lg text-xs font-medium transition-all duration-200 ${
              !hasCodeFile
                ? 'bg-surface-700/30 text-surface-500 cursor-not-allowed'
                : 'bg-gradient-to-r from-purple-600/50 to-blue-600/50 text-purple-200 hover:from-purple-500 hover:to-blue-500 hover:text-white'
            }`}
            title={!hasCodeFile ? 'No code file available' : 'View detailed diff analysis'}
          >
            <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5H7a2 2 0 00-2 2v12a2 2 0 002 2h10a2 2 0 002-2V7a2 2 0 00-2-2h-2M9 5a2 2 0 002 2h2a2 2 0 002-2M9 5a2 2 0 012-2h2a2 2 0 012 2m-3 7h3m-3 4h3m-6-4h.01M9 16h.01" />
            </svg>
            <span className="hidden sm:inline">Diff</span>
          </button>
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
