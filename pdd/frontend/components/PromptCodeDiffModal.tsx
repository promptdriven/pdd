/**
 * PromptCodeDiffModal.tsx
 *
 * A full-screen modal for detailed bidirectional prompt-code diff visualization.
 * Shows matched sections side-by-side with summaries, expandable to see full content.
 * Unmatched sections are highlighted in red.
 */

import React, { useState, useEffect, useCallback } from 'react';
import {
  api,
  DiffAnalysisResponse,
  DiffSection,
  DiffAnalysisRequest,
  PromptInfo,
  PromptVersionInfo,
  PromptHistoryResponse,
  PromptDiffResponse,
  LinguisticChange,
} from '../api';
import { CommandType } from '../types';

interface PromptCodeDiffModalProps {
  isOpen: boolean;
  onClose: () => void;
  promptContent: string;
  codeContent: string;
  promptPath?: string;
  codePath?: string;
  prompt?: PromptInfo;
  onRunCommand?: (command: CommandType, options?: Record<string, any>) => void;
}

// Color scheme for different statuses
const STATUS_COLORS = {
  matched: { bg: 'bg-emerald-500/10', border: 'border-emerald-500/30', text: 'text-emerald-400', headerBg: 'bg-emerald-500/20' },
  partial: { bg: 'bg-yellow-500/10', border: 'border-yellow-500/30', text: 'text-yellow-400', headerBg: 'bg-yellow-500/20' },
  missing: { bg: 'bg-red-500/15', border: 'border-red-500/50', text: 'text-red-400', headerBg: 'bg-red-500/30' },
  extra: { bg: 'bg-red-500/15', border: 'border-red-500/50', text: 'text-red-400', headerBg: 'bg-red-500/30' },
};

export const PromptCodeDiffModal: React.FC<PromptCodeDiffModalProps> = ({
  isOpen,
  onClose,
  promptContent,
  codeContent,
  promptPath,
  codePath,
  prompt,
  onRunCommand,
}) => {
  const [diffResult, setDiffResult] = useState<DiffAnalysisResponse | null>(null);
  const [isAnalyzing, setIsAnalyzing] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [mode, setMode] = useState<'quick' | 'detailed'>('detailed');
  const [strength, setStrength] = useState(0.5);
  const [expandedSections, setExpandedSections] = useState<Set<string>>(new Set());
  const [includeTests, setIncludeTests] = useState(true);

  // Version History state
  const [activeTab, setActiveTab] = useState<'alignment' | 'history'>('alignment');
  const [historyResponse, setHistoryResponse] = useState<PromptHistoryResponse | null>(null);
  const [isLoadingHistory, setIsLoadingHistory] = useState(false);
  const [historyError, setHistoryError] = useState<string | null>(null);
  const [selectedVersionA, setSelectedVersionA] = useState<string>('working');
  const [selectedVersionB, setSelectedVersionB] = useState<string>('');
  const [versionDiff, setVersionDiff] = useState<PromptDiffResponse | null>(null);
  const [isLoadingDiff, setIsLoadingDiff] = useState(false);
  const [expandedHistorySections, setExpandedHistorySections] = useState<Set<number>>(new Set());
  const [historyStrength, setHistoryStrength] = useState(0.5);

  const toggleExpanded = (sectionId: string) => {
    setExpandedSections(prev => {
      const next = new Set(prev);
      if (next.has(sectionId)) {
        next.delete(sectionId);
      } else {
        next.add(sectionId);
      }
      return next;
    });
  };

  // Run analysis when modal opens
  useEffect(() => {
    if (isOpen && promptContent && codeContent) {
      runAnalysis();
    }
  }, [isOpen]);

  const runAnalysis = async () => {
    setIsAnalyzing(true);
    setError(null);
    setExpandedSections(new Set());
    try {
      const request: DiffAnalysisRequest = {
        prompt_content: promptContent,
        code_content: codeContent,
        strength,
        mode,
        include_tests: includeTests,
        prompt_path: promptPath,
        code_path: codePath,
      };
      const result = await api.analyzeDiff(request);
      setDiffResult(result);

      // Auto-expand mismatched sections (missing/extra) so users can focus on issues
      const mismatchedIds = new Set<string>();
      result.result.sections
        .filter(s => s.status === 'missing' || s.status === 'partial')
        .forEach(s => mismatchedIds.add(`prompt-${s.id}`));
      result.result.codeSections
        .filter(s => s.status === 'extra')
        .forEach(s => mismatchedIds.add(`code-${s.id}`));
      setExpandedSections(mismatchedIds);
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Failed to analyze diff');
    } finally {
      setIsAnalyzing(false);
    }
  };

  // Load git history for prompt
  const loadHistory = async () => {
    if (!promptPath) {
      setHistoryError('No prompt path available');
      return;
    }

    setIsLoadingHistory(true);
    setHistoryError(null);
    try {
      const response = await api.getPromptHistory({ prompt_path: promptPath, limit: 10 });
      setHistoryResponse(response);
      // Set default version B to the first commit if available
      if (response.versions.length > 0 && !selectedVersionB) {
        setSelectedVersionB(response.versions[0].commit_hash);
      }
    } catch (err) {
      setHistoryError(err instanceof Error ? err.message : 'Failed to load history');
    } finally {
      setIsLoadingHistory(false);
    }
  };

  // Compare two versions
  const compareVersions = async () => {
    if (!promptPath || !selectedVersionA || !selectedVersionB) return;

    setIsLoadingDiff(true);
    setHistoryError(null);
    try {
      const response = await api.getPromptDiff({
        prompt_path: promptPath,
        version_a: selectedVersionA,
        version_b: selectedVersionB,
        code_path: codePath,
        strength: historyStrength,
      });
      setVersionDiff(response);
    } catch (err) {
      setHistoryError(err instanceof Error ? err.message : 'Failed to compare versions');
    } finally {
      setIsLoadingDiff(false);
    }
  };

  // Load history when switching to history tab
  useEffect(() => {
    if (activeTab === 'history' && !historyResponse && promptPath) {
      loadHistory();
    }
  }, [activeTab, promptPath]);

  // Auto-expand changed sections (breaking/enhancement) when diff loads
  useEffect(() => {
    if (versionDiff) {
      const changedIndices = new Set<number>();
      versionDiff.linguistic_changes.forEach((change, i) => {
        // Auto-expand breaking and enhancement changes, keep clarifications collapsed
        if (change.impact === 'breaking' || change.impact === 'enhancement') {
          changedIndices.add(i);
        }
      });
      setExpandedHistorySections(changedIndices);
    }
  }, [versionDiff]);

  // Combine and sort sections for unified view
  const getUnifiedSections = useCallback(() => {
    if (!diffResult) return [];

    const sections: Array<{
      id: string;
      type: 'prompt' | 'code';
      section: DiffSection;
      sortKey: number;
    }> = [];

    // Add prompt sections
    diffResult.result.sections.forEach(s => {
      sections.push({
        id: `prompt-${s.id}`,
        type: 'prompt',
        section: s,
        sortKey: s.promptRange.startLine,
      });
    });

    // Add code sections that are "extra" (not documented in prompt)
    diffResult.result.codeSections
      .filter(s => s.status === 'extra')
      .forEach(s => {
        sections.push({
          id: `code-${s.id}`,
          type: 'code',
          section: s,
          sortKey: s.codeRanges[0]?.startLine || 0,
        });
      });

    // Sort by line number
    return sections.sort((a, b) => a.sortKey - b.sortKey);
  }, [diffResult]);

  if (!isOpen) return null;

  const unifiedSections = getUnifiedSections();

  return (
    <div className="fixed inset-0 bg-black/80 backdrop-blur-sm flex items-center justify-center z-50 animate-fade-in">
      <div className="w-full h-full max-w-[1600px] max-h-[95vh] m-4 glass rounded-2xl border border-surface-600/50 shadow-2xl flex flex-col overflow-hidden animate-scale-in">
        {/* Header */}
        <div className="px-6 py-4 border-b border-surface-700/50 flex items-center justify-between flex-shrink-0">
          <div className="flex items-center gap-4">
            <div className="w-10 h-10 rounded-xl bg-gradient-to-br from-purple-500/30 to-blue-500/30 flex items-center justify-center">
              <svg className="w-5 h-5 text-purple-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5H7a2 2 0 00-2 2v12a2 2 0 002 2h10a2 2 0 002-2V7a2 2 0 00-2-2h-2M9 5a2 2 0 002 2h2a2 2 0 002-2M9 5a2 2 0 012-2h2a2 2 0 012 2m-3 7h3m-3 4h3m-6-4h.01M9 16h.01" />
              </svg>
            </div>
            <div>
              <div className="flex items-center gap-4">
                <h2 className="text-lg font-semibold text-white">Prompt Analysis</h2>
                {/* Tab Navigation */}
                <div className="flex items-center bg-surface-800 rounded-lg p-0.5">
                  <button
                    onClick={() => setActiveTab('alignment')}
                    className={`px-3 py-1.5 text-xs rounded-md transition-all ${
                      activeTab === 'alignment' ? 'bg-purple-600 text-white' : 'text-surface-400 hover:text-white'
                    }`}
                  >
                    Alignment
                  </button>
                  <button
                    onClick={() => setActiveTab('history')}
                    className={`px-3 py-1.5 text-xs rounded-md transition-all ${
                      activeTab === 'history' ? 'bg-purple-600 text-white' : 'text-surface-400 hover:text-white'
                    }`}
                  >
                    Version History
                  </button>
                </div>
              </div>
              <p className="text-sm text-surface-400">
                {activeTab === 'alignment' && diffResult?.cached && <span className="text-emerald-400">(cached) </span>}
                {activeTab === 'alignment' && diffResult?.tests_included && (
                  <span className="text-purple-400" title={diffResult.test_files.join(', ')}>
                    ({diffResult.test_files.length} test{diffResult.test_files.length > 1 ? 's' : ''} included){' '}
                  </span>
                )}
                {activeTab === 'alignment' && (promptPath && codePath ? `${promptPath} ↔ ${codePath}` : 'Click sections to expand details')}
                {activeTab === 'history' && (promptPath ? `Git history for ${promptPath}` : 'No prompt path available')}
              </p>
            </div>
          </div>

          <div className="flex items-center gap-4">
            {/* Alignment Tab Controls */}
            {activeTab === 'alignment' && (
              <>
                {/* Regeneration Risk and Scores */}
                {diffResult && (
                  <div className="flex items-center gap-3">
                    {/* Regeneration Risk Badge */}
                    <div className={`flex items-center gap-2 px-3 py-1.5 rounded-lg ${
                      diffResult.result.regenerationRisk === 'critical' ? 'bg-red-500/20 border border-red-500/50' :
                      diffResult.result.regenerationRisk === 'high' ? 'bg-orange-500/20 border border-orange-500/50' :
                      diffResult.result.regenerationRisk === 'medium' ? 'bg-yellow-500/20 border border-yellow-500/50' :
                      'bg-emerald-500/20 border border-emerald-500/50'
                    }`}>
                      <span className={`text-xs font-medium ${
                        diffResult.result.regenerationRisk === 'critical' ? 'text-red-400' :
                        diffResult.result.regenerationRisk === 'high' ? 'text-orange-400' :
                        diffResult.result.regenerationRisk === 'medium' ? 'text-yellow-400' :
                        'text-emerald-400'
                      }`}>
                        {diffResult.result.regenerationRisk === 'critical' ? 'CRITICAL RISK' :
                         diffResult.result.regenerationRisk === 'high' ? 'HIGH RISK' :
                         diffResult.result.regenerationRisk === 'medium' ? 'MEDIUM RISK' :
                         'LOW RISK'}
                      </span>
                      {diffResult.result.canRegenerate ? (
                        <svg className="w-4 h-4 text-emerald-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
                        </svg>
                      ) : (
                        <svg className="w-4 h-4 text-red-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
                        </svg>
                      )}
                    </div>
                    {/* Score */}
                    <div className="flex items-center gap-2 px-3 py-1.5 bg-surface-800 rounded-lg">
                      <span className="text-xs text-purple-400">Score</span>
                      <span
                        className="text-lg font-bold"
                        style={{
                          color: diffResult.result.overallScore >= 80 ? '#10b981' :
                                 diffResult.result.overallScore >= 50 ? '#f59e0b' : '#ef4444'
                        }}
                      >
                        {diffResult.result.overallScore}%
                      </span>
                    </div>
                  </div>
                )}

                {/* Mode toggle */}
                <div className="flex items-center bg-surface-800 rounded-lg p-0.5">
                  <button
                    onClick={() => setMode('quick')}
                    className={`px-3 py-1.5 text-xs rounded-md transition-all ${
                      mode === 'quick' ? 'bg-purple-600 text-white' : 'text-surface-400 hover:text-white'
                    }`}
                  >
                    Quick
                  </button>
                  <button
                    onClick={() => setMode('detailed')}
                    className={`px-3 py-1.5 text-xs rounded-md transition-all ${
                      mode === 'detailed' ? 'bg-purple-600 text-white' : 'text-surface-400 hover:text-white'
                    }`}
                  >
                    Detailed
                  </button>
                </div>

                {/* Include Tests toggle */}
                <button
                  onClick={() => setIncludeTests(!includeTests)}
                  className={`flex items-center gap-2 px-3 py-1.5 rounded-lg text-xs transition-all ${
                    includeTests
                      ? 'bg-emerald-500/20 border border-emerald-500/50 text-emerald-400'
                      : 'bg-surface-800 text-surface-400 hover:text-white'
                  }`}
                  title={includeTests ? 'Tests will be included in analysis' : 'Click to include tests in analysis'}
                >
                  <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z" />
                  </svg>
                  Include Tests
                  {diffResult?.tests_included && diffResult.test_files.length > 0 && (
                    <span className="text-[10px] opacity-70">
                      ({diffResult.test_files.length})
                    </span>
                  )}
                </button>

                {/* Strength Slider */}
                <div className="flex items-center gap-3 bg-surface-800 rounded-lg px-3 py-1.5">
                  <span className="text-xs text-surface-400">Strength</span>
                  <input
                    type="range"
                    min="0"
                    max="1"
                    step="0.1"
                    value={strength}
                    onChange={(e) => setStrength(parseFloat(e.target.value))}
                    className="w-20 h-1.5 bg-surface-700 rounded-lg appearance-none cursor-pointer accent-purple-500"
                  />
                  <span className="text-xs text-purple-400 w-8">{(strength * 100).toFixed(0)}%</span>
                </div>

                {/* Re-analyze button */}
                <button
                  onClick={runAnalysis}
                  disabled={isAnalyzing}
                  className="px-4 py-2 bg-purple-600 text-white rounded-lg text-sm hover:bg-purple-500 disabled:opacity-50 flex items-center gap-2"
                >
                  {isAnalyzing ? (
                    <>
                      <svg className="w-4 h-4 animate-spin" viewBox="0 0 24 24">
                        <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                        <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                      </svg>
                      Analyzing...
                    </>
                  ) : (
                    <>
                      <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                        <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
                      </svg>
                      Re-analyze
                    </>
                  )}
                </button>
              </>
            )}

            {/* History Tab Controls */}
            {activeTab === 'history' && (
              <>
                {/* Strength Slider */}
                <div className="flex items-center gap-3 bg-surface-800 rounded-lg px-3 py-1.5">
                  <span className="text-xs text-surface-400">Strength</span>
                  <input
                    type="range"
                    min="0"
                    max="1"
                    step="0.1"
                    value={historyStrength}
                    onChange={(e) => setHistoryStrength(parseFloat(e.target.value))}
                    className="w-20 h-1.5 bg-surface-700 rounded-lg appearance-none cursor-pointer accent-purple-500"
                  />
                  <span className="text-xs text-purple-400 w-8">{(historyStrength * 100).toFixed(0)}%</span>
                </div>

                <button
                  onClick={loadHistory}
                  disabled={isLoadingHistory}
                  className="px-4 py-2 bg-purple-600 text-white rounded-lg text-sm hover:bg-purple-500 disabled:opacity-50 flex items-center gap-2"
                >
                  {isLoadingHistory ? (
                    <>
                      <svg className="w-4 h-4 animate-spin" viewBox="0 0 24 24">
                        <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                        <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                      </svg>
                      Loading...
                    </>
                  ) : (
                    <>
                      <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                        <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
                      </svg>
                      Refresh
                    </>
                  )}
                </button>
              </>
            )}

            {/* Close button */}
            <button
              onClick={onClose}
              className="p-2 text-surface-400 hover:text-white hover:bg-surface-700 rounded-lg transition-colors"
            >
              <svg className="w-5 h-5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
              </svg>
            </button>
          </div>
        </div>

        {/* Alignment Tab Content */}
        {activeTab === 'alignment' && (
          <>
            {/* Column headers */}
            <div className="flex border-b border-surface-700/50 bg-surface-800/30 flex-shrink-0">
              <div className="flex-1 px-6 py-2 border-r border-surface-700/50">
                <div className="flex items-center justify-between">
                  <span className="text-sm font-medium text-purple-400">Prompt Requirements</span>
                  {diffResult && (
                    <span className="text-xs text-surface-500">
                      {diffResult.result.stats.matchedRequirements}/{diffResult.result.stats.totalRequirements} matched
                    </span>
                  )}
                </div>
              </div>
              <div className="flex-1 px-6 py-2">
                <div className="flex items-center justify-between">
                  <span className="text-sm font-medium text-emerald-400">Code Implementation</span>
                  {diffResult && (
                    <div className="flex items-center gap-3 text-xs">
                      <span className="text-surface-500">
                        {diffResult.result.stats.documentedFeatures}/{diffResult.result.stats.totalCodeFeatures} documented
                      </span>
                      {diffResult.result.hiddenKnowledge && diffResult.result.hiddenKnowledge.length > 0 && (
                        <span className="text-orange-400">
                          {diffResult.result.hiddenKnowledge.length} hidden
                        </span>
                      )}
                    </div>
                  )}
                </div>
              </div>
            </div>

            {/* Main content - unified section view */}
            <div className="flex-1 overflow-y-auto">
              {isAnalyzing && (
                <div className="flex items-center justify-center py-16">
                  <div className="text-center">
                    <svg className="w-8 h-8 animate-spin text-purple-500 mx-auto mb-3" viewBox="0 0 24 24">
                      <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                      <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                    </svg>
                    <p className="text-surface-400">Analyzing prompt and code alignment...</p>
                  </div>
                </div>
              )}

              {error && (
                <div className="p-6">
                  <div className="bg-red-500/10 border border-red-500/30 rounded-xl p-4 flex items-center gap-3">
                    <svg className="w-5 h-5 text-red-400 flex-shrink-0" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 8v4m0 4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
                    </svg>
                    <span className="text-red-400">{error}</span>
                  </div>
                </div>
              )}

          {!isAnalyzing && !error && diffResult && (
            <div className="divide-y divide-surface-700/30">
              {unifiedSections.map(({ id, type, section }) => {
                const isExpanded = expandedSections.has(id);
                const colors = STATUS_COLORS[section.status as keyof typeof STATUS_COLORS];
                const isMismatch = section.status === 'missing' || section.status === 'extra';

                return (
                  <div
                    key={id}
                    className={`flex transition-colors ${isMismatch ? 'bg-red-500/5' : ''}`}
                  >
                    {/* Prompt side */}
                    <div className={`flex-1 border-r border-surface-700/30 ${
                      type === 'code' ? 'bg-red-500/10' : ''
                    }`}>
                      {type === 'prompt' ? (
                        <div
                          className={`p-4 cursor-pointer hover:bg-surface-700/20 transition-colors ${colors.bg}`}
                          onClick={() => toggleExpanded(id)}
                        >
                          {/* Summary header */}
                          <div className="flex items-start gap-3">
                            <div className={`w-2 h-2 rounded-full mt-1.5 flex-shrink-0 ${
                              section.status === 'matched' ? 'bg-emerald-500' :
                              section.status === 'partial' ? 'bg-yellow-500' : 'bg-red-500'
                            }`} />
                            <div className="flex-1 min-w-0">
                              <div className="flex items-center justify-between gap-2">
                                <span className="font-medium text-white text-sm">{section.semanticLabel}</span>
                                <div className="flex items-center gap-2 flex-shrink-0">
                                  <span className={`text-xs ${colors.text}`}>
                                    {section.matchConfidence}%
                                  </span>
                                  <svg
                                    className={`w-4 h-4 text-surface-400 transition-transform ${isExpanded ? 'rotate-180' : ''}`}
                                    fill="none" stroke="currentColor" viewBox="0 0 24 24"
                                  >
                                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                                  </svg>
                                </div>
                              </div>
                              <p className="text-xs text-surface-400 mt-1">
                                Lines {section.promptRange.startLine}-{section.promptRange.endLine}
                              </p>
                              {section.notes && (
                                <p className={`text-xs mt-2 ${colors.text}`}>
                                  {section.notes}
                                </p>
                              )}
                            </div>
                          </div>

                          {/* Expanded content */}
                          {isExpanded && section.promptRange.text && (
                            <div className="mt-3 ml-5">
                              <pre className="text-xs text-purple-300 p-3 bg-surface-900/80 rounded-lg overflow-x-auto whitespace-pre-wrap max-h-64 overflow-y-auto border border-surface-700/30">
                                {section.promptRange.text}
                              </pre>
                            </div>
                          )}
                        </div>
                      ) : (
                        /* Empty prompt side for "extra" code sections - suggest pdd update */
                        <div className="p-4 flex flex-col items-center justify-center min-h-[80px] gap-2">
                          <span className="text-xs text-red-400/60 italic">Not documented in prompt</span>
                          {prompt && onRunCommand && (
                            <button
                              onClick={(e) => {
                                e.stopPropagation();
                                onRunCommand(CommandType.UPDATE, { '_code': prompt.code });
                                onClose();
                              }}
                              className="px-3 py-1.5 text-xs bg-purple-600 hover:bg-purple-500 text-white rounded-lg transition-colors flex items-center gap-1.5"
                            >
                              <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 16v1a3 3 0 003 3h10a3 3 0 003-3v-1m-4-8l-4-4m0 0L8 8m4-4v12" />
                              </svg>
                              Run pdd update
                            </button>
                          )}
                        </div>
                      )}
                    </div>

                    {/* Code side */}
                    <div className={`flex-1 ${
                      type === 'prompt' && section.status === 'missing' ? 'bg-red-500/10' : ''
                    }`}>
                      {type === 'prompt' && section.status !== 'missing' && section.codeRanges.length > 0 ? (
                        <div
                          className={`p-4 cursor-pointer hover:bg-surface-700/20 transition-colors ${colors.bg}`}
                          onClick={() => toggleExpanded(id)}
                        >
                          {/* Summary header */}
                          <div className="flex items-start gap-3">
                            <div className={`w-2 h-2 rounded-full mt-1.5 flex-shrink-0 ${
                              section.status === 'matched' ? 'bg-emerald-500' :
                              section.status === 'partial' ? 'bg-yellow-500' : 'bg-red-500'
                            }`} />
                            <div className="flex-1 min-w-0">
                              <div className="flex items-center justify-between gap-2">
                                <span className="font-medium text-white text-sm">Implementation</span>
                                <span className="text-xs text-surface-500">
                                  {section.codeRanges.length} location{section.codeRanges.length > 1 ? 's' : ''}
                                </span>
                              </div>
                              <p className="text-xs text-surface-400 mt-1">
                                Lines {section.codeRanges[0]?.startLine}-{section.codeRanges[0]?.endLine}
                                {section.codeRanges.length > 1 && ` (+${section.codeRanges.length - 1} more)`}
                              </p>
                            </div>
                          </div>

                          {/* Expanded content */}
                          {isExpanded && (
                            <div className="mt-3 ml-5 space-y-2">
                              {section.codeRanges.map((range, i) => (
                                <div key={i}>
                                  {section.codeRanges.length > 1 && (
                                    <span className="text-[10px] text-surface-500 uppercase">
                                      Location {i + 1} (L{range.startLine}-{range.endLine})
                                    </span>
                                  )}
                                  <pre className="text-xs text-emerald-300 p-3 bg-surface-900/80 rounded-lg overflow-x-auto whitespace-pre-wrap max-h-64 overflow-y-auto border border-surface-700/30">
                                    {range.text || `Lines ${range.startLine}-${range.endLine}`}
                                  </pre>
                                </div>
                              ))}
                            </div>
                          )}
                        </div>
                      ) : type === 'prompt' && section.status === 'missing' ? (
                        /* Missing code for prompt requirement - suggest pdd sync */
                        <div className="p-4 flex flex-col items-center justify-center min-h-[80px] bg-red-500/10 gap-2">
                          <div className="text-center">
                            <svg className="w-5 h-5 text-red-400 mx-auto mb-1" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
                            </svg>
                            <span className="text-xs text-red-400 font-medium">Not implemented</span>
                          </div>
                          {prompt && onRunCommand && (
                            <button
                              onClick={(e) => {
                                e.stopPropagation();
                                onRunCommand(CommandType.SYNC);
                                onClose();
                              }}
                              className="px-3 py-1.5 text-xs bg-emerald-600 hover:bg-emerald-500 text-white rounded-lg transition-colors flex items-center gap-1.5"
                            >
                              <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
                              </svg>
                              Run pdd sync
                            </button>
                          )}
                        </div>
                      ) : type === 'code' ? (
                        /* Extra code section */
                        <div
                          className="p-4 cursor-pointer hover:bg-surface-700/20 transition-colors bg-red-500/5"
                          onClick={() => toggleExpanded(id)}
                        >
                          <div className="flex items-start gap-3">
                            <div className="w-2 h-2 rounded-full mt-1.5 flex-shrink-0 bg-red-500" />
                            <div className="flex-1 min-w-0">
                              <div className="flex items-center justify-between gap-2">
                                <span className="font-medium text-white text-sm">{section.semanticLabel}</span>
                                <div className="flex items-center gap-2 flex-shrink-0">
                                  <span className="text-xs text-red-400">Undocumented</span>
                                  <svg
                                    className={`w-4 h-4 text-surface-400 transition-transform ${isExpanded ? 'rotate-180' : ''}`}
                                    fill="none" stroke="currentColor" viewBox="0 0 24 24"
                                  >
                                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                                  </svg>
                                </div>
                              </div>
                              <p className="text-xs text-surface-400 mt-1">
                                Lines {section.codeRanges[0]?.startLine}-{section.codeRanges[0]?.endLine}
                              </p>
                              {section.notes && (
                                <p className="text-xs mt-2 text-red-400">
                                  {section.notes}
                                </p>
                              )}
                            </div>
                          </div>

                          {isExpanded && section.codeRanges[0]?.text && (
                            <div className="mt-3 ml-5">
                              <pre className="text-xs text-emerald-300 p-3 bg-surface-900/80 rounded-lg overflow-x-auto whitespace-pre-wrap max-h-64 overflow-y-auto border border-red-500/30">
                                {section.codeRanges[0].text}
                              </pre>
                            </div>
                          )}
                        </div>
                      ) : null}
                    </div>
                  </div>
                );
              })}

              {unifiedSections.length === 0 && (
                <div className="p-12 text-center text-surface-500">
                  No sections found. Try re-analyzing with different settings.
                </div>
              )}
            </div>
          )}
            </div>
          </>
        )}

        {/* History Tab Content */}
        {activeTab === 'history' && (
          <>
            {/* Version Selector Bar */}
            <div className="px-6 py-3 border-b border-surface-700/50 bg-surface-800/30 flex-shrink-0">
              {!isLoadingHistory && historyResponse && (
                <div className="flex items-center gap-4">
                  <div className="flex-1 flex items-center gap-3">
                    <label className="text-xs text-surface-400">Version A:</label>
                    <select
                      value={selectedVersionA}
                      onChange={(e) => setSelectedVersionA(e.target.value)}
                      className="flex-1 max-w-xs px-3 py-1.5 bg-surface-900 border border-surface-700 rounded-lg text-xs text-white"
                    >
                      <option value="working">Current (Working)</option>
                      {historyResponse.versions.map((v) => (
                        <option key={v.commit_hash} value={v.commit_hash}>
                          {v.commit_hash.slice(0, 7)} - {v.commit_message.slice(0, 30)}
                        </option>
                      ))}
                    </select>
                  </div>
                  <span className="text-surface-500 text-sm">vs</span>
                  <div className="flex-1 flex items-center gap-3">
                    <label className="text-xs text-surface-400">Version B:</label>
                    <select
                      value={selectedVersionB}
                      onChange={(e) => setSelectedVersionB(e.target.value)}
                      className="flex-1 max-w-xs px-3 py-1.5 bg-surface-900 border border-surface-700 rounded-lg text-xs text-white"
                    >
                      {historyResponse.versions.map((v) => (
                        <option key={v.commit_hash} value={v.commit_hash}>
                          {v.commit_hash.slice(0, 7)} - {v.commit_message.slice(0, 30)}
                        </option>
                      ))}
                    </select>
                  </div>
                  <button
                    onClick={compareVersions}
                    disabled={isLoadingDiff || !selectedVersionA || !selectedVersionB}
                    className="px-4 py-1.5 bg-purple-600 text-white rounded-lg text-xs hover:bg-purple-500 disabled:opacity-50"
                  >
                    {isLoadingDiff ? 'Comparing...' : 'Compare'}
                  </button>
                </div>
              )}
            </div>

            {/* Column Headers - only show when we have diff results */}
            {versionDiff && (
              <div className="flex border-b border-surface-700/50 bg-surface-800/30 flex-shrink-0">
                <div className="flex-1 px-6 py-2 border-r border-surface-700/50">
                  <div className="flex items-center justify-between">
                    <div className="flex items-center gap-2">
                      <span className="text-sm font-medium text-purple-400">
                        Older: {versionDiff.version_a_label}
                      </span>
                      {versionDiff.versions_swapped && (
                        <span className="text-[10px] text-surface-500 bg-surface-700 px-1.5 py-0.5 rounded">
                          auto-ordered
                        </span>
                      )}
                    </div>
                    {versionDiff.linguistic_changes.filter(c => c.change_type === 'removed').length > 0 && (
                      <span className="text-xs text-red-400">
                        {versionDiff.linguistic_changes.filter(c => c.change_type === 'removed').length} removed
                      </span>
                    )}
                  </div>
                </div>
                <div className="flex-1 px-6 py-2">
                  <div className="flex items-center justify-between">
                    <span className="text-sm font-medium text-emerald-400">
                      Newer: {versionDiff.version_b_label}
                    </span>
                    {versionDiff.linguistic_changes.filter(c => c.change_type === 'added').length > 0 && (
                      <span className="text-xs text-emerald-400">
                        {versionDiff.linguistic_changes.filter(c => c.change_type === 'added').length} added
                      </span>
                    )}
                  </div>
                </div>
              </div>
            )}

            {/* Main Content */}
            <div className="flex-1 overflow-y-auto">
              {isLoadingHistory && (
                <div className="flex items-center justify-center py-16">
                  <div className="text-center">
                    <svg className="w-8 h-8 animate-spin text-purple-500 mx-auto mb-3" viewBox="0 0 24 24">
                      <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                      <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                    </svg>
                    <p className="text-surface-400">Loading version history...</p>
                  </div>
                </div>
              )}

              {historyError && (
                <div className="p-6">
                  <div className="bg-red-500/10 border border-red-500/30 rounded-xl p-4 flex items-center gap-3">
                    <svg className="w-5 h-5 text-red-400 flex-shrink-0" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 8v4m0 4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
                    </svg>
                    <span className="text-red-400">{historyError}</span>
                  </div>
                </div>
              )}

              {!isLoadingHistory && historyResponse && !versionDiff && (
                <div className="p-6">
                  {/* Summary section when no diff yet */}
                  <div className="mb-6 p-4 bg-surface-800/50 rounded-xl border border-surface-700/50">
                    <p className="text-sm text-surface-400">
                      Select two versions above and click "Compare" to see side-by-side differences.
                    </p>
                  </div>

                  {/* Version Timeline */}
                  <div className="bg-surface-800/50 rounded-xl p-4 border border-surface-700/50">
                    <h3 className="text-sm font-medium text-white mb-3">
                      Version History ({historyResponse.versions.length} commits)
                      {historyResponse.has_uncommitted_changes && (
                        <span className="ml-2 text-xs text-yellow-400">(uncommitted changes)</span>
                      )}
                    </h3>
                    <div className="space-y-2">
                      {historyResponse.versions.map((version) => (
                        <div
                          key={version.commit_hash}
                          className={`flex items-center gap-3 p-2 rounded-lg hover:bg-surface-700/30 cursor-pointer ${
                            selectedVersionB === version.commit_hash ? 'bg-purple-500/20 border border-purple-500/30' : ''
                          }`}
                          onClick={() => setSelectedVersionB(version.commit_hash)}
                        >
                          <div className={`w-2 h-2 rounded-full ${
                            selectedVersionB === version.commit_hash ? 'bg-purple-400' : 'bg-surface-500'
                          }`} />
                          <div className="flex-1 min-w-0">
                            <div className="flex items-center gap-2">
                              <span className="text-xs font-mono text-purple-400">
                                {version.commit_hash.slice(0, 7)}
                              </span>
                              <span className="text-sm text-white truncate">
                                {version.commit_message}
                              </span>
                            </div>
                            <div className="text-xs text-surface-500">
                              {version.author} • {new Date(version.commit_date).toLocaleString()}
                            </div>
                          </div>
                        </div>
                      ))}
                    </div>
                  </div>
                </div>
              )}

              {/* Side-by-side Diff View */}
              {versionDiff && (
                <div className="divide-y divide-surface-700/30">
                  {/* Summary Row */}
                  <div className="flex bg-surface-800/20">
                    <div className="flex-1 p-4 border-r border-surface-700/30">
                      <div className="text-xs text-surface-500 mb-1">Summary</div>
                      <p className="text-sm text-surface-300">{versionDiff.summary || 'No changes detected'}</p>
                    </div>
                    <div className="flex-1 p-4">
                      <div className="text-xs text-surface-500 mb-1">Changes</div>
                      <div className="flex gap-3 text-xs">
                        {versionDiff.linguistic_changes.filter(c => c.impact === 'breaking').length > 0 && (
                          <span className="text-red-400">
                            {versionDiff.linguistic_changes.filter(c => c.impact === 'breaking').length} breaking
                          </span>
                        )}
                        {versionDiff.linguistic_changes.filter(c => c.impact === 'enhancement').length > 0 && (
                          <span className="text-emerald-400">
                            {versionDiff.linguistic_changes.filter(c => c.impact === 'enhancement').length} enhancements
                          </span>
                        )}
                        {versionDiff.linguistic_changes.filter(c => c.impact === 'clarification').length > 0 && (
                          <span className="text-blue-400">
                            {versionDiff.linguistic_changes.filter(c => c.impact === 'clarification').length} clarifications
                          </span>
                        )}
                      </div>
                    </div>
                  </div>

                  {/* Linguistic Change Sections */}
                  {versionDiff.linguistic_changes.map((change, i) => {
                    const isExpanded = expandedHistorySections.has(i);
                    const toggleHistorySection = () => {
                      setExpandedHistorySections(prev => {
                        const next = new Set(prev);
                        if (next.has(i)) {
                          next.delete(i);
                        } else {
                          next.add(i);
                        }
                        return next;
                      });
                    };

                    const bgColor = change.impact === 'breaking' ? 'bg-red-500/5' :
                                    change.impact === 'enhancement' ? 'bg-emerald-500/5' :
                                    'bg-blue-500/5';
                    const borderColor = change.impact === 'breaking' ? 'border-red-500/30' :
                                        change.impact === 'enhancement' ? 'border-emerald-500/30' :
                                        'border-blue-500/30';

                    // Get short summary: first sentence or first 80 chars
                    const getShortSummary = (desc: string) => {
                      const firstSentence = desc.split(/[.!?]\s/)[0];
                      if (firstSentence.length <= 100) {
                        return firstSentence + (desc.length > firstSentence.length ? '.' : '');
                      }
                      return desc.slice(0, 80) + '...';
                    };
                    const shortSummary = getShortSummary(change.description);
                    const hasLongerDescription = change.description.length > shortSummary.length;

                    return (
                      <div key={i} className={`${bgColor} cursor-pointer hover:bg-surface-700/10 transition-colors`} onClick={toggleHistorySection}>
                        {/* Header row spanning full width - shows description prominently */}
                        <div className="px-4 pt-4 pb-2 border-b border-surface-700/20">
                          <div className="flex items-start justify-between gap-4">
                            <div className="flex items-start gap-3 flex-1 min-w-0">
                              <div className={`w-2.5 h-2.5 rounded-full mt-1 flex-shrink-0 ${
                                change.change_type === 'added' ? 'bg-emerald-500' :
                                change.change_type === 'removed' ? 'bg-red-500' :
                                'bg-yellow-500'
                              }`} />
                              <div className="flex-1 min-w-0">
                                {/* Short summary when collapsed, full when expanded */}
                                <p className="text-sm text-white font-medium leading-relaxed">
                                  {isExpanded ? change.description : shortSummary}
                                </p>
                                {/* Show "more" indicator if truncated */}
                                {!isExpanded && hasLongerDescription && (
                                  <span className="text-xs text-surface-500 ml-1">(click to see more)</span>
                                )}
                              </div>
                            </div>
                            <div className="flex items-center gap-2 flex-shrink-0">
                              <span className={`text-xs px-2 py-0.5 rounded-full ${
                                change.change_type === 'added' ? 'bg-emerald-500/20 text-emerald-400' :
                                change.change_type === 'removed' ? 'bg-red-500/20 text-red-400' :
                                'bg-yellow-500/20 text-yellow-400'
                              }`}>
                                {change.change_type}
                              </span>
                              <span className="text-xs text-surface-500">{change.category}</span>
                              <span className={`text-xs px-2 py-0.5 rounded-full ${
                                change.impact === 'breaking' ? 'bg-red-500/20 text-red-400' :
                                change.impact === 'enhancement' ? 'bg-emerald-500/20 text-emerald-400' :
                                'bg-blue-500/20 text-blue-400'
                              }`}>
                                {change.impact}
                              </span>
                              <svg
                                className={`w-4 h-4 text-surface-400 transition-transform ${isExpanded ? 'rotate-180' : ''}`}
                                fill="none" stroke="currentColor" viewBox="0 0 24 24"
                              >
                                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                              </svg>
                            </div>
                          </div>
                        </div>

                        {/* Side-by-side content row */}
                        <div className="flex">
                          {/* Left side - Old text / Version A */}
                          <div className={`flex-1 border-r border-surface-700/30 p-4 pt-2 ${
                            change.change_type === 'added' ? 'bg-surface-800/20' : ''
                          }`}>
                            {change.old_text ? (
                              <>
                                <p className={`text-xs text-red-400/90 ${isExpanded ? '' : 'line-clamp-3'}`}>
                                  {isExpanded ? '' : change.old_text.slice(0, 200)}{!isExpanded && change.old_text.length > 200 ? '...' : ''}
                                </p>
                                {isExpanded && (
                                  <pre className="mt-2 text-xs text-red-300 p-3 bg-surface-900/80 rounded-lg overflow-x-auto whitespace-pre-wrap max-h-64 overflow-y-auto border border-red-500/20">
                                    {change.old_text}
                                  </pre>
                                )}
                              </>
                            ) : (
                              <p className="text-xs text-surface-500 italic">
                                {change.change_type === 'added' ? 'Not present in older version' : '—'}
                              </p>
                            )}
                          </div>

                          {/* Right side - New text / Version B */}
                          <div className={`flex-1 p-4 pt-2 ${
                            change.change_type === 'removed' ? 'bg-surface-800/20' : ''
                          }`}>
                            {change.new_text ? (
                              <>
                                <p className={`text-xs text-emerald-400/90 ${isExpanded ? '' : 'line-clamp-3'}`}>
                                  {isExpanded ? '' : change.new_text.slice(0, 200)}{!isExpanded && change.new_text.length > 200 ? '...' : ''}
                                </p>
                                {isExpanded && (
                                  <pre className="mt-2 text-xs text-emerald-300 p-3 bg-surface-900/80 rounded-lg overflow-x-auto whitespace-pre-wrap max-h-64 overflow-y-auto border border-emerald-500/20">
                                    {change.new_text}
                                  </pre>
                                )}
                              </>
                            ) : (
                              <p className="text-xs text-surface-500 italic">
                                {change.change_type === 'removed' ? 'Removed in newer version' : '—'}
                              </p>
                            )}
                          </div>
                        </div>
                      </div>
                    );
                  })}

                  {/* Raw Diff Section - Collapsed by default */}
                  {versionDiff.text_diff && (
                    <div className="flex">
                      <div
                        className="flex-1 p-4 cursor-pointer hover:bg-surface-700/10 transition-colors"
                        onClick={() => {
                          setExpandedHistorySections(prev => {
                            const next = new Set(prev);
                            if (next.has(-1)) {
                              next.delete(-1);
                            } else {
                              next.add(-1);
                            }
                            return next;
                          });
                        }}
                      >
                        <div className="flex items-center justify-between">
                          <div className="flex items-center gap-2">
                            <span className="text-sm font-medium text-surface-300">Raw Text Diff</span>
                            <span className="text-xs text-surface-500">
                              ({versionDiff.text_diff.split('\n').filter(l => l.startsWith('+')).length} additions,
                              {versionDiff.text_diff.split('\n').filter(l => l.startsWith('-')).length} deletions)
                            </span>
                          </div>
                          <svg
                            className={`w-4 h-4 text-surface-400 transition-transform ${expandedHistorySections.has(-1) ? 'rotate-180' : ''}`}
                            fill="none" stroke="currentColor" viewBox="0 0 24 24"
                          >
                            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                          </svg>
                        </div>

                        {expandedHistorySections.has(-1) && (
                          <pre className="mt-3 text-xs font-mono p-3 bg-surface-900 rounded-lg overflow-x-auto whitespace-pre max-h-96 overflow-y-auto border border-surface-700/30">
                            {versionDiff.text_diff.split('\n').map((line, i) => (
                              <div
                                key={i}
                                className={
                                  line.startsWith('+') && !line.startsWith('+++') ? 'text-emerald-400 bg-emerald-500/10' :
                                  line.startsWith('-') && !line.startsWith('---') ? 'text-red-400 bg-red-500/10' :
                                  line.startsWith('@') ? 'text-blue-400 bg-blue-500/10' :
                                  'text-surface-400'
                                }
                              >
                                {line}
                              </div>
                            ))}
                          </pre>
                        )}
                      </div>
                    </div>
                  )}

                  {versionDiff.linguistic_changes.length === 0 && (
                    <div className="p-12 text-center text-surface-500">
                      No semantic differences detected between versions.
                    </div>
                  )}
                </div>
              )}

              {!isLoadingHistory && !historyResponse && !historyError && (
                <div className="text-center py-16 text-surface-500">
                  <p>No history available. Click Refresh to load.</p>
                </div>
              )}
            </div>
          </>
        )}

        {/* Footer with summary */}
        <div className="px-6 py-3 border-t border-surface-700/50 flex items-center justify-between bg-surface-900/50 flex-shrink-0">
          <div className="flex items-center gap-6">
            {activeTab === 'alignment' && diffResult && (
              <>
                <div className="text-sm text-surface-300">{diffResult.result.summary}</div>
                <div className="flex items-center gap-4 text-xs">
                  {diffResult.result.stats.criticalGaps > 0 && (
                    <span className="text-red-400 flex items-center gap-1 font-medium">
                      <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                        <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
                      </svg>
                      {diffResult.result.stats.criticalGaps} critical gaps
                    </span>
                  )}
                  {diffResult.result.stats.hiddenKnowledgeCount > 0 && (
                    <span className="text-orange-400 flex items-center gap-1">
                      <span className="w-2 h-2 rounded-full bg-orange-500" />
                      {diffResult.result.stats.hiddenKnowledgeCount} hidden knowledge
                    </span>
                  )}
                  {diffResult.result.stats.missingRequirements > 0 && (
                    <span className="text-red-400 flex items-center gap-1">
                      <span className="w-2 h-2 rounded-full bg-red-500" />
                      {diffResult.result.stats.missingRequirements} missing
                    </span>
                  )}
                  {diffResult.result.stats.undocumentedFeatures > 0 && (
                    <span className="text-red-400 flex items-center gap-1">
                      <span className="w-2 h-2 rounded-full bg-red-500" />
                      {diffResult.result.stats.undocumentedFeatures} undocumented
                    </span>
                  )}
                  {!diffResult.result.canRegenerate && (
                    <span className="text-red-400 flex items-center gap-1 font-medium">
                      Cannot safely regenerate
                    </span>
                  )}
                  {diffResult.result.canRegenerate && diffResult.result.stats.criticalGaps === 0 && (
                    <span className="text-emerald-400 flex items-center gap-1">
                      <span className="w-2 h-2 rounded-full bg-emerald-500" />
                      Safe to regenerate
                    </span>
                  )}
                </div>
              </>
            )}
            {activeTab === 'history' && historyResponse && (
              <div className="text-sm text-surface-300">
                {historyResponse.versions.length} version{historyResponse.versions.length !== 1 ? 's' : ''} found
                {historyResponse.has_uncommitted_changes && (
                  <span className="text-yellow-400 ml-2">• Uncommitted changes present</span>
                )}
              </div>
            )}
          </div>

          {activeTab === 'alignment' && diffResult && (
            <div className="text-xs text-surface-500">
              {diffResult.model} (${diffResult.cost.toFixed(4)})
            </div>
          )}
          {activeTab === 'history' && versionDiff && versionDiff.cost > 0 && (
            <div className="text-xs text-surface-500">
              {versionDiff.model} (${versionDiff.cost.toFixed(4)})
            </div>
          )}
        </div>
      </div>
    </div>
  );
};

export default PromptCodeDiffModal;
