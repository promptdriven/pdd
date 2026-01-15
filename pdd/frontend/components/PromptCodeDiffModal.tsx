/**
 * PromptCodeDiffModal.tsx
 *
 * A full-screen modal for detailed bidirectional prompt-code diff visualization.
 * Shows matched sections side-by-side with summaries, expandable to see full content.
 * Unmatched sections are highlighted in red.
 */

import React, { useState, useEffect, useCallback } from 'react';
import { api, DiffAnalysisResponse, DiffSection, DiffAnalysisRequest, PromptInfo } from '../api';
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
              <h2 className="text-lg font-semibold text-white">Prompt-Code Alignment</h2>
              <p className="text-sm text-surface-400">
                {diffResult?.cached && <span className="text-emerald-400">(cached) </span>}
                {promptPath && codePath ? `${promptPath} ↔ ${codePath}` : 'Click sections to expand details'}
              </p>
            </div>
          </div>

          <div className="flex items-center gap-4">
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

        {/* Footer with summary */}
        <div className="px-6 py-3 border-t border-surface-700/50 flex items-center justify-between bg-surface-900/50 flex-shrink-0">
          <div className="flex items-center gap-6">
            {diffResult && (
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
          </div>

          {diffResult && (
            <div className="text-xs text-surface-500">
              {diffResult.model} (${diffResult.cost.toFixed(4)})
            </div>
          )}
        </div>
      </div>
    </div>
  );
};

export default PromptCodeDiffModal;
