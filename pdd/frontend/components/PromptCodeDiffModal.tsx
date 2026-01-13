/**
 * PromptCodeDiffModal.tsx
 *
 * A full-screen modal for detailed bidirectional prompt-code diff visualization.
 * Shows both directions:
 * - Prompt → Code: How well code implements the prompt requirements
 * - Code → Prompt: How well the prompt describes what the code does
 */

import React, { useState, useEffect, useRef, useCallback } from 'react';
import { api, DiffAnalysisResponse, DiffSection, DiffAnalysisRequest } from '../api';

interface PromptCodeDiffModalProps {
  isOpen: boolean;
  onClose: () => void;
  promptContent: string;
  codeContent: string;
  promptPath?: string;
  codePath?: string;
}

// Color scheme for different statuses
const STATUS_COLORS = {
  matched: { bg: 'bg-emerald-500/20', border: 'border-emerald-500', text: 'text-emerald-400', dot: 'bg-emerald-500' },
  partial: { bg: 'bg-yellow-500/20', border: 'border-yellow-500', text: 'text-yellow-400', dot: 'bg-yellow-500' },
  missing: { bg: 'bg-red-500/20', border: 'border-red-500', text: 'text-red-400', dot: 'bg-red-500' },
  extra: { bg: 'bg-blue-500/20', border: 'border-blue-500', text: 'text-blue-400', dot: 'bg-blue-500' },
};

type Direction = 'prompt-to-code' | 'code-to-prompt';

export const PromptCodeDiffModal: React.FC<PromptCodeDiffModalProps> = ({
  isOpen,
  onClose,
  promptContent,
  codeContent,
  promptPath,
  codePath,
}) => {
  const [diffResult, setDiffResult] = useState<DiffAnalysisResponse | null>(null);
  const [isAnalyzing, setIsAnalyzing] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [mode, setMode] = useState<'quick' | 'detailed'>('detailed');
  const [strength, setStrength] = useState(0.5);
  const [selectedSection, setSelectedSection] = useState<string | null>(null);
  const [hoveredSection, setHoveredSection] = useState<string | null>(null);
  const [direction, setDirection] = useState<Direction>('prompt-to-code');

  const promptRef = useRef<HTMLDivElement>(null);
  const codeRef = useRef<HTMLDivElement>(null);

  // Run analysis when modal opens
  useEffect(() => {
    if (isOpen && promptContent && codeContent) {
      runAnalysis();
    }
  }, [isOpen]);

  // Reset selected section when direction changes
  useEffect(() => {
    setSelectedSection(null);
    setHoveredSection(null);
  }, [direction]);

  const runAnalysis = async () => {
    setIsAnalyzing(true);
    setError(null);
    try {
      const request: DiffAnalysisRequest = {
        prompt_content: promptContent,
        code_content: codeContent,
        strength,
        mode,
      };
      const result = await api.analyzeDiff(request);
      setDiffResult(result);
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Failed to analyze diff');
    } finally {
      setIsAnalyzing(false);
    }
  };

  // Get current sections based on direction
  const getCurrentSections = useCallback((): DiffSection[] => {
    if (!diffResult) return [];
    return direction === 'prompt-to-code'
      ? diffResult.result.sections
      : diffResult.result.codeSections;
  }, [diffResult, direction]);

  // Scroll to section in both panels
  const scrollToSection = useCallback((section: DiffSection) => {
    setSelectedSection(section.id);

    // Scroll prompt panel
    if (promptRef.current) {
      const lineHeight = 20;
      const scrollTop = (section.promptRange.startLine - 1) * lineHeight;
      promptRef.current.scrollTop = Math.max(0, scrollTop - 50);
    }

    // Scroll code panel
    if (codeRef.current && section.codeRanges.length > 0) {
      const lineHeight = 20;
      const scrollTop = (section.codeRanges[0].startLine - 1) * lineHeight;
      codeRef.current.scrollTop = Math.max(0, scrollTop - 50);
    }
  }, []);

  // Get highlight style for a line
  const getLineHighlight = useCallback((
    lineNum: number,
    isPrompt: boolean,
    sections: DiffSection[]
  ): string | null => {
    const activeSection = hoveredSection || selectedSection;
    if (!activeSection) return null;

    const section = sections.find(s => s.id === activeSection);
    if (!section) return null;

    if (isPrompt) {
      if (lineNum >= section.promptRange.startLine && lineNum <= section.promptRange.endLine) {
        return STATUS_COLORS[section.status as keyof typeof STATUS_COLORS]?.bg || '';
      }
    } else {
      for (const range of section.codeRanges) {
        if (lineNum >= range.startLine && lineNum <= range.endLine) {
          return STATUS_COLORS[section.status as keyof typeof STATUS_COLORS]?.bg || '';
        }
      }
    }
    return null;
  }, [hoveredSection, selectedSection]);

  if (!isOpen) return null;

  const promptLines = promptContent.split('\n');
  const codeLines = codeContent.split('\n');
  const currentSections = getCurrentSections();

  return (
    <div className="fixed inset-0 bg-black/80 backdrop-blur-sm flex items-center justify-center z-50 animate-fade-in">
      <div className="w-full h-full max-w-[1800px] max-h-[95vh] m-4 glass rounded-2xl border border-surface-600/50 shadow-2xl flex flex-col overflow-hidden animate-scale-in">
        {/* Header */}
        <div className="px-6 py-4 border-b border-surface-700/50 flex items-center justify-between flex-shrink-0">
          <div className="flex items-center gap-4">
            <div className="w-10 h-10 rounded-xl bg-gradient-to-br from-purple-500/30 to-blue-500/30 flex items-center justify-center">
              <svg className="w-5 h-5 text-purple-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5H7a2 2 0 00-2 2v12a2 2 0 002 2h10a2 2 0 002-2V7a2 2 0 00-2-2h-2M9 5a2 2 0 002 2h2a2 2 0 002-2M9 5a2 2 0 012-2h2a2 2 0 012 2m-3 7h3m-3 4h3m-6-4h.01M9 16h.01" />
              </svg>
            </div>
            <div>
              <h2 className="text-lg font-semibold text-white">Bidirectional Diff Analysis</h2>
              <p className="text-sm text-surface-400">
                {diffResult?.cached && <span className="text-emerald-400">(cached) </span>}
                {promptPath && codePath ? `${promptPath} vs ${codePath}` : 'Comparing prompt and code in both directions'}
              </p>
            </div>
          </div>

          <div className="flex items-center gap-4">
            {/* Bidirectional scores */}
            {diffResult && (
              <div className="flex items-center gap-3">
                <div className="flex items-center gap-2 px-3 py-1.5 bg-surface-800 rounded-lg">
                  <span className="text-xs text-purple-400">Prompt→Code</span>
                  <span
                    className="text-lg font-bold"
                    style={{
                      color: diffResult.result.promptToCodeScore >= 80 ? '#10b981' :
                             diffResult.result.promptToCodeScore >= 50 ? '#f59e0b' : '#ef4444'
                    }}
                  >
                    {diffResult.result.promptToCodeScore}%
                  </span>
                </div>
                <div className="flex items-center gap-2 px-3 py-1.5 bg-surface-800 rounded-lg">
                  <span className="text-xs text-emerald-400">Code→Prompt</span>
                  <span
                    className="text-lg font-bold"
                    style={{
                      color: diffResult.result.codeToPromptScore >= 80 ? '#10b981' :
                             diffResult.result.codeToPromptScore >= 50 ? '#f59e0b' : '#ef4444'
                    }}
                  >
                    {diffResult.result.codeToPromptScore}%
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

        {/* Main content area */}
        <div className="flex-1 flex overflow-hidden">
          {/* Section Navigator (left sidebar) */}
          <div className="w-72 border-r border-surface-700/50 flex flex-col overflow-hidden flex-shrink-0">
            {/* Direction toggle */}
            <div className="px-4 py-3 border-b border-surface-700/50">
              <div className="flex items-center bg-surface-800 rounded-lg p-0.5 mb-3">
                <button
                  onClick={() => setDirection('prompt-to-code')}
                  className={`flex-1 px-2 py-1.5 text-xs rounded-md transition-all flex items-center justify-center gap-1 ${
                    direction === 'prompt-to-code' ? 'bg-purple-600 text-white' : 'text-surface-400 hover:text-white'
                  }`}
                >
                  <span>Prompt</span>
                  <svg className="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M14 5l7 7m0 0l-7 7m7-7H3" />
                  </svg>
                  <span>Code</span>
                </button>
                <button
                  onClick={() => setDirection('code-to-prompt')}
                  className={`flex-1 px-2 py-1.5 text-xs rounded-md transition-all flex items-center justify-center gap-1 ${
                    direction === 'code-to-prompt' ? 'bg-emerald-600 text-white' : 'text-surface-400 hover:text-white'
                  }`}
                >
                  <span>Code</span>
                  <svg className="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M14 5l7 7m0 0l-7 7m7-7H3" />
                  </svg>
                  <span>Prompt</span>
                </button>
              </div>
              <h3 className="text-sm font-medium text-white">
                {direction === 'prompt-to-code' ? 'Requirements' : 'Code Features'}
              </h3>
              {diffResult && (
                <p className="text-xs text-surface-500 mt-1">
                  {direction === 'prompt-to-code'
                    ? `${diffResult.result.stats.matchedRequirements}/${diffResult.result.stats.totalRequirements} implemented`
                    : `${diffResult.result.stats.documentedFeatures}/${diffResult.result.stats.totalCodeFeatures} documented`
                  }
                </p>
              )}
            </div>

            <div className="flex-1 overflow-y-auto p-2 space-y-1">
              {isAnalyzing && (
                <div className="flex items-center justify-center py-8">
                  <svg className="w-6 h-6 animate-spin text-purple-500" viewBox="0 0 24 24">
                    <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                    <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                  </svg>
                </div>
              )}
              {currentSections.length === 0 && !isAnalyzing && diffResult && (
                <p className="text-xs text-surface-500 text-center py-4">No sections found</p>
              )}
              {currentSections.map((section) => {
                const colors = STATUS_COLORS[section.status as keyof typeof STATUS_COLORS];
                return (
                  <button
                    key={section.id}
                    onClick={() => scrollToSection(section)}
                    onMouseEnter={() => setHoveredSection(section.id)}
                    onMouseLeave={() => setHoveredSection(null)}
                    className={`w-full text-left px-3 py-2 rounded-lg transition-all ${
                      selectedSection === section.id
                        ? `${colors.bg} ${colors.border} border`
                        : 'hover:bg-surface-700/50'
                    }`}
                  >
                    <div className="flex items-center gap-2">
                      <span className={`w-2 h-2 rounded-full flex-shrink-0 ${colors.dot}`} />
                      <span className="text-sm text-white truncate flex-1">{section.semanticLabel}</span>
                      <span className={`text-xs flex-shrink-0 ${colors.text}`}>{section.matchConfidence}%</span>
                    </div>
                    <p className="text-xs text-surface-500 mt-1 truncate">
                      {direction === 'prompt-to-code'
                        ? `Prompt L${section.promptRange.startLine}-${section.promptRange.endLine}`
                        : `Code L${section.codeRanges[0]?.startLine || '?'}-${section.codeRanges[0]?.endLine || '?'}`
                      }
                    </p>
                  </button>
                );
              })}
            </div>

            {/* Legend */}
            <div className="px-4 py-3 border-t border-surface-700/50 space-y-1.5">
              <p className="text-[10px] text-surface-500 uppercase tracking-wider mb-2">Legend</p>
              {direction === 'prompt-to-code' ? (
                <>
                  <div className="flex items-center gap-2 text-xs">
                    <span className="w-2 h-2 rounded-full bg-emerald-500" />
                    <span className="text-surface-400">Implemented in code</span>
                  </div>
                  <div className="flex items-center gap-2 text-xs">
                    <span className="w-2 h-2 rounded-full bg-yellow-500" />
                    <span className="text-surface-400">Partially implemented</span>
                  </div>
                  <div className="flex items-center gap-2 text-xs">
                    <span className="w-2 h-2 rounded-full bg-red-500" />
                    <span className="text-surface-400">Missing in code</span>
                  </div>
                </>
              ) : (
                <>
                  <div className="flex items-center gap-2 text-xs">
                    <span className="w-2 h-2 rounded-full bg-emerald-500" />
                    <span className="text-surface-400">Documented in prompt</span>
                  </div>
                  <div className="flex items-center gap-2 text-xs">
                    <span className="w-2 h-2 rounded-full bg-yellow-500" />
                    <span className="text-surface-400">Partially documented</span>
                  </div>
                  <div className="flex items-center gap-2 text-xs">
                    <span className="w-2 h-2 rounded-full bg-blue-500" />
                    <span className="text-surface-400">Not in prompt (extra)</span>
                  </div>
                </>
              )}
            </div>
          </div>

          {/* Split panels */}
          <div className="flex-1 flex overflow-hidden">
            {/* Prompt panel */}
            <div className="flex-1 flex flex-col border-r border-surface-700/50 overflow-hidden">
              <div className="px-4 py-2 border-b border-surface-700/50 bg-surface-800/50 flex items-center justify-between">
                <h4 className="text-sm font-medium text-purple-400">Prompt Requirements</h4>
                {diffResult && (
                  <span className="text-xs text-surface-500">
                    {diffResult.result.stats.promptToCodeCoverage.toFixed(0)}% implemented
                  </span>
                )}
              </div>
              <div ref={promptRef} className="flex-1 overflow-y-auto font-mono text-sm">
                {promptLines.map((line, idx) => {
                  const lineNum = idx + 1;
                  const highlight = diffResult ? getLineHighlight(lineNum, true, currentSections) : null;
                  return (
                    <div
                      key={idx}
                      className={`flex hover:bg-surface-700/30 ${highlight || ''}`}
                    >
                      <span className="w-12 px-2 text-right text-surface-600 select-none flex-shrink-0 border-r border-surface-700/30">
                        {lineNum}
                      </span>
                      <span className="px-3 py-0.5 text-surface-300 whitespace-pre-wrap break-all">
                        {line || '\u00A0'}
                      </span>
                    </div>
                  );
                })}
              </div>
            </div>

            {/* Code panel */}
            <div className="flex-1 flex flex-col overflow-hidden">
              <div className="px-4 py-2 border-b border-surface-700/50 bg-surface-800/50 flex items-center justify-between">
                <h4 className="text-sm font-medium text-emerald-400">Code Implementation</h4>
                {diffResult && (
                  <span className="text-xs text-surface-500">
                    {diffResult.result.stats.codeToPromptCoverage.toFixed(0)}% documented
                  </span>
                )}
              </div>
              <div ref={codeRef} className="flex-1 overflow-y-auto font-mono text-sm">
                {codeLines.map((line, idx) => {
                  const lineNum = idx + 1;
                  const highlight = diffResult ? getLineHighlight(lineNum, false, currentSections) : null;
                  return (
                    <div
                      key={idx}
                      className={`flex hover:bg-surface-700/30 ${highlight || ''}`}
                    >
                      <span className="w-12 px-2 text-right text-surface-600 select-none flex-shrink-0 border-r border-surface-700/30">
                        {lineNum}
                      </span>
                      <span className="px-3 py-0.5 text-surface-300 whitespace-pre-wrap break-all">
                        {line || '\u00A0'}
                      </span>
                    </div>
                  );
                })}
              </div>
            </div>
          </div>
        </div>

        {/* Footer with summary */}
        <div className="px-6 py-3 border-t border-surface-700/50 flex items-center justify-between bg-surface-900/50 flex-shrink-0">
          {error ? (
            <div className="flex items-center gap-2 text-red-400">
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 8v4m0 4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
              </svg>
              <span className="text-sm">{error}</span>
            </div>
          ) : diffResult ? (
            <div className="flex items-center gap-6">
              <div className="text-sm text-surface-300">{diffResult.result.summary}</div>
              <div className="flex items-center gap-4 text-xs">
                <span className="text-purple-400">
                  {diffResult.result.stats.missingRequirements} missing in code
                </span>
                <span className="text-blue-400">
                  {diffResult.result.stats.undocumentedFeatures} undocumented features
                </span>
                <span className="text-surface-500">
                  Overall: {diffResult.result.overallScore}%
                </span>
              </div>
            </div>
          ) : (
            <div className="text-sm text-surface-500">Click "Re-analyze" to compare prompt and code</div>
          )}

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
