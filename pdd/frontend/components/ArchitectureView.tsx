import React, { useState, useEffect, useCallback, useRef, useMemo } from 'react';
import { api, ArchitectureModule, PromptInfo, PromptGenerationResult, GenerationGlobalOptions } from '../api';
import DependencyViewer from './DependencyViewer';
import FileBrowser from './FileBrowser';
import GenerationProgressModal from './GenerationProgressModal';
import PromptOrderModal from './PromptOrderModal';
import { GLOBAL_DEFAULTS } from '../constants';

interface ArchitectureViewProps {
  serverConnected: boolean;
  isExecuting: boolean;
  onOpenPromptSpace: (prompt: PromptInfo) => void;
  // Batch operation callbacks for job dashboard tracking
  onBatchStart?: (name: string, total: number) => void;
  onBatchProgress?: (current: number, total: number, currentItem: string) => void;
  onBatchComplete?: (success: boolean) => void;
}

type EditorMode = 'empty' | 'editor' | 'graph';

const ArchitectureView: React.FC<ArchitectureViewProps> = ({
  serverConnected,
  isExecuting,
  onOpenPromptSpace,
  onBatchStart,
  onBatchProgress,
  onBatchComplete,
}) => {
  // Architecture state
  const [architecture, setArchitecture] = useState<ArchitectureModule[] | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  // Editor state
  const [mode, setMode] = useState<EditorMode>('empty');
  const [appName, setAppName] = useState('');
  const [prdContent, setPrdContent] = useState('');
  const [prdPath, setPrdPath] = useState<string | null>(null);
  const [techStackContent, setTechStackContent] = useState('');
  const [techStackPath, setTechStackPath] = useState<string | null>(null);
  const [showTechStack, setShowTechStack] = useState(false);
  const [showFileBrowser, setShowFileBrowser] = useState<'prd' | 'techStack' | 'architecture' | null>(null);
  const [architecturePathInput, setArchitecturePathInput] = useState('architecture.json');
  const [loadArchitectureError, setLoadArchitectureError] = useState<string | null>(null);

  // Architecture generation state
  const [isGenerating, setIsGenerating] = useState(false);
  const [generationError, setGenerationError] = useState<string | null>(null);

  // Prompt generation state
  const [isGeneratingPrompts, setIsGeneratingPrompts] = useState(false);
  const [promptGenerationProgress, setPromptGenerationProgress] = useState<{
    current: number;
    total: number;
    currentModule: string;
  } | null>(null);
  const [promptGenerationResults, setPromptGenerationResults] = useState<PromptGenerationResult[] | null>(null);
  const [showProgressModal, setShowProgressModal] = useState(false);
  const [showOrderModal, setShowOrderModal] = useState(false);

  // Global options state
  const [showAdvancedOptions, setShowAdvancedOptions] = useState(false);
  const [globalOptions, setGlobalOptions] = useState<GenerationGlobalOptions>({
    strength: GLOBAL_DEFAULTS.strength,
    verbose: GLOBAL_DEFAULTS.verbose,
    force: GLOBAL_DEFAULTS.force,
  });

  // Cancel ref for batch generation
  const cancelRequestedRef = useRef(false);

  // Sidebar collapsed state
  const [sidebarCollapsed, setSidebarCollapsed] = useState(false);

  // Existing prompts state - track which prompts already exist with their file info
  const [existingPrompts, setExistingPrompts] = useState<Set<string>>(new Set());
  const [promptsInfo, setPromptsInfo] = useState<PromptInfo[]>([]);

  // Load existing prompts
  const loadExistingPrompts = useCallback(async () => {
    try {
      const prompts = await api.listPrompts();
      // Store full prompts info for file tracking
      setPromptsInfo(prompts);
      // Extract prompt filenames (e.g., "prompts/orders_Python.prompt" -> "orders_Python.prompt")
      const promptFilenames = new Set(
        prompts.map(p => p.prompt.split('/').pop() || '')
      );
      setExistingPrompts(promptFilenames);
    } catch (e) {
      console.error('Failed to load existing prompts:', e);
    }
  }, []);

  // Load architecture on mount
  useEffect(() => {
    const loadArchitecture = async () => {
      if (!serverConnected) {
        setLoading(false);
        return;
      }

      // Set loading true when server connects (handles reconnection case)
      setLoading(true);

      try {
        const result = await api.checkArchitectureExists();
        if (result.exists) {
          const modules = await api.getArchitecture();
          setArchitecture(modules);
          setMode('graph');
          // Load existing prompts after architecture is loaded
          await loadExistingPrompts();
        } else {
          setMode('empty');
        }
      } catch (e: any) {
        console.error('Failed to load architecture:', e);
        setMode('empty');
      } finally {
        setLoading(false);
      }
    };

    loadArchitecture();
  }, [serverConnected, loadExistingPrompts]);

  // Handle file selection from browser
  const handleFileSelect = useCallback(async (path: string) => {
    try {
      const content = await api.getFileContent(path);
      if (showFileBrowser === 'prd') {
        setPrdContent(content.content);
        setPrdPath(path);
        // Transition to editor mode if we were in empty state
        if (mode === 'empty') {
          setMode('editor');
        }
      } else if (showFileBrowser === 'techStack') {
        setTechStackContent(content.content);
        setTechStackPath(path);
      } else if (showFileBrowser === 'architecture') {
        // Load architecture.json file directly
        try {
          const modules = JSON.parse(content.content) as ArchitectureModule[];
          setArchitecture(modules);
          setMode('graph');
          // Load existing prompts after architecture is loaded
          await loadExistingPrompts();
        } catch (parseError) {
          console.error('Failed to parse architecture.json:', parseError);
          alert('Invalid architecture.json format. Please select a valid architecture file.');
          return;
        }
      }
      setShowFileBrowser(null);
    } catch (e: any) {
      console.error('Failed to load file:', e);
    }
  }, [showFileBrowser, mode, loadExistingPrompts]);

  // Load architecture from path input
  const handleLoadArchitectureFromPath = useCallback(async () => {
    if (!architecturePathInput.trim()) {
      setLoadArchitectureError('Please enter a file path');
      return;
    }

    setLoadArchitectureError(null);
    try {
      const content = await api.getFileContent(architecturePathInput.trim());
      const modules = JSON.parse(content.content) as ArchitectureModule[];
      setArchitecture(modules);
      setMode('graph');
      await loadExistingPrompts();
    } catch (e: any) {
      console.error('Failed to load architecture:', e);
      if (e.message?.includes('404') || e.message?.includes('not found')) {
        setLoadArchitectureError(`File not found: ${architecturePathInput}`);
      } else if (e instanceof SyntaxError) {
        setLoadArchitectureError('Invalid JSON format in file');
      } else {
        setLoadArchitectureError(e.message || 'Failed to load architecture file');
      }
    }
  }, [architecturePathInput, loadExistingPrompts]);

  // Generate architecture from PRD
  const handleGenerate = async () => {
    if (!prdContent.trim() && !prdPath) {
      setGenerationError('Please provide a PRD (Product Requirements Document)');
      return;
    }

    setIsGenerating(true);
    setGenerationError(null);

    try {
      const result = await api.generateArchitecture({
        prdPath: prdPath || undefined,
        prdContent: prdPath ? undefined : prdContent,
        techStackPath: techStackPath || undefined,
        techStackContent: techStackPath ? undefined : (techStackContent || undefined),
        appName: appName || undefined,
        globalOptions,
      });

      if (result.success) {
        // Reload architecture
        const modules = await api.getArchitecture();
        setArchitecture(modules);
        setMode('graph');
        setSidebarCollapsed(true);
      } else {
        setGenerationError(result.message || 'Generation failed');
      }
    } catch (e: any) {
      console.error('Failed to generate architecture:', e);
      setGenerationError(e.message || 'Failed to generate architecture');
    } finally {
      setIsGenerating(false);
    }
  };

  // Cancel running architecture generation
  const handleCancelArchitectureGeneration = async () => {
    try {
      await api.cancelCommand();
      setIsGenerating(false);
    } catch (e) {
      console.error('Failed to cancel:', e);
    }
  };

  // Handle module click - navigate to PromptSpace
  const handleModuleClick = useCallback((module: ArchitectureModule) => {
    // Extract language from filename (e.g., "models_Python.prompt" -> "python")
    const match = module.filename.match(/_([A-Za-z]+)\.prompt$/);
    const language = match ? match[1].toLowerCase() : undefined;

    // Extract basename (e.g., "models_Python.prompt" -> "models")
    const basename = module.filename.replace(/_[A-Za-z]+\.prompt$/, '');

    const promptInfo: PromptInfo = {
      prompt: `prompts/${module.filename}`,
      sync_basename: basename,
      language,
      code: module.filepath,
    };

    onOpenPromptSpace(promptInfo);
  }, [onOpenPromptSpace]);

  // Handle regenerate
  const handleRegenerate = useCallback(() => {
    setSidebarCollapsed(false);
    setMode('editor');
  }, []);

  // Open the order modal before generating prompts
  const handleGeneratePrompts = useCallback(() => {
    if (!architecture || architecture.length === 0) return;
    setShowOrderModal(true);
  }, [architecture]);

  // Handle generation with user-selected order
  const handleConfirmGeneratePrompts = useCallback(async (orderedModules: ArchitectureModule[]) => {
    setShowOrderModal(false);

    if (orderedModules.length === 0) return;

    cancelRequestedRef.current = false;
    setIsGeneratingPrompts(true);
    setPromptGenerationResults(null);
    setShowProgressModal(true);

    // Parse module info from filenames in the user-specified order
    const moduleRequests = orderedModules.map(m => {
      // Parse "orders_Python.prompt" → { module: "orders", langOrFramework: "Python" }
      const match = m.filename.match(/^(.+)_([^_]+)\.prompt$/);
      return {
        module: match?.[1] || m.filename.replace('.prompt', ''),
        langOrFramework: match?.[2] || 'Python',
      };
    });

    // Notify parent that batch operation is starting (for job dashboard)
    onBatchStart?.('Generating Prompts', moduleRequests.length);

    try {
      const results = await api.batchGeneratePrompts(
        {
          modules: moduleRequests,
          architectureFile: 'architecture.json',
          prdFile: prdPath || undefined,
          techStackFile: techStackPath || undefined,
          globalOptions,
        },
        (current, total, module) => {
          setPromptGenerationProgress({ current, total, currentModule: module });
          // Also notify parent for job dashboard
          onBatchProgress?.(current, total, module);
        },
        () => cancelRequestedRef.current
      );
      setPromptGenerationResults(results);
      // Notify parent that batch completed successfully
      const allSucceeded = results.every(r => r.success);
      onBatchComplete?.(allSucceeded);
    } catch (e: any) {
      console.error('Failed to generate prompts:', e);
      setPromptGenerationResults([{
        module: 'error',
        success: false,
        error: e.message || 'Failed to generate prompts',
      }]);
      // Notify parent that batch failed
      onBatchComplete?.(false);
    } finally {
      setIsGeneratingPrompts(false);
      setPromptGenerationProgress(null);
    }
  }, [prdPath, techStackPath, globalOptions, onBatchStart, onBatchProgress, onBatchComplete]);

  // Cancel prompt generation and current running command
  const handleCancelPromptGeneration = useCallback(async () => {
    cancelRequestedRef.current = true;
    try {
      await api.cancelCommand();
    } catch (e) {
      console.error('Failed to cancel command:', e);
    }
  }, []);

  // Close progress modal and refresh existing prompts
  const handleCloseProgressModal = useCallback(async () => {
    setShowProgressModal(false);
    setPromptGenerationResults(null);
    cancelRequestedRef.current = false;
    // Refresh existing prompts after generation
    await loadExistingPrompts();
  }, [loadExistingPrompts]);

  if (loading) {
    return (
      <div className="flex items-center justify-center h-64">
        <div className="flex items-center gap-3 text-surface-400">
          <svg className="animate-spin h-5 w-5" viewBox="0 0 24 24">
            <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
            <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
          </svg>
          Loading architecture...
        </div>
      </div>
    );
  }

  // Empty state - no architecture.json
  if (mode === 'empty') {
    return (
      <div className="flex items-center justify-center min-h-[400px]">
        <div className="glass rounded-2xl p-8 max-w-lg text-center border border-surface-700/50">
          <div className="w-16 h-16 rounded-2xl bg-accent-500/20 flex items-center justify-center mx-auto mb-4">
            <svg className="w-8 h-8 text-accent-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={1.5} d="M19 11H5m14 0a2 2 0 012 2v6a2 2 0 01-2 2H5a2 2 0 01-2-2v-6a2 2 0 012-2m14 0V9a2 2 0 00-2-2M5 11V9a2 2 0 012-2m0 0V5a2 2 0 012-2h6a2 2 0 012 2v2M7 7h10" />
            </svg>
          </div>
          <h2 className="text-xl font-semibold text-white mb-2">No architecture.json found</h2>
          <p className="text-surface-400 text-sm mb-6">
            Generate a new architecture from a PRD, or load an existing architecture.json file.
          </p>

          {/* Primary actions */}
          <div className="flex gap-3 justify-center mb-4">
            <button
              onClick={() => setMode('editor')}
              className="px-4 py-2.5 bg-accent-600 hover:bg-accent-500 text-white rounded-xl font-medium transition-colors"
              disabled={!serverConnected}
            >
              Write PRD
            </button>
            <button
              onClick={() => setShowFileBrowser('prd')}
              className="px-4 py-2.5 bg-surface-700 hover:bg-surface-600 text-white rounded-xl font-medium transition-colors"
              disabled={!serverConnected}
            >
              Load PRD
            </button>
          </div>

          {/* Secondary action - load existing architecture */}
          <div className="pt-4 border-t border-surface-700/50">
            <p className="text-surface-500 text-xs mb-3">Or load an existing architecture file</p>
            <div className="flex gap-2">
              <input
                type="text"
                value={architecturePathInput}
                onChange={(e) => {
                  setArchitecturePathInput(e.target.value);
                  setLoadArchitectureError(null);
                }}
                placeholder="architecture.json"
                className="flex-1 px-3 py-2 bg-surface-900/50 border border-surface-600 rounded-lg text-sm text-white placeholder-surface-500 focus:outline-none focus:border-accent-500"
                disabled={!serverConnected}
                onKeyDown={(e) => {
                  if (e.key === 'Enter') handleLoadArchitectureFromPath();
                }}
              />
              <button
                onClick={handleLoadArchitectureFromPath}
                className="px-4 py-2 bg-surface-700 hover:bg-surface-600 text-surface-300 hover:text-white rounded-lg text-sm font-medium transition-colors"
                disabled={!serverConnected}
              >
                Load
              </button>
            </div>
            {loadArchitectureError && (
              <p className="text-red-400 text-xs mt-2">{loadArchitectureError}</p>
            )}
          </div>

          {!serverConnected && (
            <p className="text-yellow-400 text-xs mt-4">
              Connect to server to enable architecture generation
            </p>
          )}
        </div>

        {/* File Browser Modal */}
        {showFileBrowser && (
          <FileBrowser
            onSelect={handleFileSelect}
            onClose={() => setShowFileBrowser(null)}
            filter=".md"
            title={showFileBrowser === 'prd' ? 'Select PRD File' : 'Select Tech Stack File'}
          />
        )}
      </div>
    );
  }

  // Editor mode or Graph mode with sidebar
  return (
    <div className="flex gap-4 h-[calc(100vh-200px)] min-h-[500px]">
      {/* Sidebar - PRD/Tech Stack Editor */}
      <div className={`flex-shrink-0 transition-all duration-300 ${sidebarCollapsed ? 'w-12' : 'w-80'}`}>
        <div className="glass rounded-xl border border-surface-700/50 h-full flex flex-col overflow-hidden">
          {/* Sidebar Header */}
          <div className="p-3 border-b border-surface-700/50 flex items-center justify-between">
            {!sidebarCollapsed && (
              <div className="flex-1 min-w-0">
                <input
                  type="text"
                  value={appName}
                  onChange={(e) => setAppName(e.target.value)}
                  placeholder="Project Name"
                  className="w-full bg-transparent text-white text-sm font-medium placeholder-surface-500 focus:outline-none"
                />
              </div>
            )}
            <button
              onClick={() => setSidebarCollapsed(!sidebarCollapsed)}
              className="p-1.5 hover:bg-surface-700 rounded-lg transition-colors flex-shrink-0"
              title={sidebarCollapsed ? 'Expand sidebar' : 'Collapse sidebar'}
            >
              <svg className={`w-4 h-4 text-surface-400 transition-transform ${sidebarCollapsed ? 'rotate-180' : ''}`} fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M11 19l-7-7 7-7m8 14l-7-7 7-7" />
              </svg>
            </button>
          </div>

          {!sidebarCollapsed && (
            <>
              {/* PRD Section */}
              <div className="flex-1 flex flex-col min-h-0">
                <div className="p-2 border-b border-surface-700/50 flex items-center justify-between">
                  <span className="text-xs font-medium text-surface-400 uppercase tracking-wider">PRD</span>
                  <button
                    onClick={() => setShowFileBrowser('prd')}
                    className="p-1 hover:bg-surface-700 rounded text-surface-400 hover:text-white transition-colors"
                    title="Browse files"
                  >
                    <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M3 7v10a2 2 0 002 2h14a2 2 0 002-2V9a2 2 0 00-2-2h-6l-2-2H5a2 2 0 00-2 2z" />
                    </svg>
                  </button>
                </div>
                {prdPath && (
                  <div className="px-2 py-1 bg-surface-800/50 text-xs text-surface-400 truncate">
                    {prdPath}
                  </div>
                )}
                <textarea
                  value={prdContent}
                  onChange={(e) => {
                    setPrdContent(e.target.value);
                    setPrdPath(null); // Clear path when editing
                  }}
                  placeholder="# Product Requirements&#10;&#10;## Overview&#10;Describe your product...&#10;&#10;## Features&#10;- Feature 1&#10;- Feature 2"
                  className="flex-1 p-3 bg-transparent text-sm text-white placeholder-surface-600 resize-none focus:outline-none font-mono"
                />
              </div>

              {/* Tech Stack Section (Collapsible) */}
              <div className="border-t border-surface-700/50">
                <button
                  onClick={() => setShowTechStack(!showTechStack)}
                  className="w-full p-2 flex items-center justify-between text-left hover:bg-surface-800/30 transition-colors"
                >
                  <span className="text-xs font-medium text-surface-400 uppercase tracking-wider">Tech Stack (optional)</span>
                  <svg className={`w-4 h-4 text-surface-400 transition-transform ${showTechStack ? 'rotate-180' : ''}`} fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                  </svg>
                </button>
                {showTechStack && (
                  <div className="border-t border-surface-700/30">
                    <div className="p-2 flex items-center justify-end">
                      <button
                        onClick={() => setShowFileBrowser('techStack')}
                        className="p-1 hover:bg-surface-700 rounded text-surface-400 hover:text-white transition-colors"
                        title="Browse files"
                      >
                        <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M3 7v10a2 2 0 002 2h14a2 2 0 002-2V9a2 2 0 00-2-2h-6l-2-2H5a2 2 0 00-2 2z" />
                        </svg>
                      </button>
                    </div>
                    {techStackPath && (
                      <div className="px-2 py-1 bg-surface-800/50 text-xs text-surface-400 truncate">
                        {techStackPath}
                      </div>
                    )}
                    <textarea
                      value={techStackContent}
                      onChange={(e) => {
                        setTechStackContent(e.target.value);
                        setTechStackPath(null);
                      }}
                      placeholder="Backend: Python, FastAPI&#10;Frontend: React, TypeScript&#10;Database: PostgreSQL"
                      className="w-full h-24 p-3 bg-transparent text-sm text-white placeholder-surface-600 resize-none focus:outline-none font-mono"
                    />
                  </div>
                )}
              </div>

              {/* Advanced Options (Collapsible) */}
              <div className="border-t border-surface-700/50">
                <button
                  onClick={() => setShowAdvancedOptions(!showAdvancedOptions)}
                  className="w-full p-2 flex items-center justify-between text-left hover:bg-surface-800/30 transition-colors"
                >
                  <span className="text-xs font-medium text-surface-400 uppercase tracking-wider">Model Options</span>
                  <svg className={`w-4 h-4 text-surface-400 transition-transform ${showAdvancedOptions ? 'rotate-180' : ''}`} fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                  </svg>
                </button>
                {showAdvancedOptions && (
                  <div className="border-t border-surface-700/30 p-3 space-y-4">
                    {/* Strength slider */}
                    <div className="space-y-2">
                      <div className="flex items-center justify-between">
                        <label className="text-xs font-medium text-surface-300">Strength</label>
                        <span className="text-xs font-mono text-accent-400 bg-accent-500/10 px-2 py-0.5 rounded">
                          {(globalOptions.strength ?? GLOBAL_DEFAULTS.strength).toFixed(2)}
                        </span>
                      </div>
                      <input
                        type="range"
                        min={0}
                        max={1}
                        step={0.05}
                        value={globalOptions.strength ?? GLOBAL_DEFAULTS.strength}
                        onChange={(e) => setGlobalOptions(prev => ({ ...prev, strength: parseFloat(e.target.value) }))}
                        className="w-full h-2 bg-surface-700 rounded-full appearance-none cursor-pointer accent-accent-500"
                      />
                      <p className="text-[10px] text-surface-500">&lt;0.5 cheaper, 0.5 base, &gt;0.5 stronger</p>
                    </div>

                    {/* Checkbox options */}
                    <div className="space-y-2">
                      <label className="flex items-center gap-2 cursor-pointer group">
                        <input
                          type="checkbox"
                          checked={globalOptions.local ?? false}
                          onChange={(e) => setGlobalOptions(prev => ({ ...prev, local: e.target.checked }))}
                          className="w-4 h-4 rounded border-surface-600 bg-surface-800 text-accent-500 focus:ring-accent-500"
                        />
                        <span className="text-xs text-surface-300 group-hover:text-white">Run locally (not cloud)</span>
                      </label>
                      <label className="flex items-center gap-2 cursor-pointer group">
                        <input
                          type="checkbox"
                          checked={globalOptions.verbose ?? false}
                          onChange={(e) => setGlobalOptions(prev => ({ ...prev, verbose: e.target.checked }))}
                          className="w-4 h-4 rounded border-surface-600 bg-surface-800 text-accent-500 focus:ring-accent-500"
                        />
                        <span className="text-xs text-surface-300 group-hover:text-white">Verbose output</span>
                      </label>
                      <label className="flex items-center gap-2 cursor-pointer group">
                        <input
                          type="checkbox"
                          checked={globalOptions.force ?? false}
                          onChange={(e) => setGlobalOptions(prev => ({ ...prev, force: e.target.checked }))}
                          className="w-4 h-4 rounded border-surface-600 bg-surface-800 text-accent-500 focus:ring-accent-500"
                        />
                        <span className="text-xs text-surface-300 group-hover:text-white">Force (skip prompts)</span>
                      </label>
                    </div>
                  </div>
                )}
              </div>

              {/* Generate Button */}
              <div className="p-3 border-t border-surface-700/50">
                {generationError && (
                  <div className="mb-2 p-2 bg-red-500/10 border border-red-500/20 rounded-lg text-xs text-red-400">
                    {generationError}
                  </div>
                )}
                {isGenerating ? (
                  <div className="flex gap-2">
                    <div className="flex-1 px-4 py-2.5 bg-surface-700 rounded-xl flex items-center justify-center gap-2">
                      <svg className="animate-spin h-4 w-4 text-surface-400" viewBox="0 0 24 24">
                        <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                        <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                      </svg>
                      <span className="text-sm text-surface-400">Generating...</span>
                    </div>
                    <button
                      onClick={handleCancelArchitectureGeneration}
                      className="px-3 py-2.5 bg-red-500/20 hover:bg-red-500/30 text-red-300 border border-red-500/30 rounded-xl text-sm font-medium transition-colors"
                    >
                      Stop
                    </button>
                  </div>
                ) : (
                  <button
                    onClick={handleGenerate}
                    disabled={isExecuting || !serverConnected || (!prdContent.trim() && !prdPath)}
                    className={`w-full px-4 py-2.5 rounded-xl font-medium transition-all duration-200 flex items-center justify-center gap-2 ${
                      isExecuting || !serverConnected || (!prdContent.trim() && !prdPath)
                        ? 'bg-surface-700 text-surface-500 cursor-not-allowed'
                        : 'bg-gradient-to-r from-accent-600 to-accent-500 hover:from-accent-500 hover:to-accent-400 text-white shadow-lg shadow-accent-500/25'
                    }`}
                  >
                    {architecture ? 'Regenerate' : 'Generate Architecture'}
                  </button>
                )}
              </div>

              {/* Load Different Architecture File */}
              <div className="border-t border-surface-700/50">
                <div className="p-3">
                  <p className="text-xs font-medium text-surface-400 uppercase tracking-wider mb-2">Load Architecture File</p>
                  <div className="flex gap-2">
                    <input
                      type="text"
                      value={architecturePathInput}
                      onChange={(e) => {
                        setArchitecturePathInput(e.target.value);
                        setLoadArchitectureError(null);
                      }}
                      placeholder="architecture.json"
                      className="flex-1 px-2 py-1.5 bg-surface-900/50 border border-surface-600 rounded text-xs text-white placeholder-surface-500 focus:outline-none focus:border-accent-500"
                      onKeyDown={(e) => {
                        if (e.key === 'Enter') handleLoadArchitectureFromPath();
                      }}
                    />
                    <button
                      onClick={handleLoadArchitectureFromPath}
                      className="px-3 py-1.5 bg-surface-700 hover:bg-surface-600 text-surface-300 hover:text-white rounded text-xs font-medium transition-colors"
                    >
                      Load
                    </button>
                  </div>
                  {loadArchitectureError && (
                    <p className="text-red-400 text-[10px] mt-1">{loadArchitectureError}</p>
                  )}
                </div>
              </div>
            </>
          )}
        </div>
      </div>

      {/* Main Content - Architecture Graph */}
      <div className="flex-1 min-w-0">
        {mode === 'graph' && architecture ? (
          <DependencyViewer
            architecture={architecture}
            prdContent={prdContent}
            appName={appName}
            onRegenerate={handleRegenerate}
            onModuleClick={handleModuleClick}
            onGeneratePrompts={handleGeneratePrompts}
            isGeneratingPrompts={isGeneratingPrompts}
            existingPrompts={existingPrompts}
            promptsInfo={promptsInfo}
          />
        ) : (
          <div className="glass rounded-xl border border-surface-700/50 h-full flex items-center justify-center">
            <div className="text-center text-surface-400">
              <svg className="w-12 h-12 mx-auto mb-3 opacity-50" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={1.5} d="M9 17V7m0 10a2 2 0 01-2 2H5a2 2 0 01-2-2V7a2 2 0 012-2h2a2 2 0 012 2m0 10a2 2 0 002 2h2a2 2 0 002-2M9 7a2 2 0 012-2h2a2 2 0 012 2m0 10V7m0 10a2 2 0 002 2h2a2 2 0 002-2V7a2 2 0 00-2-2h-2a2 2 0 00-2 2" />
              </svg>
              <p className="text-sm">Write your PRD and click Generate to create the architecture</p>
            </div>
          </div>
        )}
      </div>

      {/* File Browser Modal */}
      {showFileBrowser && (
        <FileBrowser
          onSelect={handleFileSelect}
          onClose={() => setShowFileBrowser(null)}
          filter=".md"
          title={showFileBrowser === 'prd' ? 'Select PRD File' : 'Select Tech Stack File'}
        />
      )}

      {/* Prompt Order Selection Modal */}
      {showOrderModal && architecture && (
        <PromptOrderModal
          isOpen={showOrderModal}
          modules={architecture}
          existingPrompts={existingPrompts}
          onClose={() => setShowOrderModal(false)}
          onConfirm={handleConfirmGeneratePrompts}
        />
      )}

      {/* Prompt Generation Progress Modal */}
      {showProgressModal && (
        <GenerationProgressModal
          isOpen={showProgressModal}
          progress={promptGenerationProgress}
          results={promptGenerationResults}
          onClose={handleCloseProgressModal}
          onCancel={isGeneratingPrompts ? handleCancelPromptGeneration : undefined}
        />
      )}
    </div>
  );
};

export default ArchitectureView;
