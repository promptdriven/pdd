import React, { useEffect, useRef, useState, useMemo, useCallback } from 'react';
import { EditorState, Compartment } from '@codemirror/state';
import { EditorView, lineNumbers, highlightActiveLine, keymap } from '@codemirror/view';
import { defaultKeymap, history, historyKeymap } from '@codemirror/commands';
import { completionKeymap } from '@codemirror/autocomplete';
import { markdown } from '@codemirror/lang-markdown';
import { python } from '@codemirror/lang-python';
import { javascript } from '@codemirror/lang-javascript';
import { java } from '@codemirror/lang-java';
import { oneDark } from '@codemirror/theme-one-dark';
import { marked, Marked } from 'marked';
import { api, PromptInfo, PromptAnalyzeResponse, TokenMetrics, RunResult } from '../api';
import { CommandType, CommandConfig, CommandOption, GlobalOption } from '../types';
import { COMMANDS, GLOBAL_OPTIONS, GLOBAL_DEFAULTS } from '../constants';
import type { GlobalDefaults } from '../types';
import PromptMetricsBar from './PromptMetricsBar';
import GuidanceSidebar from './GuidanceSidebar';
import SyncStatusBadge from './SyncStatusBadge';
import ModelSliders from './ModelSliders';
import { ModelInfo } from '../api';
import { resolveModelForStrength, ALL_MODELS } from '../lib/modelResolver';
import { pddAutocompleteExtension } from '../lib/pddAutocomplete';
import { findIncludeAtCursor, IncludeTagInfo, parseIncludeManyPaths } from '../lib/includeAnalyzer';
import PromptCodeDiffModal from './PromptCodeDiffModal';
import FilePickerInput from './FilePickerInput';
import SyncOptionsModal from './SyncOptionsModal';

// Helper to get language extension based on file path
function getLanguageExtension(filePath: string) {
  const ext = filePath.split('.').pop()?.toLowerCase();
  switch (ext) {
    case 'py':
      return python();
    case 'js':
    case 'jsx':
    case 'ts':
    case 'tsx':
      return javascript({ jsx: true, typescript: ext === 'ts' || ext === 'tsx' });
    case 'java':
      return java();
    default:
      return [];
  }
}

// Create a configured marked instance
const markedInstance = new Marked({
  breaks: true,
  gfm: true,
});

// Helper to format option names for display
function formatOptionName(name: string): string {
  return name
    .split('-')
    .map(word => word.charAt(0).toUpperCase() + word.slice(1))
    .join(' ');
}

// Individual option input component - responsive modern styling
const OptionInput: React.FC<{
  option: CommandOption | GlobalOption;
  value: any;
  onChange: (value: any) => void;
  compact?: boolean;
}> = ({ option, value, onChange, compact = false }) => {
  const inputId = `option-${option.name}`;

  if (option.type === 'checkbox') {
    return (
      <label htmlFor={inputId} className={`flex items-start gap-3 ${compact ? 'p-2' : 'p-3'} rounded-xl bg-surface-800/30 hover:bg-surface-800/50 transition-colors cursor-pointer group`}>
        <input
          type="checkbox"
          id={inputId}
          checked={!!value}
          onChange={(e) => onChange(e.target.checked)}
          className="w-4 h-4 mt-0.5 rounded bg-surface-700 border-surface-600 text-accent-500 focus:ring-accent-500 focus:ring-offset-surface-800"
        />
        <div className="flex-1 min-w-0">
          <div className={`${compact ? 'text-xs' : 'text-sm'} font-medium text-white group-hover:text-accent-300 transition-colors`}>{formatOptionName(option.name)}</div>
          <div className={`${compact ? 'text-[10px]' : 'text-xs'} text-surface-400 mt-0.5`}>{option.description}</div>
        </div>
      </label>
    );
  }

  if (option.type === 'range') {
    const min = option.min ?? 0;
    const max = option.max ?? 1;
    const step = option.step ?? 0.1;
    const displayValue = value ?? option.defaultValue ?? min;

    return (
      <div className={compact ? 'space-y-1.5' : 'space-y-2'}>
        <div className="flex items-center justify-between">
          <label htmlFor={inputId} className={`${compact ? 'text-xs' : 'text-sm'} font-medium text-white`}>
            {formatOptionName(option.name)}
          </label>
          <span className={`${compact ? 'text-xs' : 'text-sm'} font-mono text-accent-400 bg-accent-500/10 px-2 py-0.5 rounded-lg`}>
            {typeof displayValue === 'number' ? displayValue.toFixed(2) : displayValue}
          </span>
        </div>
        <p className={`${compact ? 'text-[10px]' : 'text-xs'} text-surface-400`}>{option.description}</p>
        <div className="flex items-center gap-3">
          <span className="text-[10px] text-surface-500 w-6 text-right">{min}</span>
          <input
            type="range"
            id={inputId}
            min={min}
            max={max}
            step={step}
            value={displayValue}
            onChange={(e) => onChange(parseFloat(e.target.value))}
            className="flex-1 h-2 bg-surface-700 rounded-full appearance-none cursor-pointer accent-accent-500
              [&::-webkit-slider-thumb]:appearance-none [&::-webkit-slider-thumb]:w-4 [&::-webkit-slider-thumb]:h-4
              [&::-webkit-slider-thumb]:rounded-full [&::-webkit-slider-thumb]:bg-accent-500
              [&::-webkit-slider-thumb]:shadow-lg [&::-webkit-slider-thumb]:shadow-accent-500/30
              [&::-webkit-slider-thumb]:hover:bg-accent-400 [&::-webkit-slider-thumb]:transition-colors"
          />
          <span className="text-[10px] text-surface-500 w-6">{max}</span>
        </div>
      </div>
    );
  }

  return (
    <div>
      <label htmlFor={inputId} className={`block ${compact ? 'text-xs' : 'text-sm'} font-medium text-white mb-1.5`}>
        {formatOptionName(option.name)}
        {option.required && <span className="text-red-400 ml-1">*</span>}
      </label>
      <p className={`${compact ? 'text-[10px]' : 'text-xs'} text-surface-400 mb-2`}>{option.description}</p>
      {option.type === 'textarea' ? (
        <textarea
          id={inputId}
          value={value || ''}
          onChange={(e) => onChange(e.target.value)}
          placeholder={option.placeholder}
          required={option.required}
          rows={3}
          className="w-full px-3 py-2.5 bg-surface-900/50 border border-surface-600 rounded-xl text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 focus:ring-1 focus:ring-accent-500/50 text-sm transition-all resize-none"
        />
      ) : (
        <input
          type={option.type === 'number' ? 'number' : 'text'}
          id={inputId}
          value={value || ''}
          onChange={(e) => onChange(option.type === 'number' ? (e.target.value ? Number(e.target.value) : '') : e.target.value)}
          placeholder={option.placeholder}
          required={option.required}
          className="w-full px-3 py-2.5 bg-surface-900/50 border border-surface-600 rounded-xl text-white placeholder-surface-500 focus:outline-none focus:border-accent-500 focus:ring-1 focus:ring-accent-500/50 text-sm transition-all"
        />
      )}
    </div>
  );
};

// Options Modal Component
const CommandOptionsModal: React.FC<{
  command: CommandConfig;
  prompt: PromptInfo;
  onRun: (options: Record<string, any>) => void;
  onAddToQueue?: (options: Record<string, any>) => void;
  onCancel: () => void;
  currentGlobalValues?: { strength: number; time: number; temperature: number };
}> = ({ command, prompt, onRun, onAddToQueue, onCancel, currentGlobalValues }) => {
  const [showAdvanced, setShowAdvanced] = useState(false);

  const [optionValues, setOptionValues] = useState<Record<string, any>>(() => {
    const defaults: Record<string, any> = {};

    // Set defaults from command options
    command.options.forEach(opt => {
      if (opt.defaultValue !== undefined) {
        if (opt.type === 'checkbox') {
          defaults[opt.name] = opt.defaultValue === 'true' || opt.defaultValue === true;
        } else if (opt.type === 'number' || opt.type === 'range') {
          defaults[opt.name] = opt.defaultValue;
        } else {
          defaults[opt.name] = opt.defaultValue;
        }
      }
    });

    // Pre-fill file paths from detected files
    if (command.requiresCode) {
      defaults['_code'] = prompt.code || '';
    }
    if (command.requiresTest) {
      defaults['_test'] = prompt.test || '';
    }

    // Special case: for Submit Example, pre-fill verification-program with example file
    if (command.name === CommandType.SUBMIT_EXAMPLE && prompt.example) {
      defaults['verification-program'] = prompt.example;
    }

    // Set global option defaults, using current slider values if available
    GLOBAL_OPTIONS.forEach(opt => {
      if (currentGlobalValues && opt.name === 'strength') {
        defaults[`_global_${opt.name}`] = currentGlobalValues.strength;
      } else if (currentGlobalValues && opt.name === 'time') {
        defaults[`_global_${opt.name}`] = currentGlobalValues.time;
      } else if (currentGlobalValues && opt.name === 'temperature') {
        defaults[`_global_${opt.name}`] = currentGlobalValues.temperature;
      } else {
        defaults[`_global_${opt.name}`] = opt.defaultValue;
      }
    });

    return defaults;
  });

  const handleValueChange = (optionName: string, value: any) => {
    setOptionValues(prev => ({ ...prev, [optionName]: value }));
  };

  const handleSubmit = (e: React.FormEvent) => {
    e.preventDefault();
    const cleanedOptions: Record<string, any> = {};

    // Add command-specific options
    Object.entries(optionValues).forEach(([key, value]) => {
      // Skip internal prefixed keys and empty values
      if (key.startsWith('_global_')) return;
      if (value !== '' && value !== undefined && value !== null) {
        cleanedOptions[key] = value;
      }
    });

    // Add global options (only if different from defaults)
    GLOBAL_OPTIONS.forEach(opt => {
      const value = optionValues[`_global_${opt.name}`];
      const defaultVal = opt.defaultValue;
      // Only include if value differs from default
      if (value !== defaultVal && value !== undefined && value !== null) {
        cleanedOptions[`_global_${opt.name}`] = value;
      }
    });

    onRun(cleanedOptions);
  };

  const handleAddToQueue = () => {
    const cleanedOptions: Record<string, any> = {};

    // Add command-specific options
    Object.entries(optionValues).forEach(([key, value]) => {
      if (key.startsWith('_global_')) return;
      if (value !== '' && value !== undefined && value !== null) {
        cleanedOptions[key] = value;
      }
    });

    // Add global options (only if different from defaults)
    GLOBAL_OPTIONS.forEach(opt => {
      const value = optionValues[`_global_${opt.name}`];
      const defaultVal = opt.defaultValue;
      if (value !== defaultVal && value !== undefined && value !== null) {
        cleanedOptions[`_global_${opt.name}`] = value;
      }
    });

    onAddToQueue?.(cleanedOptions);
  };

  // Check if any global options differ from defaults
  const hasCustomGlobalOptions = GLOBAL_OPTIONS.some(opt => {
    const value = optionValues[`_global_${opt.name}`];
    // Compare against slider values (if provided) rather than static defaults
    let baseline = opt.defaultValue;
    if (currentGlobalValues && opt.name === 'strength') baseline = currentGlobalValues.strength;
    else if (currentGlobalValues && opt.name === 'time') baseline = currentGlobalValues.time;
    else if (currentGlobalValues && opt.name === 'temperature') baseline = currentGlobalValues.temperature;
    return value !== baseline;
  });

  return (
    <div className="fixed inset-0 bg-black/60 backdrop-blur-sm flex items-center justify-center z-50 p-4 animate-fade-in" onClick={onCancel}>
      <div
        className="glass rounded-2xl border border-surface-600/50 shadow-2xl w-full max-w-md animate-scale-in"
        onClick={e => e.stopPropagation()}
      >
        <div className="px-4 sm:px-6 py-4 border-b border-surface-700/50">
          <div className="flex items-center gap-3">
            <div className="w-10 h-10 rounded-xl bg-accent-500/20 flex items-center justify-center">
              <span className="text-xl">{command.icon}</span>
            </div>
            <div>
              <h3 className="text-lg font-semibold text-white">{command.shortDescription}</h3>
              <p className="text-xs sm:text-sm text-surface-400 line-clamp-1">{command.description}</p>
            </div>
          </div>
        </div>

        <form onSubmit={handleSubmit}>
          <div className="px-4 sm:px-6 py-4 space-y-4 max-h-[50vh] sm:max-h-[60vh] overflow-y-auto">
            {/* Target prompt */}
            <div className="bg-surface-800/50 rounded-xl px-3 py-2.5 border border-surface-700/50">
              <div className="text-xs text-surface-400 mb-0.5">Target Prompt</div>
              <div className="text-sm text-white font-mono truncate">{prompt.sync_basename}</div>
            </div>

            {/* File path inputs for required files */}
            {command.requiresCode && (
              <FilePickerInput
                label="Code File"
                value={optionValues['_code'] || ''}
                onChange={(path) => handleValueChange('_code', path)}
                placeholder="e.g., src/calculator.py"
                description={prompt.code
                  ? 'Auto-detected code file. Change if needed.'
                  : 'No code file detected. Enter the path to use.'}
                required
                filter={['.py', '.ts', '.tsx', '.js', '.jsx', '.java', '.go', '.rs', '.rb', '.php', '.cs', '.cpp', '.c', '.h']}
                title="Select Code File"
                isDetected={!!prompt.code}
              />
            )}

            {command.requiresTest && (
              <FilePickerInput
                label="Test File"
                value={optionValues['_test'] || ''}
                onChange={(path) => handleValueChange('_test', path)}
                placeholder="e.g., tests/test_calculator.py"
                description={prompt.test
                  ? 'Auto-detected test file. Change if needed.'
                  : 'No test file detected. Enter the path to use.'}
                required
                filter={['.py', '.ts', '.tsx', '.js', '.jsx', '.java', '.go', '.rs', '.rb', '.php', '.cs', '.cpp', '.c']}
                title="Select Test File"
                isDetected={!!prompt.test}
              />
            )}

            {/* Command options */}
            {command.options.length > 0 ? (
              command.options.map(opt => (
                <OptionInput
                  key={opt.name}
                  option={opt}
                  value={optionValues[opt.name]}
                  onChange={(val) => handleValueChange(opt.name, val)}
                />
              ))
            ) : !command.requiresCode && !command.requiresTest ? (
              <p className="text-surface-400 text-sm">No additional options for this command.</p>
            ) : null}

            {/* Advanced Options (Global) - Collapsible */}
            <div className="border-t border-surface-700/30 pt-3 mt-2">
              <button
                type="button"
                onClick={() => setShowAdvanced(!showAdvanced)}
                className="w-full flex items-center justify-between text-left group"
              >
                <div className="flex items-center gap-2">
                  <span className="text-xs font-semibold text-surface-400 uppercase tracking-wider">
                    Advanced Options
                  </span>
                  {hasCustomGlobalOptions && (
                    <span className="w-2 h-2 rounded-full bg-accent-500 animate-pulse" title="Custom settings applied" />
                  )}
                </div>
                <svg
                  className={`w-4 h-4 text-surface-400 transition-transform duration-200 ${showAdvanced ? 'rotate-180' : ''}`}
                  fill="none"
                  stroke="currentColor"
                  viewBox="0 0 24 24"
                >
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                </svg>
              </button>

              {showAdvanced && (
                <div className="mt-3 space-y-3 animate-slide-down">
                  {/* Model Settings Group */}
                  <div className="space-y-3 p-3 rounded-xl bg-surface-800/20 border border-surface-700/30">
                    <div className="text-[10px] font-medium text-surface-500 uppercase tracking-wider">Model Settings</div>
                    {GLOBAL_OPTIONS.filter(opt => ['strength', 'temperature', 'time'].includes(opt.name)).map(opt => (
                      <OptionInput
                        key={opt.name}
                        option={opt}
                        value={optionValues[`_global_${opt.name}`]}
                        onChange={(val) => handleValueChange(`_global_${opt.name}`, val)}
                        compact
                      />
                    ))}
                  </div>

                  {/* Execution Options Group */}
                  <div className="space-y-1 p-3 rounded-xl bg-surface-800/20 border border-surface-700/30">
                    <div className="text-[10px] font-medium text-surface-500 uppercase tracking-wider mb-2">Execution Options</div>
                    {GLOBAL_OPTIONS.filter(opt => ['local', 'verbose', 'quiet', 'force', 'review-examples'].includes(opt.name)).map(opt => (
                      <OptionInput
                        key={opt.name}
                        option={opt}
                        value={optionValues[`_global_${opt.name}`]}
                        onChange={(val) => handleValueChange(`_global_${opt.name}`, val)}
                        compact
                      />
                    ))}
                  </div>
                </div>
              )}
            </div>
          </div>

          <div className="px-4 sm:px-6 py-4 border-t border-surface-700/50 flex flex-col-reverse sm:flex-row justify-end gap-2 sm:gap-3">
            <button
              type="button"
              onClick={onCancel}
              className="w-full sm:w-auto px-4 py-2.5 rounded-xl text-sm font-medium bg-surface-700/50 text-surface-300 hover:bg-surface-600 transition-colors"
            >
              Cancel
            </button>
            {onAddToQueue && (
              <button
                type="button"
                onClick={handleAddToQueue}
                className="w-full sm:w-auto px-4 py-2.5 rounded-xl text-sm font-medium bg-emerald-600/20 text-emerald-300 hover:bg-emerald-600 hover:text-white border border-emerald-600/30 hover:border-emerald-500/50 transition-all flex items-center justify-center gap-2"
              >
                <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 6v6m0 0v6m0-6h6m-6 0H6" />
                </svg>
                <span>Add to Queue</span>
              </button>
            )}
            <button
              type="submit"
              className="w-full sm:w-auto px-4 py-2.5 rounded-xl text-sm font-medium bg-gradient-to-r from-accent-600 to-accent-500 hover:from-accent-500 hover:to-accent-400 text-white shadow-lg shadow-accent-500/25 transition-all flex items-center justify-center gap-2"
            >
              <span>{command.icon}</span>
              <span>Run {command.shortDescription}</span>
            </button>
          </div>
        </form>
      </div>
    </div>
  );
};

interface PromptSpaceProps {
  prompt: PromptInfo;
  onBack: () => void;
  onRunCommand: (command: CommandType, options?: Record<string, any>) => void;
  onAddToQueue?: (command: CommandType, options?: Record<string, any>) => void;
  isExecuting: boolean;
  executionStatus?: 'idle' | 'running' | 'success' | 'failed';
  lastCommand?: string | null;
  lastRunResult?: RunResult | null;
  onCancelCommand?: () => void;
  /** When true, PromptSpace renders inside App layout without its own header */
  embedded?: boolean;
}

const PromptSpace: React.FC<PromptSpaceProps> = ({
  prompt,
  onBack,
  onRunCommand,
  onAddToQueue,
  isExecuting,
  executionStatus = 'idle',
  lastCommand = null,
  lastRunResult = null,
  onCancelCommand,
  embedded = false,
}) => {
  const editorContainerRef = useRef<HTMLDivElement>(null);
  const editorViewRef = useRef<EditorView | null>(null);
  const originalContentRef = useRef<string>('');
  const editedContentRef = useRef<string>('');  // Track user's edited content
  const editableCompartment = useRef(new Compartment());

  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [content, setContent] = useState<string | null>(null);
  const [hasChanges, setHasChanges] = useState(false);
  const [saving, setSaving] = useState(false);
  const [saveSuccess, setSaveSuccess] = useState(false);
  const [modalCommand, setModalCommand] = useState<CommandConfig | null>(null);

  // Token metrics and view mode state
  const [viewMode, setViewMode] = useState<'raw' | 'processed'>('raw');
  const [analysisResult, setAnalysisResult] = useState<PromptAnalyzeResponse | null>(null);
  const [isAnalyzing, setIsAnalyzing] = useState(false);
  const [showPreview, setShowPreview] = useState(false);

  // Model selection state - uses full catalog from data/llm_model.csv
  const [selectedModel, setSelectedModel] = useState<ModelInfo | null>(() => resolveModelForStrength(ALL_MODELS, GLOBAL_DEFAULTS.strength));
  const [strength, setStrength] = useState(GLOBAL_DEFAULTS.strength);
  const [timeValue, setTimeValue] = useState(GLOBAL_DEFAULTS.time);
  const [temperature, setTemperature] = useState(GLOBAL_DEFAULTS.temperature);

  // Include token analysis state
  const [includeAnalysis, setIncludeAnalysis] = useState<{
    visible: boolean;
    loading: boolean;
    tagInfo: IncludeTagInfo | null;
    metrics: TokenMetrics | null;
    error: string | null;
  }>({ visible: false, loading: false, tagInfo: null, metrics: null, error: null });

  // Track content for preview (updated when toggling preview on)
  const [previewContent, setPreviewContent] = useState<string>('');

  // Code panel state for side-by-side view
  const [showCodePanel, setShowCodePanel] = useState(false);
  const [codeContent, setCodeContent] = useState<string | null>(null);
  const [codeLoading, setCodeLoading] = useState(false);
  const [codeError, setCodeError] = useState<string | null>(null);
  const [codeCollapsed, setCodeCollapsed] = useState(false);
  const codeEditorContainerRef = useRef<HTMLDivElement>(null);
  const codeEditorViewRef = useRef<EditorView | null>(null);

  // Test panel state for side-by-side view
  const [showTestPanel, setShowTestPanel] = useState(false);
  const [testContent, setTestContent] = useState<string | null>(null);
  const [testLoading, setTestLoading] = useState(false);
  const [testError, setTestError] = useState<string | null>(null);
  const [testCollapsed, setTestCollapsed] = useState(false);
  const testEditorContainerRef = useRef<HTMLDivElement>(null);
  const testEditorViewRef = useRef<EditorView | null>(null);

  // Example panel state for side-by-side view
  const [showExamplePanel, setShowExamplePanel] = useState(false);
  const [exampleContent, setExampleContent] = useState<string | null>(null);
  const [exampleLoading, setExampleLoading] = useState(false);
  const [exampleError, setExampleError] = useState<string | null>(null);
  const [exampleCollapsed, setExampleCollapsed] = useState(false);
  const exampleEditorContainerRef = useRef<HTMLDivElement>(null);
  const exampleEditorViewRef = useRef<EditorView | null>(null);

  // Diff analysis modal state
  const [showDiffModal, setShowDiffModal] = useState(false);

  // Sync options modal state (for configuring sync options before running Generate/Sync)
  const [showSyncOptionsModal, setShowSyncOptionsModal] = useState(false);

  // Sync from architecture state
  const [isSyncingFromArch, setIsSyncingFromArch] = useState(false);
  const [syncFromArchError, setSyncFromArchError] = useState<string | null>(null);
  const [syncFromArchSuccess, setSyncFromArchSuccess] = useState(false);

  // Resolve model whenever strength changes
  useEffect(() => {
    const resolved = resolveModelForStrength(ALL_MODELS, strength);
    if (resolved) setSelectedModel(resolved);
  }, [strength]);

  // Update preview content when toggling preview on or when view mode changes
  useEffect(() => {
    if (showPreview) {
      // Get latest content from editor if available
      let contentToRender: string;
      if (viewMode === 'processed' && analysisResult?.processed_content) {
        contentToRender = analysisResult.processed_content;
      } else if (editorViewRef.current) {
        contentToRender = editorViewRef.current.state.doc.toString();
      } else {
        contentToRender = editedContentRef.current || content || '';
      }
      setPreviewContent(contentToRender);
    }
  }, [showPreview, viewMode, analysisResult?.processed_content, content]);

  // Memoized rendered markdown
  const renderedMarkdown = useMemo(() => {
    if (!previewContent) return '';
    try {
      const result = markedInstance.parse(previewContent);
      // marked.parse can return string or Promise<string>, handle both
      if (typeof result === 'string') {
        return result;
      }
      return '';
    } catch (e) {
      console.error('Markdown rendering error:', e);
      return '<p class="text-red-400">Error rendering markdown</p>';
    }
  }, [previewContent]);

  // Load file content
  useEffect(() => {
    let cancelled = false;

    const loadContent = async () => {
      setLoading(true);
      setError(null);
      try {
        const file = await api.getFileContent(prompt.prompt);
        if (!cancelled) {
          originalContentRef.current = file.content;
          editedContentRef.current = file.content;  // Initialize edited content
          setContent(file.content);
        }
      } catch (e: any) {
        if (!cancelled) {
          setError(e.message || 'Failed to load file');
        }
      } finally {
        if (!cancelled) {
          setLoading(false);
        }
      }
    };

    loadContent();

    return () => {
      cancelled = true;
    };
  }, [prompt.prompt]);

  // Initialize editor after content is loaded and container is rendered
  // Re-initialize when switching back from preview mode
  useEffect(() => {
    // Don't initialize if in preview mode or no content
    if (showPreview || content === null || !editorContainerRef.current) return;

    // Clean up existing editor
    if (editorViewRef.current) {
      editorViewRef.current.destroy();
      editorViewRef.current = null;
    }

    // Use edited content if available (preserves user changes when toggling preview)
    const docContent = editedContentRef.current || content;

    const state = EditorState.create({
      doc: docContent,
      extensions: [
        lineNumbers(),
        highlightActiveLine(),
        history(),
        keymap.of([...completionKeymap, ...defaultKeymap, ...historyKeymap]),
        markdown(),
        oneDark,
        // PDD directive autocomplete
        ...pddAutocompleteExtension(),
        // Editable compartment - starts as editable (raw mode)
        editableCompartment.current.of(EditorView.editable.of(viewMode === 'raw')),
        EditorView.updateListener.of((update) => {
          if (update.docChanged) {
            const newContent = update.state.doc.toString();
            // Only track edits when in raw mode (editable)
            if (update.view.state.facet(EditorView.editable)) {
              editedContentRef.current = newContent;
            }
            setHasChanges(newContent !== originalContentRef.current);
          }
        }),
        EditorView.theme({
          '&': {
            height: '100%',
            fontSize: '14px',
            backgroundColor: 'rgb(17 24 39)',
          },
          '.cm-scroller': {
            overflow: 'auto',
            fontFamily: 'ui-monospace, SFMono-Regular, "SF Mono", Menlo, Consolas, monospace',
          },
          '.cm-gutters': {
            backgroundColor: 'rgb(31 41 55)',
            borderRight: '1px solid rgb(55 65 81)',
          },
          '.cm-activeLineGutter': {
            backgroundColor: 'rgb(55 65 81)',
          },
          '.cm-activeLine': {
            backgroundColor: 'rgba(55, 65, 81, 0.5)',
          },
        }),
      ],
    });

    editorViewRef.current = new EditorView({
      state,
      parent: editorContainerRef.current,
    });

    // Cleanup on unmount or when dependencies change
    return () => {
      if (editorViewRef.current) {
        editorViewRef.current.destroy();
        editorViewRef.current = null;
      }
    };
  }, [content, showPreview, viewMode]);

  // Analyze prompt for metrics (debounced) - uses current editor content and selected model
  useEffect(() => {
    if (content === null) return;

    const analyzePrompt = async () => {
      setIsAnalyzing(true);
      try {
        // Get current content from editor or ref
        const currentContent = editorViewRef.current
          ? editorViewRef.current.state.doc.toString()
          : editedContentRef.current || content;

        // Use selected model for cost estimation, fallback to Claude Sonnet
        const modelForAnalysis = selectedModel?.model || 'claude-sonnet-4-20250514';

        const result = await api.analyzePrompt({
          path: prompt.prompt,
          model: modelForAnalysis,
          preprocess: true,
          content: currentContent,  // Send current content instead of reading from file
        });
        setAnalysisResult(result);
      } catch (e: any) {
        console.error('Failed to analyze prompt:', e);
        // Don't show error to user, just log it - metrics are optional
      } finally {
        setIsAnalyzing(false);
      }
    };

    // Debounce by 500ms
    const timeoutId = setTimeout(analyzePrompt, 500);
    return () => clearTimeout(timeoutId);
  }, [content, prompt.prompt, hasChanges, selectedModel]);  // Re-analyze when content or model changes

  // Load code content when code panel is opened
  const loadCodeContent = useCallback(async () => {
    if (!prompt.code) {
      setCodeError('No code file associated with this prompt');
      return;
    }

    setCodeLoading(true);
    setCodeError(null);

    try {
      const file = await api.getFileContent(prompt.code);
      setCodeContent(file.content);
    } catch (e: any) {
      setCodeError(e.message || 'Failed to load code file');
    } finally {
      setCodeLoading(false);
    }
  }, [prompt.code]);

  // Toggle code panel
  const handleToggleCodePanel = useCallback(() => {
    if (!showCodePanel && !codeContent && prompt.code) {
      loadCodeContent();
    }
    setShowCodePanel(!showCodePanel);
  }, [showCodePanel, codeContent, prompt.code, loadCodeContent]);

  // Reload code content (for refresh button)
  const handleReloadCode = useCallback(() => {
    loadCodeContent();
  }, [loadCodeContent]);

  // Handle showing diff modal - load code content if needed
  const handleShowDiff = useCallback(async () => {
    if (!codeContent && prompt.code) {
      await loadCodeContent();
    }
    setShowDiffModal(true);
  }, [codeContent, prompt.code, loadCodeContent]);

  // Initialize code editor when content is loaded and panel is visible and not collapsed
  useEffect(() => {
    if (!showCodePanel || codeCollapsed || codeContent === null || !codeEditorContainerRef.current) return;

    if (codeEditorViewRef.current) {
      codeEditorViewRef.current.destroy();
      codeEditorViewRef.current = null;
    }

    const state = EditorState.create({
      doc: codeContent,
      extensions: [
        lineNumbers(),
        highlightActiveLine(),
        EditorView.editable.of(false),
        getLanguageExtension(prompt.code || ''),
        oneDark,
        EditorView.theme({
          '&': { height: '100%', fontSize: '13px', backgroundColor: 'rgb(17 24 39)' },
          '.cm-scroller': { overflow: 'auto', fontFamily: 'ui-monospace, SFMono-Regular, "SF Mono", Menlo, Consolas, monospace' },
          '.cm-gutters': { backgroundColor: 'rgb(31 41 55)', borderRight: '1px solid rgb(55 65 81)' },
          '.cm-activeLineGutter': { backgroundColor: 'rgb(55 65 81)' },
          '.cm-activeLine': { backgroundColor: 'rgba(55, 65, 81, 0.5)' },
        }),
      ],
    });

    codeEditorViewRef.current = new EditorView({ state, parent: codeEditorContainerRef.current });

    return () => {
      if (codeEditorViewRef.current) { codeEditorViewRef.current.destroy(); codeEditorViewRef.current = null; }
    };
  }, [showCodePanel, codeCollapsed, codeContent, prompt.code]);

  // Load test content when test panel is opened
  const loadTestContent = useCallback(async () => {
    if (!prompt.test) {
      setTestError('No test file associated with this prompt');
      return;
    }

    setTestLoading(true);
    setTestError(null);

    try {
      const file = await api.getFileContent(prompt.test);
      setTestContent(file.content);
    } catch (e: any) {
      setTestError(e.message || 'Failed to load test file');
    } finally {
      setTestLoading(false);
    }
  }, [prompt.test]);

  // Toggle test panel
  const handleToggleTestPanel = useCallback(() => {
    if (!showTestPanel && !testContent && prompt.test) {
      loadTestContent();
    }
    setShowTestPanel(!showTestPanel);
  }, [showTestPanel, testContent, prompt.test, loadTestContent]);

  // Initialize test editor when content is loaded and panel is visible
  useEffect(() => {
    if (!showTestPanel || testCollapsed || testContent === null || !testEditorContainerRef.current) return;

    if (testEditorViewRef.current) {
      testEditorViewRef.current.destroy();
      testEditorViewRef.current = null;
    }

    const state = EditorState.create({
      doc: testContent,
      extensions: [
        lineNumbers(),
        highlightActiveLine(),
        EditorView.editable.of(false),
        getLanguageExtension(prompt.test || ''),
        oneDark,
        EditorView.theme({
          '&': { height: '100%', fontSize: '13px', backgroundColor: 'rgb(17 24 39)' },
          '.cm-scroller': { overflow: 'auto', fontFamily: 'ui-monospace, SFMono-Regular, "SF Mono", Menlo, Consolas, monospace' },
          '.cm-gutters': { backgroundColor: 'rgb(31 41 55)', borderRight: '1px solid rgb(55 65 81)' },
          '.cm-activeLineGutter': { backgroundColor: 'rgb(55 65 81)' },
          '.cm-activeLine': { backgroundColor: 'rgba(55, 65, 81, 0.5)' },
        }),
      ],
    });

    testEditorViewRef.current = new EditorView({ state, parent: testEditorContainerRef.current });

    return () => {
      if (testEditorViewRef.current) { testEditorViewRef.current.destroy(); testEditorViewRef.current = null; }
    };
  }, [showTestPanel, testCollapsed, testContent, prompt.test]);

  // Load example content when example panel is opened
  const loadExampleContent = useCallback(async () => {
    if (!prompt.example) {
      setExampleError('No example file associated with this prompt');
      return;
    }

    setExampleLoading(true);
    setExampleError(null);

    try {
      const file = await api.getFileContent(prompt.example);
      setExampleContent(file.content);
    } catch (e: any) {
      setExampleError(e.message || 'Failed to load example file');
    } finally {
      setExampleLoading(false);
    }
  }, [prompt.example]);

  // Toggle example panel
  const handleToggleExamplePanel = useCallback(() => {
    if (!showExamplePanel && !exampleContent && prompt.example) {
      loadExampleContent();
    }
    setShowExamplePanel(!showExamplePanel);
  }, [showExamplePanel, exampleContent, prompt.example, loadExampleContent]);

  // Initialize example editor when content is loaded and panel is visible
  useEffect(() => {
    if (!showExamplePanel || exampleCollapsed || exampleContent === null || !exampleEditorContainerRef.current) return;

    if (exampleEditorViewRef.current) {
      exampleEditorViewRef.current.destroy();
      exampleEditorViewRef.current = null;
    }

    const state = EditorState.create({
      doc: exampleContent,
      extensions: [
        lineNumbers(),
        highlightActiveLine(),
        EditorView.editable.of(false),
        getLanguageExtension(prompt.example || ''),
        oneDark,
        EditorView.theme({
          '&': { height: '100%', fontSize: '13px', backgroundColor: 'rgb(17 24 39)' },
          '.cm-scroller': { overflow: 'auto', fontFamily: 'ui-monospace, SFMono-Regular, "SF Mono", Menlo, Consolas, monospace' },
          '.cm-gutters': { backgroundColor: 'rgb(31 41 55)', borderRight: '1px solid rgb(55 65 81)' },
          '.cm-activeLineGutter': { backgroundColor: 'rgb(55 65 81)' },
          '.cm-activeLine': { backgroundColor: 'rgba(55, 65, 81, 0.5)' },
        }),
      ],
    });

    exampleEditorViewRef.current = new EditorView({ state, parent: exampleEditorContainerRef.current });

    return () => {
      if (exampleEditorViewRef.current) { exampleEditorViewRef.current.destroy(); exampleEditorViewRef.current = null; }
    };
  }, [showExamplePanel, exampleCollapsed, exampleContent, prompt.example]);

  // Whether any right panel is visible
  const anyRightPanelOpen = showCodePanel || showTestPanel || showExamplePanel;

  // Keyboard shortcut for include analysis (Cmd+. / Ctrl+.)
  useEffect(() => {
    const handleKeyDown = (e: KeyboardEvent) => {
      // Check for Cmd+. (Mac) or Ctrl+. (Windows/Linux) - common for "quick actions"
      if ((e.metaKey || e.ctrlKey) && e.key === '.') {
        e.preventDefault();
        analyzeIncludeAtCursor();
      }
      // Escape to close the popup
      if (e.key === 'Escape' && includeAnalysis.visible) {
        closeIncludeAnalysis();
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [includeAnalysis.visible]);

  // Handle view mode changes - update editor content and editability
  const handleViewModeChange = (mode: 'raw' | 'processed') => {
    // Before switching away from raw mode, save current editor content
    if (viewMode === 'raw' && editorViewRef.current) {
      editedContentRef.current = editorViewRef.current.state.doc.toString();
    }

    // Always update the view mode state (needed for preview mode too)
    setViewMode(mode);

    // If editor exists, update its content and editability
    if (editorViewRef.current) {
      // Update editor content based on mode
      let displayContent: string;
      const isEditable = mode === 'raw';

      if (mode === 'processed' && analysisResult?.processed_content) {
        displayContent = analysisResult.processed_content;
      } else {
        // Use edited content when switching back to raw mode
        displayContent = editedContentRef.current || content || '';
      }

      const currentContent = editorViewRef.current.state.doc.toString();

      // Build transaction effects
      const effects: any[] = [
        // Toggle editability
        editableCompartment.current.reconfigure(EditorView.editable.of(isEditable)),
      ];

      // Update content if different
      if (currentContent !== displayContent) {
        editorViewRef.current.dispatch({
          changes: {
            from: 0,
            to: currentContent.length,
            insert: displayContent,
          },
          effects,
        });
      } else {
        // Just update editability
        editorViewRef.current.dispatch({ effects });
      }
    }
  };

  const handleSave = async () => {
    if (!editorViewRef.current) return;

    setSaving(true);
    setSaveSuccess(false);
    setError(null);

    try {
      const newContent = editorViewRef.current.state.doc.toString();
      await api.writeFile(prompt.prompt, newContent);
      originalContentRef.current = newContent;
      editedContentRef.current = newContent;  // Sync edited content after save
      setHasChanges(false);
      setSaveSuccess(true);

      setTimeout(() => setSaveSuccess(false), 2000);
    } catch (e: any) {
      setError(e.message || 'Failed to save');
    } finally {
      setSaving(false);
    }
  };

  const handleBack = () => {
    if (hasChanges && !window.confirm('Discard unsaved changes?')) return;
    onBack();
  };

  // Sync PDD tags from architecture.json into the prompt
  const handleSyncFromArchitecture = async () => {
    if (!editorViewRef.current) return;

    setIsSyncingFromArch(true);
    setSyncFromArchError(null);
    setSyncFromArchSuccess(false);

    try {
      // Get the prompt filename from the path
      const promptFilename = prompt.prompt.split('/').pop() || prompt.prompt;

      // Call the API to generate tags
      const result = await api.generateTagsForPrompt(promptFilename);

      if (!result.success) {
        setSyncFromArchError(result.error || 'Failed to generate tags');
        return;
      }

      if (!result.tags) {
        setSyncFromArchError('No architecture entry found for this prompt');
        return;
      }

      if (result.has_existing_tags) {
        // Prompt already has tags - ask user if they want to replace
        if (!window.confirm('This prompt already has PDD tags. Replace them with tags from architecture.json?')) {
          return;
        }
        // Remove existing tags before inserting new ones
        const currentContent = editorViewRef.current.state.doc.toString();
        // Remove existing pdd tags (simple regex approach)
        const cleanedContent = currentContent
          .replace(/<pdd-reason>[\s\S]*?<\/pdd-reason>\s*/g, '')
          .replace(/<pdd-interface>[\s\S]*?<\/pdd-interface>\s*/g, '')
          .replace(/<pdd-dependency>[\s\S]*?<\/pdd-dependency>\s*/g, '')
          .trimStart();

        // Insert new tags at the beginning
        const newContent = result.tags + '\n\n' + cleanedContent;
        editorViewRef.current.dispatch({
          changes: { from: 0, to: editorViewRef.current.state.doc.length, insert: newContent },
        });
      } else {
        // No existing tags - insert at the beginning
        const currentContent = editorViewRef.current.state.doc.toString();
        const newContent = result.tags + '\n\n' + currentContent;
        editorViewRef.current.dispatch({
          changes: { from: 0, to: editorViewRef.current.state.doc.length, insert: newContent },
        });
      }

      // Update state
      editedContentRef.current = editorViewRef.current.state.doc.toString();
      setHasChanges(editedContentRef.current !== originalContentRef.current);
      setSyncFromArchSuccess(true);
      setTimeout(() => setSyncFromArchSuccess(false), 3000);
    } catch (e: any) {
      setSyncFromArchError(e.message || 'Failed to sync from architecture');
    } finally {
      setIsSyncingFromArch(false);
    }
  };

  // Analyze include tag at cursor (triggered by Cmd+. or button click)
  const analyzeIncludeAtCursor = async () => {
    if (!editorViewRef.current) return;

    const state = editorViewRef.current.state;
    const tagInfo = findIncludeAtCursor(state);

    if (!tagInfo) {
      // No include tag at cursor - show brief message
      setIncludeAnalysis({
        visible: true,
        loading: false,
        tagInfo: null,
        metrics: null,
        error: 'Place cursor inside an <include>, <shell>, or <web> tag to analyze',
      });
      setTimeout(() => setIncludeAnalysis(prev => ({ ...prev, visible: false })), 3000);
      return;
    }

    // Start loading
    setIncludeAnalysis({
      visible: true,
      loading: true,
      tagInfo,
      metrics: null,
      error: null,
    });

    try {
      // For include-many, analyze the first file (could be extended to show all)
      let pathToAnalyze = tagInfo.path;
      if (tagInfo.tagType === 'include-many') {
        const paths = parseIncludeManyPaths(tagInfo.path);
        if (paths.length > 0) {
          pathToAnalyze = paths[0];
        }
      }

      const metrics = await api.analyzeFile(pathToAnalyze);
      setIncludeAnalysis({
        visible: true,
        loading: false,
        tagInfo,
        metrics,
        error: null,
      });
    } catch (e: any) {
      setIncludeAnalysis({
        visible: true,
        loading: false,
        tagInfo,
        metrics: null,
        error: e.message || 'Failed to analyze file',
      });
    }
  };

  // Close include analysis popup
  const closeIncludeAnalysis = () => {
    setIncludeAnalysis(prev => ({ ...prev, visible: false }));
  };

  const handleCommandClick = (command: CommandType) => {
    const config = COMMANDS[command];
    // Show modal for commands with options OR that require file inputs
    if ((config.options && config.options.length > 0) || config.requiresCode || config.requiresTest) {
      setModalCommand(config);
    } else {
      onRunCommand(command);
    }
  };

  const handleRunWithOptions = (options: Record<string, any>) => {
    if (modalCommand) {
      onRunCommand(modalCommand.name, options);
      setModalCommand(null);
    }
  };

  const handleAddToQueueWithOptions = (options: Record<string, any>) => {
    if (modalCommand && onAddToQueue) {
      onAddToQueue(modalCommand.name, options);
      setModalCommand(null);
    }
  };

  // Check if command has missing required files (for visual indication only)
  const getMissingFiles = (cmd: CommandConfig): string[] => {
    const missing: string[] = [];
    if (cmd.requiresCode && !prompt.code) missing.push('code');
    if (cmd.requiresTest && !prompt.test) missing.push('test');
    return missing;
  };

  // Split commands into regular and advanced
  const regularCommands = Object.values(COMMANDS).filter(cmd => cmd.requiresPrompt && !cmd.isAdvanced);
  const advancedCommands = Object.values(COMMANDS).filter(cmd => cmd.isAdvanced);
  // Commands shown in the vertical command bar (excludes sync/update and generate-group which have dedicated UI)
  const commandBarCommands = regularCommands.filter(cmd => cmd.group !== 'sync-update' && cmd.group !== 'generate');

  // State for mobile sidebar toggle and advanced commands
  const [sidebarOpen, setSidebarOpen] = useState(false);
  const [showAdvancedCommands, setShowAdvancedCommands] = useState(false);
  const [guidanceSidebarOpen, setGuidanceSidebarOpen] = useState(false);

  return (
    <div className={embedded ? "flex-1 flex flex-col bg-surface-950" : "h-screen flex flex-col bg-surface-950"}>
      {/* Header - Modern responsive design (hidden in embedded mode) */}
      {!embedded && (
      <header className="glass flex items-center justify-between px-3 sm:px-4 py-2.5 sm:py-3 border-b border-surface-700/50 sticky top-0 z-30">
        <div className="flex items-center gap-2 sm:gap-4 min-w-0">
          <button
            onClick={handleBack}
            className="flex items-center gap-1.5 sm:gap-2 text-surface-400 hover:text-white transition-colors px-2 py-1.5 rounded-lg hover:bg-surface-700/50"
          >
            <svg className="w-4 h-4 sm:w-5 sm:h-5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M10 19l-7-7m0 0l7-7m-7 7h18" />
            </svg>
            <span className="hidden sm:inline text-sm">Back</span>
          </button>
          <div className="h-5 w-px bg-surface-700 hidden sm:block" />
          <div className="flex items-center gap-2 min-w-0">
            <h1 className="text-sm sm:text-lg font-semibold text-white truncate">{prompt.sync_basename}</h1>
            {prompt.language && (
              <span className="px-1.5 sm:px-2 py-0.5 rounded-full text-[10px] sm:text-xs bg-accent-500/15 text-accent-300 border border-accent-500/30 font-medium flex-shrink-0">
                {prompt.language}
              </span>
            )}
            {prompt.sync_basename && prompt.language && (
              <SyncStatusBadge
                basename={prompt.sync_basename}
                language={prompt.language}
                refreshTrigger={saveSuccess ? 1 : 0}
              />
            )}
          </div>
        </div>

        {/* Save status and actions */}
        <div className="flex items-center gap-2 sm:gap-3">
          {/* Mobile sidebar toggle */}
          <button
            onClick={() => setSidebarOpen(!sidebarOpen)}
            className="lg:hidden flex items-center gap-1.5 px-2.5 py-1.5 text-surface-400 hover:text-white bg-surface-700/50 hover:bg-surface-600 rounded-lg transition-colors"
          >
            <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 6h16M4 12h16m-7 6h7" />
            </svg>
          </button>

          {hasChanges && (
            <span className="text-yellow-400 text-xs sm:text-sm flex items-center gap-1.5 px-2 py-1 rounded-full bg-yellow-500/10 border border-yellow-500/20">
              <span className="w-1.5 h-1.5 sm:w-2 sm:h-2 bg-yellow-400 rounded-full animate-pulse"></span>
              <span className="hidden xs:inline">Unsaved</span>
            </span>
          )}
          {saveSuccess && (
            <span className="text-green-400 text-xs sm:text-sm flex items-center gap-1.5 px-2 py-1 rounded-full bg-green-500/10 border border-green-500/20">
              <svg className="w-3.5 h-3.5 sm:w-4 sm:h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
              </svg>
            </span>
          )}
          {syncFromArchSuccess && (
            <span className="text-emerald-400 text-xs sm:text-sm flex items-center gap-1.5 px-2 py-1 rounded-full bg-emerald-500/10 border border-emerald-500/20">
              <svg className="w-3.5 h-3.5 sm:w-4 sm:h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
              </svg>
              <span className="hidden sm:inline">Tags injected</span>
            </span>
          )}
          {syncFromArchError && (
            <span className="text-red-400 text-xs flex items-center gap-1 px-2 py-1 rounded-full bg-red-500/10 border border-red-500/20" title={syncFromArchError}>
              <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 8v4m0 4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
              </svg>
            </span>
          )}
          {/* Sync from Architecture button */}
          <button
            onClick={handleSyncFromArchitecture}
            disabled={isSyncingFromArch || viewMode === 'processed'}
            className={`px-2.5 sm:px-3 py-1.5 text-xs sm:text-sm rounded-lg flex items-center gap-1.5 transition-all duration-200 ${
              !isSyncingFromArch && viewMode === 'raw'
                ? 'bg-surface-700/50 text-surface-300 hover:text-white hover:bg-surface-600 border border-surface-600'
                : 'bg-surface-700/30 text-surface-500 cursor-not-allowed'
            }`}
            title="Inject PDD tags from architecture.json"
          >
            {isSyncingFromArch ? (
              <svg className="animate-spin h-3.5 w-3.5 sm:h-4 sm:w-4" viewBox="0 0 24 24">
                <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
              </svg>
            ) : (
              <svg className="w-3.5 h-3.5 sm:w-4 sm:h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
              </svg>
            )}
            <span className="hidden sm:inline">{isSyncingFromArch ? 'Syncing...' : 'Sync from JSON'}</span>
          </button>
          <button
            onClick={handleSave}
            disabled={!hasChanges || saving || viewMode === 'processed'}
            className={`px-2.5 sm:px-4 py-1.5 text-xs sm:text-sm rounded-lg flex items-center gap-1.5 sm:gap-2 transition-all duration-200 ${
              hasChanges && !saving && viewMode === 'raw'
                ? 'bg-gradient-to-r from-accent-600 to-accent-500 hover:from-accent-500 hover:to-accent-400 text-white shadow-lg shadow-accent-500/25'
                : 'bg-surface-700/50 text-surface-500 cursor-not-allowed'
            }`}
            title={viewMode === 'processed' ? 'Switch to Raw view to save changes' : undefined}
          >
            {saving ? (
              <svg className="animate-spin h-3.5 w-3.5 sm:h-4 sm:w-4" viewBox="0 0 24 24">
                <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
              </svg>
            ) : (
              <svg className="w-3.5 h-3.5 sm:w-4 sm:h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M8 7H5a2 2 0 00-2 2v9a2 2 0 002 2h14a2 2 0 002-2V9a2 2 0 00-2-2h-3m-1 4l-3 3m0 0l-3-3m3 3V4" />
              </svg>
            )}
            <span className="hidden xs:inline">{saving ? 'Saving...' : 'Save'}</span>
          </button>
        </div>
      </header>
      )}

      {/* Embedded mode action bar - Save/Sync buttons when header is hidden */}
      {embedded && (
        <div className="flex items-center justify-end gap-2 sm:gap-3 px-3 sm:px-4 py-2 border-b border-surface-700/50 bg-surface-900/50">
          {hasChanges && (
            <span className="text-yellow-400 text-xs sm:text-sm flex items-center gap-1.5 px-2 py-1 rounded-full bg-yellow-500/10 border border-yellow-500/20">
              <span className="w-1.5 h-1.5 sm:w-2 sm:h-2 bg-yellow-400 rounded-full animate-pulse"></span>
              <span className="hidden xs:inline">Unsaved</span>
            </span>
          )}
          {saveSuccess && (
            <span className="text-green-400 text-xs sm:text-sm flex items-center gap-1.5 px-2 py-1 rounded-full bg-green-500/10 border border-green-500/20">
              <svg className="w-3.5 h-3.5 sm:w-4 sm:h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
              </svg>
            </span>
          )}
          {syncFromArchSuccess && (
            <span className="text-emerald-400 text-xs sm:text-sm flex items-center gap-1.5 px-2 py-1 rounded-full bg-emerald-500/10 border border-emerald-500/20">
              <svg className="w-3.5 h-3.5 sm:w-4 sm:h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
              </svg>
              <span className="hidden sm:inline">Tags injected</span>
            </span>
          )}
          {syncFromArchError && (
            <span className="text-red-400 text-xs flex items-center gap-1 px-2 py-1 rounded-full bg-red-500/10 border border-red-500/20" title={syncFromArchError}>
              <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 8v4m0 4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
              </svg>
            </span>
          )}
          <button
            onClick={handleSyncFromArchitecture}
            disabled={isSyncingFromArch || viewMode === 'processed'}
            className={`px-2.5 sm:px-3 py-1.5 text-xs sm:text-sm rounded-lg flex items-center gap-1.5 transition-all duration-200 ${
              !isSyncingFromArch && viewMode === 'raw'
                ? 'bg-surface-700/50 text-surface-300 hover:text-white hover:bg-surface-600 border border-surface-600'
                : 'bg-surface-700/30 text-surface-500 cursor-not-allowed'
            }`}
            title="Inject PDD tags from architecture.json"
          >
            {isSyncingFromArch ? (
              <svg className="animate-spin h-3.5 w-3.5 sm:h-4 sm:w-4" viewBox="0 0 24 24">
                <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
              </svg>
            ) : (
              <svg className="w-3.5 h-3.5 sm:w-4 sm:h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
              </svg>
            )}
            <span className="hidden sm:inline">{isSyncingFromArch ? 'Syncing...' : 'Sync from JSON'}</span>
          </button>
          <button
            onClick={handleSave}
            disabled={!hasChanges || saving || viewMode === 'processed'}
            className={`px-2.5 sm:px-4 py-1.5 text-xs sm:text-sm rounded-lg flex items-center gap-1.5 sm:gap-2 transition-all duration-200 ${
              hasChanges && !saving && viewMode === 'raw'
                ? 'bg-gradient-to-r from-accent-600 to-accent-500 hover:from-accent-500 hover:to-accent-400 text-white shadow-lg shadow-accent-500/25'
                : 'bg-surface-700/50 text-surface-500 cursor-not-allowed'
            }`}
            title={viewMode === 'processed' ? 'Switch to Raw view to save changes' : undefined}
          >
            {saving ? (
              <svg className="animate-spin h-3.5 w-3.5 sm:h-4 sm:w-4" viewBox="0 0 24 24">
                <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
              </svg>
            ) : (
              <svg className="w-3.5 h-3.5 sm:w-4 sm:h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M8 7H5a2 2 0 00-2 2v9a2 2 0 002 2h14a2 2 0 002-2V9a2 2 0 00-2-2h-3m-1 4l-3 3m0 0l-3-3m3 3V4" />
              </svg>
            )}
            <span className="hidden xs:inline">{saving ? 'Saving...' : 'Save'}</span>
          </button>
        </div>
      )}

      {/* Execution status bar - responsive (hidden in embedded mode, App has its own) */}
      {!embedded && executionStatus !== 'idle' && (
        <div className={`
          px-3 sm:px-4 py-2 text-center text-xs sm:text-sm font-medium border-b animate-slide-down
          ${executionStatus === 'running' ? 'bg-accent-500/10 text-accent-300 border-accent-500/20' : ''}
          ${executionStatus === 'success' ? 'bg-green-500/10 text-green-300 border-green-500/20' : ''}
          ${executionStatus === 'failed' ? 'bg-red-500/10 text-red-300 border-red-500/20' : ''}
        `}>
          {executionStatus === 'running' && (
            <span className="flex items-center justify-center gap-2 flex-wrap">
              <svg className="animate-spin h-4 w-4" viewBox="0 0 24 24">
                <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
              </svg>
              <code className="bg-surface-800/80 px-2 py-0.5 rounded text-xs font-mono max-w-[150px] sm:max-w-none truncate">{lastCommand}</code>
              {onCancelCommand && (
                <button
                  onClick={onCancelCommand}
                  className="ml-2 px-2.5 py-1 bg-red-500/20 hover:bg-red-500/30 text-red-300 border border-red-500/30 rounded-lg text-xs font-medium transition-colors"
                >
                  Stop
                </button>
              )}
            </span>
          )}
          {executionStatus === 'success' && <span className="flex items-center justify-center gap-2">
            <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
            </svg>
            Done
          </span>}
          {executionStatus === 'failed' && (
            <div className="flex flex-col items-center gap-2">
              <span className="flex items-center justify-center gap-2">
                <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
                </svg>
                Failed
                {lastRunResult?.exit_code ? ` (exit code: ${lastRunResult.exit_code})` : ''}
              </span>
              {lastRunResult?.error_details && (
                <div className="text-xs text-red-200/80 max-w-xl text-center px-4">
                  {lastRunResult.error_details}
                </div>
              )}
            </div>
          )}
        </div>
      )}

      {/* Main content */}
      <div className="flex-1 flex overflow-hidden relative">
        {/* Mobile sidebar overlay */}
        {sidebarOpen && (
          <div className="lg:hidden fixed inset-0 bg-black/50 z-40 animate-fade-in" onClick={() => setSidebarOpen(false)} />
        )}

        {/* Sidebar with commands - responsive slide-out on mobile, hidden when comparing code */}
        <aside className={`
          ${sidebarOpen ? 'translate-x-0' : '-translate-x-full lg:translate-x-0'}
          ${anyRightPanelOpen ? 'lg:hidden' : ''}
          fixed lg:relative z-50 lg:z-auto
          w-56 sm:w-52 lg:w-48 h-full
          glass lg:bg-surface-800/30 border-r border-surface-700/50
          flex flex-col transition-transform duration-300 ease-out
        `}>
          {/* Mobile close button */}
          <div className="lg:hidden flex items-center justify-between p-3 border-b border-surface-700/50">
            <span className="text-sm font-semibold text-white">Menu</span>
            <button onClick={() => setSidebarOpen(false)} className="p-1.5 text-surface-400 hover:text-white rounded-lg hover:bg-surface-700/50">
              <svg className="w-5 h-5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
              </svg>
            </button>
          </div>

          <div className="p-3 border-b border-surface-700/50 hidden lg:block">
            <h2 className="text-xs font-semibold text-surface-400 uppercase tracking-wider">Commands</h2>
          </div>
          <div className="flex-1 overflow-y-auto">
            {/* Sync + Update Group (highlighted) */}
            <div className="p-2">
              <div className="p-1.5 rounded-xl bg-accent-500/10 border border-accent-500/20 space-y-0.5">
                {regularCommands.filter(cmd => cmd.group === 'sync-update').map(cmd => {
                  const missingFiles = getMissingFiles(cmd);
                  const hasMissingFiles = missingFiles.length > 0;
                  return (
                    <button
                      key={cmd.name}
                      onClick={() => { if (!isExecuting) { handleCommandClick(cmd.name); setSidebarOpen(false); } }}
                      disabled={isExecuting}
                      className={`w-full flex items-center gap-2.5 px-3 py-2.5 rounded-lg text-sm text-left transition-all duration-200 ${
                        isExecuting ? 'text-surface-500 cursor-not-allowed' : 'text-accent-300 hover:bg-accent-500/20 hover:text-white'
                      }`}
                      title={hasMissingFiles ? `${cmd.description} (${missingFiles.join(', ')} file${missingFiles.length > 1 ? 's' : ''} not auto-detected)` : cmd.description}
                    >
                      <span className="text-base">{cmd.icon}</span>
                      <span className="flex-1">{cmd.shortDescription}</span>
                      {hasMissingFiles && (
                        <span className="w-5 h-5 rounded-full bg-yellow-500/20 text-yellow-400 text-xs flex items-center justify-center">!</span>
                      )}
                    </button>
                  );
                })}
              </div>
            </div>

            {/* Generate Group */}
            <div className="px-2 pb-2">
              <div className="p-1.5 rounded-xl bg-surface-700/30 border border-surface-700/50 space-y-0.5">
                {regularCommands.filter(cmd => cmd.group === 'generate').map(cmd => {
                  const missingFiles = getMissingFiles(cmd);
                  const hasMissingFiles = missingFiles.length > 0;
                  return (
                    <button
                      key={cmd.name}
                      onClick={() => { if (!isExecuting) { handleCommandClick(cmd.name); setSidebarOpen(false); } }}
                      disabled={isExecuting}
                      className={`w-full flex items-center gap-2.5 px-3 py-2.5 rounded-lg text-sm text-left transition-all duration-200 ${
                        isExecuting ? 'text-surface-500 cursor-not-allowed' : 'text-surface-300 hover:bg-surface-700/50 hover:text-white'
                      }`}
                      title={hasMissingFiles ? `${cmd.description} (${missingFiles.join(', ')} file${missingFiles.length > 1 ? 's' : ''} not auto-detected)` : cmd.description}
                    >
                      <span className="text-base">{cmd.icon}</span>
                      <span className="flex-1">{cmd.shortDescription}</span>
                      {hasMissingFiles && (
                        <span className="w-5 h-5 rounded-full bg-yellow-500/20 text-yellow-400 text-xs flex items-center justify-center">!</span>
                      )}
                    </button>
                  );
                })}
              </div>
            </div>

            {/* Remainder */}
            <div className="px-2 pb-2 space-y-0.5">
              {regularCommands.filter(cmd => !cmd.group || (cmd.group !== 'sync-update' && cmd.group !== 'generate')).map(cmd => {
                const missingFiles = getMissingFiles(cmd);
                const hasMissingFiles = missingFiles.length > 0;
                return (
                  <button
                    key={cmd.name}
                    onClick={() => { if (!isExecuting) { handleCommandClick(cmd.name); setSidebarOpen(false); } }}
                    disabled={isExecuting}
                    className={`w-full flex items-center gap-2.5 px-3 py-2.5 rounded-lg text-sm text-left transition-all duration-200 ${
                      isExecuting ? 'text-surface-500 cursor-not-allowed' : 'text-surface-300 hover:bg-surface-700/50 hover:text-white'
                    }`}
                    title={hasMissingFiles ? `${cmd.description} (${missingFiles.join(', ')} file${missingFiles.length > 1 ? 's' : ''} not auto-detected)` : cmd.description}
                  >
                    <span className="text-base">{cmd.icon}</span>
                    <span className="flex-1">{cmd.shortDescription}</span>
                    {hasMissingFiles && (
                      <span className="w-5 h-5 rounded-full bg-yellow-500/20 text-yellow-400 text-xs flex items-center justify-center">!</span>
                    )}
                  </button>
                );
              })}
            </div>

            {/* Advanced Operations - Collapsible */}
            {advancedCommands.length > 0 && (
              <div className="border-t border-surface-700/30">
                <button
                  onClick={() => setShowAdvancedCommands(!showAdvancedCommands)}
                  className="w-full p-3 flex items-center justify-between text-left hover:bg-surface-700/30 transition-colors"
                >
                  <span className="text-xs font-semibold text-surface-400 uppercase tracking-wider">
                    Advanced Operations
                  </span>
                  <svg
                    className={`w-4 h-4 text-surface-400 transition-transform duration-200 ${showAdvancedCommands ? 'rotate-180' : ''}`}
                    fill="none"
                    stroke="currentColor"
                    viewBox="0 0 24 24"
                  >
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                  </svg>
                </button>

                {showAdvancedCommands && (
                  <div className="p-2 pt-0 space-y-1">
                    {advancedCommands.map(cmd => {
                      const missingFiles = getMissingFiles(cmd);
                      const hasMissingFiles = missingFiles.length > 0;
                      return (
                        <button
                          key={cmd.name}
                          onClick={() => { if (!isExecuting) { handleCommandClick(cmd.name); setSidebarOpen(false); } }}
                          disabled={isExecuting}
                          className={`w-full flex items-center gap-2.5 px-3 py-2 rounded-lg text-sm text-left transition-all duration-200 ${
                            isExecuting ? 'text-surface-500 cursor-not-allowed' : 'text-surface-300 hover:bg-surface-700/50 hover:text-white'
                          }`}
                          title={cmd.description}
                        >
                          <span className="text-surface-500 text-xs">{cmd.icon}</span>
                          <span className="flex-1 text-xs">{cmd.shortDescription}</span>
                          {hasMissingFiles && (
                            <span className="w-4 h-4 rounded-full bg-yellow-500/20 text-yellow-400 text-[10px] flex items-center justify-center">!</span>
                          )}
                        </button>
                      );
                    })}
                  </div>
                )}
              </div>
            )}
          </div>

          {/* File info */}
          <div className="p-3 border-t border-surface-700/50 space-y-2">
            <h3 className="text-xs font-semibold text-surface-400 uppercase tracking-wider">Files</h3>
            <div className="space-y-1.5 text-xs">
              <FileLink label="Prompt" path={prompt.prompt} exists={true} />
              <FileLink label="Code" path={prompt.code} exists={!!prompt.code} />
              <FileLink label="Test" path={prompt.test} exists={!!prompt.test} />
              <FileLink label="Example" path={prompt.example} exists={!!prompt.example} />
            </div>
          </div>
        </aside>

        {/* Editor area */}
        <main className="flex-1 flex flex-col overflow-hidden min-w-0">
          {loading ? (
            <div className="flex-1 flex flex-col items-center justify-center">
              <div className="w-10 h-10 rounded-xl bg-accent-500/20 flex items-center justify-center mb-4">
                <svg className="animate-spin h-5 w-5 text-accent-400" viewBox="0 0 24 24">
                  <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                  <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                </svg>
              </div>
              <div className="text-surface-400 text-sm">Loading prompt...</div>
            </div>
          ) : error && content === null ? (
            <div className="flex-1 flex flex-col items-center justify-center">
              <div className="w-12 h-12 rounded-xl bg-red-500/20 flex items-center justify-center mb-4">
                <svg className="w-6 h-6 text-red-400" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
                </svg>
              </div>
              <div className="text-red-400 mb-2">{error}</div>
              <button onClick={() => window.location.reload()} className="px-4 py-2 bg-surface-700/50 hover:bg-surface-600 rounded-xl text-sm text-white transition-colors border border-surface-600">Retry</button>
            </div>
          ) : (
            <>
              {/* Metrics bar with view toggle */}
              <PromptMetricsBar
                rawMetrics={analysisResult?.raw_metrics || null}
                processedMetrics={analysisResult?.processed_metrics || null}
                viewMode={viewMode}
                onViewModeChange={handleViewModeChange}
                isLoading={isAnalyzing}
                preprocessingError={analysisResult?.preprocessing_error}
                timeValue={timeValue}
                promptLineCount={content ? content.split('\n').length : undefined}
                codeLineCount={codeContent ? codeContent.split('\n').length : undefined}
                selectedModel={selectedModel}
                showCodePanel={showCodePanel}
                onToggleCodePanel={handleToggleCodePanel}
                hasCodeFile={!!prompt.code}
                showTestPanel={showTestPanel}
                onToggleTestPanel={handleToggleTestPanel}
                hasTestFile={!!prompt.test}
                showExamplePanel={showExamplePanel}
                onToggleExamplePanel={handleToggleExamplePanel}
                hasExampleFile={!!prompt.example}
                showPreview={showPreview}
                onTogglePreview={() => setShowPreview(!showPreview)}
                onShowDiff={handleShowDiff}
              />

              {/* Model Selection sliders (collapsible) */}
              <ModelSliders
                models={ALL_MODELS}
                strength={strength}
                onStrengthChange={setStrength}
                time={timeValue}
                onTimeChange={setTimeValue}
                temperature={temperature}
                onTemperatureChange={setTemperature}
                resolvedModel={selectedModel}
              />

              {/* Editor path bar - responsive */}
              <div className="px-3 sm:px-4 py-2 bg-surface-800/30 border-b border-surface-700/50 text-xs sm:text-sm text-surface-400 font-mono flex items-center gap-2 overflow-hidden">
                <span className="truncate flex-1">{prompt.prompt}</span>
                {viewMode === 'processed' && (
                  <span className="px-2 py-0.5 rounded-full text-[10px] sm:text-xs bg-yellow-500/15 text-yellow-300 border border-yellow-500/30 flex-shrink-0">Read Only</span>
                )}
                {/* Analyze Include button */}
                <button
                  onClick={analyzeIncludeAtCursor}
                  disabled={showPreview}
                  className={`flex items-center gap-1.5 px-2.5 py-1 rounded-lg text-xs font-medium transition-all duration-200 flex-shrink-0 ${
                    showPreview
                      ? 'bg-surface-700/30 text-surface-500 cursor-not-allowed'
                      : 'bg-surface-700/50 text-surface-300 hover:bg-surface-600 hover:text-white'
                  }`}
                  title="Analyze include tag at cursor (Cmd+.)"
                >
                  <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 19v-6a2 2 0 00-2-2H5a2 2 0 00-2 2v6a2 2 0 002 2h2a2 2 0 002-2zm0 0V9a2 2 0 012-2h2a2 2 0 012 2v10m-6 0a2 2 0 002 2h2a2 2 0 002-2m0 0V5a2 2 0 012-2h2a2 2 0 012 2v14a2 2 0 01-2 2h-2a2 2 0 01-2-2z" />
                  </svg>
                  <span className="hidden sm:inline">Tokens</span>
                </button>
                {/* Guide toggle button */}
                <button
                  onClick={() => setGuidanceSidebarOpen(!guidanceSidebarOpen)}
                  className={`flex items-center gap-1.5 px-2.5 py-1 rounded-lg text-xs font-medium transition-all duration-200 flex-shrink-0 ${
                    guidanceSidebarOpen
                      ? 'bg-accent-600 text-white'
                      : 'bg-surface-700/50 text-surface-300 hover:bg-surface-600 hover:text-white'
                  }`}
                  title={guidanceSidebarOpen ? 'Hide prompting guide' : 'Show prompting guide'}
                >
                  <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M13 16h-1v-4h-1m1-4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
                  </svg>
                  <span className="hidden sm:inline">Guide</span>
                </button>
              </div>

              {/* Editor or Preview with optional right panels */}
              <div className="flex-1 flex overflow-hidden">
                {/* Main Editor / Preview Panel */}
                <div className={`flex-1 flex flex-col overflow-hidden ${anyRightPanelOpen ? 'flex-1' : 'w-full'}`}>
                  {showPreview ? (
                    <div className="flex-1 overflow-auto bg-surface-900/50 p-4 sm:p-6 lg:p-8">
                      <div
                        className="markdown-body max-w-4xl mx-auto"
                        dangerouslySetInnerHTML={{ __html: renderedMarkdown }}
                      />
                    </div>
                  ) : (
                    <div ref={editorContainerRef} className="flex-1 overflow-hidden" />
                  )}
                </div>

                {/* Vertical Command Bar - prompt <-> code (Sync/Update) + other commands */}
                {anyRightPanelOpen && (
                  <div className="flex flex-col items-center justify-center py-4 px-1 bg-surface-800/50 border-x border-surface-700/50">
                    <div className="flex flex-col gap-1">
                      {/* Generate: prompt → code */}
                      {showCodePanel && (
                        <div className="flex flex-col gap-1 p-1.5 rounded-xl bg-accent-500/10 border border-accent-500/20">
                          <button
                            onClick={() => { if (!isExecuting) handleCommandClick(CommandType.GENERATE); }}
                            disabled={isExecuting}
                            className={`flex flex-col items-center gap-1 p-2 rounded-lg text-xs font-medium transition-all duration-200 min-w-[52px] ${
                              isExecuting ? 'text-surface-500 cursor-not-allowed' : 'text-accent-300 hover:bg-accent-500/20 hover:text-white'
                            }`}
                            title="Generate: prompt → code"
                          >
                            <svg className="w-5 h-5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M14 5l7 7m0 0l-7 7m7-7H3" />
                            </svg>
                            <span className="text-[10px] leading-tight text-center">Generate</span>
                          </button>
                          <button
                            onClick={() => { if (!isExecuting) handleCommandClick(CommandType.UPDATE); }}
                            disabled={isExecuting}
                            className={`flex flex-col items-center gap-1 p-2 rounded-lg text-xs font-medium transition-all duration-200 min-w-[52px] ${
                              isExecuting ? 'text-surface-500 cursor-not-allowed' : 'text-accent-300 hover:bg-accent-500/20 hover:text-white'
                            }`}
                            title="Update: code → prompt"
                          >
                            <svg className="w-5 h-5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M10 19l-7-7m0 0l7-7m-7 7h18" />
                            </svg>
                            <span className="text-[10px] leading-tight text-center">Update</span>
                          </button>
                        </div>
                      )}

                      {/* Other commands (Fix, Verify, etc.) */}
                      {commandBarCommands.length > 0 && (
                        <>
                          <div className="h-2" />
                          <div className="flex flex-col gap-1 p-1.5 rounded-xl bg-surface-700/30 border border-surface-700/50">
                            {commandBarCommands.map(cmd => {
                              const missingFiles = getMissingFiles(cmd);
                              const hasMissingFiles = missingFiles.length > 0;
                              return (
                                <button
                                  key={cmd.name}
                                  onClick={() => { if (!isExecuting) handleCommandClick(cmd.name); }}
                                  disabled={isExecuting}
                                  className={`flex flex-col items-center gap-1 p-2 rounded-lg text-xs font-medium transition-all duration-200 min-w-[52px] ${
                                    isExecuting ? 'text-surface-500 cursor-not-allowed' : 'text-surface-400 hover:bg-surface-700/70 hover:text-white'
                                  }`}
                                  title={hasMissingFiles ? `${cmd.description} (${missingFiles.join(', ')} not auto-detected)` : cmd.description}
                                >
                                  <span className="text-lg relative">
                                    {cmd.icon}
                                    {hasMissingFiles && (
                                      <span className="absolute -top-1 -right-1 w-2.5 h-2.5 rounded-full bg-yellow-500/80"></span>
                                    )}
                                  </span>
                                  <span className="text-[10px] leading-tight text-center">{cmd.shortDescription}</span>
                                </button>
                              );
                            })}
                          </div>
                        </>
                      )}
                    </div>
                  </div>
                )}

                {/* Right Panels - stacked vertically with inter-panel action arrows */}
                {anyRightPanelOpen && (
                  <div className="flex-1 flex flex-col bg-surface-900/50 overflow-hidden">
                    {/* Code Panel */}
                    {showCodePanel && (
                      <div className={`flex flex-col ${codeCollapsed ? '' : 'flex-1 min-h-0'}`}>
                        <div className="px-3 py-2 bg-surface-800/50 border-b border-surface-700/50 flex items-center justify-between flex-shrink-0 cursor-pointer" onClick={() => setCodeCollapsed(!codeCollapsed)}>
                          <div className="flex items-center gap-2 min-w-0">
                            <svg className={`w-3 h-3 text-surface-400 transition-transform ${codeCollapsed ? '-rotate-90' : ''}`} fill="none" stroke="currentColor" viewBox="0 0 24 24">
                              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                            </svg>
                            <svg className="w-4 h-4 text-blue-400 flex-shrink-0" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M10 20l4-16m4 4l4 4-4 4M6 16l-4-4 4-4" />
                            </svg>
                            <span className="text-xs text-surface-400 font-mono truncate" title={prompt.code || ''}>
                              {prompt.code?.split('/').pop() || 'Code'}
                            </span>
                            <span className="px-1.5 py-0.5 rounded text-[10px] bg-blue-500/20 text-blue-300 flex-shrink-0">Read Only</span>
                          </div>
                          <div className="flex items-center gap-1" onClick={e => e.stopPropagation()}>
                            <button onClick={handleReloadCode} disabled={codeLoading} className="p-1.5 text-surface-400 hover:text-white hover:bg-surface-700 rounded transition-colors" title="Reload">
                              <svg className={`w-3.5 h-3.5 ${codeLoading ? 'animate-spin' : ''}`} fill="none" stroke="currentColor" viewBox="0 0 24 24">
                                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
                              </svg>
                            </button>
                            <button onClick={() => setShowCodePanel(false)} className="p-1.5 text-surface-400 hover:text-white hover:bg-surface-700 rounded transition-colors" title="Close">
                              <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
                              </svg>
                            </button>
                          </div>
                        </div>
                        {!codeCollapsed && (
                          codeLoading ? (
                            <div className="flex-1 flex items-center justify-center py-8">
                              <svg className="animate-spin h-5 w-5 text-blue-400" viewBox="0 0 24 24"><circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" /><path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" /></svg>
                            </div>
                          ) : codeError ? (
                            <div className="flex-1 flex items-center justify-center py-4">
                              <span className="text-xs text-red-300">{codeError}</span>
                            </div>
                          ) : (
                            <div ref={codeEditorContainerRef} className="flex-1 overflow-hidden" />
                          )
                        )}
                      </div>
                    )}

                    {/* Arrow: prompt + code → test */}
                    {showCodePanel && showTestPanel && (
                      <div className="flex items-center justify-center py-1 px-2 bg-surface-800/30 border-y border-surface-700/30 flex-shrink-0">
                        <button
                          onClick={() => { if (!isExecuting) handleCommandClick(CommandType.TEST); }}
                          disabled={isExecuting}
                          className={`flex items-center gap-1.5 px-3 py-1 rounded-lg text-[10px] font-medium transition-all duration-200 ${
                            isExecuting ? 'text-surface-500 cursor-not-allowed' : 'text-yellow-300 hover:bg-yellow-500/20 hover:text-white'
                          }`}
                          title="Generate test from prompt + code"
                        >
                          <span className="text-[10px] text-surface-500">prompt + code</span>
                          <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 14l-7 7m0 0l-7-7m7 7V3" />
                          </svg>
                          <span>Gen Test</span>
                        </button>
                      </div>
                    )}

                    {/* Test Panel */}
                    {showTestPanel && (
                      <div className={`flex flex-col ${testCollapsed ? '' : 'flex-1 min-h-0'}`}>
                        <div className="px-3 py-2 bg-surface-800/50 border-b border-surface-700/50 flex items-center justify-between flex-shrink-0 cursor-pointer" onClick={() => setTestCollapsed(!testCollapsed)}>
                          <div className="flex items-center gap-2 min-w-0">
                            <svg className={`w-3 h-3 text-surface-400 transition-transform ${testCollapsed ? '-rotate-90' : ''}`} fill="none" stroke="currentColor" viewBox="0 0 24 24">
                              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                            </svg>
                            <svg className="w-4 h-4 text-yellow-400 flex-shrink-0" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5H7a2 2 0 00-2 2v12a2 2 0 002 2h10a2 2 0 002-2V7a2 2 0 00-2-2h-2M9 5a2 2 0 002 2h2a2 2 0 002-2M9 5a2 2 0 012-2h2a2 2 0 012 2m-6 9l2 2 4-4" />
                            </svg>
                            <span className="text-xs text-surface-400 font-mono truncate" title={prompt.test || ''}>
                              {prompt.test?.split('/').pop() || 'Test'}
                            </span>
                            <span className="px-1.5 py-0.5 rounded text-[10px] bg-yellow-500/20 text-yellow-300 flex-shrink-0">Read Only</span>
                          </div>
                          <div className="flex items-center gap-1" onClick={e => e.stopPropagation()}>
                            <button onClick={() => loadTestContent()} disabled={testLoading} className="p-1.5 text-surface-400 hover:text-white hover:bg-surface-700 rounded transition-colors" title="Reload">
                              <svg className={`w-3.5 h-3.5 ${testLoading ? 'animate-spin' : ''}`} fill="none" stroke="currentColor" viewBox="0 0 24 24">
                                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
                              </svg>
                            </button>
                            <button onClick={() => setShowTestPanel(false)} className="p-1.5 text-surface-400 hover:text-white hover:bg-surface-700 rounded transition-colors" title="Close">
                              <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
                              </svg>
                            </button>
                          </div>
                        </div>
                        {!testCollapsed && (
                          testLoading ? (
                            <div className="flex-1 flex items-center justify-center py-8">
                              <svg className="animate-spin h-5 w-5 text-yellow-400" viewBox="0 0 24 24"><circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" /><path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" /></svg>
                            </div>
                          ) : testError ? (
                            <div className="flex-1 flex items-center justify-center py-4">
                              <span className="text-xs text-red-300">{testError}</span>
                            </div>
                          ) : (
                            <div ref={testEditorContainerRef} className="flex-1 overflow-hidden" />
                          )
                        )}
                      </div>
                    )}

                    {/* Arrow: prompt + code → example */}
                    {showCodePanel && showExamplePanel && (
                      <div className="flex items-center justify-center py-1 px-2 bg-surface-800/30 border-y border-surface-700/30 flex-shrink-0">
                        <button
                          onClick={() => { if (!isExecuting) handleCommandClick(CommandType.EXAMPLE); }}
                          disabled={isExecuting}
                          className={`flex items-center gap-1.5 px-3 py-1 rounded-lg text-[10px] font-medium transition-all duration-200 ${
                            isExecuting ? 'text-surface-500 cursor-not-allowed' : 'text-green-300 hover:bg-green-500/20 hover:text-white'
                          }`}
                          title="Generate example from prompt + code"
                        >
                          <span className="text-[10px] text-surface-500">prompt + code</span>
                          <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 14l-7 7m0 0l-7-7m7 7V3" />
                          </svg>
                          <span>Gen Example</span>
                        </button>
                      </div>
                    )}

                    {/* Example Panel */}
                    {showExamplePanel && (
                      <div className={`flex flex-col ${exampleCollapsed ? '' : 'flex-1 min-h-0'}`}>
                        <div className="px-3 py-2 bg-surface-800/50 border-b border-surface-700/50 flex items-center justify-between flex-shrink-0 cursor-pointer" onClick={() => setExampleCollapsed(!exampleCollapsed)}>
                          <div className="flex items-center gap-2 min-w-0">
                            <svg className={`w-3 h-3 text-surface-400 transition-transform ${exampleCollapsed ? '-rotate-90' : ''}`} fill="none" stroke="currentColor" viewBox="0 0 24 24">
                              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M19 9l-7 7-7-7" />
                            </svg>
                            <svg className="w-4 h-4 text-green-400 flex-shrink-0" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 6.253v13m0-13C10.832 5.477 9.246 5 7.5 5S4.168 5.477 3 6.253v13C4.168 18.477 5.754 18 7.5 18s3.332.477 4.5 1.253m0-13C13.168 5.477 14.754 5 16.5 5c1.747 0 3.332.477 4.5 1.253v13C19.832 18.477 18.247 18 16.5 18c-1.746 0-3.332.477-4.5 1.253" />
                            </svg>
                            <span className="text-xs text-surface-400 font-mono truncate" title={prompt.example || ''}>
                              {prompt.example?.split('/').pop() || 'Example'}
                            </span>
                            <span className="px-1.5 py-0.5 rounded text-[10px] bg-green-500/20 text-green-300 flex-shrink-0">Read Only</span>
                          </div>
                          <div className="flex items-center gap-1" onClick={e => e.stopPropagation()}>
                            <button onClick={() => loadExampleContent()} disabled={exampleLoading} className="p-1.5 text-surface-400 hover:text-white hover:bg-surface-700 rounded transition-colors" title="Reload">
                              <svg className={`w-3.5 h-3.5 ${exampleLoading ? 'animate-spin' : ''}`} fill="none" stroke="currentColor" viewBox="0 0 24 24">
                                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" />
                              </svg>
                            </button>
                            <button onClick={() => setShowExamplePanel(false)} className="p-1.5 text-surface-400 hover:text-white hover:bg-surface-700 rounded transition-colors" title="Close">
                              <svg className="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
                              </svg>
                            </button>
                          </div>
                        </div>
                        {!exampleCollapsed && (
                          exampleLoading ? (
                            <div className="flex-1 flex items-center justify-center py-8">
                              <svg className="animate-spin h-5 w-5 text-green-400" viewBox="0 0 24 24"><circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" /><path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" /></svg>
                            </div>
                          ) : exampleError ? (
                            <div className="flex-1 flex items-center justify-center py-4">
                              <span className="text-xs text-red-300">{exampleError}</span>
                            </div>
                          ) : (
                            <div ref={exampleEditorContainerRef} className="flex-1 overflow-hidden" />
                          )
                        )}
                      </div>
                    )}
                  </div>
                )}
              </div>

              {/* Error bar */}
              {error && (
                <div className="px-3 sm:px-4 py-2 bg-red-500/10 border-t border-red-500/20 text-red-300 text-xs sm:text-sm">{error}</div>
              )}
            </>
          )}
        </main>


        {/* Guidance Sidebar */}
        <GuidanceSidebar
          isOpen={guidanceSidebarOpen}
          onClose={() => setGuidanceSidebarOpen(false)}
        />
      </div>

      {/* Command Options Modal */}
      {modalCommand && (
        <CommandOptionsModal
          command={modalCommand}
          prompt={prompt}
          onRun={handleRunWithOptions}
          onAddToQueue={onAddToQueue ? handleAddToQueueWithOptions : undefined}
          onCancel={() => setModalCommand(null)}
          currentGlobalValues={{ strength, time: timeValue, temperature }}
        />
      )}

      {/* Include Analysis Popup */}
      {includeAnalysis.visible && (
        <div className="fixed bottom-4 right-4 z-50 animate-slide-up">
          <div className="bg-surface-800 border border-surface-600 rounded-xl shadow-2xl p-4 w-80">
            <div className="flex items-center justify-between mb-3">
              <h4 className="text-sm font-semibold text-white flex items-center gap-2">
                <svg className="w-4 h-4 text-accent-400" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 19v-6a2 2 0 00-2-2H5a2 2 0 00-2 2v6a2 2 0 002 2h2a2 2 0 002-2zm0 0V9a2 2 0 012-2h2a2 2 0 012 2v10m-6 0a2 2 0 002 2h2a2 2 0 002-2m0 0V5a2 2 0 012-2h2a2 2 0 012 2v14a2 2 0 01-2 2h-2a2 2 0 01-2-2z" />
                </svg>
                Include Analysis
              </h4>
              <button
                onClick={closeIncludeAnalysis}
                className="p-1 rounded hover:bg-surface-700 text-surface-400 hover:text-white transition-colors"
              >
                <svg className="w-4 h-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
                </svg>
              </button>
            </div>

            {includeAnalysis.loading ? (
              <div className="flex items-center justify-center py-4">
                <svg className="animate-spin h-5 w-5 text-accent-400" viewBox="0 0 24 24">
                  <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                  <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
                </svg>
                <span className="ml-2 text-sm text-surface-400">Analyzing...</span>
              </div>
            ) : includeAnalysis.error ? (
              <div className="text-sm text-surface-400 bg-surface-900/50 rounded-lg p-3">
                {includeAnalysis.error}
              </div>
            ) : includeAnalysis.metrics && includeAnalysis.tagInfo ? (
              <div className="space-y-3">
                <div className="bg-surface-900/50 rounded-lg p-3">
                  <div className="text-xs text-surface-500 mb-1">File</div>
                  <div className="text-sm text-white font-mono truncate">{includeAnalysis.tagInfo.path}</div>
                </div>
                <div className="grid grid-cols-2 gap-3">
                  <div className="bg-surface-900/50 rounded-lg p-3">
                    <div className="text-xs text-surface-500 mb-1">Tokens</div>
                    <div className="text-lg font-semibold text-accent-400">
                      {includeAnalysis.metrics.token_count.toLocaleString()}
                    </div>
                  </div>
                  <div className="bg-surface-900/50 rounded-lg p-3">
                    <div className="text-xs text-surface-500 mb-1">Context Usage</div>
                    <div className="text-lg font-semibold text-white">
                      {includeAnalysis.metrics.context_usage_percent.toFixed(1)}%
                    </div>
                  </div>
                </div>
                {includeAnalysis.metrics.cost_estimate && (
                  <div className="bg-surface-900/50 rounded-lg p-3">
                    <div className="text-xs text-surface-500 mb-1">Estimated Cost</div>
                    <div className="text-sm text-green-400">
                      ${includeAnalysis.metrics.cost_estimate.input_cost.toFixed(4)} USD
                    </div>
                  </div>
                )}
              </div>
            ) : null}

            <div className="mt-3 pt-3 border-t border-surface-700">
              <p className="text-[10px] text-surface-500">
                Press <kbd className="px-1 py-0.5 bg-surface-700 rounded text-surface-400">Cmd+.</kbd> to analyze include at cursor
              </p>
            </div>
          </div>
        </div>
      )}

      {/* Diff Analysis Modal */}
      <PromptCodeDiffModal
        isOpen={showDiffModal}
        onClose={() => setShowDiffModal(false)}
        promptContent={
          editorViewRef.current
            ? editorViewRef.current.state.doc.toString()
            : editedContentRef.current || content || ''
        }
        codeContent={codeContent || ''}
        promptPath={prompt?.prompt}
        codePath={prompt?.code}
        prompt={prompt}
        onRunCommand={onRunCommand}
      />
    </div>
  );
};

// Small component for file links in sidebar - modernized
const FileLink: React.FC<{ label: string; path?: string; exists: boolean }> = ({ label, path, exists }) => (
  <div className={`flex items-center gap-2 ${exists ? 'text-surface-300' : 'text-surface-500'}`}>
    <span className={`w-4 h-4 rounded flex items-center justify-center text-[10px] ${exists ? 'bg-green-500/20 text-green-400' : 'bg-surface-700/50 text-surface-500'}`}>
      {exists ? '✓' : '✗'}
    </span>
    <span>{label}</span>
  </div>
);

export default PromptSpace;
